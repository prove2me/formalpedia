-- Prove2me | Definitions.Def_MaxIsoVertexCuts_Shredders_GraphData
-- name    : MaxIsoVertexCuts_Shredders_GraphData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:54:39.696381+00:00
-- url     : https://prove2.me/theorems/14cbd45a-3e69-435c-968f-15b46a83ab94
-- title:
--   GraphData
-- statement:
--   A graph input is n,m and an arbitrary duplicate-free edge list, each edge oriented by increasing label, representing a connected simple graph. Certificates and collections are explicitly framed vertex lists, with arbitrary order permitted on output; malformed output never satisfies validity. Listing validity requires genuine k-shredders and valid certificates; listing completeness simultaneously requires κ, exactly all minimum shredders and complete certificates. Section 5, printed pp.28–31 (PDF 30–33). Internal collection outputs additionally support fully serialized shared dictionaries, as specified on printed pp.28 and 39–41; the final listing output is always explicit.
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission, Sections 2–5; machine conventions specified in the mission.

import Mathlib
import Definitions.Def_MaxIsoVertexCuts_Shredders_Representations
import Definitions.Def_CongruencyTU_Machine

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

structure GraphData where
  n : ℕ
  G : SimpleGraph (Fin n)
  edges : List (Fin n × Fin n)

def GraphData.m (I : GraphData) : ℕ := I.edges.length

def GraphData.Valid (I : GraphData) : Prop :=
  I.G.Connected ∧ I.edges.Nodup ∧ (∀ e ∈ I.edges, e.1 < e.2) ∧
  ∀ u v, I.G.Adj u v ↔ (u,v) ∈ I.edges ∨ (v,u) ∈ I.edges

def GraphData.encode (I : GraphData) : List ℤ :=
  ([I.n, I.m] : List ℤ) ++ I.edges.flatMap (fun e => [(e.1.val : ℤ), (e.2.val : ℤ)])

noncomputable def encSet {n : ℕ} (S : VSet n) : List ℤ :=
  (S.sort (· ≤ ·)).map fun v => (v.val : ℤ)
noncomputable def EncCert {n : ℕ} (S : VSet n) (z : Certificate n) (out : List ℤ) : Prop :=
  ∃ (ss ws : List (Fin n)) (cc : List (List (Fin n))),
    ss.Nodup ∧ ss.toFinset = S ∧ ws.Nodup ∧ ws.toFinset = z.W ∧
    (∀ l ∈ cc, l.Nodup) ∧ (cc.map List.toFinset).Nodup ∧
    (cc.map List.toFinset).toFinset = z.C ∧
    out = CongruencyTU.pack [ss.map (fun v => (v.val : ℤ)),
      CongruencyTU.pack (cc.map fun l => l.map fun v => (v.val : ℤ)),
      ws.map (fun v => (v.val : ℤ))]

noncomputable def EncCollection {n : ℕ} (zs : List (VSet n × Certificate n))
    (out : List ℤ) : Prop :=
  ∃ blocks : List (List ℤ), List.Forall₂ (fun z b => EncCert z.1 z.2 b) zs blocks ∧
    out = CongruencyTU.pack blocks


structure CollectionRow (n ns nc : ℕ) where
  separator : Fin ns
  components : Fin nc
  witnesses : VSet n


noncomputable def EncSharedCollection {n : ℕ} (zs : List (VSet n × Certificate n))
    (out : List ℤ) : Prop :=
  ∃ (seps : List (List (Fin n))) (comps : List (List (List (Fin n))))
    (rows : List (CollectionRow n seps.length comps.length)),
    (∀ s ∈ seps, s.Nodup) ∧
    (∀ cs ∈ comps, (∀ C ∈ cs, C.Nodup) ∧ (cs.map List.toFinset).Nodup) ∧
    zs = rows.map (fun r => ((seps.get r.separator).toFinset,
      ⟨((comps.get r.components).map List.toFinset).toFinset,r.witnesses⟩)) ∧
    out = CongruencyTU.pack [CongruencyTU.pack (seps.map fun vs => vs.map fun v => (v.val : ℤ)),
      CongruencyTU.pack (comps.map fun cs => CongruencyTU.pack
        (cs.map fun vs => vs.map fun v => (v.val : ℤ))),
      CongruencyTU.pack (rows.map fun r =>
        [(r.separator.val : ℤ), (r.components.val : ℤ)] ++ encSet r.witnesses)]

noncomputable def sharedCollectionValid {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (out : List ℤ) : Prop :=
  ∃ zs, EncSharedCollection zs out ∧
    ∀ z ∈ zs, IsKShredder G k z.1 ∧ ValidCertificate G z.1 z.2

noncomputable def collectionValid {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (out : List ℤ) : Prop :=
  ∃ zs, EncCollection zs out ∧
    ∀ z ∈ zs, IsKShredder G k z.1 ∧ ValidCertificate G z.1 z.2

noncomputable def listingValid (I : GraphData) (out : List ℤ) : Prop :=
  ∃ k : ℕ, ∃ rest, out = (k : ℤ) :: rest ∧ collectionValid I.G k rest

noncomputable def listingComplete (I : GraphData) (out : List ℤ) : Prop :=
  ∃ zs, EncCollection zs (out.drop 1) ∧ out.head? = some (kappa I.G : ℤ) ∧
    (∀ z ∈ zs, IsKShredder I.G (kappa I.G) z.1 ∧ Complete I.G z.1 z.2) ∧
    ∀ S, IsKShredder I.G (kappa I.G) S → ∃ z ∈ zs, z.1 = S

noncomputable def minDegree (I : GraphData) : ℕ :=
  if h : Nonempty (Fin I.n) then
    (Finset.univ.image fun v : Fin I.n => (HypRecov.nbhd I.G {v}).card).min'
      (by let := h; exact Finset.Nonempty.image Finset.univ_nonempty _)
  else 0

end MaxIsoVertexCuts.Shredders


