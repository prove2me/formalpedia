-- Prove2me | Definitions.Def_MaxIsoVertexCuts_Shredders_WeightedInputs
-- name    : MaxIsoVertexCuts_Shredders_WeightedInputs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:57:39.53578+00:00
-- url     : https://prove2.me/theorems/c8521f8e-add4-4da8-be1f-e76f96802485
-- title:
--   WeightedInputs
-- statement:
--   Positive integral input weights have a polynomial bound n^d with d fixed before the input. Weighted and terminal-set encodings use explicit lists. Maximal isolating output includes, for every terminal, its maximal shore, separator and all edges incident to the shore. Source-sink Steiner output always consists of genuine minimum source-sink Steiner shredders and valid certificates, and is complete when the two connectivity values agree. Isolating Steiner output has precisely the certificate shape and conditional T-terminal completeness of Lemma 5.16. Terminal entries and output lists may be ordered arbitrarily. Lemma 5.16 uses explicit shared dictionaries of separators and component lists, with terminal/separator-index/component-list-index/other-terminal rows; the serialized dictionary and all rows count toward the output length. This sharing is permitted on printed pp.28 and 34. Other output contracts remain explicit lists.
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission, Sections 2–5; machine conventions specified in the mission.

import Mathlib
import Definitions.Def_MaxIsoVertexCuts_Shredders_VertexFlow

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

def BoundedWeights (I : GraphData) (d : ℕ) (w : Fin I.n → ℕ) : Prop :=
  ∀ v, 0 < w v ∧ w v ≤ I.n ^ d

def realWeights {n : ℕ} (w : Fin n → ℕ) : Fin n → ℝ := fun v => w v

def encWeighted (I : GraphData) (w : Fin I.n → ℕ) : List ℤ :=
  I.encode ++ List.ofFn (fun v => (w v : ℤ))

noncomputable def encTerminals (I : GraphData) (w : Fin I.n → ℕ) (T : VSet I.n) : List ℤ :=
  encWeighted I w ++ CongruencyTU.pack [encSet T]

noncomputable def logarithmicFactor {α : Type*} (T : Finset α) : ℕ := max 1 ⌈logTwo T.card⌉₊

noncomputable def isolatingOutput (I : GraphData) (w : Fin I.n → ℕ) (T : VSet I.n)
    (out : List ℤ) : Prop :=
  ∃ (cuts : Fin I.n → Cut I.n) (order : List (Fin I.n)) (ls ss : Fin I.n → List (Fin I.n))
    (es : Fin I.n → List (Fin I.n × Fin I.n)),
    order.Nodup ∧ order.toFinset = T ∧
    (∀ t ∈ T, IsMaxMinCut I.G (realWeights w) T {t} (cuts t) ∧
      (ls t).Nodup ∧ (ls t).toFinset = (cuts t).L ∧
      (ss t).Nodup ∧ (ss t).toFinset = (cuts t).S ∧ (es t).Nodup ∧
      ∀ e, e ∈ es t ↔ e ∈ I.edges ∧ (e.1 ∈ (cuts t).L ∨ e.2 ∈ (cuts t).L)) ∧
    out = CongruencyTU.pack (order.map fun t =>
      (t.val : ℤ) :: CongruencyTU.pack [
        (ls t).map (fun v => (v.val : ℤ)), (ss t).map (fun v => (v.val : ℤ)),
        (es t).flatMap (fun e => [(e.1.val : ℤ), (e.2.val : ℤ)])])

noncomputable def stOutput (I : GraphData) (w : Fin I.n → ℕ) (U : VSet I.n)
    (s t : Fin I.n) (out : List ℤ) : Prop :=
  ∃ zs, EncCollection zs out ∧
    (∀ z ∈ zs, STShredder I.G (realWeights w) U s t z.1 ∧ ValidSteinerCertificate I.G U z.1 z.2) ∧
    (stKappa I.G (realWeights w) s t = steinerKappa I.G (realWeights w) U →
      ∀ S, STShredder I.G (realWeights w) U s t S →
        ∃ z ∈ zs, z.1 = S ∧ SteinerComplete I.G U S z.2)


structure SharedRow (n ns nc : ℕ) where
  terminal : Fin n
  separator : Fin ns
  components : Fin nc
  witness : Fin n

structure SharedCertificates (n : ℕ) where
  separators : List (List (Fin n))
  componentLists : List (List (List (Fin n)))
  rows : List (SharedRow n separators.length componentLists.length)

noncomputable def SharedCertificates.encode {n : ℕ} (D : SharedCertificates n) : List ℤ :=
  CongruencyTU.pack [
    CongruencyTU.pack (D.separators.map fun vs => vs.map fun v => (v.val : ℤ)),
    CongruencyTU.pack (D.componentLists.map fun cs => CongruencyTU.pack
      (cs.map fun vs => vs.map fun v => (v.val : ℤ))),
    D.rows.flatMap fun r => [(r.terminal.val : ℤ), (r.separator.val : ℤ),
      (r.components.val : ℤ), (r.witness.val : ℤ)]]

noncomputable def SharedCertificates.entries {n : ℕ} (D : SharedCertificates n) :
    List (Fin n × VSet n × Certificate n) :=
  D.rows.map fun r => (r.terminal, (D.separators.get r.separator).toFinset,
    ⟨((D.componentLists.get r.components).map List.toFinset).toFinset, {r.terminal,r.witness}⟩)

noncomputable def isolatingSteinerOutput (I : GraphData) (w : Fin I.n → ℕ)
    (U T : VSet I.n) (k : ℤ) (out : List ℤ) : Prop :=
  ∃ D : SharedCertificates I.n, D.encode = out ∧
    (∀ s ∈ D.separators, s.Nodup) ∧
    (∀ cs ∈ D.componentLists, (∀ C ∈ cs, C.Nodup) ∧ (cs.map List.toFinset).Nodup) ∧
    (∀ r ∈ D.rows, r.terminal ∈ T ∧ r.witness ∈ T ∧ r.witness ≠ r.terminal) ∧
    (∀ z ∈ D.entries,
      IsolatingSteinerShredder I.G (realWeights w) U T z.1 z.2.1 ∧
      weight (realWeights w) z.2.1 = k ∧ ValidSteinerCertificate I.G U z.2.1 z.2.2 ∧
      ∀ C ∈ z.2.2.C, Disjoint C T) ∧
    (ENNReal.ofReal (k : ℝ) = steinerKappa I.G (realWeights w) U →
      ∀ t ∈ T, ∀ S, IsolatingSteinerShredder I.G (realWeights w) U T t S →
        weight (realWeights w) S = k → ∃ z ∈ D.entries,
          z.1 = t ∧ z.2.1 = S ∧ TerminalComplete I.G U T S z.2.2)

end MaxIsoVertexCuts.Shredders


