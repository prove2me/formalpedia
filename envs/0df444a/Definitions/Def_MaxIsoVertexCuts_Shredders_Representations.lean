-- Prove2me | Definitions.Def_MaxIsoVertexCuts_Shredders_Representations
-- name    : MaxIsoVertexCuts_Shredders_Representations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:53:17.194576+00:00
-- url     : https://prove2.me/theorems/f18a2066-8a7f-4410-b985-faac9c603114
-- title:
--   Representations
-- statement:
--   Standard cuts have at least two components in L and |L|≤2|R|. A reconstructible representation existentially orders the components by cardinality and has either one cut with all but the largest component on L, or d−1 cuts with C_i⊆L_i and 3|C_i|≤2|L_i|. Target choices fix such a representation for every minimum shredder. Linkedness uses 2ℓ·2^((log₂ n)^0.7). MergePremise is exactly the certificate premise of Lemma 5.8. Definitions 5.4–5.5,5.17, printed pp.29–30,35 (PDF 31–32,37).
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission, Sections 2–5; machine conventions specified in the mission.

import Mathlib
import Definitions.Def_MaxIsoVertexCuts_Shredders_Certificates

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

def Standard {n : ℕ} (G : SimpleGraph (Fin n)) (c : Cut n) : Prop :=
  IsCut G c ∧ IsShredder G c.S ∧
  2 ≤ (components G (Finset.univ \ c.L)).card ∧ c.L.card ≤ 2 * c.R.card

def Reconstructible {n : ℕ} (G : SimpleGraph (Fin n)) (S : VSet n)
    (cs : List (Cut n)) : Prop :=
  IsShredder G S ∧ (∀ c ∈ cs, Standard G c ∧ c.S = S) ∧
  ∃ ds : List (VSet n), ds.Nodup ∧ ds.toFinset = components G S ∧
    ds.Pairwise (fun C D => C.card ≤ D.card) ∧
    ((∃ c, cs = [c] ∧ c.L = ds.dropLast.toFinset.biUnion id) ∨
      (cs.length = ds.length - 1 ∧ ∀ i : Fin cs.length,
        ds[i.val]! ⊆ (cs.get i).L ∧ 3 * ds[i.val]!.card ≤ 2 * (cs.get i).L.card))

def TargetChoice {n : ℕ} (G : SimpleGraph (Fin n))
    (F : VSet n → List (Cut n)) : Prop :=
  ∀ S, IsKShredder G (kappa G) S → Reconstructible G S (F S)

noncomputable def logTwo (n : ℕ) : ℝ := Real.log (n : ℝ) / Real.log 2
noncomputable def subpolyExponent (n : ℕ) : ℝ := (logTwo n) ^ (0.7 : ℝ)

def Linked {n : ℕ} (G : SimpleGraph (Fin n)) (ell : ℕ) (c : Cut n) : Prop :=
  ∃ s ∈ c.S, ((HypRecov.nbhd G {s} ∩ c.R).card : ℝ) ≤
    2 * (ell : ℝ) * (2 : ℝ) ^ subpolyExponent n

def MergePremise {n : ℕ} (G : SimpleGraph (Fin n)) (S : VSet n)
    (cs : List (Cut n)) (zs : List (Certificate n)) : Prop :=
  IsShredder G S ∧ Reconstructible G S cs ∧
  (∀ z ∈ zs, ValidCertificate G S z) ∧
  ∀ c ∈ cs, ∀ D, HypRecov.IsCompOf G (Finset.univ \ c.L) D →
    3 * D.card ≤ 2 * c.L.card → ∃ z ∈ zs, LComplete G c z ∧ D ∈ z.C

end MaxIsoVertexCuts.Shredders


