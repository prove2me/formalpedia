-- Prove2me | Definitions.Def_JinQLearning_Bernstein_Statistics
-- name    : JinQLearning_Bernstein_Statistics
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:36:14.486247+00:00
-- url     : https://prove2.me/theorems/a64e5ac8-95b2-4f6f-aa74-461d08f1f5b2
-- title:
--   Visit-indexed errors, concentration notation and printed C.4
-- statement:
--   The visit count is the length of the historical observation list. visitSum ranges over earlier episodes that visited the specified triple, weighting episode j by alpha_t^(N_h^j(x,a)+1). nextError is (V^{j}_{h+1}-V^star_{h+1}) at the observed successor; phi is the analogous current-stage error at the visited state. errorBase is alpha_t^0 H plus the weighted nextError sum. CoarseBound is precisely the printed simultaneous (C.4): phi at the visited state is bounded using every arbitrary pair (x,a). It is not assumed by the model or process, and is only an explicit hypothesis where the source uses (C.4). At zero count the singular bound is nonrestrictive. varianceRadius is SA sqrt(H^7 iota)/t+sqrt(H^7 S A iota/t) for positive counts. C.6's delta is V^star-V^k at the successor, and xi=(P-P_hat)(V^star-V^k), preserving the printed definitions despite their proof discrepancy. These are distinct from Section 4's policy-gap delta.
-- source:
--   Jin, Allen-Zhu, Bubeck & Jordan, Is Q-learning Provably Efficient?, arXiv:1807.03765v1, pp. 15–16, 20–22, notation for Lemmas C.1–C.7.

import Definitions.Def_JinQLearning_Bernstein_Process

open scoped BigOperators
noncomputable section

namespace JinQLearning.Bernstein

variable {S A H K : ℕ} [NeZero A]

/-- Number of visits strictly before episode k. -/
def count (M : Model S A H) (c₁ c₂ ℓ : ℝ) (ω : Path S A H K)
    (k : ℕ) (h : Fin H) (x : Fin S) (a : Fin A) : ℕ :=
  ((snapshot M c₁ c₂ ℓ ω k).observations h x a).length

/-- A sum over the earlier visits, indexed by episode j with its visit rank N^j+1. -/
def visitSum (M : Model S A H) (c₁ c₂ ℓ : ℝ) (ω : Path S A H K)
    (k : Fin K) (h : Fin H) (x : Fin S) (a : Fin A) (f : Fin K → ℝ) : ℝ := by
  classical
  exact ∑ j : Fin K, if j.val < k.val ∧ (ω j).2 h.castSucc = x ∧ episodeAction (ω j) h = a then
    VLearning.CCE.lrW H (count M c₁ c₂ ℓ ω k.val h x a)
      (count M c₁ c₂ ℓ ω j.val h x a + 1) * f j else 0

def nextError (M : Model S A H) (c₁ c₂ ℓ : ℝ) (ω : Path S A H K)
    (j : Fin K) (h : Fin H) : ℝ :=
  tableValue (snapshot M c₁ c₂ ℓ ω j.val) (h.val + 1) ((ω j).2 h.succ) -
    optimalValue M (h.val + 1) ((ω j).2 h.succ)

def phi (M : Model S A H) (c₁ c₂ ℓ : ℝ) (ω : Path S A H K)
    (k : Fin K) (h : Fin H) : ℝ :=
  tableValue (snapshot M c₁ c₂ ℓ ω k.val) h.val ((ω k).2 h.castSucc) -
    optimalValue M h.val ((ω k).2 h.castSucc)

/-- Initial contribution plus the weighted next-stage errors. -/
def errorBase (M : Model S A H) (c₁ c₂ ℓ : ℝ) (ω : Path S A H K)
    (k : Fin K) (h : Fin H) (x : Fin S) (a : Fin A) : ℝ :=
  VLearning.CCE.lrW H (count M c₁ c₂ ℓ ω k.val h x a) 0 * H +
    visitSum M c₁ c₂ ℓ ω k h x a (fun j => nextError M c₁ c₂ ℓ ω j h)

/-- (C.4) exactly as printed: its left side is at the visited state but x,a on the
right are universally quantified. Zero counts have an infinite radius, encoded by implication. -/
def CoarseBound (M : Model S A H) (c₁ c₂ ℓ : ℝ) (ω : Path S A H K) : Prop :=
  ∀ (k : Fin K) (h : Fin H) (x : Fin S) (a : Fin A),
    0 < count M c₁ c₂ ℓ ω k.val h x a →
    phi M c₁ c₂ ℓ ω k h ≤ errorBase M c₁ c₂ ℓ ω k h x a +
      4 * c₂ * Real.sqrt ((H : ℝ) ^ 3 * ℓ / count M c₁ c₂ ℓ ω k.val h x a)

/-- C.3's and C.6's positive-count radius; zero counts are handled in the event itself. -/
def varianceRadius (S A H : ℕ) (ℓ : ℝ) (t : ℕ) : ℝ :=
  (S : ℝ) * A * Real.sqrt ((H : ℝ) ^ 7 * ℓ) / t +
    Real.sqrt ((H : ℝ) ^ 7 * S * A * ℓ / t)

/-- C.6's printed δ, distinct from the policy-gap δ in §4. -/
def deltaC6 (M : Model S A H) (c₁ c₂ ℓ : ℝ) (ω : Path S A H K)
    (k : Fin K) (h : Fin H) : ℝ := - nextError M c₁ c₂ ℓ ω k h

/-- C.6's printed ξ=(P-P̂)(V⋆-Vᵏ). -/
def xiC6 (M : Model S A H) (c₁ c₂ ℓ : ℝ) (ω : Path S A H K)
    (k : Fin K) (h : Fin H) : ℝ :=
  expectation M h ((ω k).2 h.castSucc) (episodeAction (ω k) h)
    (fun y => optimalValue M (h.val + 1) y -
      tableValue (snapshot M c₁ c₂ ℓ ω k.val) (h.val + 1) y) - deltaC6 M c₁ c₂ ℓ ω k h

end JinQLearning.Bernstein


