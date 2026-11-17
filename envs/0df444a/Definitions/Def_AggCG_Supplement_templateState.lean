-- Prove2me | Definitions.Def_AggCG_Supplement_templateState
-- name    : AggCG_Supplement_templateState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:23:06.22759+00:00
-- url     : https://prove2.me/theorems/6f28ecf4-2678-48e0-b3e1-c265a2a9fde3
-- title:
--   Renormalizable binary controller state
-- statement:
--   A renormalizable controller maintains a normalized coordinate in $[0,1]$, decides whether it lies above a common split $\tau$, and applies the branch-dependent renormalization $R_a$. The witness for a word $b$ is the reverse composition $h_{b_1}\circ\cdots\circ h_{b_T}(1/2)$.
-- source:
--   Sharma, STOC 2027 submission (manuscript sha256 f7ea0248…), Definition F.6, p.39, PDF p.40; Theorem F.7, p.40, PDF p.41

import Mathlib

namespace AggCG.Supplement

/-- The normalized coordinate of a renormalizable state template (Sharma, *Computational Complexity of
Data-Driven Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027
submission (manuscript sha256 f7ea0248…), Definition F.6, p.39, PDF p.40) after `k` decisions, started at
`ν_∅(θ) = θ`: the decision is `a = 1{ν > τ}` and the successor coordinate is `R_a(ν)`
(Def. F.6 (i)–(iii): `ν_{q_a} = R_a ∘ ν_q`).

**Formalization Note** The controller states `q` and their intervals `J_q` are represented by the
normalized coordinate they carry; the transition `q' = U(q, a)` does not read `θ`, so the whole run is
determined by this coordinate. -/
noncomputable def templateState (τ : ℝ) (R : Bool → ℝ → ℝ) (θ : ℝ) : ℕ → ℝ
  | 0 => θ
  | k + 1 => R (decide (τ < templateState τ R θ k)) (templateState τ R θ k)

/-- The parameter `θ` realizes the decisions `b ∈ {0,1}^T` off the boundary: at each of the first `T`
stages the normalized coordinate lies in `[0, 1]`, differs from the split `τ`, and the decision
`1{ν > τ}` equals `b_k`. -/
def TemplateRealizes (τ : ℝ) (R : Bool → ℝ → ℝ) (θ : ℝ) {T : ℕ} (b : Fin T → Bool) : Prop :=
  ∀ k : Fin T, templateState τ R θ k ∈ Set.Icc 0 1 ∧ templateState τ R θ k ≠ τ ∧
    decide (τ < templateState τ R θ k) = b k

/-- The witness `θ_b = h_{b_1} ∘ ⋯ ∘ h_{b_T}(1/2)` of Theorem F.7 (p.40, PDF p.41). -/
noncomputable def templateWitness (h : Bool → ℝ → ℝ) {T : ℕ} (b : Fin T → Bool) : ℝ :=
  (List.ofFn b).foldr (fun a x => h a x) (1 / 2)

end AggCG.Supplement


