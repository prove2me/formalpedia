-- Prove2me | Definitions.Def_FuchsThesis_Daroczy_SatisfiesRecursion
-- name    : FuchsThesis_Daroczy_SatisfiesRecursion
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:21:44.005484+00:00
-- url     : https://prove2.me/theorems/aeb7dac2-069b-4fff-9d56-ea707b45c926
-- title:
--   The recursion of type $\alpha$ (eq. 2.111)
-- statement:
--   Let $\alpha$ be a real parameter. A function $H : \Gamma \to \mathbb R$ **satisfies the recursion of type $\alpha$** (Eq. (2.111)) if for every $n \ge 2$ and every $(p_1,\dots,p_n) \in \Gamma_n$ with $p_1 + p_2 > 0$,
--
--   $$
--   H(p_1,\dots,p_n) = H(p_1+p_2, p_3,\dots,p_n) + (p_1+p_2)^{\alpha}\, H\!\left(\frac{p_1}{p_1+p_2}, \frac{p_2}{p_1+p_2}\right).
--   $$
--
--   For $\alpha = 1$ this is the "objectivity" requirement (2.110): the expected information gained does not depend on whether one first learns whether the outcome is among the first two and then which of them occurred. Daróczy's device is to introduce a positive parameter $\alpha \ne 1$ and recover the Shannon entropy in the limit $\alpha \to 1$.
--
--   **Formalization Note** The right-hand side is undefined when $p_1 + p_2 = 0$, so the recursion is required only where it is defined; no condition is imposed on $H$ at such points. Powers are real powers.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (2.111), p.32 (PDF p.41)

import Mathlib
import Definitions.Def_FuchsThesis_Daroczy_IsDist

namespace FuchsThesis.Daroczy

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eq. (2.111), p.32 (PDF p.41), required "for each n ≥ 2" in
Theorem 2.7: the recursion of type `α`,
`H_α(p₁, …, pₙ) = H_α(p₁ + p₂, p₃, …, pₙ) + (p₁ + p₂)^α H_α(p₁/(p₁ + p₂), p₂/(p₁ + p₂))`,
for every `n ≥ 2` and every `(p₁, …, pₙ) ∈ Γₙ`.

**Formalization Note.** `n = m + 2`; the source's `p₁, p₂` are `p 0, p 1`, and the merged
vector `(p₁ + p₂, p₃, …, pₙ)` is `Fin.cons (p 0 + p 1) (fun i => p i.succ.succ)`. The right side
of (2.111) contains `p₁/(p₁ + p₂)`, which is undefined when `p₁ + p₂ = 0`; the recursion is
therefore required only where it is defined, `0 < p₁ + p₂` (for `p ∈ Γₙ` the sum is `≥ 0`).
This is the weakest reading, so it does not let Lean's `0 / 0 = 0` impose any condition on `H`
that the source does not state. `(p₁ + p₂)^α` is `Real.rpow`. -/
def SatisfiesRecursion (α : ℝ) (H : (n : ℕ) → (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (m : ℕ) (p : Fin (m + 2) → ℝ), IsDist p → 0 < p 0 + p 1 →
    H (m + 2) p =
      H (m + 1) (Fin.cons (p 0 + p 1) (fun i : Fin m => p i.succ.succ) : Fin (m + 1) → ℝ)
        + (p 0 + p 1) ^ α * H 2 ![p 0 / (p 0 + p 1), p 1 / (p 0 + p 1)]

end FuchsThesis.Daroczy


