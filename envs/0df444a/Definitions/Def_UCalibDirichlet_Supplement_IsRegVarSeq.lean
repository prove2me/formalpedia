-- Prove2me | Definitions.Def_UCalibDirichlet_Supplement_IsRegVarSeq
-- name    : UCalibDirichlet_Supplement_IsRegVarSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:11:09.674266+00:00
-- url     : https://prove2.me/theorems/96826f10-a515-45df-9f4f-83688666b269
-- title:
--   Regularly varying sequence with index $\rho$
-- statement:
--   A real sequence $(A(n))_{n\ge 0}$ is **regularly varying with index $\rho$** if $A(n)>0$ for all sufficiently large $n$ and, for every fixed $\lambda>0$,
--   $$\frac{A(\lfloor\lambda x\rfloor)}{A(\lfloor x\rfloor)}\longrightarrow\lambda^{\rho}\qquad(x\to\infty\text{ through the reals}).$$
--   That is, the step interpolation $x\mapsto A(\lfloor x\rfloor)$ is a regularly varying function at infinity in the sense of Bingham, Goldie and Teugels.
--
--   Regular variation of the Bernstein gap $L_F$ (or comparability of $L_F$ with a regularly varying sequence) is the hypothesis of Theorem 1.14 under which the regret of Algorithm 1 and the minimax regret are both of order $L_F(T)$.
--
--   **Formalization Note** $\lfloor\cdot\rfloor$ is the floor to a natural number and $\lambda^\rho$ the real power. Positivity is required only for large $n$ ("defined for all sufficiently large arguments").
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), §1.1.3, p.8; App. E.1.2, pp.40–41

import Mathlib

namespace UCalibDirichlet.Supplement

/-- **Regularly varying sequence with index `ρ`.** Frongillo, Luo, Mehta & Schneider (manuscript,
STOC 2027 submission), §1.1.3, p.8: "We say `L_F` is regularly varying [Bingham et al., 1987] with
index `ρ` if `L_F(⌊λx⌋)/L_F(⌊x⌋) → λ^ρ` as `x → ∞` through the reals, for every fixed `λ > 0`";
App. E.1.2, pp.40–41: "A positive measurable function `A`, defined for all sufficiently large
arguments, is regularly varying at infinity with index `ρ` if `A(λx)/A(x) → λ^ρ` … A positive
sequence `(A(n))_{n≥1}` … is regularly varying if its step interpolation `x ↦ A(⌊x⌋)` is".

`IsRegVarSeq A ρ`: `A(n) > 0` for all sufficiently large `n`, and for every `λ > 0`,
`A(⌊λx⌋)/A(⌊x⌋) → λ^ρ` as the real `x → ∞`.

**Formalization Note.** `⌊·⌋` is `Nat.floor` and `λ^ρ` is `Real.rpow`. Positivity is required only
eventually ("defined for all sufficiently large arguments"); the step interpolation of a sequence
is automatically measurable. -/
def IsRegVarSeq (A : ℕ → ℝ) (ρ : ℝ) : Prop :=
  (∀ᶠ n in Filter.atTop, 0 < A n) ∧
    ∀ c : ℝ, 0 < c →
      Filter.Tendsto (fun x : ℝ => A ⌊c * x⌋₊ / A ⌊x⌋₊) Filter.atTop (nhds (c ^ ρ))

end UCalibDirichlet.Supplement


