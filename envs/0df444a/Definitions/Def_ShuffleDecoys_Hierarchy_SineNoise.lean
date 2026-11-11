-- Prove2me | Definitions.Def_ShuffleDecoys_Hierarchy_SineNoise
-- name    : ShuffleDecoys_Hierarchy_SineNoise
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:21:36.587321+00:00
-- url     : https://prove2.me/theorems/edcc17a3-e334-4962-bd12-766445ea67ac
-- title:
--   The correlated sine-squared count noise of construction (8): L = ⌊(n − 1)/(d − 1)⌋ + 1, θ = π/(L + 1), r(j) = (2/(L + 1)) sin²((j + 1)θ)
-- statement:
--   Fix $d\ge2$ and $n\ge d$. Put
--   $$L=\Big\lfloor\frac{n-1}{d-1}\Big\rfloor+1,\qquad \theta=\frac{\pi}{L+1},\qquad r(j)=\frac{2}{L+1}\sin^2\big((j+1)\theta\big)\quad(j=0,\dots,L-1),$$
--   with $r(j)=0$ for every other integer $j$ (`sineL`, `sineTheta`, `sineWeight`). Draw $X_1,\dots,X_{d-1}$ independently from $r$, independently of the message, and set
--   $$S=\Big(X_1,\dots,X_{d-1},\ n-1-\sum_{i=1}^{d-1}X_i\Big)$$
--   (`sineHist`: coordinates $0,\dots,d-2$ of `Fin d` carry the $X_i$, the last coordinate the balance). `IsSineNoise d n S` says that the integer vector law $S$ is the law of this histogram: $S$ is the image under `sineHist` of the law of $(X_1,\dots,X_{d-1})$, which puts mass $\prod_i r(x_i)$ on $x$.
--
--   **Formalization Note.** $r$ is a real function on $\mathbb Z$; that it sums to $1$ (so that the law of $X$ exists) is a fact, not part of the definition, and `IsSineNoise` asserts that such a law is given.
-- source:
--   Su, Cheng, Wang, The Information-Theoretic Limits of Hiding Among Decoys in the Shuffle Model, STOC 2027 submission (manuscript sha256 445baceb…), p. 17, Construction (8)

import Mathlib

open scoped ENNReal

namespace ShuffleDecoys.Hierarchy

/-!
# The correlated sine-squared count noise, construction (8)

Su, Cheng, Wang, *The Information-Theoretic Limits of Hiding Among Decoys in the Shuffle Model*,
STOC 2027 submission, p. 17, construction (8): for `d ≥ 2`, `n ≥ d`,
`L = ⌊(n − 1)/(d − 1)⌋ + 1`, `θ = π/(L + 1)`, `r(j) = (2/(L + 1)) sin²((j + 1)θ)` on
`j = 0, …, L − 1` (zero elsewhere on `ℤ`); `X₁, …, X_{d−1}` i.i.d. from `r` and
`S = (X₁, …, X_{d−1}, n − 1 − Σ Xᵢ)`.
-/

/-- `L = ⌊(n − 1)/(d − 1)⌋ + 1` (natural-number division is the floor). -/
def sineL (d n : ℕ) : ℕ := (n - 1) / (d - 1) + 1

/-- `θ = π/(L + 1)`. -/
noncomputable def sineTheta (d n : ℕ) : ℝ := Real.pi / ((sineL d n : ℝ) + 1)

/-- The sine-squared weights `r(j) = (2/(L + 1)) sin²((j + 1)θ)` for `0 ≤ j ≤ L − 1`, extended by
zero to all of `ℤ`. -/
noncomputable def sineWeight (d n : ℕ) (j : ℤ) : ℝ :=
  if 0 ≤ j ∧ j < (sineL d n : ℤ) then
    2 / ((sineL d n : ℝ) + 1) * Real.sin (((j : ℝ) + 1) * sineTheta d n) ^ 2
  else 0

/-- The histogram `(x₁, …, x_{d−1}, n − 1 − Σ xᵢ)`: coordinates `0, …, d − 2` of `Fin d` carry `x`,
the last coordinate `d − 1` carries the balance. -/
def sineHist (d n : ℕ) (x : Fin (d - 1) → ℤ) : Fin d → ℤ :=
  fun i => if h : i.val < d - 1 then x ⟨i.val, h⟩ else ((n : ℤ) - 1) - ∑ j, x j

/-- `S` has the law of construction (8): `S = sineHist (X₁, …, X_{d−1})` with `X` the law of
`d − 1` independent draws from `r` (mass `∏ᵢ r(xᵢ)` at `x`). -/
def IsSineNoise (d n : ℕ) (S : PMF (Fin d → ℤ)) : Prop :=
  ∃ X : PMF (Fin (d - 1) → ℤ),
    (∀ x, X x = ∏ i, ENNReal.ofReal (sineWeight d n (x i))) ∧ S = X.map (sineHist d n)

end ShuffleDecoys.Hierarchy


