-- Prove2me | Definitions.Def_PlantedIQP_xebHat
-- name    : PlantedIQP_xebHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:20:28.212456+00:00
-- url     : https://prove2.me/theorems/89ab8a5b-1c96-447b-b78c-22e5f4cd9aed
-- title:
--   The empirical XEB $\hat\chi$, the test $\mathrm{XEB}_{1,\ell}$ and tuple probabilities
-- statement:
--   Given polynomials $f_1,\dots,f_L$ and samples $x^{f_j}_i$ ($i\in[\ell]$, $j\in[L]$), the **empirical average XEB** is
--
--   $$
--   \hat\chi\big(\{x^{f_j}_i\}\big)=2^n\cdot\frac1{\ell L}\sum_{j=1}^L\sum_{i=1}^{\ell}p_{f_j}\big(x^{f_j}_i\big)-1 ,
--   $$
--
--   and the samples **pass** $\mathrm{XEB}_{1,\ell}(f_1,\dots,f_L)$ (Task 33 with $b=1$) when $\hat\chi\ge1$. The integer $\sum_{j,i}\mathrm{gap}\big(f_j+\langle x^{f_j}_i,\cdot\rangle\big)^2=\sum_{j,i}\big(2^na_{f_j}(x^{f_j}_i)\big)^2$ determines $\hat\chi$. Finally, the probability of an event when $f_1,\dots,f_L$ are independent with a given law and, given them, the $\ell L$ samples are independent with laws $q(f_j,\cdot)$ is recorded as a finite sum.
--
--   The ideal value of $\hat\chi$ is $m_2-1\approx2$ for samples from $p_f$ and $0$ for uniform samples, which is what makes $\hat\chi\ge1$ a test.
--
--   **Formalization Note** At $L=0$ or $\ell=0$, Lean's $1/0=0$ gives $\hat\chi=-1$, so the test fails; the statements take $L,\ell\ge1$.
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), Section 3.2, Eq. (43) and Task 33, p.22

import Mathlib
import Definitions.Def_PlantedIQP_amplitude

set_option autoImplicit false

namespace PlantedIQP

/-!
# The empirical average XEB `χ̂`, passing `XEB_{1,ℓ}`, and tuple probabilities

Bläser et al., arXiv:2609.39918 (sha256 6e261694…), Section 3.2, p.22: "the average XEB can be
estimated given samples x^f_1, …, x^f_ℓ ← q_f for f = f₁, …, f_L sampled from M(n) as
χ̂({x^{f_j}_i}_{ij}) = 2ⁿ · (1/(ℓL)) Σ_{j=1}^{L} Σ_{i=1}^{ℓ} p_{f_j}(x^{f_j}_i) − 1. (43)"
"Task 33 (XEB_{b,ℓ}). Given polynomials f₁, …, f_L ∈ 𝔽₂[x₁, …, xₙ], output samples
x^{f₁}_1, …, x^{f_L}_ℓ satisfying χ̂({x^{f_j}_i}_{i∈[ℓ],j∈[L]}) ≥ b. (45)"

**Formalization Note.**
* Polynomials are `f : Fin L → CubicPoly n` and samples `x : Fin L → Fin ℓ → Vec n`, `x j i` being
  `x^{f_j}_i` (indices shifted by one).
* `Passes f x` is Task 33 with `b = 1`: `χ̂ ≥ 1` (not strict). At `L = 0` or `ℓ = 0`, Lean's
  `1/0 = 0` makes `χ̂ = −1`, so the test fails; the statements of the mission take `L, ℓ ≥ 1`.
* `xebNumerator f x = Σ_{j,i} gap(f_j + ⟨x^{f_j}_i, ·⟩)²` is the integer with
  `χ̂ = xebNumerator / (2ⁿ ℓ L) − 1` (since `2ⁿ a_f(x) = gap(f + ⟨x, ·⟩)`); the verifier of Theorem 43
  outputs it.
* `tupleProb n L ℓ w q E` is the probability of an event `E(f, x)` when `f_1, …, f_L` are drawn
  independently with weight `w` and, given them, the `ℓL` samples `x^{f_j}_i` independently from
  `q(f_j, ·)`.
-/

/-- The empirical average XEB `χ̂({x^{f_j}_i}) = 2ⁿ (1/(ℓL)) Σ_j Σ_i p_{f_j}(x^{f_j}_i) − 1`
(Eq. (43)). -/
noncomputable def xebHat {n L ℓ : ℕ} (f : Fin L → CubicPoly n) (x : Fin L → Fin ℓ → Vec n) : ℝ :=
  2 ^ n * (1 / ((ℓ : ℝ) * L)) * (∑ j, ∑ i, pf (f j) (x j i)) - 1

/-- The samples pass `XEB_{1,ℓ}(f₁, …, f_L)`: `χ̂ ≥ 1` (Task 33 with `b = 1`). -/
def Passes {n L ℓ : ℕ} (f : Fin L → CubicPoly n) (x : Fin L → Fin ℓ → Vec n) : Prop :=
  1 ≤ xebHat f x

/-- `Σ_{j,i} gap(f_j + ⟨x^{f_j}_i, ·⟩)² = Σ_{j,i} (2ⁿ a_{f_j}(x^{f_j}_i))²`, an integer. -/
def xebNumerator {n L ℓ : ℕ} (f : Fin L → CubicPoly n) (x : Fin L → Fin ℓ → Vec n) : ℤ :=
  ∑ j, ∑ i, gap (fun y => (f j).eval y + ∑ k, x j i k * y k) ^ 2

open Classical in
/-- The probability of the event `E(f, x)` when `f_1, …, f_L` are independent with weight `w` and,
given them, the samples `x^{f_j}_i` are independent with law `q(f_j, ·)`. -/
noncomputable def tupleProb (n L ℓ : ℕ) (w : CubicPoly n → ℝ) (q : CubicPoly n → Vec n → ℝ)
    (E : (Fin L → CubicPoly n) → (Fin L → Fin ℓ → Vec n) → Prop) : ℝ :=
  ∑ f : Fin L → CubicPoly n, (∏ j, w (f j)) *
    ∑ x : Fin L → Fin ℓ → Vec n, (∏ j, ∏ i, q (f j) (x j i)) * (if E f x then 1 else 0)

end PlantedIQP


