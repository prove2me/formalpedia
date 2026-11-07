-- Prove2me | Definitions.Def_CritWinSpin_gibbs
-- name    : CritWinSpin_gibbs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:37:05.323196+00:00
-- url     : https://prove2.me/theorems/6b63427b-0460-4613-9a18-7efa4565295a
-- title:
--   Gibbs distribution $\pi^\rho_{J,h}$ on $A^\iota$ and the width $\mathrm{wd}(J,h)$
-- statement:
--   For a finite index set $\iota$, a real matrix $J$ and a real vector $h$ on $\iota$, the **Gibbs distribution** on configurations $x\in A^\iota$ is
--   $$\pi^\rho_{J,h}(x)=\frac{1}{Z^\rho_{J,h}}\exp\Bigl(\tfrac12x^\top Jx+h^\top x\Bigr)\prod_{i}\rho(x_i),$$
--   and the **width** is $\mathrm{wd}(J,h)=\max_i\bigl(|h_i|+\sum_j|J_{ij}|\bigr)$. The module also provides the extension of $\pi$ to $A^\iota\cup\{\bot\}$ with mass $0$ on $\bot$, and the product law $\pi^{\otimes k}$ with the same extension.
--
--   The diagonal of $J$ is kept, because it changes the law as soon as $x_i^2$ is not constant on $A$.
--
--   **Formalization Note** Rational instances are used through their entrywise casts `castM`, `castV`. The index set is general so that both $[N]$ and the clouds $[n]\times[r]$ of §6 are covered.
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), §2.1, p.9, eq. (6)

import Mathlib
import Definitions.Def_CritWinSpin_SpinLaw
set_option autoImplicit false

namespace CritWinSpin

/-- A spin configuration `x ∈ A^ι` on a finite index set `ι` (for the paper, `ι = [N]`, or the
clouds `[n] × [r]` of §6.1). -/
abbrev Config (S : SpinLaw) (ι : Type) : Type := ι → {x : ℚ // x ∈ S.A}

/-- The real spin values `(x_i)_i` of a configuration. -/
noncomputable def spinVal {S : SpinLaw} {ι : Type} (x : Config S ι) : ι → ℝ :=
  fun i => (((x i : ℚ)) : ℝ)

/-- The energy `½ vᵀ J v + hᵀ v` of a real vector `v` (the exponent of (6), p.9). -/
noncomputable def energy {ι : Type} [Fintype ι] (J : Matrix ι ι ℝ) (h : ι → ℝ) (v : ι → ℝ) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, J i j * v i * v j + ∑ i, h i * v i

/-- The product weight `ρ^{⊗ι}(x) = ∏_i ρ(x_i)`. -/
noncomputable def prodRho (S : SpinLaw) {ι : Type} [Fintype ι] (x : Config S ι) : ℝ :=
  ∏ i, ((S.ρ (x i : ℚ) : ℚ) : ℝ)

/-- The unnormalised Gibbs weight `exp(½ xᵀJx + hᵀx) ∏_i ρ(x_i)`, eq. (6), p.9. -/
noncomputable def gibbsWeight (S : SpinLaw) {ι : Type} [Fintype ι] (J : Matrix ι ι ℝ) (h : ι → ℝ)
    (x : Config S ι) : ℝ :=
  Real.exp (energy J h (spinVal x)) * prodRho S x

/-- **The Gibbs distribution** `π^ρ_{J,h}(x) = Z^{-1} exp(½ xᵀJx + hᵀx) ∏_i ρ(x_i)` on `A^ι`,
eq. (6), p.9 (Liu–Zhang–Ren, STOC 2027 submission, manuscript sha256 f77584da…).

**Formalization Note.** `J` and `h` are real; a rational instance `(J, h)` is used through its
entrywise cast. The diagonal of `J` is kept, as on p.9 (it matters when `x_i²` is not constant on
`A`). The partition function is positive because every weight is positive. -/
noncomputable def gibbs (S : SpinLaw) {ι : Type} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι ℝ) (h : ι → ℝ)
    (x : Config S ι) : ℝ :=
  gibbsWeight S J h x / ∑ y, gibbsWeight S J h y

/-- The Gibbs law extended to `A^ι ∪ {⊥}` (`none` = `⊥`), with mass `0` on `⊥` (Definition 2.2,
p.9: outputs outside `A^N` are replaced by `⊥ ∉ A^N`). -/
noncomputable def gibbsOpt (S : SpinLaw) {ι : Type} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι ℝ) (h : ι → ℝ) :
    Option (Config S ι) → ℝ
  | none => 0
  | some x => gibbs S J h x

/-- The product law `π^{⊗k}` on `(A^ι)^k`. -/
noncomputable def gibbsProd (S : SpinLaw) {ι : Type} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι ℝ) (h : ι → ℝ)
    {k : ℕ} (xs : Fin k → Config S ι) : ℝ :=
  ∏ j, gibbs S J h (xs j)

/-- The product law `π^{⊗k}` extended to `(A^ι)^k ∪ {⊥}`, with mass `0` on `⊥`. -/
noncomputable def gibbsTupleOpt (S : SpinLaw) {ι : Type} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι ℝ)
    (h : ι → ℝ) (k : ℕ) : Option (Fin k → Config S ι) → ℝ
  | none => 0
  | some xs => gibbsProd S J h xs

/-- The width `wd(J, h) = max_i (|h_i| + ∑_j |J_ij|)`, eq. (6), p.9.

**Formalization Note.** The real `⨆` over the finite index set is the maximum; it is `0` on an
empty index set. -/
noncomputable def width {ι : Type} [Fintype ι] (J : Matrix ι ι ℝ) (h : ι → ℝ) : ℝ :=
  ⨆ i, (|h i| + ∑ j, |J i j|)

/-- Entrywise cast of a rational matrix. -/
noncomputable def castM {ι : Type} (J : Matrix ι ι ℚ) : Matrix ι ι ℝ := J.map (fun q : ℚ => (q : ℝ))

/-- Entrywise cast of a rational vector. -/
noncomputable def castV {ι : Type} (h : ι → ℚ) : ι → ℝ := fun i => (h i : ℝ)

end CritWinSpin


