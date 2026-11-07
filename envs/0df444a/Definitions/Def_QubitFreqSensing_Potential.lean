-- Prove2me | Definitions.Def_QubitFreqSensing_Potential
-- name    : QubitFreqSensing_Potential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:21:59.538589+00:00
-- url     : https://prove2.me/theorems/b3a96a0a-08ef-458d-ac16-9f6fecdea32d
-- title:
--   The class $\mathbb T$, the set $K$, the inner product $\langle f,g\rangle$, the cosines $g_i$ and the potential $J$ (13)
-- statement:
--   Fix frequencies $\omega_1,\dots,\omega_N>0$ and a constant $C>0$.
--
--   1. $\mathbb T$ is the set of measurable functions $u$ with $|u(x)|<1$ for every $x\in[0,2\pi]$ ("the set of L2 integrable functions that map $[0,2\pi]\to\mathbb D$", p.16).
--   2. $K$ is the set of functions on $[0,2\pi]$ with $|v(x)|\le 1$ almost everywhere, the $L^2$-closure of $\mathbb T$ (App. A, p.33).
--   3. The inner product and norm are
--   $$
--   \langle f,g\rangle=\frac1{2\pi}\int_0^{2\pi}\overline{f(x)}\,g(x)\,dx,\qquad \|f\|^2=\langle f,f\rangle ,
--   $$
--   conjugate-linear in the first argument.
--   4. $g_i(x)=\cos(\omega_i x)$.
--   5. The potential is
--   $$
--   J(f)=\sum_{i=1}^N\log|\langle g_i,f\rangle|+CN\cdot\frac1{2\pi}\int_0^{2\pi}\log\bigl(1-|f(x)|^2\bigr)\,dx\ \in\ \mathbb R\cup\{-\infty\},
--   $$
--   with the convention $\log 0=-\infty$.
--
--   The proof of Theorem 5.1 takes a maximizer of $J$ over $\mathbb T$ and shows that all its correlations $|\langle g_i,u\rangle|$ are at least $c/\sqrt N$.
--
--   **Formalization Note** $J$ takes values in `EReal`. A vanishing correlation contributes $-\infty$, and the penalty is $-\frac1{2\pi}\int^-\bigl(-\log(1-|f|^2)\bigr)$, a lower Lebesgue integral of a $[0,\infty]$-valued function that is $+\infty$ where $|f(x)|\ge1$; this avoids Lean's junk values $\log 0=0$ and $\int(\text{non-integrable})=0$. Membership in $\mathbb T$ uses Borel measurability; every quantity depends only on the a.e. class, so this changes no maximum or existence statement.
-- source:
--   Chen, Coladangelo, Li, Zhang, Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit, manuscript (STOC 2027 submission; held version sha256 fd015276…c95c9a2), §5, p.16 (the class 𝕋); eq. (13), p.18 (⟨·,·⟩, g_i, J); App. A, p.33 (K)

import Mathlib

open MeasureTheory Real

namespace QubitFreqSensing

/-- **The class 𝕋** (Chen, Coladangelo, Li, Zhang, manuscript (STOC 2027 submission), §5, p.16:
"Let T denote the set of L2 integrable functions that map [0, 2π] → D", `D` the open unit disc):
measurable `u : ℝ → ℂ` with `|u(x)| < 1` for every `x ∈ [0, 2π]`.

**Formalization Note** Values outside `[0, 2π]` play no role. Square integrability on `[0, 2π]` is
automatic for a measurable function bounded by `1`. Lebesgue-measurable functions agree a.e. with
Borel-measurable ones, and every quantity below depends only on the a.e. class, so requiring
`Measurable` changes no maximum and no existence statement. -/
def discFns : Set (ℝ → ℂ) :=
  {u | Measurable u ∧ ∀ x ∈ Set.Icc 0 (2 * π), ‖u x‖ < 1}

/-- **The set K** (App. A, p.33: "K = {v ∈ L2([0, 2π]; C) : |v(x)| ≤ 1 almost everywhere}", the
L²-closure of 𝕋): a.e.-strongly measurable functions on `[0, 2π]` with `|v| ≤ 1` a.e. there. -/
def closedDiscFns : Set (ℝ → ℂ) :=
  {v | AEStronglyMeasurable v (volume.restrict (Set.Icc 0 (2 * π))) ∧
    ∀ᵐ x ∂(volume.restrict (Set.Icc 0 (2 * π))), ‖v x‖ ≤ 1}

/-- **The inner product** `⟨f, g⟩ = (1/2π) ∫₀^{2π} \overline{f(x)} g(x) dx` (p.18), conjugate-linear
in the first argument. -/
noncomputable def inner2pi (f g : ℝ → ℂ) : ℂ :=
  ((1 / (2 * π) : ℝ) : ℂ) * ∫ x in (0 : ℝ)..2 * π, (starRingEnd ℂ) (f x) * g x

/-- The squared norm `‖f‖² = ⟨f, f⟩` (p.18), a real number. -/
noncomputable def normSq2pi (f : ℝ → ℂ) : ℝ := (inner2pi f f).re

/-- The cosines `g_i(x) = cos(ω_i x)` (p.18), as complex-valued functions. -/
noncomputable def gcos {N : ℕ} (ω : Fin N → ℝ) (i : Fin N) : ℝ → ℂ :=
  fun x => (Real.cos (ω i * x) : ℂ)

/-- The logarithm with the convention `log 0 = −∞` (p.18), on `[0, ∞)`, valued in `EReal`. -/
noncomputable def logE (r : ℝ) : EReal := if r = 0 then ⊥ else ((Real.log r : ℝ) : EReal)

/-- The pointwise penalty `−log(1 − |f(x)|²) ∈ [0, ∞]`, equal to `+∞` where `|f(x)| ≥ 1`
(the convention `log 0 = −∞` on `K`, App. A, p.33). -/
noncomputable def penIntegrand (f : ℝ → ℂ) (x : ℝ) : ENNReal :=
  if ‖f x‖ < 1 then ENNReal.ofReal (-Real.log (1 - ‖f x‖ ^ 2)) else ⊤

/-- The penalty `(1/2π) ∫₀^{2π} log(1 − |f(x)|²) dx ∈ [−∞, 0]` of (13), p.18, written as minus a
lower Lebesgue integral of the nonnegative integrand `−log(1 − |f|²)`. -/
noncomputable def penalty (f : ℝ → ℂ) : EReal :=
  -(((ENNReal.ofReal (1 / (2 * π)) * ∫⁻ x in Set.Icc 0 (2 * π), penIntegrand f x : ENNReal) :
    EReal))

/-- **The potential functional J** (Chen, Coladangelo, Li, Zhang, manuscript (STOC 2027
submission), §5, eq. (13), p.18):
`J(f) = Σ_{i=1}^N log |⟨g_i, f⟩| + C N · (1/2π) ∫₀^{2π} log(1 − |f(x)|²) dx`, valued in
`ℝ ∪ {−∞}` with `log 0 = −∞`.

**Formalization Note** `J` is `EReal`-valued: a vanishing correlation contributes `⊥` (`logE`), and
the penalty is computed through `∫⁻`, so a divergent penalty is `⊥` rather than Lean's junk `0`
(`Real.log 0 = 0` and a non-integrable Bochner integral is `0`, either of which would hide the
`−∞`). On `K` (App. A) the penalty integrand is `+∞` where `|f(x)| = 1`. -/
noncomputable def J {N : ℕ} (C : ℝ) (ω : Fin N → ℝ) (f : ℝ → ℂ) : EReal :=
  ∑ i, logE ‖inner2pi (gcos ω i) f‖ + ((C * N : ℝ) : EReal) * penalty f

end QubitFreqSensing


