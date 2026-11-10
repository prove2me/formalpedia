-- Prove2me | Definitions.Def_KSATSingleFlip_Connect_SoftField
-- name    : KSATSingleFlip_Connect_SoftField
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:05:46.308492+00:00
-- url     : https://prove2.me/theorems/5d5ef455-586c-4f54-896c-1289e156b6a5
-- title:
--   The soft-field recursion $R_\beta$ and the critical constant $\gamma^*$
-- statement:
--   Section 4.1 (pp. 19–21): for $q\in(0,1)$, $z\in\mathbb R$: $q(z) = e^{2z}/(1+e^{2z})$ (`qOf`), $z(q) = \tfrac12\ln\frac{q}{1-q}$ (`zOf`), $f(q) = 2\sqrt{q(1-q)}$ (`fW`), $g(q) = 2(\sqrt q + \sqrt{1-q} - 1)$ (`gW`), $a(z) = \tfrac12\ln(1+e^{-2z})$ (`aShift`), $w(z) = \sqrt{1+e^{2z}}$ (`wInt`), $c_0 = 2(\sqrt2-1)$ (`c0`).
--
--   * The pairing (4.1): $\langle\psi,\nu\rangle = \int \cosh(z)\,\psi(q(z))\,\nu(dz)$ (`pairing`, a Bochner integral); $m(\nu) = \nu(\mathbb R)$ in $[0,\infty]$ (`massM`); $h(\nu) = \langle g,\nu\rangle$ (`hPot`). The integrand $\cosh z\, g(q(z))$ lies in $[0,1]$, so $h$ is a genuine integral against every finite measure.
--   * $K_\nu$ (Definition 4.2): the law of $X - X'$ for independent copies of $\sum_{z\in\Pi} a(z)$, $\Pi$ a Poisson point process with intensity $w(z)\nu(dz)$. The law of $\sum_{z\in\Pi} a(z)$ is the compound Poisson law with intensity $\mu = a_*(w\cdot\nu)$, written as $e^{-\mu(\mathbb R)}\sum_j \mu^{*j}/j!$ (`compoundPoisson`, `convPow`; Mathlib convolution `∗`); `Kmeas ν` convolves it with its reflection. (`compoundPoisson` returns $0$ for an infinite intensity, which does not occur below: every iterate is a finite measure and $u(\nu)<\infty$.)
--   * $R_\beta\nu = \beta e^{h(\nu)}K_\nu$ (`Rbeta`, (4.2)); iterates $\nu^\gamma_0 = 0$, $\nu^\gamma_{r+1} = R_{e^{-\gamma}}\nu^\gamma_r$ (`nuIter`), $m^\gamma_r$ (`mIter`, in $[0,\infty]$), $h^\gamma_r$ (`hIter`).
--   * (4.8): $\gamma^* = \inf\{\gamma\in\mathbb R : \sup_{r\ge0} m^\gamma_r < \infty\}$ (`gammaStar`); the supremum is taken in $[0,\infty]$, so "finite" is literal; the infimum is `sInf` in $\mathbb R$ (Theorem 4.4 asserts that the set is nonempty and bounded below).
-- source:
--   Wang, Yin, Yu, Zhang (2026), Single-Variable Connectivity in Random k-SAT, arXiv:2611.05981 (held version, SHA-256 1821a501…58b80f5), §4.1, printed pp. 19–21 (PDF 21–23): (4.1), Definition 4.2, (4.8)

import Mathlib

noncomputable section

open scoped Classical BigOperators ENNReal

open MeasureTheory

namespace KSATSingleFlip.Connect

/-! # The soft-field recursion and the critical constant `γ*` (§4.1, printed pp. 19–21)

Wang, Yin, Yu, Zhang (2026), arXiv:2611.05981, §4.1: (4.1), Definition 4.2, (4.8). -/

/-- The half-log-odds inverse `q(z) = e^{2z}/(1 + e^{2z})`. -/
def qOf (z : ℝ) : ℝ := Real.exp (2 * z) / (1 + Real.exp (2 * z))

/-- The half-log-odds `z(q) = ½ ln(q/(1−q))` for `q ∈ (0,1)`. -/
def zOf (q : ℝ) : ℝ := (1 / 2) * Real.log (q / (1 - q))

/-- `f(q) = 2√(q(1−q))` (= `sech z(q)`). -/
def fW (q : ℝ) : ℝ := 2 * Real.sqrt (q * (1 - q))

/-- `g(q) = 2(√q + √(1−q) − 1)`. -/
def gW (q : ℝ) : ℝ := 2 * (Real.sqrt q + Real.sqrt (1 - q) - 1)

/-- `a(z) = ½ ln(1 + e^{−2z})` (= `−½ ln q(z)`): the shift of a single-soft-child clause. -/
def aShift (z : ℝ) : ℝ := (1 / 2) * Real.log (1 + Real.exp (-2 * z))

/-- `w(z) = √(1 + e^{2z})` (= `2√(q(z)) cosh z`): the Poisson intensity density. -/
def wInt (z : ℝ) : ℝ := Real.sqrt (1 + Real.exp (2 * z))

/-- `c₀ = 2(√2 − 1)`. -/
def c0 : ℝ := 2 * (Real.sqrt 2 - 1)

/-- The weighted pairing (4.1): `⟨ψ, ν⟩ = ∫ cosh(z) ψ(q(z)) ν(dz)`. -/
def pairing (ψ : ℝ → ℝ) (ν : Measure ℝ) : ℝ := ∫ z, Real.cosh z * ψ (qOf z) ∂ν

/-- The `f`-weighted mass `m(ν) = ⟨f, ν⟩ = ν(ℝ)`, in `ℝ≥0∞` so that "finite" is literal. -/
def massM (ν : Measure ℝ) : ℝ≥0∞ := ν Set.univ

/-- `h(ν) = ⟨g, ν⟩ = ∫ cosh(z) g(q(z)) ν(dz)`. The integrand lies in `[0, 1]` (`g ≤ f` and
`cosh z · f(q(z)) = 1`), so it is integrable against every finite measure; every measure this
is applied to below is finite. -/
def hPot (ν : Measure ℝ) : ℝ := pairing gW ν

/-- The `j`-fold additive convolution power `μ^{*j}` (`μ^{*0} = δ₀`). -/
def convPow (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | j + 1 => μ ∗ convPow μ j

/-- The compound Poisson law of `∑_{z ∈ Π} z` for a Poisson point process `Π` with finite intensity
`μ`: `e^{−μ(ℝ)} ∑_j μ^{*j}/j!`. (Returns `0` when `μ(ℝ) = ∞`, which never happens below: the
intensities used are finite.) -/
def compoundPoisson (μ : Measure ℝ) : Measure ℝ :=
  if μ Set.univ = ∞ then 0 else
    Measure.sum fun j : ℕ =>
      ENNReal.ofReal (Real.exp (-(μ Set.univ).toReal) / (j.factorial : ℝ)) • convPow μ j

/-- `K_ν` (Definition 4.2): the law of `X − X′` for independent copies `X, X′` of `∑_{z ∈ Π} a(z)`,
where `Π` is a Poisson point process on `ℝ` with intensity `w(z) ν(dz)`. The law of `∑ a(z)` is the
compound Poisson law with intensity `a_*(w · ν)`. -/
def Kmeas (ν : Measure ℝ) : Measure ℝ :=
  let μ : Measure ℝ := Measure.map aShift (ν.withDensity fun z => ENNReal.ofReal (wInt z))
  let X : Measure ℝ := compoundPoisson μ
  X ∗ Measure.map (fun z => -z) X

/-- The soft-field recursion (4.2): `R_β ν = β e^{h(ν)} K_ν`. -/
def Rbeta (β : ℝ) (ν : Measure ℝ) : Measure ℝ := ENNReal.ofReal (β * Real.exp (hPot ν)) • Kmeas ν

/-- The iterates `ν^γ_0 = 0`, `ν^γ_{r+1} = R_{e^{−γ}} ν^γ_r`. -/
def nuIter (γ : ℝ) : ℕ → Measure ℝ
  | 0 => 0
  | r + 1 => Rbeta (Real.exp (-γ)) (nuIter γ r)

/-- `m^γ_r = m(ν^γ_r)` (in `ℝ≥0∞`). -/
def mIter (γ : ℝ) (r : ℕ) : ℝ≥0∞ := massM (nuIter γ r)

/-- `h^γ_r = h(ν^γ_r)`. -/
def hIter (γ : ℝ) (r : ℕ) : ℝ := hPot (nuIter γ r)

/-- The critical threshold (4.8): `γ* = inf {γ ∈ ℝ : sup_{r ≥ 0} m^γ_r < ∞}` (the supremum taken in
`ℝ≥0∞`, so "finite" is literal; the infimum is `sInf` in `ℝ`, which Theorem 4.4 asserts to be the
infimum of a nonempty set bounded below). -/
def gammaStar : ℝ := sInf {γ : ℝ | (⨆ r : ℕ, mIter γ r) < ∞}

end KSATSingleFlip.Connect


