-- Prove2me | Definitions.Def_MasulloGRH_MellinRpos
-- name    : MasulloGRH_MellinRpos
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-20T21:16:55.186168+00:00
-- url     : https://prove2.me/theorems/c40ba7be-abff-45a4-90fc-a77fc28bc271
-- title:
--   Schwartz–Bruhat functions on $\mathbb R_{>0}$, exponential decay, and Schwartz decay on vertical strips
-- statement:
--   These are the function classes on the multiplicative group $\mathbb R_{>0}$ and on vertical strips that are used for Mellin transforms and contour integrals.
--
--   A function on $\mathbb R_{>0}$ is written $\phi$, and $\psi(x)=\phi(e^x)$ is the same function in the additive coordinate $x=\log t$.
--
--   1. $\phi\in\mathcal S(\mathbb R_{>0})$, a **Schwartz–Bruhat function** on $\mathbb R_{>0}$, if $\psi$ is a Schwartz function on $\mathbb R$.
--   2. $\phi$ has **forward semi-exponential decay** if $\phi\in\mathcal S(\mathbb R_{>0})$ and $\phi$ and its derivatives decay faster than every power of $t^{-1}$ as $t\to+\infty$: for all integers $N,k\ge 0$ the function $e^{Nx}\,\psi^{(k)}(x)$ is bounded on $x\ge 0$.
--   3. $\phi$ has **backward semi-exponential decay** if $\phi\in\mathcal S(\mathbb R_{>0})$ and $\phi$ and its derivatives decay faster than every power of $t$ as $t\to0^+$: for all $N,k\ge0$ the function $e^{-Nx}\,\psi^{(k)}(x)$ is bounded on $x\le 0$.
--   4. $\phi$ has **exponential decay**, $\phi\in\mathcal S_E(\mathbb R_{>0})$, if $\phi\in\mathcal S(\mathbb R_{>0})$ and for all $N,k\ge 0$ the function $e^{N|x|}\,\psi^{(k)}(x)$ is bounded on $\mathbb R$.
--   5. For real $\sigma$, $t^\sigma\phi$ denotes the function $t\mapsto t^\sigma\phi(t)$.
--   6. $\mathbb C_{(a,b)}=\{s: a<\operatorname{Re}s<b\}$ and $\mathbb C_{[a,b]}=\{s:a\le\operatorname{Re}s\le b\}$ are the open and closed **vertical strips**.
--   7. A function $\Phi$ on $\mathbb C_{(a,b)}$ is **uniformly Schwartz over the strip** if for every $\varepsilon>0$ with $a+\varepsilon<b-\varepsilon$ and every integer $N\ge 1$ there is $C>0$ such that
--   $$|\Phi(\sigma+iy)|\le\frac{C}{|y|^N}$$
--   for all sufficiently large $|y|$, uniformly in $a+\varepsilon\le\sigma\le b-\varepsilon$.
--   8. A function $\Phi$ on $\mathbb C_{<b}$ is **Schwartz on the half-plane** if for every $\varepsilon>0$ and every $N\ge1$ the same bound holds for all sufficiently large $|y|$, uniformly in $\sigma\le b-\varepsilon$.
--   9. The integral over the upward vertical line $\operatorname{Re}s=c$ is $\int_{c-i\infty}^{c+i\infty}g(s)\,ds=i\int_{\mathbb R}g(c+iy)\,dy$. It is absolutely convergent if $y\mapsto g(c+iy)$ is integrable.
--
--   These notions are used in the Mellin inversion statements, the Asymptotic Cauchy Integral Formula and the Asymptotic Residue Theorem of Appendix B.
--
--   **Formalization Note** A function on $\mathbb R_{>0}$ is a function $\mathbb R\to\mathbb C$ of which only the values on $(0,\infty)$ are used. In items 2–4 the derivatives are taken in the coordinate $x$, i.e. they are $(t\,\partial_t)^k\phi$; since every power of $t$ is allowed as a weight, this is the same condition as for the derivatives $\partial_t^k\phi$. In items 7–8 the source also assumes $\Phi$ holomorphic; holomorphy is a separate hypothesis in the statements.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix B, §B.2, Definition B.2.1.1 (p. 593) and Definition B.2.2.1 (p. 600)

import Mathlib

/-!
# Schwartz–Bruhat functions on `ℝ_{>0}` and decay conditions on vertical strips

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Appendix B, §B.2:
Definition B.2.1.1 (p. 593) and Definition B.2.2.1 (p. 600).

A function on `ℝ_{>0}` is represented by a function `ϕ : ℝ → ℂ`; only its values on `(0, ∞)` are
used.  The Mellin transform `M(ϕ)(s) = ∫_0^∞ ϕ(t) t^s dt/t` is Mathlib's `mellin ϕ s`.
-/

namespace MasulloGRH

noncomputable section

/-- `ϕ ∈ S(ℝ_{>0})`: `ϕ` is a Schwartz–Bruhat function on the multiplicative group `ℝ_{>0}`, i.e.
`x ↦ ϕ (exp x)` is a Schwartz function on `ℝ`. -/
def IsSchwartzRpos (ϕ : ℝ → ℂ) : Prop :=
  ∃ ψ : SchwartzMap ℝ ℂ, ∀ x : ℝ, ψ x = ϕ (Real.exp x)

/-- Forward semi-exponential decay (Definition B.2.1.1(1)): `ϕ ∈ S(ℝ_{>0})` and `ϕ` and its
derivatives decay faster than any positive power of `t⁻¹` as `t → +∞`.  In the coordinate
`t = exp x` this says that `exp (N x) · (d/dx)^k (ϕ ∘ exp)` is bounded on `x ≥ 0` for all `N, k`. -/
def HasForwardSemiExpDecay (ϕ : ℝ → ℂ) : Prop :=
  IsSchwartzRpos ϕ ∧ ∀ N k : ℕ, ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x →
    Real.exp (N * x) * ‖iteratedDeriv k (fun u : ℝ => ϕ (Real.exp u)) x‖ ≤ C

/-- Backward semi-exponential decay (Definition B.2.1.1(1)): `ϕ ∈ S(ℝ_{>0})` and `ϕ` and its
derivatives decay faster than any positive power of `t` as `t → 0⁺`. -/
def HasBackwardSemiExpDecay (ϕ : ℝ → ℂ) : Prop :=
  IsSchwartzRpos ϕ ∧ ∀ N k : ℕ, ∃ C : ℝ, ∀ x : ℝ, x ≤ 0 →
    Real.exp (-(N * x)) * ‖iteratedDeriv k (fun u : ℝ => ϕ (Real.exp u)) x‖ ≤ C

/-- Exponential decay (Definition B.2.1.1(2)), the space `S_E(ℝ_{>0})`: `ϕ ∈ S(ℝ_{>0})` and `ϕ`
and its derivatives decay faster than any positive power of `exp (-|log t|)` as
`|log t| → +∞`. -/
def HasExpDecay (ϕ : ℝ → ℂ) : Prop :=
  IsSchwartzRpos ϕ ∧ ∀ N k : ℕ, ∃ C : ℝ, ∀ x : ℝ,
    Real.exp (N * |x|) * ‖iteratedDeriv k (fun u : ℝ => ϕ (Real.exp u)) x‖ ≤ C

/-- The function `t ↦ t^σ ϕ(t)` on `ℝ_{>0}`. -/
def powMul (σ : ℝ) (ϕ : ℝ → ℂ) : ℝ → ℂ := fun t => ((t ^ σ : ℝ) : ℂ) * ϕ t

/-- The open vertical strip `ℂ_{(a,b)} = {s : a < Re s < b}`. -/
def openStrip (a b : ℝ) : Set ℂ := {s : ℂ | a < s.re ∧ s.re < b}

/-- The closed vertical strip `ℂ_{[a,b]} = {s : a ≤ Re s ≤ b}`. -/
def closedStrip (a b : ℝ) : Set ℂ := {s : ℂ | a ≤ s.re ∧ s.re ≤ b}

/-- Definition B.2.2.1: the decay condition of a function that is *uniformly Schwartz over the
vertical strip* `ℂ_{(a,b)}`: for every `ε > 0` with `a + ε < b - ε` and every integer `N ≥ 1`
there is `C > 0` with `|Φ(σ + iy)| ≤ C / |y|^N` for all sufficiently large `|y|`, uniformly in
`a + ε ≤ σ ≤ b - ε`.  (The source applies the notion to functions holomorphic on the strip;
holomorphy is a separate hypothesis.) -/
def UniformlySchwartzOnStrip (Φ : ℂ → ℂ) (a b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → a + ε < b - ε → ∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, 0 < C ∧ ∃ Y : ℝ, ∀ s : ℂ,
    a + ε ≤ s.re → s.re ≤ b - ε → Y ≤ |s.im| → ‖Φ s‖ ≤ C / |s.im| ^ N

/-- Definition B.2.2.1: the decay condition of a function that is *Schwartz on the half-plane*
`ℂ_{<b}`: for every `ε > 0` and every integer `N ≥ 1` there is `C > 0` with
`|Φ(σ + iy)| ≤ C / |y|^N` for all sufficiently large `|y|`, uniformly in `σ ≤ b - ε`. -/
def SchwartzOnLeftHalfPlane (Φ : ℂ → ℂ) (b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, 1 ≤ N → ∃ C : ℝ, 0 < C ∧ ∃ Y : ℝ, ∀ s : ℂ,
    s.re ≤ b - ε → Y ≤ |s.im| → ‖Φ s‖ ≤ C / |s.im| ^ N

/-- The integral of `g` over the upward vertical line `Re s = c`:
`∫_{c - i∞}^{c + i∞} g(s) ds = i ∫_ℝ g(c + iy) dy`. -/
def verticalLineIntegral (g : ℂ → ℂ) (c : ℝ) : ℂ :=
  Complex.I * ∫ y : ℝ, g (c + y * Complex.I)

/-- Absolute convergence of the integral of `g` over the vertical line `Re s = c`. -/
def VerticalLineIntegrable (g : ℂ → ℂ) (c : ℝ) : Prop :=
  MeasureTheory.Integrable (fun y : ℝ => g (c + y * Complex.I))

end

end MasulloGRH


