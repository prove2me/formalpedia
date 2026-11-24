-- Prove2me | Definitions.Def_Arxiv1503_02159_Basic
-- name    : Arxiv1503_02159_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T12:36:20.446419+00:00
-- url     : https://prove2.me/theorems/8d46fd92-996c-4904-b1d7-6bfd97dc6d43
-- title:
--   One-dimensional scattering for half-line potentials: admissible potentials, the scattering solution $\psi^+$, and the phaseless data $S_1,S_2,S_3$
-- statement:
--   Objects of Sections 1 and 2 of Novikov (2015), for the one-dimensional Schrödinger equation
--
--   $$-\psi''+v(x)\psi=E\psi,\qquad x\in\mathbb R,\quad E=k^2>0. \tag{1.1}$$
--
--   1. **Admissible potentials (eqs. 1.2-1.3).** $v:\mathbb R\to\mathbb R$ is real-valued, $v\in L^1_1(\mathbb R)=\{u\in L^1(\mathbb R):\int_{\mathbb R}(1+|x|)|u(x)|\,dx<\infty\}$, and $v(x)=0$ for $x<0$.
--   2. **Scattering solution (eq. 1.4).** For $k>0$, a function $\psi:\mathbb R\to\mathbb C$ is called a scattering solution $\psi^+(\cdot,k)$ with reflection coefficient to the left $s_{21}$ and transmission coefficient to the right $s_{22}$ if $\psi$ is differentiable, solves (1.1) in the integrated form $\psi'(b)-\psi'(a)=\int_a^b(v(t)-k^2)\psi(t)\,dt$ for all $a,b$, is bounded on $\mathbb R$, and
--   $$\psi(x)=e^{ikx}+s_{21}e^{-ikx}+o(1)\ \ (x\to-\infty),\qquad \psi(x)=s_{22}e^{ikx}+o(1)\ \ (x\to+\infty).$$
--   A family $\psi^+(x,k)$, $s_{21}(k)$, $s_{22}(k)$ is the scattering data of $v$ if this holds for every $k>0$.
--   3. **The function $a$ (eq. 2.2).** $a(x,k)=|\psi^+(x,k)|^2-1$.
--   4. **Phaseless data (eqs. 1.10-1.12).** $S_1(x_1,x_2,k)=\{|s_{21}(k)|^2,|\psi^+(x_1,k)|^2,|\psi^+(x_2,k)|^2\}$, $S_2(x_1,x_2,x_3,k)=\{|\psi^+(x_i,k)|^2\}_{i=1,2,3}$, and $S_3(x,k)=\{|\psi^+(x,k)|^2,\ \tfrac{d}{dx}|\psi^+(x,k)|^2\}$.
--
--   **Formalization Note** The equation is imposed in the integrated (Carathéodory) form, the standard meaning of (1.1) when $v$ is only integrable. The paper's asymptotics (1.4) are read with an $o(1)$ remainder on both sides, as is standard. The data $S_1,S_2,S_3$ are encoded as ordered tuples of their real entries. The scattering solution is characterized by these properties rather than constructed; for admissible $v$ and $k>0$ such a triple $(\psi,s_{21},s_{22})$ exists and is unique (classical), but this is not proved here.
-- source:
--   R. G. Novikov, Phaseless inverse scattering in the one-dimensional case, arXiv:1503.02159v1, Section 1 (eqs. (1.1)-(1.4), (1.10)-(1.12)), Section 2 (eq. (2.2))

import Mathlib

/-!
R. G. Novikov, *Phaseless inverse scattering in the one-dimensional case*, arXiv:1503.02159v1 (2015):
the potentials of eq. (1.2)-(1.3), the scattering solution `ψ⁺` and the coefficients
`s₂₁`, `s₂₂` of eqs. (1.1), (1.4), the function `a` of eq. (2.2), and the phaseless scattering
data `S₁`, `S₂`, `S₃` of eqs. (1.10)-(1.12).
-/

open MeasureTheory Filter Topology

noncomputable section

namespace Arxiv1503_02159

/-- Eq. (1.2)-(1.3), Section 1, p. 1: the potential `v` is real-valued, lies in
`L¹₁(ℝ) = {u ∈ L¹(ℝ) : ∫ (1 + |x|) |u(x)| dx < ∞}`, and `v(x) = 0` for `x < 0`. -/
def IsAdmissiblePotential (v : ℝ → ℝ) : Prop :=
  Integrable v ∧ Integrable (fun x => (1 + |x|) * v x) ∧ ∀ x : ℝ, x < 0 → v x = 0

/-- Eqs. (1.1) and (1.4), Section 1, p. 1: `ψ` is a scattering solution `ψ⁺(·, k)` of
`-ψ'' + v ψ = k² ψ` with reflection coefficient to the left `s21` and transmission
coefficient to the right `s22`. That is, `ψ` is differentiable on `ℝ` and solves the equation in
integrated form, `ψ'(b) - ψ'(a) = ∫_a^b (v(t) - k²) ψ(t) dt` (so `ψ'` is absolutely continuous
and `ψ'' = (v - k²) ψ` almost everywhere); `ψ` is bounded; and
`ψ(x) = e^{ikx} + s21 e^{-ikx} + o(1)` as `x → -∞`, `ψ(x) = s22 e^{ikx} + o(1)` as `x → +∞`. -/
def IsScatteringSolution (v : ℝ → ℝ) (k : ℝ) (ψ : ℝ → ℂ) (s21 s22 : ℂ) : Prop :=
  Differentiable ℝ ψ ∧
  (∀ a b : ℝ, deriv ψ b - deriv ψ a = ∫ t in a..b, ((v t : ℂ) - (k : ℂ) ^ 2) * ψ t) ∧
  (∃ C : ℝ, ∀ x : ℝ, ‖ψ x‖ ≤ C) ∧
  Tendsto (fun x : ℝ => ψ x - (Complex.exp (k * x * Complex.I) +
    s21 * Complex.exp (-(k * x * Complex.I)))) atBot (𝓝 0) ∧
  Tendsto (fun x : ℝ => ψ x - s22 * Complex.exp (k * x * Complex.I)) atTop (𝓝 0)

/-- Eq. (1.4), Section 1, p. 1, for all energies: `ψ x k = ψ⁺(x, k)`, `s21 k = s₂₁(k)` and
`s22 k = s₂₂(k)` are the scattering solution and the scattering coefficients of `v` for every
`k = √E > 0`. -/
def IsScatteringData (v : ℝ → ℝ) (ψ : ℝ → ℝ → ℂ) (s21 s22 : ℝ → ℂ) : Prop :=
  ∀ k : ℝ, 0 < k → IsScatteringSolution v k (fun x => ψ x k) (s21 k) (s22 k)

/-- Eq. (2.2), Section 2, p. 3: `a(x, k) = |ψ⁺(x, k)|² - 1`, for the scattering solution
`ψ = ψ⁺(·, k)` at a fixed `k`. -/
def phaselessA (ψ : ℝ → ℂ) (x : ℝ) : ℝ :=
  ‖ψ x‖ ^ 2 - 1

/-- Eq. (1.10), Section 1, p. 3: the phaseless data
`S₁(x₁, x₂, k) = {|s₂₁(k)|², |ψ⁺(x₁, k)|², |ψ⁺(x₂, k)|²}`. -/
def dataS1 (ψ : ℝ → ℝ → ℂ) (s21 : ℝ → ℂ) (x1 x2 k : ℝ) : ℝ × ℝ × ℝ :=
  (‖s21 k‖ ^ 2, ‖ψ x1 k‖ ^ 2, ‖ψ x2 k‖ ^ 2)

/-- Eq. (1.11), Section 1, p. 3: the phaseless data
`S₂(x₁, x₂, x₃, k) = {|ψ⁺(x₁, k)|², |ψ⁺(x₂, k)|², |ψ⁺(x₃, k)|²}`. -/
def dataS2 (ψ : ℝ → ℝ → ℂ) (x1 x2 x3 k : ℝ) : ℝ × ℝ × ℝ :=
  (‖ψ x1 k‖ ^ 2, ‖ψ x2 k‖ ^ 2, ‖ψ x3 k‖ ^ 2)

/-- Eq. (1.12), Section 1, p. 3: the phaseless data
`S₃(x, k) = {|ψ⁺(x, k)|², d|ψ⁺(x, k)|²/dx}`. -/
def dataS3 (ψ : ℝ → ℝ → ℂ) (x k : ℝ) : ℝ × ℝ :=
  (‖ψ x k‖ ^ 2, deriv (fun y => ‖ψ y k‖ ^ 2) x)

end Arxiv1503_02159


