-- Prove2me | Definitions.Def_Arxiv2412_13833_Basic
-- name    : Arxiv2412_13833_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-26T12:54:48.113625+00:00
-- url     : https://prove2.me/theorems/838e1b14-5317-5999-aa49-4fc953f50b4a
-- title:
--   Acoustic wave operator and monopole, dipole and homogeneous Green's functions of an inhomogeneous lossless medium
-- statement:
--   Objects of Appendix A of Wapenaar (2025), *Multiple reflections on Huygens' principle*.
--
--   1. **Space and time.** A point of space is $\mathbf x=(\mathbf x_H,z)$, with $n$ horizontal coordinates $\mathbf x_H$ ($n=1$ in 2D, $n=2$ in 3D) and the depth $z$, which points downward. Space-time points are $(\mathbf x,t)$. Test functions are the smooth, compactly supported real functions $\varphi(\mathbf x,t)$. Distributions are the continuous linear functionals on them, as in Mathlib.
--   2. **Medium.** An inhomogeneous lossless acoustic medium is given by a mass density $\rho(\mathbf x)>0$ and a propagation velocity $c(\mathbf x)>0$. Both are smooth and independent of time.
--   3. **Wave operator (A-2).** $\mathcal L=\nabla\cdot\frac1\rho\nabla-\frac{1}{\rho c^2}\partial_t^2$. The operator is formally self-adjoint, so for a distribution $u$ the equation $\mathcal Lu=f$ means $u(\mathcal L\varphi)=f(\varphi)$ for every test function $\varphi$.
--   4. **Sources.** These are the right-hand sides of (A-3), (A-5) and (A-12), as functionals of $\varphi$:
--      - $-\delta(\mathbf x-\mathbf x')\delta(t)$ acts as $\varphi\mapsto-\varphi(\mathbf x',0)$;
--      - $-\delta(\mathbf x-\mathbf x')\partial_t\delta(t)$ acts as $\varphi\mapsto\partial_t\varphi(\mathbf x',0)$;
--      - $\frac{1}{\rho(\mathbf x')}\partial_z\delta(\mathbf x-\mathbf x')\delta(t)$ acts as $\varphi\mapsto-\frac{1}{\rho(\mathbf x')}\partial_z\varphi(\mathbf x',0)$.
--   5. **Causality (A-4).** $u=0$ for $t<0$: $u(\varphi)=0$ for every test function supported in $\{t<0\}$.
--   6. **Time reversal and time derivative.** $v(\mathbf x,t)=u(\mathbf x,-t)$ means $v(\varphi)=u(\varphi(\cdot,-\,\cdot))$, and $(\partial_tu)(\varphi)=-u(\partial_t\varphi)$.
--   7. **Green's functions.** All three are causal.
--      - $\mathcal G(\mathbf x,\mathbf x',t)$ solves (A-3): $\mathcal L\mathcal G=-\delta(\mathbf x-\mathbf x')\delta(t)$.
--      - The monopole Green's function $G$ solves (A-5): $\mathcal LG=-\delta(\mathbf x-\mathbf x')\partial_t\delta(t)$.
--      - The dipole Green's function $G_d$ solves (A-12): $\mathcal LG_d=\frac{1}{\rho(\mathbf x')}\partial_z\delta(\mathbf x-\mathbf x')\delta(t)$.
--
--      Each is a distribution in $(\mathbf x,t)$ for a fixed source point $\mathbf x'$.
--
--   **Formalization Note** The paper writes $\mathcal G(\mathbf x,\mathbf x',-t)$ as a function. Here a time-reversed distribution is characterized by its action on test functions, and statements take it as a second distribution together with that characterization. Smooth coefficients are needed for $\mathcal L$ to act on distributions; the paper does not state a regularity class.
-- source:
--   Wapenaar, Multiple reflections on Huygens' principle, arXiv:2412.13833v2 (2025), Appendix A (A-1 Monopole Green's function, A-2 Homogeneous Green's function, A-3 Dipole Green's function), eqs. (A-1)-(A-14), PDF pp. 20-21

import Mathlib

/-!
K. Wapenaar, *Multiple reflections on Huygens' principle*, arXiv:2412.13833v2 (2025):
the acoustic wave operator of an inhomogeneous lossless medium and the monopole, dipole and
homogeneous Green's functions of Appendix A (eqs. (A-1)-(A-14), PDF pp. 20-21).

A point of space is `x = (x_H, z)`, with `n` horizontal coordinates `x_H` (`n = 1` in 2D,
`n = 2` in 3D) and the depth `z` (pointing downward). Green's functions are distributions
(in Mathlib's sense) on space-time `(x, t)`.
-/

open TopologicalSpace

noncomputable section

namespace Arxiv2412_13833

/-- Appendix A: a point `x = (x_H, z)` of space, with `n` horizontal coordinates and the
depth `z`. -/
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n) × ℝ

/-- Appendix A: a point `(x, t)` of space-time. -/
abbrev SpaceTime (n : ℕ) := Space n × ℝ

/-- Real-valued smooth compactly supported test functions on space-time. -/
abbrev TestFn (n : ℕ) := TestFunction (⊤ : Opens (SpaceTime n)) ℝ (⊤ : ℕ∞)

/-- Real-valued distributions on space-time (continuous linear functionals on `TestFn n`). -/
abbrev Distrib (n : ℕ) := Distribution (⊤ : Opens (SpaceTime n)) ℝ (⊤ : ℕ∞)

/-- Appendix A-1: an inhomogeneous lossless acoustic medium, given by its mass density
`ρ(x) > 0` and propagation velocity `c(x) > 0`, both independent of time. The coefficients are
taken smooth so that the wave operator (A-2) acts on distributions. -/
structure Medium (n : ℕ) where
  /-- Mass density `ρ(x)`. -/
  rho : Space n → ℝ
  /-- Propagation velocity `c(x)`. -/
  c : Space n → ℝ
  rho_pos : ∀ x, 0 < rho x
  c_pos : ∀ x, 0 < c x
  rho_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) rho
  c_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c

/-- The space-time direction of the `i`-th horizontal coordinate. -/
def hDir {n : ℕ} (i : Fin n) : SpaceTime n := ((EuclideanSpace.single i 1, 0), 0)

/-- The space-time direction of the depth coordinate `z` (pointing downward). -/
def zDir {n : ℕ} : SpaceTime n := ((0, 1), 0)

/-- The space-time direction of time `t`. -/
def tDir {n : ℕ} : SpaceTime n := (0, 1)

/-- The space direction of the depth coordinate `z`, used to move a source point vertically. -/
def zSpaceDir {n : ℕ} : Space n := (0, 1)

/-- Directional derivative `∂_v f` of a function on space-time. -/
def pderiv {n : ℕ} (v : SpaceTime n) (f : SpaceTime n → ℝ) : SpaceTime n → ℝ :=
  fun p => fderiv ℝ f p v

/-- Eq. (A-2): the wave operator `L = ∇·(1/ρ)∇ - (1/(ρc²)) ∂_t²` applied to a function on
space-time. -/
def waveOp {n : ℕ} (M : Medium n) (f : SpaceTime n → ℝ) : SpaceTime n → ℝ :=
  fun p =>
    (∑ i, pderiv (hDir i) (fun q => (M.rho q.1)⁻¹ * pderiv (hDir i) f q) p) +
      pderiv zDir (fun q => (M.rho q.1)⁻¹ * pderiv zDir f q) p -
      (M.rho p.1 * M.c p.1 ^ 2)⁻¹ * pderiv tDir (pderiv tDir f) p

/-- Eq. (A-2) on distributions: `L u = f`, where `f` is a linear functional on test functions.
The operator `L` is formally self-adjoint, so `⟨L u, φ⟩ = ⟨u, L φ⟩`; the condition reads
`u(L φ) = f(φ)` for every test function `φ` (for a smooth medium, `L φ` is again a test
function). -/
def SolvesWave {n : ℕ} (M : Medium n) (u : Distrib n) (f : TestFn n → ℝ) : Prop :=
  ∀ φ ψ : TestFn n, (⇑ψ = waveOp M ⇑φ) → u ψ = f φ

/-- Eq. (A-3), right-hand side: the impulsive source `-δ(x - x') δ(t)`, i.e. `φ ↦ -φ(x', 0)`. -/
def impulseSource {n : ℕ} (x' : Space n) : TestFn n → ℝ :=
  fun φ => -φ (x', 0)

/-- Eq. (A-5), right-hand side: the source `-δ(x - x') ∂_t δ(t)` of an impulsive
volume-injection rate, i.e. `φ ↦ ∂_t φ(x', 0)`. -/
def monopoleSource {n : ℕ} (x' : Space n) : TestFn n → ℝ :=
  fun φ => pderiv tDir ⇑φ (x', 0)

/-- Eq. (A-12), right-hand side: the vertical dipole source `(1/ρ(x')) ∂_z δ(x - x') δ(t)`,
i.e. `φ ↦ -(1/ρ(x')) ∂_z φ(x', 0)`. -/
def dipoleSource {n : ℕ} (M : Medium n) (x' : Space n) : TestFn n → ℝ :=
  fun φ => -((M.rho x')⁻¹ * pderiv zDir ⇑φ (x', 0))

/-- Eq. (A-4): causality, `u = 0` for `t < 0`, i.e. `u` vanishes on every test function
supported in `{t < 0}`. -/
def IsCausal {n : ℕ} (u : Distrib n) : Prop :=
  ∀ φ : TestFn n, (∀ p ∈ tsupport ⇑φ, p.2 < 0) → u φ = 0

/-- Appendix A-2: `v` is the time reversal of `u`, `v(x, t) = u(x, -t)`, i.e.
`v(φ) = u(φ(·, -·))` for every test function `φ`. -/
def IsTimeReversal {n : ℕ} (u v : Distrib n) : Prop :=
  ∀ φ ψ : TestFn n, (⇑ψ = fun p => φ (p.1, -p.2)) → v φ = u ψ

/-- The time derivative `∂_t u` of a distribution, `(∂_t u)(φ) = -u(∂_t φ)`. -/
def timeDeriv {n : ℕ} (u : Distrib n) : Distrib n :=
  Distribution.lineDerivCLM (k := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) tDir u

/-- Eqs. (A-3)-(A-4): `u` is the Green's function `𝒢(x, x', t)` with source point `x'`, the
causal solution of `L 𝒢 = -δ(x - x') δ(t)`. -/
def IsImpulseGreen {n : ℕ} (M : Medium n) (x' : Space n) (u : Distrib n) : Prop :=
  SolvesWave M u (impulseSource x') ∧ IsCausal u

/-- Eq. (A-5): `u` is the monopole Green's function `G(x, x', t)` with source point `x'`, the
causal solution of `L G = -δ(x - x') ∂_t δ(t)`. -/
def IsMonopoleGreen {n : ℕ} (M : Medium n) (x' : Space n) (u : Distrib n) : Prop :=
  SolvesWave M u (monopoleSource x') ∧ IsCausal u

/-- Eq. (A-12): `u` is the dipole Green's function `G_d(x, x', t)` with source point `x'`, the
causal solution of `L G_d = (1/ρ(x')) ∂_z δ(x - x') δ(t)`. -/
def IsDipoleGreen {n : ℕ} (M : Medium n) (x' : Space n) (u : Distrib n) : Prop :=
  SolvesWave M u (dipoleSource M x') ∧ IsCausal u

end Arxiv2412_13833


