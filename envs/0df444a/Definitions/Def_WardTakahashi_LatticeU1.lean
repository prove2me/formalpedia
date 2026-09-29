-- Prove2me | Definitions.Def_WardTakahashi_LatticeU1
-- name    : WardTakahashi_LatticeU1
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-27T20:33:47.196717+00:00
-- url     : https://prove2.me/theorems/88936d32-fc29-447f-86c8-c2562058da80
-- title:
--   Lattice $U(1)$ scalar field: phase rotations, local variations, path integral
-- statement:
--   Lattice model of a charged (complex) scalar field used to state the Ward–Takahashi identities in a finite-dimensional, mathematically rigorous setting.
--
--   1. A **field configuration** on $N$ lattice sites is a vector $\varphi=(\varphi_y)_{y}\in\mathbb C^N$.
--   2. The **global $U(1)$ rotation** by angle $\theta\in\mathbb R$ is $(R_\theta\varphi)_y=e^{i\theta}\varphi_y$ for every site $y$.
--   3. The **local generator** at site $x$ is the tangent vector $(g_x\varphi)_y=\delta_{xy}\, i\varphi_x$, i.e. the infinitesimal phase rotation of the single site $x$.
--   4. For a real-differentiable functional $F$ of the field (real- or complex-valued), its **local variation** at $x$ is
--   $$\delta_x F(\varphi)=DF(\varphi)\,[g_x\varphi].$$
--   5. An action $S:\mathbb C^N\to\mathbb R$ is **$U(1)$-invariant** if $S(R_\theta\varphi)=S(\varphi)$ for all $\theta,\varphi$.
--   6. The (unnormalised) **path integral** of an observable $F:\mathbb C^N\to\mathbb C$ is
--   $$Z_S[F]=\int_{\mathbb C^N}F(\varphi)\,e^{-S(\varphi)}\,d\varphi,$$
--   with Lebesgue measure $d\varphi$ on $\mathbb C^N\cong\mathbb R^{2N}$.
--
--   For a $U(1)$-invariant action, $\delta_x S$ plays the role of the (lattice) divergence of the Noether current at site $x$.
--
--   **Formalization Note** The Euclidean weight $e^{-S}$ replaces the Minkowski weight $e^{iS}$ of the source; expectation values are ratios $Z_S[F]/Z_S[1]$, so identities are stated for the unnormalised $Z_S$. The integral is a Bochner integral (value $0$ for non-integrable integrands).
-- source:
--   Wikipedia, "Ward–Takahashi identity" (revision oldid=1374751657), https://en.wikipedia.org/w/index.php?title=Ward%E2%80%93Takahashi_identity&oldid=1374751657 ; section "Derivation in the path integral formulation" (finite-dimensional lattice model)

import Mathlib

namespace WardTakahashi

open MeasureTheory Complex

/-- Field configurations of a complex scalar field on `N` lattice sites:
a configuration assigns a complex number `φ y` to every site `y`. -/
abbrev FieldConfig (N : ℕ) := Fin N → ℂ

/-- The global `U(1)` phase rotation `φ ↦ e^{iθ} φ`, applied at every site. -/
noncomputable def phaseRotate {N : ℕ} (θ : ℝ) (φ : FieldConfig N) : FieldConfig N :=
  fun y => Complex.exp ((θ : ℂ) * I) * φ y

/-- Infinitesimal generator of the *local* phase rotation at site `x`:
the tangent vector whose only nonzero entry is `i φ x`, at site `x`. -/
noncomputable def localGen {N : ℕ} (x : Fin N) (φ : FieldConfig N) : FieldConfig N :=
  Pi.single x (I * φ x)

/-- Infinitesimal local variation at site `x` of a (real-)differentiable functional `F`
of the field: the directional derivative of `F` at `φ` along `localGen x φ`. -/
noncomputable def localVar {N : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x : Fin N) (F : FieldConfig N → V) (φ : FieldConfig N) : V :=
  fderiv ℝ F φ (localGen x φ)

/-- An action `S` is invariant under global `U(1)` phase rotations. -/
def IsU1Invariant {N : ℕ} (S : FieldConfig N → ℝ) : Prop :=
  ∀ (θ : ℝ) (φ : FieldConfig N), S (phaseRotate θ φ) = S φ

/-- The (unnormalised) Euclidean lattice path integral of an observable `F`
with Boltzmann weight `e^{-S}` against Lebesgue measure on `ℂ^N`. -/
noncomputable def pathIntegral {N : ℕ} (S : FieldConfig N → ℝ) (F : FieldConfig N → ℂ) : ℂ :=
  ∫ φ, F φ * (Real.exp (-S φ) : ℂ)

end WardTakahashi


