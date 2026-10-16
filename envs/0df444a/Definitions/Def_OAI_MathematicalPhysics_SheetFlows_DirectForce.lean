-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
-- name    : OAI_MathematicalPhysics_SheetFlows_DirectForce
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T00:52:25.571207+00:00
-- url     : https://prove2.me/theorems/d07b43ea-9581-49dc-ba1a-9ac092c58bb4
-- title:
--   Direct forcing $\partial_t u-\nu\Delta u$, axial shear fields and their straight particle paths
-- statement:
--   Points of $\mathbb{R}^3$ are written $x=(x_0,x_1,x_2)$, $e_0,e_1,e_2$ is the standard basis, and a *vector field* is a map $u:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$, $(t,x)\mapsto u(t,x)$. For such $u$ we use the spatial partial derivatives $\partial_j u(t,x)=D_xu(t,x)[e_j]$, the Laplacian $\Delta u=\sum_{j=0}^{2}\partial_j\partial_j u$, the divergence $\operatorname{div}u=\sum_{j=0}^{2}\partial_j u_j$, the advection term $(u\cdot\nabla)u\,(t,x)=D_xu(t,x)[u(t,x)]$, and the time derivative $\partial_t u(t,x)$ taken within the half-line $[0,\infty)$ (a right derivative at $t=0$). This file introduces the following objects.
--
--   1. **Direct force.** For a viscosity $\nu\in\mathbb{R}$ and a vector field $u$,
--   $$
--   \mathcal F_\nu(u)(t,x)=\partial_t u(t,x)-\nu\,\Delta u(t,x).
--   $$
--   2. **Erasing an axis.** For $i\in\{0,1,2\}$, $P_i:\mathbb{R}^3\to\mathbb{R}^3$ is the continuous linear map $P_ix=x-x_i\,e_i$, which replaces the $i$-th coordinate by $0$; in particular $P_ie_i=0$.
--   3. **Axial fields.** For $i\in\{0,1,2\}$ and an amplitude $a:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}$,
--   $$
--   A_{i,a}(t,x)=a\bigl(t,P_ix\bigr)\,e_i ,
--   $$
--   a field parallel to $e_i$ whose size does not depend on $x_i$. Whenever $a(t,\cdot)$ is differentiable at the point $P_ix$, the spatial derivative is $D_xA_{i,a}(t,x)[h]=D_xa(t,P_ix)[P_ih]\,e_i$ for $h\in\mathbb{R}^3$, and consequently
--   $$
--   \operatorname{div}A_{i,a}(t,x)=0,\qquad (A_{i,a}\cdot\nabla)A_{i,a}\,(t,x)=0 .
--   $$
--   In particular, if $a(t,\cdot)$ is differentiable on all of $\mathbb{R}^3$ for every $t$, then $A_{i,a}$ is divergence free at every $(t,x)$.
--   4. **Pulse trajectories.** For $i\in\{0,1,2\}$, a time profile $A:\mathbb{R}\to\mathbb{R}$, an amplitude $g:\mathbb{R}^3\to\mathbb{R}$ and a starting point $a\in\mathbb{R}^3$,
--   $$
--   \gamma_a(t)=a+A(t)\,g(P_ia)\,e_i ,
--   $$
--   and its transverse part is frozen: $P_i\gamma_a(t)=P_ia$ for all $t\in\mathbb{R}$.
--
--   These are the elementary building blocks of an explicit construction of smooth, spatially $10$-periodic forcings for the incompressible Navier–Stokes equations. If $u$ is divergence free and its advection term vanishes, then $u$ satisfies $\partial_tu+(u\cdot\nabla)u=-\nabla p+\nu\Delta u+f$ with $f=\mathcal F_\nu(u)$ and pressure $p=0$, so the forcing is read off directly from the desired velocity. Axial (shear) fields are of exactly this kind, and since $P_i\gamma_a$ is constant, $\gamma_a$ is the particle path of the velocity $A'(t)\,g(P_ix)\,e_i$ whenever $A$ is differentiable: particles move on straight lines parallel to $e_i$.
--
--   **Formalization Note** The objects are `directForce`, `eraseAxis`, `axialField` and `pulseTrajectory`; the derivative formula and its consequences are `fderiv_axialField`, `divergence_axialField`, `advection_axialField`, `axialField_divergence_free` and `eraseAxis_pulseTrajectory`. The time derivative `timePartial` is `derivWithin` on `Set.Ici 0`. The file also contains simp lemmas saying that the spatial and time partials, Laplacian, gradient, advection term and all iterated mixed space–time derivatives of the zero field vanish.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/DirectForce.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/DirectForce.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SolenoidalSheetPrograms mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms

namespace OAI

/-! SheetFlows direct force. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

@[simp] theorem spatialPartial_zero (j : Fin 3) : spatialPartial (0 : Field) j = 0 := by
  funext t x
  simp [spatialPartial]

@[simp] theorem timePartial_zero : timePartial (0 : Field) = 0 := by
  funext t x
  simp [timePartial]

@[simp] theorem laplacian_zero : laplacian (0 : Field) = 0 := by
  funext t x
  simp [laplacian]

@[simp] theorem gradient_zero : gradient (0 : Pressure) = 0 := by
  funext t x j
  simp [gradient]

@[simp] theorem advection_zero : advection (0 : Field) = 0 := by
  funext t x
  simp [advection]

@[simp] theorem mixedDerivative_zero (α : List (Fin 4)) :
    mixedDerivative (0 : Field) α = 0 := by
  induction α with
  | nil => rfl
  | cons j α ih =>
    funext z
    simp [mixedDerivative, ih]

def directForce (ν : ℝ) (u : Field) : Field :=
  fun t x => timePartial u t x - ν • laplacian u t x

def eraseAxis (i : Fin 3) : Space →L[ℝ] Space :=
  ContinuousLinearMap.id ℝ Space -
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).smulRight (basis i)

@[simp] theorem eraseAxis_apply (i : Fin 3) (x : Space) :
    eraseAxis i x = x - x i • basis i := rfl

@[simp] theorem eraseAxis_basis (i : Fin 3) : eraseAxis i (basis i) = 0 := by
  simp [eraseAxis, basis]

def axialField (i : Fin 3) (a : ℝ → Space → ℝ) : Field :=
  fun t x => a t (eraseAxis i x) • basis i

theorem fderiv_axialField (i : Fin 3) (a : ℝ → Space → ℝ) (t : ℝ) (x : Space)
    (ha : DifferentiableAt ℝ (a t) (eraseAxis i x)) :
    fderiv ℝ (axialField i a t) x =
      ((fderiv ℝ (a t) (eraseAxis i x)).comp (eraseAxis i)).smulRight (basis i) := by
  exact ((ha.hasFDerivAt.comp x (eraseAxis i).hasFDerivAt).smul_const (basis i)).fderiv

theorem divergence_axialField (i : Fin 3) (a : ℝ → Space → ℝ) (t : ℝ) (x : Space)
    (ha : DifferentiableAt ℝ (a t) (eraseAxis i x)) :
    divergence (axialField i a) t x = 0 := by
  unfold divergence
  apply Finset.sum_eq_zero
  intro j _
  dsimp [spatialPartial]
  rw [fderiv_axialField i a t x ha]
  by_cases h : j = i
  · subst j
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      eraseAxis_basis, map_zero, zero_smul, Pi.zero_apply]
  · simp [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, basis,
      Pi.single_eq_of_ne h]

theorem advection_axialField (i : Fin 3) (a : ℝ → Space → ℝ) (t : ℝ) (x : Space)
    (ha : DifferentiableAt ℝ (a t) (eraseAxis i x)) :
    advection (axialField i a) t x = 0 := by
  dsimp [advection]
  rw [fderiv_axialField i a t x ha]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    axialField, map_smul, eraseAxis_basis, smul_zero, map_zero, zero_smul]

theorem axialField_divergence_free (i : Fin 3) (a : ℝ → Space → ℝ)
    (ha : ∀ t, Differentiable ℝ (a t)) : DivergenceFree (axialField i a) := by
  intro t x
  exact divergence_axialField i a t x (ha t _)

def pulseTrajectory (i : Fin 3) (A : ℝ → ℝ) (g : Space → ℝ)
    (a : Space) (t : ℝ) : Space :=
  a + (A t * g (eraseAxis i a)) • basis i

@[simp] theorem eraseAxis_pulseTrajectory (i : Fin 3) (A : ℝ → ℝ)
    (g : Space → ℝ) (a : Space) (t : ℝ) :
    eraseAxis i (pulseTrajectory i A g a t) = eraseAxis i a := by
  simp only [pulseTrajectory, map_add, map_smul, eraseAxis_basis, smul_zero, add_zero]

end Solenoidal
end
end

end OAI


