-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work__ForcedNavierStokesComputation
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work__ForcedNavierStokesComputation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:05:40.198204+00:00
-- url     : https://prove2.me/theorems/7bd6522d-a75c-42b2-9b48-d48f49b0c0a5
-- title:
--   Divergence-free affine fields localized to a box
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   This module defines the vector calculus used to build incompressible velocity fields.
--
--   1. **Partial derivatives, curl and divergence** of fields on $\mathbb R^3$.
--   2. **Affine potential.** For a centre $c$, a translation velocity $v$ and rates $l$,
--   $A(x)=\tfrac12\,v\times(x-c)+\tfrac13\bigl((l_1-l_2)y_1y_2,\,(l_2-l_0)y_2y_0,\,(l_0-l_1)y_0y_1\bigr)$ with $y=x-c$. When $l_0+l_1+l_2=0$, its curl is the affine field $v+\mathrm{diag}(l)(x-c)$.
--   3. **Box cutoff.** For a box $[a,b]$ and $\eta>0$, a product of smooth transitions in each coordinate. It equals $1$ on the closed $\eta$-enlargement of the box and vanishes outside the open $2\eta$-enlargement. The open and closed enlargements are defined as product sets.
--   4. **Localized affine field.** The curl of the cutoff times the affine potential. It is divergence free, supported near the box, and equal to the affine field on the $\eta$-enlargement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Work.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Work.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForcedNavierStokesComputation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Model
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding__ForcedNavierStokesComputation

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def pd (i : Fin 3) (f : Space → F) (x : Space) : F :=
  fderiv ℝ f x (Pi.single i 1)

@[simp] theorem pd_const (i : Fin 3) (a : F) (x : Space) :
    pd i (fun _ => a) x = 0 := by simp [pd]

@[simp] theorem pd_coord (i j : Fin 3) (x : Space) :
    pd i (fun y : Space => y j) x = (Pi.single i (1 : ℝ) : Space) j := by
  rw [pd, (hasFDerivAt_apply j x).fderiv]
  rfl

@[simp] theorem pd_sub_const (i : Fin 3) (f : Space → F) (a : F) (x : Space) :
    pd i (fun y => f y - a) x = pd i f x := by
  simp only [pd, fderiv_sub_const]

def curl (A : Space → Space) (x : Space) : Space :=
  ![pd 1 (fun y => A y 2) x - pd 2 (fun y => A y 1) x,
    pd 2 (fun y => A y 0) x - pd 0 (fun y => A y 2) x,
    pd 0 (fun y => A y 1) x - pd 1 (fun y => A y 0) x]

def divergence (A : Space → Space) (x : Space) : ℝ :=
  ∑ i, pd i (fun y => A y i) x

@[simp] theorem curl_zero : curl (0 : Space → Space) = 0 := by
  funext x
  simp [curl]

def affinePotential (c v l : Space) (x : Space) : Space :=
  ![(1 / 2 : ℝ) * (v 1 * (x 2 - c 2) - v 2 * (x 1 - c 1)) +
      (1 / 3 : ℝ) * (l 1 - l 2) * (x 1 - c 1) * (x 2 - c 2),
    (1 / 2 : ℝ) * (v 2 * (x 0 - c 0) - v 0 * (x 2 - c 2)) +
      (1 / 3 : ℝ) * (l 2 - l 0) * (x 2 - c 2) * (x 0 - c 0),
    (1 / 2 : ℝ) * (v 0 * (x 1 - c 1) - v 1 * (x 0 - c 0)) +
      (1 / 3 : ℝ) * (l 0 - l 1) * (x 0 - c 0) * (x 1 - c 1)]

def boxCutoff (a b : Space) (η : ℝ) (x : Space) : ℝ :=
  ∏ i : Fin 3, Real.smoothTransition ((x i - a i + 2 * η) / η) *
    Real.smoothTransition ((b i + 2 * η - x i) / η)

def openEnlargement (a b : Space) (η : ℝ) : Set Space :=
  Set.pi Set.univ (fun i => Set.Ioo (a i - η) (b i + η))

def closedEnlargement (a b : Space) (η : ℝ) : Set Space :=
  Set.Icc (fun i => a i - η) (fun i => b i + η)

@[simp] theorem mem_openEnlargement (a b : Space) (η : ℝ) (x : Space) :
    x ∈ openEnlargement a b η ↔ ∀ i, a i - η < x i ∧ x i < b i + η := by
  simp [openEnlargement]

@[simp] theorem mem_closedEnlargement (a b : Space) (η : ℝ) (x : Space) :
    x ∈ closedEnlargement a b η ↔ ∀ i, a i - η ≤ x i ∧ x i ≤ b i + η := by
  simp only [closedEnlargement, mem_Icc, Pi.le_def, forall_and]

def localizedAffine (a b c v l : Space) (η : ℝ) : Space → Space :=
  curl (fun x => boxCutoff a b η x • affinePotential c v l x)

end BalancedTransport.Geometry
end

end OAI


