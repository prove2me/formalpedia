-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds__ForcedNavierStokesComputation
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds__ForcedNavierStokesComputation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:09:23.272919+00:00
-- url     : https://prove2.me/theorems/0443fc66-0201-4c3a-a3b1-ef305ef045c6
-- title:
--   Mixed derivatives, spatial supports and eventual periodicity
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   1. **Mixed derivatives.** A multi-index is a list whose entries are either time or a spatial direction $i\in\{0,1,2\}$. Its mixed derivative applies $\partial_t$ or $\partial_{x_i}$ for each entry. Here time derivatives are taken of the full two-variable field.
--   2. **Spatial support.** A field is spatially supported in $K\subseteq\mathbb R^3$ when $v(t,x)=0$ for all $t$ and all $x\notin K$. This passes to time derivatives.
--   3. **Eventual periodicity.** A field repeats after $T$ when $v(t+1,\cdot)=v(t,\cdot)$ for all $t\ge T$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/FieldBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/FieldBounds.lean by skeleton subtraction
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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work__ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity__ForcedNavierStokesComputation

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def fullMixedD : MultiIndex → Field F → Field F
  | [], v => v
  | none :: a, v => fullTimeD (fullMixedD a v)
  | some i :: a, v => spaceD i (fullMixedD a v)

def SpatiallySupported (K : Set Space) (v : Field F) : Prop :=
  ∀ t x, x ∉ K → v t x = 0

lemma SpatiallySupported.fullTimeD {K : Set Space} {v : Field F}
    (h : SpatiallySupported K v) : SpatiallySupported K (fullTimeD v) := by
  intro t x hx
  have he : (fun s => v s x) = fun _ => (0 : F) := funext (fun s => h s x hx)
  change deriv (fun s => v s x) t = 0
  rw [he]
  exact deriv_const t (0 : F)

def RepeatsAfter (T : ℝ) (v : Field F) : Prop :=
  ∀ t, T ≤ t → v (t + 1) = v t

end BalancedTransport.Geometry
end

end OAI


