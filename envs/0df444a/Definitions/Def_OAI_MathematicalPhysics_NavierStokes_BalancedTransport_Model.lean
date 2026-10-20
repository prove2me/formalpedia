-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Model
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:54:42.327988+00:00
-- url     : https://prove2.me/theorems/7dc3b684-0fd7-495a-955e-4a0e067b1c50
-- title:
--   Head moves form a finite type
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   A finite deterministic tape machine has transitions that write a symbol, change state and move the head by one of three moves: stay, left or right. This module records that the set of head moves
--   $$
--   \{\text{stay},\ \text{left},\ \text{right}\}
--   $$
--   is a finite type. It lets transition tables, recorder rows and their records be enumerated as finite sets, for example when the recorder's table of valid rows is formed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForcedNavierStokesComputation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForcedNavierStokesComputation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds__ForcedNavierStokesComputation

namespace OAI

noncomputable section
namespace BalancedTransport.Recorder

instance : Fintype Direction :=
  ⟨{.stay, .left, .right}, by intro d; cases d <;> simp⟩

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport

end BalancedTransport
end

noncomputable section
namespace BalancedTransport
open MeasureTheory
open scoped ENNReal
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

end BalancedTransport
end

end OAI


