-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T03:04:10.782468+00:00
-- url     : https://prove2.me/theorems/46f6659d-72bd-42e6-bb03-27dd2a8883eb
-- title:
--   Encodability of the universal machine's alphabets
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   The universal machine is obtained from the standard compilation of partial recursive functions into multi-stack Turing machines and then into single-tape machines. This module equips the finite types appearing there with the structure needed for computability arguments. The set of four stack names is finite, and the stack symbols are encodable through a numbering by $\{0,\dots,N-1\}$. The single-tape alphabet consists of pairs (a bottom-marker bit, an optional symbol for each stack); it is finite and encodable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/UniversalInput.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/UniversalInput.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BalancedThreeStack mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Universal
open Turing PartrecToTM2
open scoped Classical

instance : Fintype K' := ⟨{.main,.rev,.aux,.stack}, by intro k; cases k <;> simp⟩

instance : Primcodable Γ' := Primcodable.ofEquiv (Fin (Fintype.card Γ')) (Fintype.equivFin Γ')

abbrev StackAlphabet := TM2to1.Γ' K' (fun _ => Γ')

instance : Primcodable (Bool × (K' → Option Γ')) :=
  Primcodable.ofEquiv (Fin (Fintype.card StackAlphabet)) (Fintype.equivFin StackAlphabet)

instance : Primcodable StackAlphabet :=
  (inferInstance : Primcodable (Bool × (K' → Option Γ')))

end BalancedTransport.Universal
end

end OAI


