-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T02:41:02.02371+00:00
-- url     : https://prove2.me/theorems/f0d4c305-745e-421b-b7a9-80454ab8404c
-- title:
--   Boxes coding recorder configurations
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   A configuration of the recorder is coded by a point of $\mathbb R^3$: one coordinate per stack, plus an offset recording the control state.
--
--   1. **Digits.** The base is $B=2|L|+1$ where $L$ is the finite set of stack letters. Letter number $j$ gets the odd digit $2j+1$, so codes of distinct letters are separated.
--   2. **Boxes.** For an origin $o$ and three words $u_0,u_1,u_2$, the box is $\{x:x_i-o_i\in I(u_i)\text{ for }i=0,1,2\}$, where $I(u)$ is the coding interval of the prefix $u$. The box map applies the prefix replacement $u_i\mapsto v_i$ in each coordinate and moves the origin $o$ to $o'$.
--   3. **Coded points.** The point $o+(c(s_0),c(s_1),c(s_2))$, where $c$ is the stream code in base $B$.
--   4. **Placement.** Origins are $(4k,0,0)$. The halting ready state gets $k=0$ and every other control state gets a distinct positive $k$.
--   5. **Instruction boxes.** The source box of an instruction uses the origin of its source control and its three source prefixes; the target box is defined in the same way.
--
--   Applying a row then corresponds to moving its source box affinely onto its target box. Balanced rows preserve volume.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/BoxCoding.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/BoxCoding.lean by skeleton subtraction
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

namespace OAI

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Recorder.Instruction
variable {Q Γ : Type*}

def sourcePrefixes (r : Instruction Q Γ) : Fin 3 → List (Letter Q Γ) :=
  ![r.sourceLeft, r.sourceRight, r.sourceHistory]

def targetPrefixes (r : Instruction Q Γ) : Fin 3 → List (Letter Q Γ) :=
  ![r.targetLeft, r.targetRight, r.targetHistory]

end BalancedTransport.Recorder.Instruction
end

noncomputable section
namespace BalancedTransport

end BalancedTransport
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}
open Stream'

def oddDigit {n : ℕ} (a : Fin n) : Fin (2 * n + 1) :=
  ⟨2 * a.val + 1, by omega⟩

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Coding
variable {S : Type*}

def box (r : ℝ) (digit : S → ℝ) (o : Space) (u : Fin 3 → List S) : Set Space :=
  {x | ∀ i, x i - o i ∈ interval r digit (u i)}

def boxMap (r : ℝ) (digit : S → ℝ) (o o' : Space)
    (u v : Fin 3 → List S) (x : Space) : Space :=
  fun i => o' i + replacement r digit (u i) (v i) (x i - o i)

def codedPoint {B : ℕ} (digit : S → Fin B) (o : Space) (s : Fin 3 → Stream' S) : Space :=
  fun i => o i + stream digit (s i)

def origin (k : ℕ) : Space := ![4 * (k : ℝ), 0, 0]

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*}

def placement [Fintype Q] [DecidableEq Q] (M : Machine Q Γ) (s : Control Q) : ℕ :=
  if s = .ready M.halt then 0 else (Fintype.equivFin (Control Q) s).val + 1

@[simp] theorem placement_halt [Fintype Q] [DecidableEq Q] (M : Machine Q Γ) :
    placement M (.ready M.halt) = 0 := by simp [placement]

def Instruction.sourceBox (inst : Instruction Q Γ) (r : ℝ) (digit : Letter Q Γ → ℝ)
    (id : Control Q → ℕ) : Set Space :=
  Coding.box r digit (Coding.origin (id inst.sourceControl)) inst.sourcePrefixes

def Instruction.targetBox (inst : Instruction Q Γ) (r : ℝ) (digit : Letter Q Γ → ℝ)
    (id : Control Q → ℕ) : Set Space :=
  Coding.box r digit (Coding.origin (id inst.targetControl)) inst.targetPrefixes

end BalancedTransport.Recorder
end

noncomputable section
namespace BalancedTransport.Recorder
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ]

def base (Q Γ : Type*) [Fintype Q] [Fintype Γ] : ℕ :=
  2 * Fintype.card (Letter Q Γ) + 1

def digit (a : Letter Q Γ) : Fin (base Q Γ) :=
  Coding.oddDigit (Fintype.equivFin (Letter Q Γ) a)

end BalancedTransport.Recorder
end

end OAI


