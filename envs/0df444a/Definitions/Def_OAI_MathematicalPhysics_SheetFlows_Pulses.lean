-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Pulses
-- name    : OAI_MathematicalPhysics_SheetFlows_Pulses
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:03:51.364983+00:00
-- url     : https://prove2.me/theorems/76e5c22a-9c6a-4982-a95b-de2fc9263f43
-- title:
--   Stationary shear pulses on the $10$-periodic torus and programs of pulses
-- statement:
--   Points of $\mathbb{R}^3$ are $x=(x_0,x_1,x_2)$, $e_0,e_1,e_2$ is the standard basis, and $Q=[0,10)^3$ is the fundamental cell of the lattice $10\mathbb{Z}^3$.
--
--   1. **Stationary pulse.** A stationary pulse is a vector field $w:\mathbb{R}^3\to\mathbb{R}^3$ such that
--      - $w$ is $C^\infty$;
--      - $w(x+10k)=w(x)$ for all $x\in\mathbb{R}^3$ and $k\in\mathbb{Z}^3$;
--      - $\int_Q w(x)\,dx=0$;
--      - $\operatorname{div}w=\sum_{j=0}^{2}\partial_jw_j=0$ everywhere;
--      - $Dw(x)[w(x)]=0$ for all $x$, i.e. the advection term $(w\cdot\nabla)w$ vanishes;
--      - $w$ is straight invariant: $w\bigl(x+c\,w(x)\bigr)=w(x)$ for all $x\in\mathbb{R}^3$ and $c\in\mathbb{R}$.
--   2. **Action.** A pulse $w$ acts on points by the displacement $a\mapsto a+w(a)$.
--   3. **Scaling.** For $c\in\mathbb{R}$, the field $c\,w$ is again a stationary pulse.
--   4. **Tensor pulses.** Let $i\in\{0,1,2\}$, let $g_0,g_1,g_2:\mathbb{R}\to\mathbb{R}$ be $C^\infty$ and $10$-periodic with $g_i\equiv1$, and suppose $\int_{[0,10)}g_j(s)\,ds=0$ for some index $j$. Then
--   $$
--   w(x)=g_0(x_0)\,g_1(x_1)\,g_2(x_2)\,e_i
--   $$
--   is a stationary pulse.
--   5. **Programs.** A program is a finite list $P=[w_1,\dots,w_n]$ of stationary pulses; it acts by
--   $$
--   P(a)=\bigl(\mathrm{id}+w_n\bigr)\circ\cdots\circ\bigl(\mathrm{id}+w_1\bigr)(a),
--   $$
--   the pulses being applied from first to last. The empty program is the identity, the program with first pulse $w$ and remaining list $P$ maps $a$ to $P(a+w(a))$, and the concatenation of $P$ and $P'$ acts as $P'\circ P$.
--
--   A stationary pulse is precisely a field that can be switched on for a short time with a smooth time weight $\rho(t)$ without creating pressure or nonlinear effects: $\rho(t)w(x)$ is divergence free with vanishing advection term, and by straight invariance every particle moves along a straight line and is displaced by exactly $c\,w(a)$, where $c=\int\rho$. A program therefore describes the time-one map of a scheduled velocity built from its pulses, and designing a flow with a prescribed time-one map reduces to designing a program.
--
--   **Formalization Note** `StationaryPulse` is a structure with the field `field` and the six proofs `smooth`, `periodic`, `mean_zero`, `divergence_zero`, `nonlinear_zero` and `straight`. The operations are `StationaryPulse.apply`, `StationaryPulse.scale` and `StationaryPulse.tensor` (which takes the zero-integral index $j$ explicitly); `runProgram` is a left fold over the list, with simp lemmas `runProgram_nil`, `runProgram_cons` and `runProgram_append`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/Pulses.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/Pulses.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SolenoidalSheetPrograms mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RectangleGeometry
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Trajectories

namespace OAI

/-! SheetFlows pulses. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Solenoidal

structure StationaryPulse where
  field : Space → Space
  smooth : ContDiff ℝ (⊤ : ℕ∞) field
  periodic : ∀ x k, field (x + deck k) = field x
  mean_zero : (∫ x in fundamentalCell, field x) = 0
  divergence_zero : DivergenceFree (fun _ => field)
  nonlinear_zero : ∀ x, fderiv ℝ field x (field x) = 0
  straight : StraightInvariant field

namespace StationaryPulse

def apply (p : StationaryPulse) (a : Space) : Space := a + p.field a

def scale (c : ℝ) (p : StationaryPulse) : StationaryPulse where
  field := fun x => c • p.field x
  smooth := p.smooth.const_smul c
  periodic := by intro x k; rw [p.periodic]
  mean_zero := by rw [integral_smul, p.mean_zero, smul_zero]
  divergence_zero := by
    intro t x
    change ∑ j : Fin 3, (fderiv ℝ (fun a => c • p.field a) x (basis j)) j = 0
    simp only [fderiv_fun_const_smul (p.smooth.differentiable (by simp) x),
      smul_apply, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    have h := p.divergence_zero t x
    change (∑ j : Fin 3, (fderiv ℝ p.field x (basis j)) j) = 0 at h
    rw [h, mul_zero]
  nonlinear_zero := by
    intro x
    rw [fderiv_fun_const_smul (p.smooth.differentiable (by simp) x)]
    simp only [smul_apply, map_smul, p.nonlinear_zero, smul_zero]
  straight := by
    intro x s
    change c • p.field (x + s • (c • p.field x)) = c • p.field x
    rw [← mul_smul, p.straight]

def tensor (i : Fin 3) (g : Fin 3 → ℝ → ℝ)
    (hsm : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j))
    (hp : ∀ j, Function.Periodic (g j) 10)
    (hi : ∀ s, g i s = 1) (j : Fin 3)
    (hz : (∫ s in Set.Ico (0 : ℝ) 10, g j s) = 0) : StationaryPulse where
  field := tensorVelocity i g 0
  smooth := (tensorScalar_contDiff g hsm).smul contDiff_const
  periodic := (tensorVelocity_spatially_periodic i g hp) 0
  mean_zero := tensorVelocity_mean_zero i g j hz 0
  divergence_zero := tensorVelocity_divergence_free i g hsm hi
  nonlinear_zero := tensorVelocity_advection_zero i g hsm hi 0
  straight := by
    rw [tensorVelocity_eq_axial i g hi]
    exact axialField_straightInvariant i _

end StationaryPulse

def runProgram (P : List StationaryPulse) (a : Space) : Space :=
  P.foldl (fun x p => p.apply x) a

@[simp] theorem runProgram_nil (a : Space) : runProgram [] a = a := rfl
@[simp] theorem runProgram_cons (p : StationaryPulse) (P : List StationaryPulse) (a : Space) :
    runProgram (p :: P) a = runProgram P (p.apply a) := rfl
@[simp] theorem runProgram_append (P Q : List StationaryPulse) (a : Space) :
    runProgram (P ++ Q) a = runProgram Q (runProgram P a) := List.foldl_append

end Solenoidal
end

end OAI


