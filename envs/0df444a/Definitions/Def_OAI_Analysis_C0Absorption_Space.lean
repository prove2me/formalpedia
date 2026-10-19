-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Space
-- name    : OAI_Analysis_C0Absorption_Space
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T21:38:26.793814+00:00
-- url     : https://prove2.me/theorems/49daa271-cf29-4230-ab85-ab360def3ec3
-- title:
--   The correction operator on the concrete space and the radial lift
-- statement:
--   These notions belong to the construction of a separable Banach space $Z$ that contains no linear copy of $c_0$, yet $Z\times c_0$ is bi-Lipschitz equivalent to $Z$ and $Z$ is Lipschitz-universal for separable metric spaces. $Z$ is a completion of the space of molecules on the unit ball of $c_0$ (finitely supported functions with total sum zero), normed by test functions from carefully chosen Lipschitz classes. Levels are pairs $(i,n)$, labels are (level, band, grid tag), and the coordinates of $c_0$ are split into row coordinates indexed by $\mathbb N$ and label coordinates indexed by labels. Let $Z$ be the concrete space and $\zeta:B\to Z$ the map sending $s$ to the class of $\delta_s-\delta_0$.
--
--   1. **Corrections as tests.** Each correction $\mathrm{corr}(\gamma)$ is the value of the empty generated representation, so it lies in the class $T_0$. Hence $|\langle\mathrm{corr}(\gamma),m\rangle|\le K\|m\|$ for a uniform $K$.
--   2. **Molecule correction.** $m\mapsto(\langle\mathrm{corr}(\gamma),m\rangle)_\gamma$ maps molecules into $C_0(\mathrm{Labels})$. It is bounded by $K\|m\|$ and extends to a bounded operator
--   $$
--   Q:Z\to C_0(\mathrm{Labels}).
--   $$
--   3. **Lift.** The concrete lift is the radial extension of $\zeta$, $x\mapsto\|x\|\,\zeta(x/\|x\|)$, a map $c_0\to Z$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Space.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Space.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the C0Absorption mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection
import Definitions.Def_OAI_Analysis_C0Absorption_Supports
import Definitions.Def_OAI_Analysis_C0Absorption_Operations
import Definitions.Def_OAI_Analysis_C0Absorption_Detection
import Definitions.Def_OAI_Analysis_C0Absorption_Grid
import Definitions.Def_OAI_Analysis_C0Absorption_Weights
import Definitions.Def_OAI_Analysis_C0Absorption_Angles
import Definitions.Def_OAI_Analysis_C0Absorption_Blocks
import Definitions.Def_OAI_Analysis_C0Absorption_Correction
import Definitions.Def_OAI_Analysis_C0Absorption_Frozen
import Definitions.Def_OAI_Analysis_C0Absorption_Tags
import Definitions.Def_OAI_Analysis_C0Absorption_Operators
import Definitions.Def_OAI_Analysis_C0Absorption_Shift

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

def baseRepresentation (γ : Label) : GeneratedRepresentation concreteBases γ where
  operations := []
  ordered := by simp
  budget := by simpa only [List.map_nil,List.sum_nil] using half_pos (concreteBases.ell_pos (concreteBases.band γ))

theorem baseRepresentation_value (γ : Label) : (baseRepresentation γ).value=correction γ := by
  funext s
  change correctionBase γ (cubeRestrict (correctionCoordinates γ.level) s)=correction γ s
  exact correctionBase_restrict γ s

theorem correction_mem_TClass (γ : Label) : correction γ∈TClass concreteBases 0 :=
  ⟨γ,baseRepresentation γ,Nat.zero_le _,(baseRepresentation_value γ).symm⟩

def correctionDualBound : ℝ≥0 := Classical.choose (TClass_pairing_bound concreteBases 0)

theorem correction_pairing_bound (γ : Label) (m : PreSpace (sourceClasses concreteBases) c0Origin) :
    |pairing C0Ball (correction γ) m|≤correctionDualBound*‖m‖ :=
  Classical.choose_spec (TClass_pairing_bound concreteBases 0) (correction γ) (correction_mem_TClass γ) m

def moleculeCorrection : Molecule C0Ball →ₗ[ℝ] BlockC0 :=
  (Finsupp.linearCombination ℝ correctionC0).comp (MoleculeSpace C0Ball).subtype

theorem moleculeCorrection_apply (m : Molecule C0Ball) (γ : Label) :
    moleculeCorrection m γ=pairing C0Ball (correction γ) m := by
  classical
  simp only [moleculeCorrection,pairing,LinearMap.comp_apply,Submodule.subtype_apply,
    Finsupp.linearCombination_apply,Finsupp.sum]
  induction (m.val.support) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha,ZeroAtInftyContinuousMap.add_apply,
      ZeroAtInftyContinuousMap.smul_apply,smul_eq_mul,ih,correctionC0_apply]

def initialCorrection : PreSpace (sourceClasses concreteBases) c0Origin →L[ℝ] BlockC0 :=
  (show PreSpace (sourceClasses concreteBases) c0Origin →ₗ[ℝ] BlockC0 from by unfold PreSpace; exact moleculeCorrection).mkContinuous
    correctionDualBound (fun m => by
      apply cfun_norm_le _ (mul_nonneg correctionDualBound.coe_nonneg (norm_nonneg m))
      intro γ
      change |moleculeCorrection m γ|≤_
      exact (congrArg abs (moleculeCorrection_apply (show Molecule C0Ball from m) γ)).le.trans
        (correction_pairing_bound γ m))

def correctionQ : ConcreteSpace →L[ℝ] BlockC0 :=
  initialCorrection.extend (toTestSpace (sourceClasses concreteBases) c0Origin)

def concreteLift : C0 → ConcreteSpace := radialLift (zeta (sourceClasses concreteBases) c0Origin)

end
end C0Absorption

end OAI


