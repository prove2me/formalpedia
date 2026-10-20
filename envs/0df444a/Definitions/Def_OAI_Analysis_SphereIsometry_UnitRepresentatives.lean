-- Prove2me | Definitions.Def_OAI_Analysis_SphereIsometry_UnitRepresentatives
-- name    : OAI_Analysis_SphereIsometry_UnitRepresentatives
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T20:58:06.402006+00:00
-- url     : https://prove2.me/theorems/a1589322-c6ac-4d52-909d-a04d1e311f73
-- title:
--   Normalizing vectors with a fallback unit vector
-- statement:
--   These notions belong to a proof of Tingley's theorem in full generality: every surjective isometry $f$ between the unit spheres $S_X,S_Y$ of real normed spaces extends to the linear isometry $x\mapsto\|x\|\,f(x/\|x\|)$ of $X$ onto $Y$. The proof studies the cross-radius defects $\delta_q(x,y)=\|f(x)-qf(y)\|-\|x-qy\|$ for $0\le q\le1$. It shows that a positive maximal defect may be assumed to be attained, after passing to ultrapowers and completions, and rules out an attained positive defect by a fixed-point construction of aligned chords. Fix a unit vector $e\in S_X$.
--
--   1. **Unitize.** For $a\in X$, $\mathrm{unit}_e(a)=a/\|a\|$ if $a\ne0$ and $e$ if $a=0$. It satisfies $\|a\|\,\mathrm{unit}_e(a)=a$.
--   2. **Error identity.**
--   $$
--   \|a-\mathrm{unit}_e(a)\|=\bigl|\|a\|-1\bigr| ,
--   $$
--   so a vector of norm close to $1$ is close to its normalization. This lets arbitrary representatives of a unit class in an ultrapower be replaced by unit vectors.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SphereIsometry/UnitRepresentatives.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SphereIsometry/UnitRepresentatives.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TingleySphereIsometry mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.SeparationQuotient
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Encodable.Pi
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Cauchy
import Definitions.Def_TingleySphereIsometry
import Definitions.Def_OAI_Analysis_SphereIsometry_Basic

namespace OAI

/-!
# Unit representatives, including the zero vector

The fallback unit vector is used only at zero. The exact error identity permits
normalization of arbitrary representatives of a unit ultranorm class.
-/

noncomputable section
namespace Tingley

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

def unitize (e : UnitSphere X) (a : X) : UnitSphere X := by
  classical
  exact if ha : a = 0 then e else normalize a ha

@[simp] theorem unitize_zero (e : UnitSphere X) : unitize e 0 = e := by
  simp [unitize]

theorem unitize_of_ne_zero (e : UnitSphere X) {a : X} (ha : a ≠ 0) :
    unitize e a = normalize a ha := by
  simp [unitize, ha]

theorem norm_smul_unitize (e : UnitSphere X) (a : X) :
    ‖a‖ • (unitize e a : X) = a := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [unitize_of_ne_zero e ha]
    exact norm_smul_normalize a ha

theorem sub_unitize (e : UnitSphere X) (a : X) :
    a - (unitize e a : X) = (‖a‖ - 1) • (unitize e a : X) := by
  rw [sub_smul, norm_smul_unitize, one_smul]

theorem norm_sub_unitize (e : UnitSphere X) (a : X) :
    ‖a - (unitize e a : X)‖ = |‖a‖ - 1| := by
  rw [sub_unitize, norm_smul, Real.norm_eq_abs, UnitSphere.norm_coe, mul_one]

end Tingley

end

end OAI


