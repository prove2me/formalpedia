-- Prove2me | Definitions.Def_OAI_Analysis_SegmentLenses_AtomicBalls
-- name    : OAI_Analysis_SegmentLenses_AtomicBalls
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T20:55:56.462258+00:00
-- url     : https://prove2.me/theorems/bfc21f93-0461-44a6-bd40-68bdbecbb821
-- title:
--   Local segment families, coefficient budgets, atomic bodies and finite polar tests
-- statement:
--   Let $V$ be a set with decidable equality and a segment system. Let $J_V^{*}$ be the full dual of the completion $J_V$ of the finitely supported functions under the segment norm, with unit vectors $e_v\in J_V$ and coordinate functionals $e_v^{*}$. For finite $S\subseteq V$ let $\sigma_S=\sum_{v\in S}e_v^{*}$ be the segment functional. Recall that a segment family is a finite set of pairwise disjoint segments.
--
--   1. **Local families.** A segment family is determined by its set of members. For a finite $K\subseteq V$, a *local family* of $K$ is a segment family all of whose members are subsets of $K$. There are only finitely many local families.
--   2. **Family coefficients and values.** For a segment family $\mathcal F$ the coefficient space is the Euclidean space $\ell_2(\mathcal F)$. The value map is the linear map
--   $$
--   \Lambda_{\mathcal F}:\ell_2(\mathcal F)\to J_V^{*},\qquad \Lambda_{\mathcal F}c=\sum_{S\in\mathcal F}c_S\,\sigma_S ,
--   $$
--   so that $(\Lambda_{\mathcal F}c)(u)=\sum_{S}c_S\sum_{v\in S}u(v)$ for every test $u$. *Local coefficients* on $K$ are families $c=(c_{\mathcal F})$, indexed by all local families $\mathcal F$ of $K$, with $c_{\mathcal F}\in\ell_2(\mathcal F)$. Their value is $\Lambda_Kc=\sum_{\mathcal F}\Lambda_{\mathcal F}c_{\mathcal F}$, which is linear in $c$.
--   3. **Budget and atomic body.** The coefficient budget is $\beta_K(c)=\sum_{\mathcal F}\|c_{\mathcal F}\|_2$. For $R\in\mathbb{R}$ the atomic body is
--   $$
--   \mathcal A_K(R)=\{\Lambda_Kc:\ \beta_K(c)\le R\}\subseteq J_V^{*}.
--   $$
--   For $R\ge0$ this is $R$ times the convex hull of the images $\Lambda_{\mathcal F}(\text{unit ball of }\ell_2(\mathcal F))$ over the local families of $K$.
--   4. **Finite tests.** For a finite $K$ and $a:V\to\mathbb{R}$, the test $u_{K,a}=\sum_{v\in K}a(v)\,\delta_v$ equals $a$ on $K$ and $0$ off $K$. In $J_V$ it equals $\sum_{v\in K}a(v)e_v$, so $z(u_{K,a})=\sum_{v\in K}a(v)\,z(e_v)$ for all $z\in J_V^{*}$.
--   5. **Polar test.** For a continuous linear functional $f$ on $J_V^{*}$ (an element of the bidual), the polar test on $K$ is $\sum_{v\in K}f(e_v^{*})\,\delta_v$, i.e. $u_{K,a}$ with $a(v)=f(e_v^{*})$.
--
--   Atomic bodies describe dual functionals supported on $K$ through finitely many unit-energy atoms $\Lambda_{\mathcal F}d$ with $\|d\|_2\le1$. Polar tests are the finitely supported vectors used to separate a functional from such a body.
--
--   **Formalization Note** `LocalFamily K` is the subtype of `SegmentFamily V` with all members contained in `K`. It has `Finite` and `Fintype` instances, obtained through the injection into `K.powerset.powerset` given by `SegmentFamily.ext`. `FamilyCoefficients F` is `EuclideanSpace ℝ F.sets`, and `LocalCoefficients K` is the dependent product over local families. The names are `familyValue`, `localValue`, `coefficientBudget`, `atomicBody`, `Test.ofFinite` (with `coeff_ofFinite`, `coe_ofFinite`, `dual_apply_ofFinite`) and `polarTest`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/AtomicBalls.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/AtomicBalls.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MidpointLenses mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing

namespace OAI

/-!
# Atomic polar descriptions of finite unit balls
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section FiniteBodies
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

@[ext] theorem SegmentFamily.ext {F G : SegmentFamily V} (h : F.sets = G.sets) : F = G := by
  have _ := decidableEqV
  cases F
  cases G
  cases h
  rfl

abbrev LocalFamily (K : Finset V) := {F : SegmentFamily V // ∀ S ∈ F.sets, S ⊆ K}

instance localFamilyFinite (K : Finset V) : Finite (LocalFamily K) := by
  let f : LocalFamily K → {s // s ∈ K.powerset.powerset} := fun F =>
    ⟨F.val.sets, Finset.mem_powerset.mpr (fun S hS => Finset.mem_powerset.mpr (F.property S hS))⟩
  exact Finite.of_injective f (fun F G h => Subtype.ext (SegmentFamily.ext
    (congrArg Subtype.val h)))

instance localFamilyFintype (K : Finset V) : Fintype (LocalFamily K) := Fintype.ofFinite _

abbrev FamilyCoefficients (F : SegmentFamily V) := EuclideanSpace ℝ F.sets

abbrev LocalCoefficients (K : Finset V) := (F : LocalFamily K) → FamilyCoefficients F.val

def familyValue (F : SegmentFamily V) : FamilyCoefficients F →ₗ[ℝ] FullDual V where
  toFun c := ∑ S, c S • segmentFunctional S.val
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, mul_smul]

@[simp] theorem familyValue_apply (F : SegmentFamily V) (c : FamilyCoefficients F) (u : Test V) :
    familyValue F c (u : Primal V) = ∑ S, c S * ∑ v ∈ S.val, u.coeff v := by
  have _ := decidableEqV
  simp only [familyValue, LinearMap.coe_mk, AddHom.coe_mk, _root_.sum_apply,
    _root_.smul_apply, smul_eq_mul, segmentFunctional_apply]

def localValue (K : Finset V) : LocalCoefficients K →ₗ[ℝ] FullDual V where
  toFun c := ∑ F, familyValue F.val (c F)
  map_add' c d := by simp [map_add, Finset.sum_add_distrib]
  map_smul' a c := by simp [map_smul, Finset.smul_sum]

def coefficientBudget (K : Finset V) (c : LocalCoefficients K) : ℝ := ∑ F, ‖c F‖

def atomicBody (K : Finset V) (R : ℝ) : Set (FullDual V) :=
  localValue K '' {c : LocalCoefficients K | coefficientBudget K c ≤ R}

end FiniteBodies

section FinitePolar
variable {V : Type*} [decidableEqV : DecidableEq V] [segmentSystemV : SegmentSystem V]

def Test.ofFinite (K : Finset V) (a : V → ℝ) : Test V :=
  ∑ v ∈ K, a v • Test.ofFinsupp (Finsupp.single v 1)

@[simp] theorem Test.coeff_ofFinite (K : Finset V) (a : V → ℝ) (v : V) :
    (Test.ofFinite K a).coeff v = if v ∈ K then a v else 0 := by
  have _ := segmentSystemV
  change (∑ w ∈ K, a w • Finsupp.single w 1) v = _
  simp [Finsupp.smul_single, Finsupp.single_apply, eq_comm]

@[simp] theorem Test.coe_ofFinite (K : Finset V) (a : V → ℝ) :
    ((Test.ofFinite K a : Test V) : Primal V) = ∑ v ∈ K, a v • unitVector v := by
  have _ := decidableEqV
  change (UniformSpace.Completion.toComplL : Test V →L[ℝ] Primal V) (Test.ofFinite K a) = _
  simp only [Test.ofFinite, map_sum, map_smul]; rfl

@[simp] theorem dual_apply_ofFinite (K : Finset V) (a : V → ℝ) (z : FullDual V) :
    z ((Test.ofFinite K a : Test V) : Primal V) = ∑ v ∈ K, a v * z (unitVector v) := by
  rw [Test.coe_ofFinite]
  simp only [map_sum, map_smul, smul_eq_mul]

def polarTest (K : Finset V) (f : FullDual V →L[ℝ] ℝ) : Test V :=
  Test.ofFinite K (fun v => f (coordinate v))

end FinitePolar

section EuclideanNormalization
variable {ι : Type*} [Fintype ι]

end EuclideanNormalization

section AtomicSeparation
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

end AtomicSeparation

end SegmentLenses

end

end OAI


