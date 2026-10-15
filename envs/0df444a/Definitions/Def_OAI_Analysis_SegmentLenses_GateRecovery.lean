-- Prove2me | Definitions.Def_OAI_Analysis_SegmentLenses_GateRecovery
-- name    : OAI_Analysis_SegmentLenses_GateRecovery
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T20:59:35.806542+00:00
-- url     : https://prove2.me/theorems/8faefd49-735f-47fe-9267-b914e37f257e
-- title:
--   Head and tail operators, replacement and error representations, gate tails and scaling
-- statement:
--   Let $V$ be a set with decidable equality and a segment system, and let $J_V^{*}$ be the dual of the segment-norm completion. It has unit vectors $e_v$, coordinate functionals $e_v^{*}$ and segment functionals $\sigma_S=\sum_{v\in S}e_v^{*}$. For finite $H\subseteq V$ let $P_Hx=\sum_{v\in H}x(e_v)e_v^{*}$ be the head and $Q_Hx=x-P_Hx$ the tail. A representation $A=(\mathcal F,c)$ is a segment family (pairwise disjoint segments) with real coefficients. Its value is $\sum_Sc_S\sigma_S$ and its energy is $\sum_Sc_S^2$. For finitely supported $p$, $p_{\mathcal F}(p)^2=\sum_{S\in\mathcal F}(\sum_{v\in S}p(v))^2$ is the family seminorm squared.
--
--   1. **Head and tail as linear maps.** $P_H$ and $Q_H=I-P_H$ are linear operators on $J_V^{*}$. On unit vectors $(Q_Hx)(e_v)=0$ if $v\in H$ and $(Q_Hx)(e_v)=x(e_v)$ otherwise, and
--   $$
--   Q_H\sigma_S=\sigma_{S\setminus H}.
--   $$
--   2. **Replacement representation.** For a segment family $\mathcal F$ and finitely supported $p:V\to\mathbb{R}$, the replacement representation is $(\mathcal F,(\sum_{v\in S}p(v))_{S\in\mathcal F})$. Its energy is $p_{\mathcal F}(p)^2$. When $V$ is a locally finite tree order with interval segments, its value at $e_g$ is the boundary sum $\partial_{\mathcal F}p(g)$, the total of $p$ over the member of $\mathcal F$ containing $g$ (or $0$).
--   3. **Error representation.** For $A=(\mathcal F,c)$ and $p$, the error representation is $(\mathcal F,(c_S-\sum_{v\in S}p(v))_S)$. Its value is the value of $A$ minus the value of the replacement representation of $p$ over $\mathcal F$. Its energy is $\sum_{S\in\mathcal F}\big(c_S-\sum_{v\in S}p(v)\big)^2$.
--   4. **Gate tail.** In the tree setting, take a segment family $\mathcal F$, a finite $H$ and a vertex $g$. If some member $S$ of $\mathcal F$ contains $g$, the gate tail is $S\setminus H$ for such an $S$, which is unique by disjointness. Otherwise it is $\emptyset$.
--   5. **Scaling.** For $t\in\mathbb{R}$, the scaled representation $(\mathcal F,(tc_S)_S)$ has value $t$ times the value of $A$ and energy $t^2$ times the energy of $A$.
--   6. **Expectations of functionals.** For a finite law $\mu$ on $\Omega$ and $f:\Omega\to J_V^{*}$, $(\mathbb{E}_\mu f)(u)=\mathbb{E}_\mu[f(\omega)(u)]$ for every $u\in J_V$. Expectation also commutes with finite sums.
--
--   Replacement representations are the canonical representations induced by a test vector $p$. The error identity splits an arbitrary representation into this canonical part plus a remainder whose energy is explicit. Gate tails isolate the part of a segment that lies beyond an ancestral set $H$. Together these are the bookkeeping tools for the energy budgets in the midpoint-lens argument.
--
--   **Formalization Note** The definitions are `headLinear`, `tailLinear`, `SegmentFamily.replacement`, `Representation.error`, `SegmentFamily.gateTail` (which picks the member with `Classical.choose`) and `Representation.scale`. The accompanying simp lemmas are `headLinear_apply`, `tailLinear_apply`, `tail_unitVector`, `tail_segmentFunctional`, `replacement_energy`, `replacement_gate`, `error_value`, `error_energy`, `scale_value`, `scale_energy`, `FiniteLaw.expect_apply` and `FiniteLaw.expect_sum`. `gateTail`, `scale` and their lemmas are stated with the tree-order and interval-segment assumptions in scope.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/GateRecovery.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/GateRecovery.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MidpointLenses mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing
import Definitions.Def_OAI_Analysis_SegmentLenses_AtomicBalls
import Definitions.Def_OAI_Analysis_SegmentLenses_LawRecovery
import Definitions.Def_OAI_Analysis_SegmentLenses_HeadTests

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Gate coefficients, cone recovery, and energy budgets
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section ProjectionAlgebra
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

def headLinear (H : Finset V) : FullDual V →ₗ[ℝ] FullDual V where
  toFun := head H
  map_add' := by intros; simp [head, add_smul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [head, mul_smul, Finset.smul_sum]

def tailLinear (H : Finset V) : FullDual V →ₗ[ℝ] FullDual V :=
  LinearMap.id - headLinear H

@[simp] theorem headLinear_apply (H : Finset V) (x : FullDual V) :
    headLinear H x = head H x := by
  have _ := decidableEqV
  exact rfl

@[simp] theorem tailLinear_apply (H : Finset V) (x : FullDual V) :
    tailLinear H x = tail H x := by
  have _ := decidableEqV
  exact rfl

@[simp] theorem tail_unitVector (H : Finset V) (x : FullDual V) (v : V) :
    tail H x (unitVector v) = if v ∈ H then 0 else x (unitVector v) := by
  simp only [tail, _root_.sub_apply, head_unitVector]
  split_ifs <;> simp

@[simp] theorem tail_segmentFunctional (H S : Finset V) :
    tail H (segmentFunctional S) = segmentFunctional (S \ H) := by
  apply dual_ext_test
  intro u
  rw [tail_pairing, segmentFunctional_apply, segmentFunctional_apply]
  change (∑ v ∈ S, (u.coeff.filter (· ∉ H)) v) = _
  simp only [Finsupp.filter_apply]
  rw [← Finset.sum_filter]
  congr 1
  ext v
  simp

namespace SegmentFamily

def replacement (F : SegmentFamily V) (p : V →₀ ℝ) : Representation V :=
  ⟨F, fun S => ∑ v ∈ S.val, p v⟩

@[simp] theorem replacement_energy (F : SegmentFamily V) (p : V →₀ ℝ) :
    (F.replacement p).energy = F.seminorm p ^ 2 := by
  have _ := decidableEqV
  exact (F.seminorm_sq p).symm

@[simp] theorem replacement_gate [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
    [IntervalSegments V] (F : SegmentFamily V) (p : V →₀ ℝ) (g : V) :
    (F.replacement p).value (unitVector g) = F.boundary p g := by
  rw [Representation.apply_unitVector]
  exact Finset.sum_coe_sort F.sets (fun S => if g ∈ S then ∑ v ∈ S, p v else 0)

end SegmentFamily

namespace Representation

def error (A : Representation V) (p : V →₀ ℝ) : Representation V :=
  ⟨A.family, fun S => A.coeff S - ∑ v ∈ S.val, p v⟩

@[simp] theorem error_value (A : Representation V) (p : V →₀ ℝ) :
    (A.error p).value = A.value - (A.family.replacement p).value := by
  apply dual_ext_test
  intro u
  rw [_root_.sub_apply, Representation.apply_test, Representation.apply_test,
    Representation.apply_test]
  change (∑ S : A.family.sets, (A.coeff S - ∑ v ∈ S.val, p v) *
    (∑ v ∈ S.val, u.coeff v)) =
    (∑ S : A.family.sets, A.coeff S * ∑ v ∈ S.val, u.coeff v) -
    (∑ S : A.family.sets, (∑ v ∈ S.val, p v) * ∑ v ∈ S.val, u.coeff v)
  simp only [sub_mul, Finset.sum_sub_distrib]

@[simp] theorem error_energy (A : Representation V) (p : V →₀ ℝ) :
    (A.error p).energy = ∑ S : A.family.sets, (A.coeff S - ∑ v ∈ S.val, p v) ^ 2 := by
  have _ := decidableEqV
  exact rfl

end Representation
end ProjectionAlgebra

section GateTails
variable {V : Type*} [DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

namespace SegmentFamily

def gateTail (F : SegmentFamily V) (H : Finset V) (g : V) : Finset V :=
  if h : ∃ S : F.sets, g ∈ S.val then (Classical.choose h).val \ H else ∅

end SegmentFamily
end GateTails

section GateRecovery
open scoped Classical
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

namespace SegmentFamily

end SegmentFamily
end GateRecovery

section ScaledLaws
variable {V : Type*} [decidableEqV : DecidableEq V] [partialOrderV : PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V] [treeOrderV : TreeOrder V]
  [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

namespace Representation

def scale (A : Representation V) (t : ℝ) : Representation V :=
  ⟨A.family, fun S => t * A.coeff S⟩

@[simp] theorem scale_value (t : ℝ) (A : Representation V) :
    (A.scale t).value = t • A.value := by
  have _ := decidableEqV
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  change (∑ S : A.family.sets, (t * A.coeff S) • segmentFunctional S.val) =
    t • (∑ S : A.family.sets, A.coeff S • segmentFunctional S.val)
  simp only [Finset.smul_sum, mul_smul]

@[simp] theorem scale_energy (t : ℝ) (A : Representation V) :
    (A.scale t).energy = t ^ 2 * A.energy := by
  have _ := decidableEqV
  have _ := partialOrderV
  have _ := locallyFiniteOrderV
  have _ := treeOrderV
  have _ := intervalSegmentsV
  change (∑ S : A.family.sets, (t * A.coeff S) ^ 2) = t ^ 2 * ∑ S, A.coeff S ^ 2
  simp only [mul_pow, Finset.mul_sum]

end Representation

end ScaledLaws

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

@[simp] theorem expect_apply {V : Type*} [SegmentSystem V] (μ : FiniteLaw Ω)
    (f : Ω → FullDual V) (u : Primal V) :
    (μ.expect f) u = μ.mean (fun ω => f ω u) := by
  simp only [expect, mean, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]

@[simp] theorem expect_sum {E ι : Type*} [AddCommMonoid E] [Module ℝ E] [Fintype ι]
    (μ : FiniteLaw Ω) (f : Ω → ι → E) :
    μ.expect (fun ω => ∑ i, f ω i) = ∑ i, μ.expect (fun ω => f ω i) := by
  simp only [expect, Finset.smul_sum]
  exact Finset.sum_comm

end FiniteLaw

end SegmentLenses

end

end OAI


