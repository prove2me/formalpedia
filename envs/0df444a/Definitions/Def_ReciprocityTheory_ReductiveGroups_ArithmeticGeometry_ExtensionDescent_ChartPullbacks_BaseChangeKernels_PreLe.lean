-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PreLe
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PreLe
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T16:41:41.821363+00:00
-- url     : https://prove2.me/theorems/1c3c2a37-625e-4b7c-987c-cafe866edf8d
-- title:
--   Pre Le
-- statement:
--   Definitions and structural lemmas for Pre Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/PreLe.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_IBIsKernel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_qB_h

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open Semi Geo.Tor PullGtPf
attribute [local instance] SplitExt.free SplitExt.finite
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (E : SplitExt S)
def jj (j : (pullExt f E).ChartIdx) : E.ChartIdx := fun k => j k PUnit.unit
lemma chart_le (j : (pullExt f E).ChartIdx) :
    (pullExt f E).chart j ≤ pullback.fst E.B.hom f ⁻¹ᵁ E.chart (jj f E j) := by
  intro y hy
  have hy' : y ∈ ((⨅ k, ((pullExt f E).O ((pullExt f E).basis k)).L.U (j k) :
      (pullExt f E).B.left.Opens) : Set _) := hy
  rw [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter] at hy'
  show (pullback.fst E.B.hom f).base y ∈ ((⨅ k, (E.O (E.basis k)).L.U (jj f E j k) : E.B.left.Opens) : Set _)
  rw [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  intro k
  exact Set.mem_iInter.1 (hy' k) PUnit.unit
variable {G : Over S} [GrpObj G] (d : E.GtDatum G)
lemma pre_le (j : (pullExt f E).ChartIdx) :
    (qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j ≤
      pullback.fst G.hom f ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart (jj f E j)) := by
  intro y hy
  have h1 := chart_le f E j hy
  have e₁ := congrArg (fun g => g y) (qB_h f d.q)
  simp only [Scheme.Hom.comp_apply] at e₁
  exact (congrArg (· ∈ E.chart (jj f E j)) e₁).mp h1
def uB (j : (pullExt f E).ChartIdx) (k : Module.Free.ChooseBasisIndex ℤ E.X) :
    Γ(((Over.pullback f).obj G).left, (qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j)ˣ :=
  res (pre_le f E d j) (pullU (pullback.fst G.hom f) _ (d.u (jj f E j) k))
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf


