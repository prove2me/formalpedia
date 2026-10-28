-- Prove2me | Definitions.Def_OAIQ66So011
-- name    : OAIQ66So011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:15:27.526567+00:00
-- url     : https://prove2.me/theorems/ea8fd9a5-1dcd-42a6-8018-ba8583acbf10
-- title:
--   Definitions bundle OAIQ66So011 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 156 declarations of OpenAI's Lean: 51 definitions, 2 inductive types or structures, 1 instance and 102 theorems. The definitions and types are `OAI.BinaryPrefixOperators.AssignmentAdditive`, `OAI.BinaryPrefixOperators.idempotents`, `OAI.BinaryPrefixOperators.threeCopies`, `OAI.CWCylinder.bottom`, `OAI.CWCylinder.boundaryMap`, `OAI.CWCylinder.faceCylinder`, `OAI.CWCylinder.faceData`, `OAI.CWCylinder.faceQuot`, `OAI.CWCylinder.side`, `OAI.CWCylinder.top`, `OAI.CWEquivariant.skeletal`, `OAI.CWWhitehead.Stage`, `OAI.CWWhitehead.allPaths`, `OAI.CWWhitehead.build`, `OAI.CWWhitehead.cellSide`, `OAI.CWWhitehead.emptyStage`, `OAI.CWWhitehead.homotopy`, `OAI.CWWhitehead.next`, `OAI.CompressedSplittings.BinaryData.doubleProjection`, `OAI.CompressedSplittings.BinaryData.projection`, `OAI.CompressedSplittings.Idempotent.units`, `OAI.CompressedSplittings.full`, `OAI.CoveringCW.chart`, `OAI.CoveringCW.cwComplex_general`, `OAI.CoveringCW.meetingCellsOver`, `OAI.EquivariantCoverCells.cellEquiv`, `OAI.EquivariantCoverCells.seed`, `OAI.FiniteIdempotentDiagrams.ThreeCopies`, `OAI.HurewiczConstruction.homotopyData`, `OAI.HurewiczConstruction.map`, `OAI.HurewiczConstruction.sphereData`, `OAI.HurewiczConstruction.sphereHomotopy`, `OAI.HurewiczConstruction.sphereMap`, `OAI.NoncommElementary.elementary`, `OAI.NonunitalCompression.units`, `OAI.OrderListChains.Chain`, `OAI.OrderListChains.simplexCone`, `OAI.PresentationGeometry.Rose.Space`, `OAI.PresentationGeometry.Rose.attaching`, `OAI.PresentationGeometry.Rose.basepoint` and 13 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `FiniteType_BasedHorn`, `FiniteType_BinaryPrefixOperators`, `FiniteType_CWCellular`, `FiniteType_CWCylinder`, `FiniteType_CWWhitehead`, `FiniteType_ClassifyingSpacesFiniteExtensionGeometricFromProducts`, `FiniteType_CompressedSplittings`, `FiniteType_CoreDeck`, `FiniteType_CoveringCellGeometry`, `FiniteType_CoveringCellGeometryHausdorff`, `FiniteType_CubeDisk`, `FiniteType_FiniteIdempotentDiagrams`, `FiniteType_HomotopyFunctor`, `FiniteType_NonunitalCompression`, `FiniteType_OrderListChains`, `FiniteType_PresentationGeometry`, `FiniteType_RingExchange`, `FiniteType_SimplexRotation`, `FiniteType_SingularAction`, `FiniteType_SingularSigmaSingleMerge`, `FiniteType_SingularSupport`, `FiniteType_Steinberg`.
--
--   **Imports.** It imports the bundles `OAIQ66So000`, `OAIQ66So001`, `OAIQ66So002`, `OAIQ66So003` and `OAIQ66So004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So017`, `OAIQ66So018`, `OAIQ66So019`, `OAIQ66So020` and `OAIQ66So021`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So000
import Definitions.Def_OAIQ66So001
import Definitions.Def_OAIQ66So002
import Definitions.Def_OAIQ66So003
import Definitions.Def_OAIQ66So004

section
-- module Solutions.OAIQ066_SO.FiniteType_CWCylinder
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
namespace CWCylinder
universe u
variable {Y : Type u} [TopologicalSpace Y]

theorem encode_decode (n : ℕ) (v : Disk (n+1)) : encode n (diskTime n v,diskTail n v) = v := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => rfl) i
  change 2*((v.1 0 + 1)/2)-1 = v.1 0
  ring

theorem encode_injective (n : ℕ) : Function.Injective (encode n) := by
  intro a b h
  exact Prod.ext (by simpa using congrArg (diskTime n) h) (by simpa using congrArg (diskTail n) h)

def bottom (n : ℕ) : C(Disk n,Boundary (n+1)) :=
  ⟨fun v => ⟨Fin.cons (-1) v,by
      rw [mem_sphere,dist_zero_right,norm_cons]
      have hv : ‖(v : Fin n → ℝ)‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using v.2
      simp only [norm_neg,norm_one,max_eq_left hv]⟩,
    (continuous_pi (fun i => Fin.cases continuous_const (fun j => by fun_prop) i)).subtype_mk _⟩

def top (n : ℕ) : C(Disk n,Boundary (n+1)) :=
  ⟨fun v => ⟨Fin.cons 1 v,by
      rw [mem_sphere,dist_zero_right,norm_cons]
      have hv : ‖(v : Fin n → ℝ)‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using v.2
      simp only [norm_one,max_eq_left hv]⟩,
    (continuous_pi (fun i => Fin.cases continuous_const (fun j => by fun_prop) i)).subtype_mk _⟩

def side (n : ℕ) : C(I × Boundary n,Boundary (n+1)) :=
  ⟨fun z => ⟨Fin.cons (2*(z.1:ℝ)-1) z.2,by
      rw [mem_sphere,dist_zero_right,norm_cons]
      have hv : ‖(z.2 : Fin n → ℝ)‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using z.2.2
      rw [hv,max_eq_right (time_bound z.1)]⟩,
    (continuous_pi (fun i => Fin.cases (by fun_prop) (fun j => by fun_prop) i)).subtype_mk _⟩

def faceQuot (n : ℕ) : C(Faces n, Boundary (n+1)) :=
  ⟨Sum.elim (bottom n) (Sum.elim (top n) (side n)),
    continuous_sum_dom.mpr ⟨(bottom n).continuous,
      continuous_sum_dom.mpr ⟨(top n).continuous,(side n).continuous⟩⟩⟩

theorem faceQuot_surjective (n : ℕ) : Function.Surjective (faceQuot n) := by
  intro v
  let d : Disk (n+1) := ⟨v,sphere_subset_closedBall v.2⟩
  by_cases h0 : v.1 0 = -1
  · refine ⟨Sum.inl (diskTail n d),?_⟩
    apply Subtype.ext
    funext i
    exact Fin.cases h0.symm (fun _ => rfl) i
  by_cases h1 : v.1 0 = 1
  · refine ⟨Sum.inr (Sum.inl (diskTail n d)),?_⟩
    apply Subtype.ext
    funext i
    exact Fin.cases h1.symm (fun _ => rfl) i
  have ht : ‖Fin.tail v.1‖ = 1 := by
    have hv : max ‖v.1 0‖ ‖Fin.tail v.1‖ = 1 := by
      rw [← norm_eq_max]
      simpa only [mem_sphere,dist_zero_right] using v.2
    have hh : ‖v.1 0‖ ≠ 1 := by
      intro hh
      rw [Real.norm_eq_abs] at hh
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hh with hh | hh
      · exact h1 hh
      · exact h0 hh
    exact (max_eq_iff.mp hv).resolve_left (fun h => hh h.1) |>.1
  refine ⟨Sum.inr (Sum.inr (diskTime n d,⟨Fin.tail v.1,by simpa only [mem_sphere,dist_zero_right] using ht⟩)),?_⟩
  apply Subtype.ext
  have he := congrArg Subtype.val (encode_decode n d)
  exact he

theorem faceQuot_isQuotientMap (n : ℕ) : IsQuotientMap (faceQuot n) :=
  IsQuotientMap.of_surjective_continuous (faceQuot_surjective n) (faceQuot n).continuous

def faceCylinder (n : ℕ) : Faces n → I × Disk n :=
  Sum.elim (fun v => (0,v)) (Sum.elim (fun v => (1,v)) (fun z => (z.1,boundaryDisk n z.2)))

theorem face_encode (n : ℕ) (v : Faces n) :
    encode n (faceCylinder n v) = boundaryDisk (n+1) (faceQuot n v) := by
  rcases v with v | v | v
  · apply Subtype.ext
    change (Fin.cons ((2:ℝ)*0-1) v : Fin (n+1) → ℝ) = Fin.cons (-1) v
    norm_num
  · apply Subtype.ext
    change (Fin.cons ((2:ℝ)*1-1) v : Fin (n+1) → ℝ) = Fin.cons 1 v
    norm_num
  · rfl

theorem faceCylinder_eq_of_faceQuot_eq (n : ℕ) {a b : Faces n}
    (h : faceQuot n a = faceQuot n b) : faceCylinder n a = faceCylinder n b := by
  apply encode_injective n
  rw [face_encode,face_encode,h]

def faceData {n : ℕ} (f₀ f₁ : C(Disk n,Y)) (h : C(I × Boundary n,Y)) : C(Faces n,Y) :=
  ⟨Sum.elim f₀ (Sum.elim f₁ h),continuous_sum_dom.mpr
    ⟨f₀.continuous,continuous_sum_dom.mpr ⟨f₁.continuous,h.continuous⟩⟩⟩

theorem faceData_factors {n : ℕ} (f₀ f₁ : C(Disk n,Y)) (h : C(I × Boundary n,Y))
    (h₀ : ∀ v, h (0,v) = f₀ (boundaryDisk n v))
    (h₁ : ∀ v, h (1,v) = f₁ (boundaryDisk n v)) :
    Function.FactorsThrough (faceData f₀ f₁ h) (faceQuot n) := by
  intro a b he
  have hc := faceCylinder_eq_of_faceQuot_eq n he
  rcases a with a | a | a <;> rcases b with b | b | b
  · exact congrArg f₀ (congrArg Prod.snd hc)
  · have he : (0 : I) = 1 := congrArg Prod.fst hc
    exact (zero_ne_one he).elim
  · have ht : b.1 = 0 := (congrArg Prod.fst hc).symm
    have hv : a = boundaryDisk n b.2 := congrArg Prod.snd hc
    change f₀ a = h b
    rw [hv,← h₀]
    exact congrArg h (Prod.ext ht.symm rfl)
  · have he : (1 : I) = 0 := congrArg Prod.fst hc
    exact (one_ne_zero he).elim
  · exact congrArg f₁ (congrArg Prod.snd hc)
  · have ht : b.1 = 1 := (congrArg Prod.fst hc).symm
    have hv : a = boundaryDisk n b.2 := congrArg Prod.snd hc
    change f₁ a = h b
    rw [hv,← h₁]
    exact congrArg h (Prod.ext ht.symm rfl)
  · have ht : a.1 = 0 := congrArg Prod.fst hc
    have hv : boundaryDisk n a.2 = b := congrArg Prod.snd hc
    change h a = f₀ b
    rw [← hv,← h₀]
    exact congrArg h (Prod.ext ht rfl)
  · have ht : a.1 = 1 := congrArg Prod.fst hc
    have hv : boundaryDisk n a.2 = b := congrArg Prod.snd hc
    change h a = f₁ b
    rw [← hv,← h₁]
    exact congrArg h (Prod.ext ht rfl)
  · apply congrArg h
    apply Prod.ext
    · exact congrArg (fun z : I × Disk n => z.1) hc
    · exact Subtype.ext (congrArg (fun z : I × Disk n => (z.2 : Fin n → ℝ)) hc)

def boundaryMap {n : ℕ} (f₀ f₁ : C(Disk n,Y)) (h : C(I × Boundary n,Y))
    (h₀ : ∀ v, h (0,v) = f₀ (boundaryDisk n v))
    (h₁ : ∀ v, h (1,v) = f₁ (boundaryDisk n v)) : C(Boundary (n+1),Y) :=
  (faceQuot_isQuotientMap n).lift (faceData f₀ f₁ h) (faceData_factors f₀ f₁ h h₀ h₁)

theorem boundaryMap_face {n : ℕ} (f₀ f₁ : C(Disk n,Y)) (h : C(I × Boundary n,Y))
    (h₀ : ∀ v, h (0,v) = f₀ (boundaryDisk n v))
    (h₁ : ∀ v, h (1,v) = f₁ (boundaryDisk n v)) (v : Faces n) :
    boundaryMap f₀ f₁ h h₀ h₁ (faceQuot n v) = faceData f₀ f₁ h v :=
  DFunLike.congr_fun ((faceQuot_isQuotientMap n).lift_comp (faceData f₀ f₁ h) (faceData_factors f₀ f₁ h h₀ h₁)) v

theorem exists_cylinder (hfill : SphereFill Y) {n : ℕ}
    (f₀ f₁ : C(Disk n,Y)) (h : C(I × Boundary n,Y))
    (h₀ : ∀ v, h (0,v) = f₀ (boundaryDisk n v))
    (h₁ : ∀ v, h (1,v) = f₁ (boundaryDisk n v)) :
    ∃ F : C(I × Disk n,Y),
      (∀ v, F (0,v) = f₀ v) ∧ (∀ v, F (1,v) = f₁ v) ∧
      ∀ t v, F (t,boundaryDisk n v) = h (t,v) := by
  obtain ⟨g,hg⟩ := hfill (n+1) (boundaryMap f₀ f₁ h h₀ h₁)
  refine ⟨g.comp (encode n),?_,?_,?_⟩
  · intro v
    change g (encode n (0,v)) = _
    rw [show (0,v) = faceCylinder n (Sum.inl v) from rfl,face_encode,hg]
    exact boundaryMap_face f₀ f₁ h h₀ h₁ (Sum.inl v)
  · intro v
    change g (encode n (1,v)) = _
    rw [show (1,v) = faceCylinder n (Sum.inr (Sum.inl v)) from rfl,face_encode,hg]
    exact boundaryMap_face f₀ f₁ h h₀ h₁ (Sum.inr (Sum.inl v))
  · intro t v
    change g (encode n (t,boundaryDisk n v)) = _
    rw [show (t,boundaryDisk n v) = faceCylinder n (Sum.inr (Sum.inr (t,v))) from rfl,face_encode,hg]
    exact boundaryMap_face f₀ f₁ h h₀ h₁ (Sum.inr (Sum.inr (t,v)))

end CWCylinder

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CubeDisk
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval

namespace WeakSphere
open Set Topology Metric
open scoped unitInterval
universe u
variable {Y : Type u} [TopologicalSpace Y]
open SphereQuotient

def loop {n : ℕ} (f : C(Boundary (n+1),Y)) : GenLoop (Fin n) Y (f (pole n)) :=
  ⟨(f.comp (quotient n)).comp (CubeDisk.toDisk n),by
    intro w hw
    change f (quotient n (CubeDisk.toDisk n w)) = f (pole n)
    rw [quotient_boundary _ (CubeDisk.norm_eq_one_of_boundary w hw)]⟩

def pathData {n : ℕ} (y : Y) (P : C(Disk n,C(I,Y))) : C(Disk n ⊕ Unit,C(I,Y)) :=
  ⟨Sum.elim P (fun _ => .const I y),continuous_sum_dom.mpr ⟨P.continuous,continuous_const⟩⟩

end WeakSphere

open Set Topology Metric
open scoped unitInterval

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_HomotopyFunctor
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open _root_.CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval

namespace HurewiczConstruction
open Set Topology Metric _root_.CategoryTheory AlgebraicTopology
open scoped unitInterval
open SphereQuotient
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

def sphereData {n : ℕ} (a : GenLoop (Fin n) X x) : C(Disk n ⊕ Unit,X) :=
  ⟨Sum.elim (a.1.comp (CubeDisk.toCube n)) (fun _ => x),
    continuous_sum_dom.mpr ⟨(a.1.comp (CubeDisk.toCube n)).continuous,continuous_const⟩⟩

theorem sphereData_boundary {n : ℕ} (a : GenLoop (Fin n) X x) (v : Disk n)
    (hv : ‖v.1‖ = 1) : a (CubeDisk.toCube n v) = x :=
  a.2 _ (CubeDisk.boundary_of_norm_eq_one v hv)

theorem sphereData_factors {n : ℕ} (a : GenLoop (Fin n) X x) :
    Function.FactorsThrough (sphereData a) (sphereQuot n) := by
  intro v w h
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      rcases quotient_eq h with h | ⟨hv,hw⟩
      · exact congrArg (a ∘ CubeDisk.toCube n) h
      · exact (sphereData_boundary a v hv).trans (sphereData_boundary a w hw).symm
    | inr w => exact sphereData_boundary a v (quotient_eq_pole h)
  | inr v =>
    cases w with
    | inl w => exact (sphereData_boundary a w (quotient_eq_pole h.symm)).symm
    | inr w => rfl

def sphereMap {n : ℕ} (a : GenLoop (Fin n) X x) : C(Boundary (n+1),X) :=
  (sphereQuot_isQuotientMap n).lift (sphereData a) (sphereData_factors a)

@[simp] theorem sphereMap_apply_quot {n : ℕ} (a : GenLoop (Fin n) X x) (v : Disk n ⊕ Unit) :
    sphereMap a (sphereQuot n v) = sphereData a v :=
  DFunLike.congr_fun ((sphereQuot_isQuotientMap n).lift_comp (sphereData a) (sphereData_factors a)) v

@[simp] theorem sphereMap_pole {n : ℕ} (a : GenLoop (Fin n) X x) : sphereMap a (pole n) = x :=
  sphereMap_apply_quot a (Sum.inr ())

def homotopyData {n : ℕ} {a b : GenLoop (Fin n) X x}
    (H : a.1.HomotopyRel b.1 (Cube.boundary (Fin n))) : C(Disk n ⊕ Unit,C(I,X)) :=
  ⟨Sum.elim ((H.toHomotopy.toContinuousMap.comp
      ⟨fun z : Disk n × I => (z.2,CubeDisk.toCube n z.1),
        continuous_snd.prodMk ((CubeDisk.toCube n).continuous.comp continuous_fst)⟩).curry)
      (fun _ => .const I x),
    continuous_sum_dom.mpr ⟨(ContinuousMap.curry _).continuous,continuous_const⟩⟩

theorem homotopyData_boundary {n : ℕ} {a b : GenLoop (Fin n) X x}
    (H : a.1.HomotopyRel b.1 (Cube.boundary (Fin n))) (v : Disk n) (hv : ‖v.1‖ = 1) :
    homotopyData H (.inl v) = .const I x := by
  ext t
  exact (H.eq_fst t (CubeDisk.boundary_of_norm_eq_one v hv)).trans (sphereData_boundary a v hv)

theorem homotopyData_factors {n : ℕ} {a b : GenLoop (Fin n) X x}
    (H : a.1.HomotopyRel b.1 (Cube.boundary (Fin n))) :
    Function.FactorsThrough (homotopyData H) (sphereQuot n) := by
  intro v w h
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      rcases quotient_eq h with h | ⟨hv,hw⟩
      · exact congrArg (fun v => homotopyData H (.inl v)) h
      · exact (homotopyData_boundary H v hv).trans (homotopyData_boundary H w hw).symm
    | inr w => exact homotopyData_boundary H v (quotient_eq_pole h)
  | inr v =>
    cases w with
    | inl w => exact (homotopyData_boundary H w (quotient_eq_pole h.symm)).symm
    | inr w => rfl

def sphereHomotopy {n : ℕ} {a b : GenLoop (Fin n) X x}
    (H : a.1.HomotopyRel b.1 (Cube.boundary (Fin n))) : (sphereMap a).Homotopy (sphereMap b) := by
  let K := (sphereQuot_isQuotientMap n).lift (homotopyData H) (homotopyData_factors H)
  have hK (v : Disk n ⊕ Unit) : K (sphereQuot n v) = homotopyData H v :=
    DFunLike.congr_fun ((sphereQuot_isQuotientMap n).lift_comp (homotopyData H) (homotopyData_factors H)) v
  refine { toFun := fun z => K z.2 z.1
           continuous_toFun := (K.continuous.comp continuous_snd).eval continuous_fst
           map_zero_left := ?_
           map_one_left := ?_ }
  · intro z
    obtain ⟨v,rfl⟩ := sphereQuot_surjective n z
    rw [hK,sphereMap_apply_quot]
    cases v with
    | inl v => exact H.apply_zero (CubeDisk.toCube n v)
    | inr v => rfl
  · intro z
    obtain ⟨v,rfl⟩ := sphereQuot_surjective n z
    rw [hK,sphereMap_apply_quot]
    cases v with
    | inl v => exact H.apply_one (CubeDisk.toCube n v)
    | inr v => rfl

def map (n : ℕ) (z : integralHomology n (Boundary (n+1))) :
    HomotopyGroup (Fin n) X x → integralHomology n X :=
  Quotient.lift (fun a => pushforward n (sphereMap a) z) (by
    rintro a b ⟨H⟩
    rw [pushforward_homotopic n (sphereHomotopy H)])

@[simp] theorem map_mk (n : ℕ) (z : integralHomology n (Boundary (n+1)))
    (a : GenLoop (Fin n) X x) : map n z ⟦a⟧ = pushforward n (sphereMap a) z := rfl

@[simp] theorem pushforward_comp (n : ℕ) {Z : Type} [TopologicalSpace Z]
    (f : C(X,Y)) (g : C(Y,Z)) :
    pushforward n (g.comp f) = (pushforward n g).comp (pushforward n f) := by
  let F := (singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)
  exact congrArg ModuleCat.Hom.hom (F.map_comp (TopCat.ofHom f) (TopCat.ofHom g))

@[simp] theorem sphereMap_const (n : ℕ) :
    sphereMap (GenLoop.const (N := Fin n) (x := x)) = .const _ x := by
  ext v
  obtain ⟨w,rfl⟩ := sphereQuot_surjective n v
  rw [sphereMap_apply_quot]
  cases w <;> rfl

end HurewiczConstruction

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometry
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology

noncomputable section

namespace PresentationGeometry

namespace Rose

def attaching (k : ℕ) : C(Cells.boundary k 1, Point) := ContinuousMap.const _ PUnit.unit

abbrev Space (k : ℕ) := Cells.Space (attaching k)

def basepoint (k : ℕ) : Space k := Adjunction.old (attaching k) PUnit.unit

def generatorLoop {k : ℕ} (i : Fin k) : Path (basepoint k) (basepoint k) :=
  ((Path.segment leftEnd rightEnd).map'
    ((Cells.characteristic_continuousOn (attaching k) i).mono segmentInDisk)).cast
    (by
      change basepoint k = Cells.chart (attaching k) i leftEnd
      rw [Cells.chart_apply_sphere (attaching k) i leftEnd leftEnd_sphere]
      rfl)
    (by
      change basepoint k = Cells.chart (attaching k) i rightEnd
      rw [Cells.chart_apply_sphere (attaching k) i rightEnd rightEnd_sphere]
      rfl)

def letterLoop {k : ℕ} (a : Fin k × Bool) : Path (basepoint k) (basepoint k) :=
  if a.2 then generatorLoop a.1 else (generatorLoop a.1).symm

def wordLoop {k : ℕ} : List (Fin k × Bool) → Path (basepoint k) (basepoint k)
  | [] => Path.refl _
  | a :: w => (wordLoop w).trans (letterLoop a)

def freeToFundamental (k : ℕ) : FreeGroup (Fin k) →* FundamentalGroup (Space k) (basepoint k) :=
  FreeGroup.lift (fun i => ⟦generatorLoop i⟧)

theorem freeToFundamental_mk {k : ℕ} (w : List (Fin k × Bool)) :
    freeToFundamental k (FreeGroup.mk w) = ⟦wordLoop w⟧ := by
  let : Group (Quotient (Path.Homotopic.setoid (basepoint k) (basepoint k))) :=
    inferInstanceAs (Group (FundamentalGroup (Space k) (basepoint k)))
  change (w.map (fun a => cond a.2
    (⟦generatorLoop a.1⟧ : FundamentalGroup (Space k) (basepoint k))
    (⟦generatorLoop a.1⟧ : FundamentalGroup (Space k) (basepoint k))⁻¹)).prod = _
  induction w with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨i, b⟩
    cases b <;> simp only [List.map_cons, List.prod_cons, ih, Bool.cond_false,
      Bool.cond_true, wordLoop, letterLoop, Bool.false_eq_true, ↓reduceIte]
    <;> rfl

end Rose

end PresentationGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSupport
attribute [-instance] _root_.OAI.CoreDeck.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
namespace SingularSupport
open _root_.CategoryTheory AlgebraicTopology Limits SingularChains
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {n m : ℕ}

lemma induction_on (S : Submodule ℤ ((chains X).X n))
    (hS : ∀ f : C(Std n,X), gen f ∈ S) (c : (chains X).X n) : c ∈ S := by
  let : Module ℤ (((chains X).X n) ⧸ S) := Submodule.Quotient.module S
  let q : (chains X).X n ⟶ ModuleCat.of ℤ (((chains X).X n) ⧸ S) := ModuleCat.ofHom S.mkQ
  have hq : q = 0 := by
    apply hom_ext
    intro f
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change S.mkQ (gen f) = 0
    change gen f ∈ LinearMap.ker S.mkQ
    rw [Submodule.ker_mkQ]
    exact hS f
  have hc := congrArg (fun h => h c) hq
  change S.mkQ c = 0 at hc
  have hc' : c ∈ LinearMap.ker S.mkQ := hc
  simpa only [Submodule.ker_mkQ] using hc'

lemma boundary_gen (f : C(Std (n+1),X)) :
    (chains X).d (n+1) n (gen f) = ∑ i : Fin (n+2), (-1:ℤ)^i.val • gen (f.comp (face i)) := by
  have h := congrArg (fun h : ModuleCat.of ℤ ℤ ⟶ (chains X).X n => h 1) (generator_boundary f)
  simpa using h

end SingularSupport

namespace SmallChains
open Set _root_.CategoryTheory AlgebraicTopology Limits SingularChains
variable {X : Type} [TopologicalSpace X] {ι : Type} (U : ι → Set X)

abbrev Small {n : ℕ} (f : C(Std n,X)) : Prop := ∃ i, range f ⊆ U i

lemma small_comp {n m : ℕ} (f : C(Std n,X)) (hf : Small U f) (g : C(Std m,Std n)) :
    Small U (f.comp g) := by
  obtain ⟨i,hi⟩ := hf
  exact ⟨i,by rintro _ ⟨s,rfl⟩; exact hi (mem_range_self _)⟩

end SmallChains

namespace SubdivisionMesh
section
open Set Topology _root_.CategoryTheory ConvexSimplex AffineSupport
variable {N n m : ℕ}

def InHull (v : Fin (n+1) → Std N) (w : Fin (m+1) → Std N) : Prop :=
  ∀ i, ((w i).weights : Fin (N+1) → ℝ) ∈
    convexHull ℝ (range (fun j => ((v j).weights : Fin (N+1) → ℝ)))

lemma hull_self (v : Fin (n+1) → Std N) : InHull v v :=
  fun i => subset_convexHull ℝ _ (mem_range_self i)

lemma hull_face_subset (v : Fin (n+2) → Std N) (i : Fin (n+2)) :
    convexHull ℝ (range (fun j => ((v (i.succAbove j)).weights : Fin (N+1) → ℝ))) ⊆
      convexHull ℝ (range (fun j => ((v j).weights : Fin (N+1) → ℝ))) :=
  convexHull_mono (by rintro _ ⟨j,rfl⟩; exact mem_range_self _)

lemma center_hull (v : Fin (n+1) → Std N) :
    ((center v).weights : Fin (N+1) → ℝ) ∈
      convexHull ℝ (range (fun j => ((v j).weights : Fin (N+1) → ℝ))) := by
  rw [center_coe,Finsupp.coe_smul,Finsupp.coe_finsetSum]
  exact AffineMesh.center_mem_hull _

end

open Set Topology _root_.CategoryTheory ConvexSimplex AffineSupport

end SubdivisionMesh

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CWCellular
attribute [-instance] _root_.OAI.CoreDeck.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric

namespace CWExtension

open Set Topology Metric
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

lemma compact_subset_skel {K : Set X} (hk : IsCompact K) (hKC : K ⊆ C) : ∃ n : ℕ, K ⊆ Skel C n := by
  classical
  by_contra hbound
  have hex (n : ℕ) : ∃ x, x ∈ K ∧ x ∉ Skel C n := by
    by_contra h
    apply hbound
    refine ⟨n,?_⟩
    intro x hx
    by_contra hn
    exact h ⟨x,hx,hn⟩
  choose z hzK hzN using hex
  have hzC : range z ⊆ C := by rintro _ ⟨n,rfl⟩; exact hKC (hzK n)
  have hc (T : Set X) (hT : T ⊆ range z) : IsClosed T := by
    apply (CWComplex.closed C T (hT.trans hzC)).mpr
    intro m i
    apply Set.Finite.isClosed
    apply ((finite_Iio (m+1)).image z).subset
    rintro x ⟨hxT,hxcell⟩
    obtain ⟨n,rfl⟩ := hT hxT
    refine ⟨n,?_,rfl⟩
    change n < m+1
    by_contra hn
    exact hzN n (RelCWComplex.skeletonLT_mono (by exact_mod_cast (le_of_not_gt hn))
      (RelCWComplex.closedCell_subset_skeletonLT m i hxcell))
  have hd : IsDiscrete (range z) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro T hT
    exact ⟨T,hc T hT,inter_eq_left.mpr hT⟩
  have hkr : IsCompact (range z) := hk.of_isClosed_subset (hc _ (Subset.rfl)) (by
    rintro _ ⟨n,rfl⟩; exact hzK n)
  obtain ⟨n,hn⟩ := finite_subset_skel (hkr.finite hd) hzC
  exact hzN n (hn (mem_range_self n))

end CWExtension

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CoveringCellGeometry
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology unitInterval

namespace CoveringCW
section
open Set Topology Metric CoveringCellGeometry
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
  [CWComplex (univ : Set X)] {p : E → X} (cov : IsCoveringMap p)

@[simp] theorem characteristic_on_disk (n : ℕ) (c : Cell (p := p) n) (v : Disk n) :
    characteristic cov n c v = characteristicLift cov (baseChar n c.1) c.2 v := by
  simp only [characteristic,dite_eq_left v.2]

theorem characteristic_proj (n : ℕ) (c : Cell (p := p) n)
    {v : Fin n → ℝ} (hv : v ∈ closedBall 0 1) :
    p (characteristic cov n c v) = RelCWComplex.map n c.1 v := by
  rw [show characteristic cov n c v = characteristicLift cov (baseChar n c.1) c.2 ⟨v,hv⟩ from
    characteristic_on_disk cov n c ⟨v,hv⟩]
  exact characteristicLift_proj cov (baseChar n c.1) c.2 ⟨v,hv⟩

theorem characteristic_continuousOn (n : ℕ) (c : Cell (p := p) n) :
    ContinuousOn (characteristic cov n c) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun v : Disk n => characteristic cov n c v)
  have he : (fun v : Disk n => characteristic cov n c v) =
      characteristicLift cov (baseChar n c.1) c.2 := by
    funext v
    exact characteristic_on_disk cov n c v
  rw [he]
  exact (characteristicLift cov (baseChar n c.1) c.2).continuous

theorem characteristic_injOn (n : ℕ) (c : Cell (p := p) n) :
    InjOn (characteristic cov n c) (ball 0 1) := by
  intro v hv w hw he
  apply (RelCWComplex.map n c.1).injOn
  · simpa only [RelCWComplex.source_eq] using hv
  · simpa only [RelCWComplex.source_eq] using hw
  · simpa only [characteristic_proj cov n c (ball_subset_closedBall hv),
      characteristic_proj cov n c (ball_subset_closedBall hw)] using congrArg p he

def chart (n : ℕ) (c : Cell (p := p) n) : PartialEquiv (Fin n → ℝ) E :=
  (characteristic_injOn cov n c).toPartialEquiv (characteristic cov n c) (ball 0 1)

@[simp] theorem chart_coe (n : ℕ) (c : Cell (p := p) n) :
    ⇑(chart cov n c) = characteristic cov n c := rfl
@[simp] theorem chart_source (n : ℕ) (c : Cell (p := p) n) :
    (chart cov n c).source = ball 0 1 := rfl
@[simp] theorem chart_target (n : ℕ) (c : Cell (p := p) n) :
    (chart cov n c).target = chart cov n c '' ball 0 1 := rfl

theorem chart_proj (n : ℕ) (c : Cell (p := p) n)
    {v : Fin n → ℝ} (hv : v ∈ closedBall 0 1) :
    p (chart cov n c v) = RelCWComplex.map n c.1 v := characteristic_proj cov n c hv

theorem chart_continuousOn (n : ℕ) (c : Cell (p := p) n) :
    ContinuousOn (chart cov n c) (closedBall 0 1) := characteristic_continuousOn cov n c

theorem chart_symm_eq (n : ℕ) (c : Cell (p := p) n) {e : E} (he : e ∈ (chart cov n c).target) :
    (chart cov n c).symm e = (RelCWComplex.map n c.1).symm (p e) := by
  rcases he with ⟨v,hv,rfl⟩
  rw [characteristic_proj cov n c (ball_subset_closedBall hv)]
  have hs : v ∈ (RelCWComplex.map n c.1).source := by
    simpa only [RelCWComplex.source_eq] using hv
  exact (chart cov n c).left_inv hv |>.trans ((RelCWComplex.map n c.1).left_inv hs).symm

theorem chart_continuousOn_symm (n : ℕ) (c : Cell (p := p) n) :
    ContinuousOn (chart cov n c).symm (chart cov n c).target := by
  apply ContinuousOn.congr ((RelCWComplex.continuousOn_symm n c.1).comp
    cov.continuous.continuousOn ?_) (fun e he => chart_symm_eq cov n c he)
  rintro e ⟨v,hv,rfl⟩
  rw [characteristic_proj cov n c (ball_subset_closedBall hv)]
  exact (RelCWComplex.map n c.1).map_source (by simpa only [RelCWComplex.source_eq] using hv)

theorem chart_cell_eq {n m : ℕ} (c : Cell (p := p) n) (d : Cell (p := p) m)
    {v : Fin n → ℝ} {w : Fin m → ℝ} (hv : v ∈ ball 0 1) (hw : w ∈ ball 0 1)
    (he : chart cov n c v = chart cov m d w) : (⟨n,c⟩ : Σ n,Cell (p := p) n) = ⟨m,d⟩ := by
  classical
  have hp : RelCWComplex.map n c.1 v = RelCWComplex.map m d.1 w := by
    simpa only [chart_proj cov n c (ball_subset_closedBall hv),
      chart_proj cov m d (ball_subset_closedBall hw)] using congrArg p he
  by_cases hbase : (⟨n,c.1⟩ : Σ n,BaseCell (X := X) n) = ⟨m,d.1⟩
  · rcases c with ⟨i,j⟩
    rcases d with ⟨i',j'⟩
    cases hbase
    have hvw : v = w := (RelCWComplex.map n i).injOn
      (by simpa only [RelCWComplex.source_eq] using hv)
      (by simpa only [RelCWComplex.source_eq] using hw) hp
    subst w
    have hj : j = j' := characteristicLift_fiber_injective cov (baseChar n i)
      (⟨v,ball_subset_closedBall hv⟩ : Disk n) (by
        exact (characteristic_on_disk cov n ⟨i,j⟩ ⟨v,ball_subset_closedBall hv⟩).symm.trans
          (he.trans (characteristic_on_disk cov n ⟨i,j'⟩ ⟨v,ball_subset_closedBall hv⟩)))
    subst j'
    rfl
  · exact False.elim (Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne hbase)
      ⟨v,hv,rfl⟩ ⟨w,hw,hp.symm⟩)

theorem chart_pairwiseDisjoint :
    (univ : Set (Σ n,Cell (p := p) n)).PairwiseDisjoint
      (fun ni => chart cov ni.1 ni.2 '' ball 0 1) := by
  rintro ⟨n,c⟩ _ ⟨m,d⟩ _ hne
  apply Set.disjoint_left.mpr
  rintro e ⟨v,hv,rfl⟩ ⟨w,hw,he⟩
  exact hne (chart_cell_eq cov c d hv hw he.symm)

theorem chart_union :
    (⋃ n, ⋃ c : Cell (p := p) n, chart cov n c '' closedBall 0 1) = univ := by
  apply eq_univ_of_forall
  intro e
  have hp : p e ∈ ⋃ n, ⋃ i : BaseCell (X := X) n, RelCWComplex.closedCell n i := by
    rw [CWComplex.union]
    trivial
  simp only [mem_iUnion,RelCWComplex.closedCell,mem_image] at hp
  rcases hp with ⟨n,i,v,hv,he⟩
  let z : Pullback (p := p) (baseChar n i) := ⟨(⟨v,hv⟩,e),he.symm⟩
  simp only [mem_iUnion,mem_image]
  refine ⟨n,⟨i,sheet cov (baseChar n i) z⟩,v,hv,?_⟩
  exact (characteristic_on_disk cov n _ ⟨v,hv⟩).trans (characteristicLift_sheet cov (baseChar n i) z)

end

open Set Topology Metric CoveringCellGeometry
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
  [CWComplex (univ : Set X)] [T2Space X] {p : E → X} (cov : IsCoveringMap p)

omit [T2Space X] in
theorem chart_closedCell_eq_range (n : ℕ) (c : Cell (p := p) n) :
    chart cov n c '' closedBall 0 1 = range (characteristicLift cov (baseChar n c.1) c.2) := by
  ext e
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact ⟨⟨v,hv⟩,(characteristic_on_disk cov n c ⟨v,hv⟩).symm⟩
  · rintro ⟨v,rfl⟩
    exact ⟨v,v.2,characteristic_on_disk cov n c v⟩

omit [T2Space X] in
theorem chart_isCompact (n : ℕ) (c : Cell (p := p) n) :
    IsCompact (chart cov n c '' closedBall 0 1) := by
  rw [chart_closedCell_eq_range]
  exact isCompact_range (characteristicLift cov (baseChar n c.1) c.2).continuous

theorem closed_over_cell (S : Set E) (n : ℕ) (i : BaseCell (X := X) n)
    (hS : ∀ j : Fiber (p := p) n i,
      IsClosed (S ∩ chart cov n ⟨i,j⟩ '' closedBall 0 1)) :
    IsClosed (S ∩ p ⁻¹' (RelCWComplex.map n i '' closedBall 0 1)) := by
  let : DiscreteTopology (Fiber (p := p) n i) :=
    (cov (baseChar n i (contractionPoint (Disk n)))).discreteTopology_fiber
  let F : Disk n × Fiber (p := p) n i → E := fun z => characteristicLift cov (baseChar n i) z.2 z.1
  have hpre : IsClosed (F ⁻¹' S) := by
    apply isClosed_discrete_slices
    intro j
    have h := (hS j).preimage (characteristicLift cov (baseChar n i) j).continuous
    have he : (fun a : Disk n => F (a,j)) ⁻¹' S =
        (characteristicLift cov (baseChar n i) j) ⁻¹' (S ∩ chart cov n ⟨i,j⟩ '' closedBall 0 1) := by
      ext a
      simp only [mem_preimage,mem_inter_iff,F]
      exact ⟨fun ha => ⟨ha,⟨a,a.2,characteristic_on_disk cov n ⟨i,j⟩ a⟩⟩,And.left⟩
    exact he ▸ h
  have hclosed := characteristicLift_isClosedMap cov (baseChar n i) _ hpre
  have he : F '' (F ⁻¹' S) = S ∩ p ⁻¹' (RelCWComplex.map n i '' closedBall 0 1) := by
    ext e
    constructor
    · rintro ⟨⟨a,j⟩,ha,rfl⟩
      refine ⟨ha,?_⟩
      exact ⟨a,a.2,(characteristicLift_proj cov (baseChar n i) j a).symm⟩
    · rintro ⟨heS,v,hv,hve⟩
      let z : Pullback (p := p) (baseChar n i) := ⟨(⟨v,hv⟩,e),hve.symm⟩
      have hz : F (⟨v,hv⟩,sheet cov (baseChar n i) z) = e :=
        characteristicLift_sheet cov (baseChar n i) z
      exact ⟨(⟨v,hv⟩,sheet cov (baseChar n i) z),by simpa only [mem_preimage,hz] using heS,hz⟩
  exact he ▸ hclosed

theorem base_isOpen_of_cells (O : Set X)
    (hO : ∀ n (i : BaseCell (X := X) n), IsOpen (baseChar n i ⁻¹' O)) : IsOpen O := by
  rw [← isClosed_compl_iff]
  apply (CWComplex.closed (univ : Set X) _ (subset_univ _)).mpr
  intro n i
  have hk : IsCompact (baseChar n i ⁻¹' Oᶜ) := (by
    simpa only [preimage_compl] using (hO n i).isClosed_compl :
      IsClosed (baseChar n i ⁻¹' Oᶜ)).isCompact
  have he : Oᶜ ∩ RelCWComplex.closedCell n i =
      baseChar n i '' (baseChar n i ⁻¹' Oᶜ) := by
    ext x
    constructor
    · rintro ⟨hx,v,hv,hvx⟩
      exact ⟨⟨v,hv⟩,by change RelCWComplex.map n i v ∈ Oᶜ; rwa [hvx],hvx⟩
    · rintro ⟨v,hv,rfl⟩
      exact ⟨hv,v,v.2,rfl⟩
  rw [he]
  exact (hk.image (baseChar n i).continuous).isClosed

theorem chart_closed_general (S : Set E)
    (hS : ∀ n (c : Cell (p := p) n), IsClosed (S ∩ chart cov n c '' closedBall 0 1)) :
    IsClosed S := by
  rw [← isOpen_compl_iff,isOpen_iff_mem_nhds]
  intro e he
  obtain ⟨t,hte,hpt⟩ := cov.isLocalHomeomorph e
  let O : Set X := t.target ∩ t.symm ⁻¹' Sᶜ
  have hO : IsOpen O := by
    apply base_isOpen_of_cells
    intro n i
    let F := S ∩ p ⁻¹' (RelCWComplex.map n i '' closedBall 0 1)
    have hF : IsClosed F := closed_over_cell cov S n i (fun j => hS n ⟨i,j⟩)
    have hcont : ContinuousOn (t.symm ∘ baseChar n i) (baseChar n i ⁻¹' t.target) :=
      t.continuousOn_invFun.comp (baseChar n i).continuous.continuousOn (fun _ hx => hx)
    have hopen := hcont.isOpen_inter_preimage
      (t.open_target.preimage (baseChar n i).continuous) hF.isOpen_compl
    have heq : baseChar n i ⁻¹' O =
        (baseChar n i ⁻¹' t.target) ∩ (t.symm ∘ baseChar n i) ⁻¹' Fᶜ := by
      ext v
      simp only [O,preimage_inter,mem_inter_iff,mem_preimage,Function.comp_apply]
      apply and_congr_right
      intro hv
      have hp : p (t.symm (baseChar n i v)) = baseChar n i v := by
        rw [hpt]
        exact t.right_inv hv
      have hc : t.symm (baseChar n i v) ∈ p ⁻¹' (RelCWComplex.map n i '' closedBall 0 1) :=
        ⟨v,v.2,hp.symm⟩
      simp only [F,mem_compl_iff,mem_inter_iff,hc,and_true]
    exact heq ▸ hopen
  have hV : IsOpen (t.symm '' O) := t.isOpen_image_symm_of_subset_target hO (inter_subset_left)
  have heV : e ∈ t.symm '' O := by
    refine ⟨t e,⟨t.map_source hte,?_⟩,t.left_inv hte⟩
    change t.symm (t e) ∈ Sᶜ
    rwa [t.left_inv hte]
  exact Filter.mem_of_superset (hV.mem_nhds heV) (by
    rintro _ ⟨x,hx,rfl⟩
    exact hx.2)

def meetingCellsOver (K : Set E) (hK : IsCompact K) (n : ℕ)
    (J : Finset (BaseCell (X := X) n)) : Finset (Cell (p := p) n) := by
  classical
  exact J.sigma (fun i => (finite_sheets_meeting cov (baseChar n i) hK).toFinset)

 theorem chart_mapsTo_general (n : ℕ) (c : Cell (p := p) n) :
    ∃ J : Π m, Finset (Cell (p := p) m),
      MapsTo (chart cov n c) (sphere 0 1)
        (⋃ (m < n) (d ∈ J m), chart cov m d '' closedBall 0 1) := by
  classical
  let K := chart cov n c '' closedBall 0 1
  have hK : IsCompact K := chart_isCompact cov n c
  obtain ⟨J0,hI⟩ := CWComplex.mapsTo n c.1
  refine ⟨fun m => meetingCellsOver cov K hK m (J0 m),?_⟩
  intro v hv
  have hp := hI hv
  simp only [mem_iUnion,mem_image] at hp
  rcases hp with ⟨m,hm,i,hi,w,hw,he⟩
  let e := chart cov n c v
  have hpe : p e = baseChar m i ⟨w,hw⟩ :=
    (chart_proj cov n c (sphere_subset_closedBall hv)).trans he.symm
  let z : Pullback (p := p) (baseChar m i) := ⟨(⟨w,hw⟩,e),hpe⟩
  let d : Cell (p := p) m := ⟨i,sheet cov (baseChar m i) z⟩
  have hd : chart cov m d w = e :=
    (characteristic_on_disk cov m d ⟨w,hw⟩).trans (characteristicLift_sheet cov (baseChar m i) z)
  have hdJ : d ∈ meetingCellsOver cov K hK m (J0 m) := by
    simp only [meetingCellsOver,Finset.mem_sigma,Set.Finite.mem_toFinset,mem_ofPred_eq]
    refine ⟨hi,⟨⟨w,hw⟩,?_⟩⟩
    change characteristicLift cov (baseChar m i) (sheet cov (baseChar m i) z) z.1.1 ∈ K
    rw [characteristicLift_sheet]
    exact ⟨v,sphere_subset_closedBall hv,rfl⟩
  simp only [mem_iUnion,mem_image]
  exact ⟨m,hm,d,hdJ,w,hw,hd⟩

@[instance_reducible] def cwComplex_general : CWComplex (univ : Set E) where
  cell := Cell (p := p)
  map := chart cov
  source_eq := chart_source cov
  continuousOn := chart_continuousOn cov
  continuousOn_symm := chart_continuousOn_symm cov
  pairwiseDisjoint' := chart_pairwiseDisjoint cov
  mapsTo' := chart_mapsTo_general cov
  closed' S _ := chart_closed_general cov S
  union' := chart_union cov

end CoveringCW

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CoveringCellGeometryHausdorff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoreDeck
open Set Topology DiscreteCoverCharts
variable {ι X Q : Type} [TopologicalSpace X] [Group Q] [TopologicalSpace Q]
  [DiscreteTopology Q] (Z : FiberBundleCore ι X Q)
  (hZ : ∀ i j x a q, Z.coordChange i j x (a*q) = Z.coordChange i j x a * q)

include hZ in
omit [DiscreteTopology Q] in
lemma right_chart (q : Q) (i : ι) (z : Z.TotalSpace) (hz : z.1 ∈ Z.baseSet i) :
    right Z q z = point Z i z.1 (((Z.localTriv i) z).2*q) := by
  simp only [right]
  change (⟨z.1,@HMul.hMul Q Q Q _ z.2 q⟩ : Z.TotalSpace) =
    ⟨z.1,Z.coordChange i (Z.indexAt z.1) z.1 (Z.coordChange (Z.indexAt z.1) i z.1 z.2 * q)⟩
  erw [hZ,Z.coordChange_comp (Z.indexAt z.1) i (Z.indexAt z.1) z.1
    ⟨⟨Z.mem_baseSet_at _,hz⟩,Z.mem_baseSet_at _⟩,
    Z.coordChange_self (Z.indexAt z.1) z.1 (Z.mem_baseSet_at _)]

include hZ in
lemma continuous_right (q : Q) : Continuous (right Z q) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let i := Z.indexAt z.1
  have hc : ContinuousOn (fun a : Z.TotalSpace => point Z i a.1 (((Z.localTriv i) a).2*q))
      (Z.localTriv i).source := by
    apply (Z.localTriv i).toOpenPartialHomeomorph.symm.continuousOn.comp
    · exact Z.continuous_proj.continuousOn.prodMk
        ((continuous_snd.comp_continuousOn (Z.localTriv i).continuousOn).mul continuousOn_const)
    · intro a ha
      exact (Z.mem_localTriv_target i _).mpr ha
  have hc' : ContinuousOn (right Z q) (Z.localTriv i).source :=
    hc.congr (fun a ha => right_chart Z hZ q i a ha)
  exact hc'.continuousAt ((Z.localTriv i).open_source.mem_nhds (Z.mem_baseSet_at _))

end CoreDeck

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_BasedHorn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open _root_.CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval
open Set Topology
open scoped unitInterval

namespace HurewiczAddition
open Set Topology _root_.CategoryTheory AlgebraicTopology Limits HomologicalComplex
open SingularChains DuffyTriangle
variable {X : Type} [TopologicalSpace X] {n : ℕ} {x : X}

lemma alternating_three {A : Type*} [AddCommGroup A] (n : ℕ) (f : Fin (n+3) → A)
    (he : ∀ i, i.val < n → f i = 0) :
    (∑ i, (-1:ℤ)^i.val • f i) = (-1:ℤ)^n •
      (f (lastFace n 0) - f (lastFace n 1) + f (lastFace n 2)) := by
  induction n with
  | zero => simp [lastFace,Fin.sum_univ_succ]; abel
  | succ n ih =>
    rw [Fin.sum_univ_succ,he 0 (by simp),smul_zero,zero_add]
    have hs : (∑ i : Fin (n+3), (-1:ℤ)^(i.val+1) • f i.succ) =
        - ∑ i : Fin (n+3), (-1:ℤ)^i.val • f i.succ := by
      simp only [pow_succ,mul_neg_one,neg_smul,Finset.sum_neg_distrib]
    simp only [Fin.val_succ]
    rw [hs,ih (fun i => f i.succ) (fun i hi => he i.succ (by simpa only [Fin.val_succ] using Nat.succ_lt_succ hi))]
    simp only [lastFace,pow_succ,mul_neg_one,neg_smul]

end HurewiczAddition

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_FiniteIdempotentDiagrams
attribute [-instance] _root_.OAI.CoreDeck.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteIdempotentDiagrams

section

open Matrix
open scoped Matrix

variable {K R T : Type*} [CommRing K] [Ring R] [AddCommGroup T]

structure ThreeCopies (K R : Type*) [CommRing K] [Ring R] where
  copy : Fin 3 → (Mat3 K →ₙ+* R)
  first_one : copy 0 1 = 1
  common_second : ∀ i, copy i (diagonalUnit 1) = copy 0 (diagonalUnit 1)
  common_third : ∀ i, copy i (diagonalUnit 2) = copy 0 (diagonalUnit 2)
  partition : copy 0 (diagonalUnit 0) =
    copy 1 (diagonalUnit 0) + copy 2 (diagonalUnit 0)
  partition_orthogonal : copy 1 (diagonalUnit 0) * copy 2 (diagonalUnit 0) = 0
  partition_orthogonal' : copy 2 (diagonalUnit 0) * copy 1 (diagonalUnit 0) = 0

end

open Matrix
open scoped Matrix

end FiniteIdempotentDiagrams

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CWWhitehead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CWWhitehead
open Set Topology Metric CWExtension
open scoped unitInterval
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] {C : Set X} [CWComplex C]

structure Stage (f₀ f₁ : C(C,Y)) (n : ℕ) where
  path : C(Skel C n,C(I,Y))
  at_zero : ∀ x, path x 0 = f₀ (skelToComplex n x)
  at_one : ∀ x, path x 1 = f₁ (skelToComplex n x)

variable {f₀ f₁ : C(C,Y)} {n : ℕ}

def cellSide (H : Stage f₀ f₁ n) (i : RelCWComplex.cell C n) : C(I × Boundary n,Y) :=
  ⟨fun z => H.path (boundarySkel n i z.2) z.1,
    (H.path.continuous.comp ((boundarySkel n i).continuous.comp continuous_snd)).eval continuous_fst⟩

theorem exists_cell_extension (hfill : CWCylinder.SphereFill Y)
    (H : Stage f₀ f₁ n) (i : RelCWComplex.cell C n) :
    ∃ g : C(Disk n,C(I,Y)),
      (∀ v, g v 0 = f₀ (charMap n i v)) ∧
      (∀ v, g v 1 = f₁ (charMap n i v)) ∧
      ∀ v : Boundary n,g (CWCylinder.boundaryDisk n v) = H.path (boundarySkel n i v) := by
  have h₀ : ∀ v,cellSide H i (0,v) = (f₀.comp (charMap n i)) (CWCylinder.boundaryDisk n v) := by
    intro v
    exact H.at_zero (boundarySkel n i v)
  have h₁ : ∀ v,cellSide H i (1,v) = (f₁.comp (charMap n i)) (CWCylinder.boundaryDisk n v) := by
    intro v
    exact H.at_one (boundarySkel n i v)
  obtain ⟨F,hF₀,hF₁,hFside⟩ := CWCylinder.exists_cylinder hfill
    (f₀.comp (charMap n i)) (f₁.comp (charMap n i)) (cellSide H i) h₀ h₁
  refine ⟨(F.comp ⟨Prod.swap,continuous_swap⟩).curry,hF₀,hF₁,?_⟩
  intro v
  ext t
  exact hFside t v

theorem exists_next (hfill : CWCylinder.SphereFill Y) (H : Stage f₀ f₁ n) :
    ∃ K : Stage f₀ f₁ (n+1),∀ x,K.path (skelIncl n x) = H.path x := by
  classical
  choose g hg₀ hg₁ hgb using exists_cell_extension hfill H
  change ∀ i (v : Boundary n), g i ⟨v,sphere_subset_closedBall v.2⟩ = H.path (boundarySkel n i v) at hgb
  let Kpath := extendSkel n H.path g hgb
  have h₀ : ∀ x,Kpath x 0 = f₀ (skelToComplex (n+1) x) := by
    intro x
    obtain ⟨a,rfl⟩ := stageQuot_surjective n x
    rcases a with a | ⟨i,v⟩
    · change (extendSkel n H.path g hgb (skelIncl n a)) 0 = _
      rw [extendSkel_prior]
      exact H.at_zero a
    · change (extendSkel n H.path g hgb (charSkel n i v)) 0 = _
      rw [extendSkel_disk]
      exact hg₀ i v
  have h₁ : ∀ x,Kpath x 1 = f₁ (skelToComplex (n+1) x) := by
    intro x
    obtain ⟨a,rfl⟩ := stageQuot_surjective n x
    rcases a with a | ⟨i,v⟩
    · change (extendSkel n H.path g hgb (skelIncl n a)) 1 = _
      rw [extendSkel_prior]
      exact H.at_one a
    · change (extendSkel n H.path g hgb (charSkel n i v)) 1 = _
      rw [extendSkel_disk]
      exact hg₁ i v
  exact ⟨⟨Kpath,h₀,h₁⟩,fun x => extendSkel_prior n H.path g hgb x⟩

def next (hfill : CWCylinder.SphereFill Y) (H : Stage f₀ f₁ n) : Stage f₀ f₁ (n+1) :=
  (exists_next hfill H).choose

theorem next_compat (hfill : CWCylinder.SphereFill Y) (H : Stage f₀ f₁ n) (x : Skel C n) :
    (next hfill H).path (skelIncl n x) = H.path x :=
  (exists_next hfill H).choose_spec x

def emptyStage (f₀ f₁ : C(C,Y)) : Stage f₀ f₁ 0 := by
  letI : IsEmpty (Skel C 0) := ⟨fun x => by
    have hx := x.2
    simp only [Skel,Nat.cast_zero,CWComplex.skeletonLT_zero_eq_empty,mem_empty_iff_false] at hx⟩
  exact ⟨⟨isEmptyElim,continuous_of_discreteTopology⟩,fun x => isEmptyElim x,fun x => isEmptyElim x⟩

def build (hfill : CWCylinder.SphereFill Y) (f₀ f₁ : C(C,Y)) : (n : ℕ) → Stage f₀ f₁ n
  | 0 => emptyStage f₀ f₁
  | n+1 => next hfill (build hfill f₀ f₁ n)

theorem build_compat (hfill : CWCylinder.SphereFill Y) (f₀ f₁ : C(C,Y)) (n : ℕ) (x : Skel C n) :
    (build hfill f₀ f₁ (n+1)).path (skelIncl n x) = (build hfill f₀ f₁ n).path x :=
  next_compat hfill (build hfill f₀ f₁ n) x

def allPaths (hfill : CWCylinder.SphereFill Y) (f₀ f₁ : C(C,Y)) : C(C,C(I,Y)) :=
  unionMap (fun n => (build hfill f₀ f₁ n).path) (build_compat hfill f₀ f₁)

theorem allPaths_zero (hfill : CWCylinder.SphereFill Y) (f₀ f₁ : C(C,Y)) (x : C) :
    allPaths hfill f₀ f₁ x 0 = f₀ x := by
  obtain ⟨⟨n,y⟩,rfl⟩ := wholeQuot_surjective (C := C) x
  change unionMap (fun k => (build hfill f₀ f₁ k).path) (build_compat hfill f₀ f₁) (skelToComplex n y) 0 = _
  rw [unionMap_skel]
  exact (build hfill f₀ f₁ n).at_zero y

theorem allPaths_one (hfill : CWCylinder.SphereFill Y) (f₀ f₁ : C(C,Y)) (x : C) :
    allPaths hfill f₀ f₁ x 1 = f₁ x := by
  obtain ⟨⟨n,y⟩,rfl⟩ := wholeQuot_surjective (C := C) x
  change unionMap (fun k => (build hfill f₀ f₁ k).path) (build_compat hfill f₀ f₁) (skelToComplex n y) 1 = _
  rw [unionMap_skel]
  exact (build hfill f₀ f₁ n).at_one y

def homotopy (hfill : CWCylinder.SphereFill Y) (f₀ f₁ : C(C,Y)) : f₀.Homotopy f₁ where
  toFun z := allPaths hfill f₀ f₁ z.2 z.1
  continuous_toFun := ((allPaths hfill f₀ f₁).continuous.comp continuous_snd).eval continuous_fst
  map_zero_left := allPaths_zero hfill f₀ f₁
  map_one_left := allPaths_one hfill f₀ f₁

end CWWhitehead

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SimplexRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open Set Topology Metric
open scoped unitInterval
open _root_.CategoryTheory AlgebraicTopology Limits
open Set Topology
open scoped unitInterval
open Set Topology
open scoped unitInterval
namespace SimplexRotation
open Set Topology
open scoped unitInterval
variable {n : ℕ}

lemma radius_nonneg (s : Std n) : 0 ≤ radius s := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n+1)))) => minimum_le s i)
  simpa only [radius,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,s.total_of_fintype] using sub_nonneg.mpr h

lemma radius_zero_iff (s : Std n) : radius s = 0 ↔ ∀ i, s.weights i = minimum s := by
  constructor
  · intro h
    have hs : ∑ i, (s.weights i - minimum s) = 0 := by
      rw [Finset.sum_sub_distrib,s.total_of_fintype]
      simpa [radius] using h
    intro i
    exact sub_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.mpr (minimum_le s j))).mp hs i (Finset.mem_univ i))
  · intro h
    have hs := s.total_of_fintype
    simp only [h,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
    exact sub_eq_zero.mpr hs.symm

def radial (s : Std n) (h : 0 < radius s) : Boundary n :=
  ⟨⟨Finsupp.equivFunOnFinite.symm (fun i => (s.weights i-minimum s)/radius s),by
    intro i
    exact div_nonneg (sub_nonneg.mpr (minimum_le s i)) h.le,by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change ∑ i, (s.weights i-minimum s)/radius s = 1
    rw [← Finset.sum_div,Finset.sum_sub_distrib,s.total_of_fintype]
    simpa only [radius,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using div_self h.ne'⟩,by
    obtain ⟨i,hi⟩ := minimum_attained s
    exact ⟨i,by simp [hi]⟩⟩

end SimplexRotation

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSigmaSingleMerge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
attribute [-instance] AddCommGroup.toIntModule

attribute [instance] AddCommGroup.toIntModule

end

namespace CWEquivariant
attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension CWCellular _root_.CategoryTheory HomologicalComplex
variable {G X : Type} [Group G] [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
  [∀ n, MulAction G (RelCWComplex.cell (univ : Set X) n)]
variable (hc : ∀ (g : G) n (i : RelCWComplex.cell (univ : Set X) n) (v : Disk n),
  g • RelCWComplex.map n i v = RelCWComplex.map n (g • i) v)

include hc in
omit [ContinuousConstSMul G X] in
lemma smul_skel (g : G) (n : ℕ) : MapsTo (g • ·) (Skel (univ : Set X) n) (Skel (univ : Set X) n) := by
  intro x hx
  obtain ⟨m,hm,i,v,hv,rfl⟩ := CWComplex.mem_skeletonLT_iff.mp hx
  refine CWComplex.mem_skeletonLT_iff.mpr ⟨m,hm,g • i,v,hv,?_⟩
  exact (hc g m i ⟨v,Metric.ball_subset_closedBall hv⟩).symm

def skeletal (g : G) : SkeletalMap (univ : Set X) (univ : Set X) where
  toMap := ⟨(g • ·),continuous_const_smul g⟩
  maps := smul_skel hc g

attribute [instance] AddCommGroup.toIntModule
end CWEquivariant

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
namespace SingularAction
attribute [-instance] AddCommGroup.toIntModule
open Set Topology _root_.CategoryTheory HomologicalComplex ProductCriterion

attribute [instance] AddCommGroup.toIntModule
end SingularAction

namespace EquivariantCoverCells
open Set Topology _root_.CategoryTheory
open CoveringCW
open scoped MonoidAlgebra
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
    [T2Space X] [T2Space E] [CWComplex (univ : Set X)]
    {G : Type u} [Group G] [MulAction G E] [ContinuousConstSMul G E]
    {p : E → X} [hproj : Fact (∀ (g : G) x, p (g • x) = p x)]
    (hfree : ∀ (g h : G) (x : E), g • x = h • x → g = h)
    (htrans : ∀ (a b : E), p a = p b → ∃ g : G, g • a = b)
    (surj : Function.Surjective p)

instance cellAction (n : ℕ) : MulAction G (Cell (p := p) n) where
  smul d c := ⟨c.1,⟨d • c.2.1,(hproj.out d c.2.1).trans c.2.2⟩⟩
  one_smul c := by
    rcases c with ⟨i,c⟩
    change (⟨i,⟨(1:G) • c.1,_⟩⟩ : Cell (p:=p) n) = ⟨i,c⟩
    exact congrArg (Sigma.mk i) (Subtype.ext (one_smul G c.1))
  mul_smul d e c := by
    change (⟨c.1,⟨(d*e) • c.2.1,_⟩⟩ : Cell (p:=p) n) = ⟨c.1,⟨d • (e • c.2.1),_⟩⟩
    exact congrArg (Sigma.mk c.1) (Subtype.ext (mul_smul d e c.2.1))

noncomputable def seed (n : ℕ) (i : BaseCell (X := X) n) : Fiber (p := p) n i :=
  ⟨Classical.choose (surj (baseChar n i (CoveringCellGeometry.contractionPoint (Disk n)))),
    Classical.choose_spec (surj (baseChar n i (CoveringCellGeometry.contractionPoint (Disk n))))⟩

noncomputable def cellEquiv (n : ℕ) : BaseCell (X := X) n × G ≃ Cell (p := p) n :=
  Equiv.ofBijective (fun z => z.2 • (⟨z.1,seed surj n z.1⟩ : Cell (p := p) n)) (by
    constructor
    · rintro ⟨i,d⟩ ⟨j,e⟩ h
      have hij : i = j := congrArg Sigma.fst h
      subst j
      have hde : d = e := hfree d e (seed surj n i).1
        (congrArg (fun c : Cell (p := p) n => (c.2 : E)) h)
      exact Prod.ext rfl hde
    · rintro ⟨i,a⟩
      obtain ⟨d,hd⟩ := htrans (seed surj n i) a ((seed surj n i).2.trans a.2.symm)
      refine ⟨(i,d),?_⟩
      change (⟨i, ⟨d • (seed surj n i).1, _⟩⟩ : Cell (p := p) n) = ⟨i,a⟩
      exact congrArg (Sigma.mk i) (Subtype.ext hd))

end EquivariantCoverCells

end

namespace EquivariantCoverCells
attribute [-instance] AddCommGroup.toIntModule
open Set Topology _root_.CategoryTheory CWEquivariant CWExtension CoveringCW

attribute [instance] AddCommGroup.toIntModule
end EquivariantCoverCells

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CoreDeck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CoreDeck
open Set Topology DiscreteCoverCharts
variable {ι X Q : Type} [TopologicalSpace X] [Group Q] [TopologicalSpace Q]
  [DiscreteTopology Q] (Z : FiberBundleCore ι X Q)
  (hZ : ∀ i j x a q, Z.coordChange i j x (a*q) = Z.coordChange i j x a * q)

include hZ in
theorem continuousLeftAction : @ContinuousConstSMul Q Z.TotalSpace _ (leftAction Z).toSMul := by
  let := leftAction Z
  exact ⟨fun q => continuous_right Z hZ q⁻¹⟩

end CoreDeck

namespace CoreDeck
attribute [-instance] AddCommGroup.toIntModule
open Set Topology _root_.CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [instance] AddCommGroup.toIntModule
end CoreDeck

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_BinaryPrefixOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace BinaryPrefixOperators

open FiniteIdempotentDiagrams

variable (K : Type*) [CommRing K]

lemma first_one : copy K 0 1 = 1 := by
  rw [← three_diagonal_sum, map_add, map_add, copy_diagonal, copy_diagonal, copy_diagonal]
  simp only [sources, targets, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  calc l K 0 * l K 0 * (r K 0 * r K 0) + l K 0 * l K 1 * (r K 1 * r K 0) +
      l K 1 * r K 1 = l K 0 * (l K 0 * r K 0 + l K 1 * r K 1) * r K 0 +
      l K 1 * r K 1 := by noncomm_ring
    _ = 1 := by rw [l_r_partition]; simpa using l_r_partition K

lemma first_partition : sources K 0 0 * targets K 0 0 =
    sources K 1 0 * targets K 1 0 + sources K 2 0 * targets K 2 0 := by
  simp only [sources, targets, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  calc l K 0 * l K 0 * (r K 0 * r K 0) =
      l K 0 * l K 0 * (l K 0 * r K 0 + l K 1 * r K 1) * (r K 0 * r K 0) := by
        rw [l_r_partition, mul_one]
    _ = _ := by noncomm_ring

noncomputable def threeCopies : ThreeCopies K (algebra K) where
  copy := copy K
  first_one := first_one K
  common_second i := by fin_cases i <;> simp [sources, targets]
  common_third i := by fin_cases i <;> simp [sources, targets]
  partition := by simpa only [copy_diagonal] using first_partition K
  partition_orthogonal := by simp [sources, targets, mul_assoc, r_l_mul]
  partition_orthogonal' := by simp [sources, targets, mul_assoc, r_l_mul]

noncomputable def idempotents : Set (algebra K) :=
  {E | E = 1 ∨ E * E = E ∧ ∃ (i : Fin 3) (M : Mat3 K), copy K i M = E}

lemma identity_mem : (1 : algebra K) ∈ idempotents K := Or.inl rfl

lemma idempotents_are_idempotent {E : algebra K} (hE : E ∈ idempotents K) :
    E * E = E := by
  rcases hE with rfl | hE
  · exact one_mul _
  · exact hE.1

lemma idempotents_finite [Finite K] : (idempotents K).Finite := by
  apply ((Set.finite_range fun x : Fin 3 × Mat3 K => copy K x.1 x.2).insert 1).subset
  rintro x (rfl | ⟨_, i, M, rfl⟩)
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨(i, M), rfl⟩

def AssignmentAdditive {T : Type*} [AddCommGroup T] (z : idempotents K → T) : Prop :=
  ∀ E P : idempotents K, ∀ hSum : E.val + P.val ∈ idempotents K,
    E.val * P.val = 0 → P.val * E.val = 0 →
    z ⟨E.val + P.val, hSum⟩ = z E + z P

end BinaryPrefixOperators

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ClassifyingSpacesFiniteExtensionGeometricFromProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Pointwise

namespace NoncommElementary
variable {R n : Type*} [Ring R] [Fintype n] [DecidableEq n]

@[simp] lemma root_zero (i j : n) (h : i≠j) : root i j h (0:R)=1 := by
  apply Units.ext; simp

lemma root_add (i j : n) (h : i≠j) (a b : R) :
    root i j h (a+b)=root i j h a*root i j h b := by
  apply Units.ext
  simp [add_mul,mul_add,Matrix.single_mul_single_of_ne _ _ _ _ h.symm,
    Matrix.single_add,add_comm,add_left_comm,add_assoc]

@[simp] lemma root_inv (i j : n) (h : i≠j) (a : R) :
    (root i j h a)⁻¹=root i j h (-a) := by apply Units.ext; rfl

def elementary : Subgroup (Matrix n n R)ˣ :=
  Subgroup.closure {g | ∃ (i j : n) (h : i≠j) (a : R), g=root i j h a}

lemma root_mem (i j : n) (h : i≠j) (a : R) : root i j h a∈elementary :=
  Subgroup.subset_closure ⟨i,j,h,a,rfl⟩

end NoncommElementary

open scoped commutatorElement
namespace NoncommElementary
variable {R n : Type*} [Ring R] [Fintype n] [DecidableEq n]

lemma root_commute (i j k l : n) (hij : i≠j) (hkl : k≠l)
    (hil : i≠l) (hjk : j≠k) (a b : R) :
    Commute (root i j hij a) (root k l hkl b) := by
  apply Units.ext
  change (1+Matrix.single i j a)*(1+Matrix.single k l b)=
    (1+Matrix.single k l b)*(1+Matrix.single i j a)
  simp [add_mul,mul_add,Matrix.single_mul_single_of_ne _ _ _ _ hjk,
    Matrix.single_mul_single_of_ne _ _ _ _ hil.symm,add_comm,add_left_comm]

lemma root_commutator (i j k : n) (hij : i≠j) (hjk : j≠k) (hik : i≠k)
    (a b : R) : ⁅root i j hij a,root j k hjk b⁆=root i k hik (a*b) := by
  apply Units.ext
  change ((1+Matrix.single i j a)*(1+Matrix.single j k b))*
    (1+Matrix.single i j (-a))*(1+Matrix.single j k (-b))=1+Matrix.single i k (a*b)
  simp only [add_mul,mul_add,one_mul,mul_one,Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ hij.symm,
    Matrix.single_mul_single_of_ne _ _ _ _ hjk.symm,
    Matrix.single_mul_single_of_ne _ _ _ _ hik.symm,
    mul_neg,neg_mul,add_zero]
  simp only [← Matrix.single_neg]
  abel
end NoncommElementary

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_Steinberg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace Steinberg
variable (n R : Type*) [Ring R]

variable {n R}

def matrix [Fintype n] [DecidableEq n] : Group n R →* (Matrix n n R)ˣ :=
  lift NoncommElementary.root
    (fun i j h a b => (NoncommElementary.root_add i j h a b).symm)
    NoncommElementary.root_commutator NoncommElementary.root_commute

@[simp] lemma matrix_root [Fintype n] [DecidableEq n] (i j : n) (h : i≠j) (a : R) :
    matrix (root i j h a)=NoncommElementary.root i j h a := by simpa only [matrix,root,lift] using (PresentedGroup.toGroup.of (rels:=relations n R) (x:=⟨i,j,h,a⟩) _)

lemma matrix_mem [Fintype n] [DecidableEq n] (g : Group n R) :
    matrix g∈NoncommElementary.elementary := by
  apply PresentedGroup.generated_by (relations n R)
    (NoncommElementary.elementary.comap matrix) _ g
  intro x
  change matrix (root x.i x.j x.different x.coefficient)∈NoncommElementary.elementary (R:=R) (n:=n)
  rw [matrix_root]
  exact NoncommElementary.root_mem x.i x.j x.different x.coefficient

def pi [Fintype n] [DecidableEq n] : Group n R →* NoncommElementary.elementary (R:=R) (n:=n) :=
  matrix.codRestrict _ matrix_mem

@[simp] lemma pi_coe [Fintype n] [DecidableEq n] (g : Group n R) :
    (pi g : (Matrix n n R)ˣ)=matrix g := rfl

end Steinberg

namespace Steinberg
variable {n R S : Type*} [Ring R] [Ring S]

@[simp] lemma map_id (z : Group n R) : map (NonUnitalRingHom.id R) z = z := by
  have h : map (NonUnitalRingHom.id R) = MonoidHom.id (Group n R) := by
    apply hom_ext
    intros
    rfl
  exact DFunLike.congr_fun h z

@[simp] lemma map_comp {T : Type*} [Ring T] (φ : R →ₙ+* S) (ψ : S →ₙ+* T)
    (z : Group n R) : map (ψ.comp φ) z = map ψ (map φ z) := by
  have h : map (n:=n) (ψ.comp φ) = (map ψ).comp (map φ) := by
    apply hom_ext
    intros
    simp
  exact DFunLike.congr_fun h z

def reindex {m : Type*} (f : n ↪ m) : Group n R →* Group m R :=
  lift (fun i j h a => root (f i) (f j) (f.injective.ne h) a)
    (by intros; exact root_add _ _ _ _ _)
    (by
      intro i j k hij hjk hik a b
      exact root_commutator _ _ _ _ _ (f.injective.ne hik) a b)
    (by
      intro i j k l hij hkl hil hjk a b
      exact root_commute _ _ _ _ _ _ (f.injective.ne hil) (f.injective.ne hjk) a b)

@[simp] lemma reindex_root {m : Type*} (f : n ↪ m) (i j : n) (h : i ≠ j) (a : R) :
    reindex f (root i j h a) = root (f i) (f j) (f.injective.ne h) a := by
  simp [reindex]

lemma root_commutator_reverse (i j k : n) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : R) :
    ⁅root j k hjk b, root i j hij a⁆ = root i k hik (-(a*b)) := by
  rw [root_neg, ← root_commutator i j k hij hjk hik a b,
    commutatorElement_inv]

lemma opposite_commute_of_support (i j k : n) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (a b e : R) (hbe : b*e = b) (hab : a*b = 0)
    (hea : e*a = 0) :
    Commute (root i j hij a) (root j i hij.symm b) := by
  have h₁ : Commute (root i j hij a) (root j k hjk b) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [root_commutator i j k hij hjk hik, hab, root_zero]
  have h₂ : Commute (root i j hij a) (root k i hik.symm e) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [root_commutator_reverse k i j hik.symm hij hjk.symm, hea, neg_zero, root_zero]
  have h := h₁.mul_right h₂
  have h' := (h.mul_right h₁.inv_right).mul_right h₂.inv_right
  rw [← commutatorElement_def, root_commutator j k i hjk hik.symm hij.symm,
    hbe] at h'
  exact h'

lemma roots_commute_orthogonal
    (hthree : ∀ i j : n, i ≠ j → ∃ k, i ≠ k ∧ j ≠ k)
    (φ ψ : R →ₙ+* S) (hφψ : ∀ a b, φ a * ψ b = 0)
    (hψφ : ∀ a b, ψ a * φ b = 0)
    (i j k l : n) (hij : i ≠ j) (hkl : k ≠ l) (a b : R) :
    Commute (root i j hij (φ a)) (root k l hkl (ψ b)) := by
  by_cases hjk : j = k
  · subst k
    by_cases hil : i = l
    · subst l
      obtain ⟨t, hit, hjt⟩ := hthree i j hij
      apply opposite_commute_of_support i j t hij hit hjt (φ a) (ψ b) (ψ 1)
      · rw [← map_mul, mul_one]
      · exact hφψ a b
      · exact hψφ 1 a
    · apply commutatorElement_eq_one_iff_commute.mp
      rw [root_commutator i j l hij hkl hil, hφψ, root_zero]
  · by_cases hil : i = l
    · subst l
      apply commutatorElement_eq_one_iff_commute.mp
      rw [root_commutator_reverse k i j hkl hij (Ne.symm hjk), hψφ, neg_zero, root_zero]
    · exact root_commute i j k l hij hkl hil hjk (φ a) (ψ b)

lemma commute_of_roots {H : Type*} [_root_.Group H] (f : Group n R →* H)
    (b : H) (hf : ∀ i j hij a, Commute (f (root i j hij a)) b)
    (z : Group n R) : Commute (f z) b := by
  have hz : z ∈ (Subgroup.centralizer ({b} : Set H)).comap f := by
    apply PresentedGroup.generated_by (relations n R)
    intro x
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (hf x.i x.j x.different x.coefficient).eq
  exact Subgroup.mem_centralizer_singleton_iff.mp hz

lemma maps_commute_orthogonal
    (hthree : ∀ i j : n, i ≠ j → ∃ k, i ≠ k ∧ j ≠ k)
    (φ ψ : R →ₙ+* S) (hφψ : ∀ a b, φ a * ψ b = 0)
    (hψφ : ∀ a b, ψ a * φ b = 0) (z w : Group n R) :
    Commute (map φ z) (map ψ w) := by
  apply commute_of_roots (map φ) (map ψ w) _ z
  intro i j hij a
  apply Commute.symm
  apply commute_of_roots (map ψ) (map φ (root i j hij a)) _ w
  intro k l hkl b
  simp only [map_root]
  exact (roots_commute_orthogonal hthree φ ψ hφψ hψφ i j k l hij hkl a b).symm

lemma map_orthogonalSum
    (hthree : ∀ i j : n, i ≠ j → ∃ k, i ≠ k ∧ j ≠ k)
    (φ ψ : R →ₙ+* S) (hφψ : ∀ a b, φ a * ψ b = 0)
    (hψφ : ∀ a b, ψ a * φ b = 0) (z : Group n R) :
    map (orthogonalSum φ ψ hφψ hψφ) z = map φ z * map ψ z := by
  let f : Group n R →* Group n S := {
    toFun z := map φ z * map ψ z
    map_one' := by simp
    map_mul' a b := by
      simp only [map_mul]
      exact (maps_commute_orthogonal hthree φ ψ hφψ hψφ b a).mul_mul_mul_comm _ _ }
  have hf : map (orthogonalSum φ ψ hφψ hψφ) = f := by
    apply hom_ext
    intro i j hij a
    simp [f, root_add]
  exact DFunLike.congr_fun hf z

end Steinberg

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_NonunitalCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace NonunitalCompression
variable {R S : Type*} [Ring R] [Ring S]
variable (φ : R →ₙ+* S)

@[simp] lemma unitValue_one : unitValue φ 1=1 := by simp [unitValue]

lemma unitValue_mul (x y : R) : unitValue φ (x*y)=unitValue φ x*unitValue φ y := by
  have hp : φ 1*φ 1=φ 1 := by rw [← map_mul,one_mul]
  have hl : φ 1*φ y=φ y := by rw [← map_mul,one_mul]
  have hr : φ x*φ 1=φ x := by rw [← map_mul,mul_one]
  simp only [unitValue,map_sub,map_mul]
  noncomm_ring [hp,hl,hr]

def units : Rˣ →* Sˣ where
  toFun u := {
    val := unitValue φ u.val
    inv := unitValue φ u.inv
    val_inv := by rw [← unitValue_mul,u.val_inv,unitValue_one]
    inv_val := by rw [← unitValue_mul,u.inv_val,unitValue_one] }
  map_one' := Units.ext (unitValue_one φ)
  map_mul' u v := Units.ext (unitValue_mul φ u.val v.val)

@[simp] lemma units_val (u : Rˣ) : (units φ u).val=1+φ (u.val-1) := rfl

end NonunitalCompression

namespace Steinberg

variable {n m R : Type*} [Ring R] [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
@[simp] lemma reindex_id (z : Group n R) :
    reindex (Function.Embedding.refl n) z = z := by
  have h : reindex (R:=R) (Function.Embedding.refl n) = MonoidHom.id (Group n R) := by
    apply hom_ext
    intros
    rfl
  exact DFunLike.congr_fun h z

end Steinberg

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_RingExchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace Steinberg

section
variable {R n m : Type*} [Ring R]

def diagonalAction (d : n → Rˣ) : Group n R →* Group n R :=
  lift (fun i j hij a => root i j hij ((d i).val*a*(d j).inv))
    (by intros; rw [root_add,mul_add,add_mul])
    (by
      intro i j k hij hjk hik a b
      rw [root_commutator i j k hij hjk hik]
      congr 1
      simp [mul_assoc])
    (by intros; apply root_commute <;> assumption)

@[simp] lemma diagonalAction_root (d : n → Rˣ) (i j : n) (hij : i≠j) (a : R) :
    diagonalAction d (root i j hij a)=root i j hij ((d i).val*a*(d j).inv) := lift_root _ _ _ _ _ _ _ _

end

end Steinberg

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CompressedSplittings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace CompressedSplittings
section
variable {R : Type*} [Ring R] (φ : R →ₙ+* R)

namespace Idempotent

variable {φ}

def units (E : Idempotent φ) : Rˣ →* Rˣ := NonunitalCompression.units E.coefficient

@[simp] lemma units_val (E : Idempotent φ) (u : Rˣ) :
    (E.units u).val=1+φ (u.val-1)*E.val := rfl

lemma units_mul (E F Q : Idempotent φ) (hQ : Q.val=E.val+F.val)
    (hEF : E.val*F.val=0) (u : Rˣ) : Q.units u=E.units u*F.units u := by
  apply Units.ext
  have hc : (φ (u.val-1)*E.val)*(φ (u.val-1)*F.val)=0 := by
    rw [mul_assoc,← mul_assoc E.val, E.commute (u.val-1) |>.eq,
      mul_assoc (φ (u.val-1)),hEF,mul_zero,mul_zero]
  simp only [Units.val_mul,units_val,hQ,mul_add]
  simp only [add_mul,one_mul,mul_one,hc,add_zero]
  abel

lemma units_conjugate (E F : Idempotent φ) (c : Rˣ)
    (hc : ∀ x, Commute c.val (φ x)) (hEF : c.val*E.val*c.inv=F.val) (u : Rˣ) :
    c*E.units u*c⁻¹=F.units u := by
  apply Units.ext
  change c.val*(1+φ (u.val-1)*E.val)*c.inv=1+φ (u.val-1)*F.val
  have he : c.val*(φ (u.val-1)*E.val)*c.inv=φ (u.val-1)*(c.val*E.val*c.inv) := by
    rw [← mul_assoc c.val (φ (u.val-1)),hc (u.val-1) |>.eq]
    simp [mul_assoc]
  rw [mul_add,mul_one,add_mul,c.val_inv,he,hEF]

end Idempotent

def full : Idempotent φ where
  val := φ 1
  idem := by rw [← map_mul,one_mul]
  commute x := by change φ 1*φ x=φ x*φ 1; rw [← map_mul,← map_mul,one_mul,mul_one]

lemma full_units (u : Rˣ) : (full φ).units u=NonunitalCompression.units φ u := by
  apply Units.ext
  change 1+φ (u.val-1)*φ 1=1+φ (u.val-1)
  rw [← map_mul,mul_one]

theorem swindle {A : Type*} [Group A] (q : Rˣ →* A)
    (hq : ∀ u v : Rˣ, q (u*v*u⁻¹)=q v)
    (P E₀ E₁ E₀₀ E₀₁ : Idempotent φ)
    (hsplit : P.val=E₀.val+E₁.val) (hsubsplit : E₀.val=E₀₀.val+E₀₁.val)
    (hcross : E₀.val*E₁.val=0) (hsubcross : E₀₀.val*E₀₁.val=0)
    (c₀ c₀₀ c₀₁ : Rˣ)
    (hc₀ : ∀ x, Commute c₀.val (φ x))
    (hc₀₀ : ∀ x, Commute c₀₀.val (φ x))
    (hc₀₁ : ∀ x, Commute c₀₁.val (φ x))
    (hconj₀ : c₀.val*E₀.val*c₀.inv=E₁.val)
    (hconj₀₀ : c₀₀.val*E₀₀.val*c₀₀.inv=E₁.val)
    (hconj₀₁ : c₀₁.val*E₀₁.val*c₀₁.inv=E₁.val) (u : Rˣ) : q (P.units u)=1 := by
  have h₀ : q (E₀.units u)=q (E₁.units u) := by
    rw [← E₀.units_conjugate E₁ c₀ hc₀ hconj₀ u,hq]
  have h₀₀ : q (E₀₀.units u)=q (E₁.units u) := by
    rw [← E₀₀.units_conjugate E₁ c₀₀ hc₀₀ hconj₀₀ u,hq]
  have h₀₁ : q (E₀₁.units u)=q (E₁.units u) := by
    rw [← E₀₁.units_conjugate E₁ c₀₁ hc₀₁ hconj₀₁ u,hq]
  have heq : q (E₁.units u)=q (E₁.units u)*q (E₁.units u) := by
    calc q (E₁.units u)=q (E₀.units u) := h₀.symm
         _ = q (E₀₀.units u)*q (E₀₁.units u) := by
           rw [Idempotent.units_mul E₀₀ E₀₁ E₀ hsubsplit hsubcross,map_mul]
         _ = _ := by rw [h₀₀,h₀₁]
  have h₁ : q (E₁.units u)=1 := mul_left_cancel (heq.symm.trans (mul_one _).symm)
  rw [Idempotent.units_mul E₀ E₁ P hsplit hcross,map_mul,h₀,h₁,one_mul]

end

variable {R : Type*} [Ring R] (φ : R →ₙ+* R)

namespace BinaryData
variable {φ} (D : BinaryData φ)

def projection (i : Fin 2) : Idempotent φ where
  val := D.s i*D.d i
  idem := by rw [mul_assoc,← mul_assoc (D.d i),D.ds_same,D.d_left]
  commute x := (D.s_commute i x).mul_left (D.d_commute i x)

def doubleProjection (i j : Fin 2) : Idempotent φ where
  val := (D.s i*D.s j)*(D.d j*D.d i)
  idem := by
    rw [mul_assoc,← mul_assoc (D.d j*D.d i),D.dd_ss,
      ← mul_assoc (φ 1),D.d_left]
  commute x := ((D.s_commute i x).mul_left (D.s_commute j x)).mul_left
    ((D.d_commute j x).mul_left (D.d_commute i x))

lemma split : (full φ).val=(D.projection 0).val+(D.projection 1).val := D.partition.symm

lemma subsplit : (D.projection 0).val=(D.doubleProjection 0 0).val+(D.doubleProjection 0 1).val := by
  change D.s 0*D.d 0=(D.s 0*D.s 0)*(D.d 0*D.d 0)+(D.s 0*D.s 1)*(D.d 1*D.d 0)
  calc D.s 0*D.d 0=D.s 0*φ 1*D.d 0 := by rw [D.s_right]
       _ = D.s 0*(D.s 0*D.d 0+D.s 1*D.d 1)*D.d 0 := by rw [D.partition]
       _ = _ := by noncomm_ring

lemma cross : (D.projection 0).val*(D.projection 1).val=0 := by
  change (D.s 0*D.d 0)*(D.s 1*D.d 1)=0
  rw [mul_assoc,← mul_assoc (D.d 0),D.ds_cross 0 1 (by decide),zero_mul,mul_zero]

lemma subcross : (D.doubleProjection 0 0).val*(D.doubleProjection 0 1).val=0 := by
  have hd : (D.d 0*D.d 0)*(D.s 0*D.s 1)=0 := by
    calc (D.d 0*D.d 0)*(D.s 0*D.s 1)
        = D.d 0*(D.d 0*D.s 0)*D.s 1 := by simp only [mul_assoc]
      _ = 0 := by rw [D.ds_same,D.d_right,D.ds_cross 0 1 (by decide)]
  change ((D.s 0*D.s 0)*(D.d 0*D.d 0))*((D.s 0*D.s 1)*(D.d 1*D.d 0))=0
  rw [mul_assoc,← mul_assoc (D.d 0*D.d 0),hd,zero_mul,mul_zero]

theorem annihilates (D : BinaryData φ) {A : Type*} [Group A] (q : Rˣ →* A)
    (hq : ∀ u v : Rˣ, q (u*v*u⁻¹)=q v) (u : Rˣ) :
    q (NonunitalCompression.units φ u)=1 := by
  rw [← full_units]
  exact swindle φ q hq (full φ) (D.projection 0) (D.projection 1)
    (D.doubleProjection 0 0) (D.doubleProjection 0 1) D.split D.subsplit D.cross D.subcross
    D.firstExchange.unit (D.secondExchange 0).unit (D.secondExchange 1).unit
    D.firstExchange_commutes (D.secondExchange_commutes 0) (D.secondExchange_commutes 1)
    D.firstExchange.conjugates (D.secondExchange 0).conjugates (D.secondExchange 1).conjugates u

end BinaryData
end CompressedSplittings

namespace CompressedSplittings.Idempotent
variable {R : Type*} [Ring R] {φ : R →ₙ+* R}

lemma coefficient_left (E : Idempotent φ) (a : R) :
    E.val*E.coefficient a=E.coefficient a := by
  change E.val*(φ a*E.val)=φ a*E.val
  rw [← mul_assoc,E.commute a |>.eq,mul_assoc,E.idem]

lemma coefficient_right (E : Idempotent φ) (a : R) :
    E.coefficient a*E.val=E.coefficient a := by
  change (φ a*E.val)*E.val=φ a*E.val
  rw [mul_assoc,E.idem]

lemma coefficient_orthogonal (E F : Idempotent φ) (hEF : E.val*F.val=0) (a b : R) :
    E.coefficient a * F.coefficient b=0 := by
  change (φ a*E.val)*(φ b*F.val)=0
  rw [mul_assoc,← mul_assoc E.val,E.commute b |>.eq,mul_assoc (φ b),hEF,mul_zero,mul_zero]

lemma coefficient_conjugate (E F : Idempotent φ) (u : Rˣ)
    (hc : ∀ x, Commute u.val (φ x)) (hEF : u.val*E.val*u.inv=F.val) (a : R) :
    F.coefficient a=u.val*E.coefficient a*u.inv := by
  change φ a*F.val=u.val*(φ a*E.val)*u.inv
  rw [← mul_assoc u.val (φ a),hc a |>.eq]
  simp only [mul_assoc,← hEF]

lemma steinberg_split {n : Type*} (hthree : ∀ i j : n, i≠j → ∃ k, i≠k ∧ j≠k)
    (P E F : Idempotent φ) (hP : P.val=E.val+F.val)
    (hEF : E.val*F.val=0) (hFE : F.val*E.val=0) (w : Steinberg.Group n R) :
    Steinberg.map P.coefficient w=Steinberg.map E.coefficient w*Steinberg.map F.coefficient w := by
  have he : P.coefficient = Steinberg.orthogonalSum E.coefficient F.coefficient
      (E.coefficient_orthogonal F hEF) (F.coefficient_orthogonal E hFE) := by
    ext a
    change φ a*P.val=φ a*E.val+φ a*F.val
    rw [hP,mul_add]
  rw [he,Steinberg.map_orthogonalSum hthree]

end CompressedSplittings.Idempotent

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderListChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderListChains
section

variable (G : Type*)

abbrev Chain := Simplex G →₀ ℤ

def simplexCone (a : G) (s : Simplex G) : Simplex G := (a, s.1 :: s.2)

end

end OrderListChains

end

end OAI
end


