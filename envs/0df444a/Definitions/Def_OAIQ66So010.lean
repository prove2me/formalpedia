-- Prove2me | Definitions.Def_OAIQ66So010
-- name    : OAIQ66So010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:13:32.756912+00:00
-- url     : https://prove2.me/theorems/e031b6ce-3303-4ed0-9123-563b7414eac4
-- title:
--   Definitions bundle OAIQ66So010 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 161 declarations of OpenAI's Lean: 48 definitions, 2 instances and 111 theorems. The definitions and types are `OAI.AscendingHNN.changeStableEquiv`, `OAI.AscendingHNN.changeStableHom`, `OAI.AscendingHNN.presentationEquiv`, `OAI.AscendingHNN.restoreStableHom`, `OAI.AscendingTorus.interleaveEquiv`, `OAI.BasedHorn.fill`, `OAI.BasedHorn.pairFaces`, `OAI.BasedHorn.pairFill`, `OAI.BasedHorn.product`, `OAI.BasedSimplex.Space`, `OAI.BasedSimplex.const`, `OAI.BasedSimplex.cubeEquiv`, `OAI.BasedSimplex.homotopyClass`, `OAI.BasedSimplex.loop`, `OAI.BasedSimplex.ofLoop`, `OAI.DuffyBased.homotopyClass`, `OAI.DuffyBased.loop`, `OAI.DuffyBased.ofLoop`, `OAI.DuffySimplex.cone`, `OAI.DuffySimplex.tail`, `OAI.DuffySimplex.toSimplex`, `OAI.DuffyTriangle.DoubleBoundary`, `OAI.DuffyTriangle.edge`, `OAI.DuffyTriangle.looped`, `OAI.DuffyTriangle.triangle`, `OAI.SimplexAddition.basedFace`, `OAI.SimplexBoundary.drop`, `OAI.SimplexBoundary.face`, `OAI.SimplexBoundary.faceQuot`, `OAI.SimplexBoundary.glueFaces`, `OAI.SimplexBoundary.glueHomotopies`, `OAI.SimplexDisk.diskEquiv`, `OAI.SimplexDisk.fstEquiv`, `OAI.SimplexHorn.fill`, `OAI.SimplexHorn.glue`, `OAI.SimplexHorn.quotient`, `OAI.SimplexHorn.retract`, `OAI.SimplexHorn.retraction`, `OAI.SingularSubdivision.iterate`, `OAI.SingularSubspace.Within` and 8 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `FiniteType_AffineSimplex`, `FiniteType_AscendingHNN`, `FiniteType_AscendingHNNInnerTwist`, `FiniteType_AscendingTorus`, `FiniteType_BasedHorn`, `FiniteType_DiskHEP`, `FiniteType_DuffySimplex`, `FiniteType_DuffyTriangle`, `FiniteType_LoopPath`, `FiniteType_PresentationGeometry`, `FiniteType_PresentationGeometryCellCoverExtensionAnyAttachingLiftNullhomotopic`, `FiniteType_SequentialLimit`, `FiniteType_SimplexHomotopy`, `FiniteType_SingularSphereCycle`, `FiniteType_SingularSubdivision`, `FiniteType_SingularSubdivisionIterate`, `FiniteType_SingularSubdivisionIterateApplyComm`, `FiniteType_SingularSupport`, `FiniteType_TorusAction`, `SimpleOvergroups_PrefixNames`, `SimpleOvergroups_PrefixProduct`.
--
--   **Imports.** It imports the bundles `OAIQ66So000`, `OAIQ66So001` and `OAIQ66So002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So017`, `OAIQ66So018`, `OAIQ66So019` and `OAIQ66So021`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So000
import Definitions.Def_OAIQ66So001
import Definitions.Def_OAIQ66So002

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometry
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology

noncomputable section

namespace PresentationGeometry

namespace AttachingLoops

open scoped unitInterval

@[simp] theorem vectorComplex_complexVector (z : ℂ) :
    vectorComplex (complexVector z) = z := by
  simp [complexVector, vectorComplex, Complex.re_add_im]

end AttachingLoops

end PresentationGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_AffineSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits Convexity
open scoped Simplicial
namespace SingularChains
open Set Topology _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial unitInterval

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

lemma map_comp (f : C(X,Y)) (g : C(Y,Z)) : map (g.comp f) = map f ≫ map g := by
  ext n : 1
  apply hom_ext
  intro s
  simp only [HomologicalComplex.comp_f,generator_map,generator_map_assoc,
    ContinuousMap.comp_assoc]

end SingularChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
namespace SingularSubdivision

open _root_.CategoryTheory AlgebraicTopology Limits ConvexSimplex AffineRealization
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

lemma subdiv_map (f : C(X,Y)) (n : ℕ) :
    subdiv n ≫ (SingularChains.map f).f n = (SingularChains.map f).f n ≫ subdiv n := by
  apply SingularChains.hom_ext
  intro s
  simp only [generator_subdiv_assoc,SingularChains.generator_map_assoc,generator_subdiv,
    SingularChains.map_comp,HomologicalComplex.comp_f]

end SingularSubdivision

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSupport
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

def span (P : C(Std n,X) → Prop) : Submodule ℤ ((chains X).X n) :=
  Submodule.span ℤ {x | ∃ f, P f ∧ x = gen f}

end SingularSupport

namespace ConvexSimplex

instance stdMetricSpace (n : ℕ) : MetricSpace (Std n) :=
  Topology.IsEmbedding.comapMetricSpace
    (fun point : Std n => (point.weights : Fin (n+1) → ℝ))
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1)))

end ConvexSimplex

namespace SubdivisionMesh

open Set Topology _root_.CategoryTheory ConvexSimplex AffineSupport
variable {N n : ℕ}

def iterate (N n k : ℕ) : (AffineChains.chains (Std N)).X n ⟶ (AffineChains.chains (Std N)).X n :=
  match k with
  | 0 => 𝟙 _
  | k+1 => iterate N n k ≫ AffineChains.subdiv (@center N) n

end SubdivisionMesh

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSubdivisionIterate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
namespace SingularSubdivision
open _root_.CategoryTheory AlgebraicTopology Limits ConvexSimplex AffineRealization
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def iterate (X : Type) [TopologicalSpace X] (n k : ℕ) :
    (SingularChains.chains X).X n ⟶ (SingularChains.chains X).X n :=
  match k with
  | 0 => 𝟙 _
  | k+1 => iterate X n k ≫ subdiv n

lemma realize_subdiv (N n : ℕ) :
    AffineChains.subdiv (@center N) n ≫ (realize N).f n =
      (realize N).f n ≫ subdiv n := by
  apply AffineChains.hom_ext
  intro v
  rw [generator_realize_assoc,generator_affine_subdiv]

@[reassoc] lemma realize_iterate (N n k : ℕ) :
    SubdivisionMesh.iterate N n k ≫ (realize N).f n =
      (realize N).f n ≫ iterate (Std N) n k := by
  induction k with
  | zero => simp [SubdivisionMesh.iterate,iterate]
  | succ k ih =>
    rw [SubdivisionMesh.iterate,Category.assoc,realize_subdiv,← Category.assoc,ih]
    simp only [iterate,Category.assoc]

@[reassoc] lemma iterate_map (f : C(X,Y)) (n k : ℕ) :
    iterate X n k ≫ (SingularChains.map f).f n =
      (SingularChains.map f).f n ≫ iterate Y n k := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    rw [iterate,Category.assoc,subdiv_map,← Category.assoc,ih]
    simp only [iterate,Category.assoc]

end SingularSubdivision

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSubdivisionIterateApplyComm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial

namespace SingularSupport
open Classical
open Set _root_.CategoryTheory AlgebraicTopology Limits SingularChains
variable {X : Type} [TopologicalSpace X] {n : ℕ}

def cut (P : C(Std n,X) → Prop) : (chains X).X n ⟶ (chains X).X n :=
  desc (fun f => if P f then generator f else 0)

@[simp] lemma cut_gen (P : C(Std n,X) → Prop) (f : C(Std n,X)) :
    cut P (gen f) = if P f then gen f else 0 := by
  change (generator f ≫ cut P) 1 = _
  rw [cut,generator_desc]
  split_ifs <;> rfl

end SingularSupport

namespace SingularSubspace
open Classical
open Set _root_.CategoryTheory AlgebraicTopology Limits SingularChains
variable {X : Type} [TopologicalSpace X] (A : Set X)

abbrev Within {n : ℕ} (f : C(Std n,X)) : Prop := range f ⊆ A

def liftSimplex {n : ℕ} (f : C(Std n,X)) (hf : Within A f) : C(Std n,A) :=
  ⟨fun s => ⟨f s,hf (mem_range_self s)⟩,f.continuous.subtype_mk _⟩

@[simp] lemma inclusion_lift {n : ℕ} (f : C(Std n,X)) (hf : Within A f) :
    (inclusionMap A).comp (liftSimplex A f hf) = f := rfl

lemma within_inclusion {n : ℕ} (f : C(Std n,A)) : Within A ((inclusionMap A).comp f) := by
  rintro _ ⟨s,rfl⟩
  exact (f s).2

@[simp] lemma lift_inclusion {n : ℕ} (f : C(Std n,A)) :
    liftSimplex A ((inclusionMap A).comp f) (within_inclusion A f) = f := rfl

def lift (n : ℕ) : (chains X).X n ⟶ (chains A).X n :=
  desc (fun f => if hf : Within A f then generator (liftSimplex A f hf) else 0)

@[reassoc] lemma generator_lift {n : ℕ} (f : C(Std n,X)) :
    generator f ≫ lift A n = if hf : Within A f then generator (liftSimplex A f hf) else 0 :=
  generator_desc _ _

end SingularSubspace
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryCellCoverExtensionAnyAttachingLiftNullhomotopic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Topology Metric
namespace SimplexDisk

def fstEquiv (n : ℕ) : Convexity.StdSimplex ℝ (Fin (n+1)) ≃ₜ Fat n where
  toFun s := ⟨fun i => s.weights (Fin.succ i),⟨fun i => s.weights_nonneg _,by
    have h := s.total_of_fintype
    rw [Fin.sum_univ_succ] at h
    linarith [s.weights_nonneg 0]⟩⟩
  invFun x := {
    weights := Finsupp.equivFunOnFinite.symm (Fin.cons (1-∑i, x.1 i) x.1)
    nonneg := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using sub_nonneg.mpr x.2.2
      · simpa using x.2.1 j
    total := by simp [Finsupp.sum_fintype, Fin.sum_univ_succ] }
  left_inv s := by
    apply Convexity.StdSimplex.ext
    apply Finsupp.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change 1 - ∑ j : Fin n, s.weights j.succ = s.weights 0
      have h := s.total_of_fintype
      rw [Fin.sum_univ_succ] at h
      linarith
    · rfl
  right_inv x := by apply Subtype.ext; rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact Convexity.StdSimplex.continuous_weights_apply ℝ (Fin.succ i)
  continuous_invFun := by
    apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).continuous_iff.mpr
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Continuous (fun x : Fat n => 1 - ∑ j, x.1 j)
      exact continuous_const.sub (continuous_finsetSum _
        (fun j _ => (continuous_apply j).comp continuous_subtype_val))
    · change Continuous (fun x : Fat n => x.1 j)
      exact (continuous_apply j).comp continuous_subtype_val

lemma fstEquiv_frontier {n : ℕ} (s : Convexity.StdSimplex ℝ (Fin (n+1))) (j : Fin (n+1))
    (hj : s.weights j = 0) : (fstEquiv n s).1 ∈ frontier (Fat n) := by
  rw [mem_frontier_iff_notMem_interior (fstEquiv n s).2]
  intro hi
  revert hj
  refine Fin.cases ?_ (fun k => ?_) j
  · intro h0
    have hs := interior_sum_lt hi
    change ∑ i : Fin n, s.weights i.succ < 1 at hs
    have hsum := s.total_of_fintype
    rw [Fin.sum_univ_succ,h0,zero_add] at hsum
    linarith
  · intro hk
    have hp := interior_pos hi k
    change 0 < s.weights k.succ at hp
    linarith

def diskEquiv (n : ℕ) : Convexity.StdSimplex ℝ (Fin (n+1)) ≃ₜ closedBall (0 : Fin n → ℝ) 1 :=
  (fstEquiv n).trans (((ambient n).image (Fat n)).trans (Homeomorph.setCongr (ambient_image n)))

@[simp] lemma diskEquiv_val (n : ℕ) (s : Convexity.StdSimplex ℝ (Fin (n+1))) :
    (diskEquiv n s).1 = ambient n (fstEquiv n s).1 := rfl

lemma diskEquiv_boundary {n : ℕ} (s : Convexity.StdSimplex ℝ (Fin (n+1))) (j : Fin (n+1))
    (hj : s.weights j = 0) : ‖(diskEquiv n s).1‖ = 1 := by
  have h : (diskEquiv n s).1 ∈ sphere (0 : Fin n → ℝ) 1 := by
    rw [diskEquiv_val,← ambient_frontier]
    exact ⟨_,fstEquiv_frontier s j hj,rfl⟩
  simpa only [mem_sphere,dist_zero_right] using h

lemma interior_of_pos {n : ℕ} {x : Fin n → ℝ}
    (hp : ∀ i, 0 < x i) (hs : ∑ i, x i < 1) : x ∈ interior (Fat n) := by
  let O : Set (Fin n → ℝ) := {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}
  have hO : IsOpen O := by
    have h : O = (⋂ i, {x : Fin n → ℝ | 0 < x i}) ∩ {x | ∑ i, x i < 1} := by
      ext x; simp [O]
    rw [h]
    exact (isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous_apply i))).inter
      (isOpen_lt (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const)
  exact hO.subset_interior_iff.mpr (show O ⊆ Fat n from fun x hx => ⟨fun i => (hx.1 i).le,hx.2.le⟩) ⟨hp,hs⟩

lemma diskEquiv_boundary_iff {n : ℕ} (s : Convexity.StdSimplex ℝ (Fin (n+1))) :
    ‖(diskEquiv n s).1‖ = 1 ↔ ∃ j, s.weights j = 0 := by
  refine ⟨fun h => ?_,fun ⟨j,hj⟩ => diskEquiv_boundary s j hj⟩
  by_contra! hne
  have hp : ∀ j, 0 < s.weights j := fun j => lt_of_le_of_ne (s.weights_nonneg j) (hne j).symm
  have hi : (fstEquiv n s).1 ∈ interior (Fat n) := by
    apply interior_of_pos
    · intro i; exact hp i.succ
    · change ∑ i : Fin n, s.weights i.succ < 1
      have hsum := s.total_of_fintype
      rw [Fin.sum_univ_succ] at hsum
      linarith [hp 0]
  have hb : (diskEquiv n s).1 ∈ sphere (0 : Fin n → ℝ) 1 := by
    simpa only [mem_sphere,dist_zero_right] using h
  rw [diskEquiv_val,← ambient_frontier] at hb
  obtain ⟨x,hx,he⟩ := hb
  have he' : x = (fstEquiv n s).1 := (ambient n).injective he
  subst x
  exact hx.2 hi

end SimplexDisk

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_DiskHEP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Topology Metric
open Set Topology Metric
open scoped unitInterval

namespace SimplexBoundary
open Set Topology Metric
open scoped unitInterval

def face {n : ℕ} (i : Fin (n+2)) : C(Simplex n, Simplex (n+1)) :=
  ⟨Convexity.StdSimplex.map i.succAbove, Convexity.StdSimplex.continuous_map ℝ _⟩

lemma face_zero {n : ℕ} (i : Fin (n+2)) (s : Simplex n) : (face i s).weights i = 0 := by
  exact Finsupp.mapDomain_of_notMem_range s.weights i (by simp)

lemma face_succAbove {n : ℕ} (i : Fin (n+2)) (s : Simplex n) (j : Fin (n+1)) :
    (face i s).weights (i.succAbove j) = s.weights j := by
  exact Finsupp.mapDomain_apply Fin.succAbove_right_injective s.weights j

def drop {n : ℕ} (i : Fin (n+2)) (s : Simplex (n+1)) (hi : s.weights i = 0) : Simplex n where
  weights := Finsupp.equivFunOnFinite.symm (fun j => s.weights (i.succAbove j))
  nonneg := by
    intro j
    exact s.weights_nonneg _
  total := by
    have hs := s.total_of_fintype
    rw [Fin.sum_univ_succAbove _ i, hi,zero_add] at hs
    simpa [Finsupp.sum_fintype] using hs

lemma face_drop {n : ℕ} (i : Fin (n+2)) (s : Simplex (n+1)) (hi : s.weights i = 0) :
    face i (drop i s hi) = s := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨k,h⟩
  · subst j
    exact (face_zero _ _).trans hi.symm
  · subst j
    exact face_succAbove i _ k

def faceQuot (n : ℕ) : C(Fin (n+2) × Simplex n, Boundary (n+1)) :=
  ⟨fun z => ⟨face z.1 z.2,⟨z.1,face_zero _ _⟩⟩,
    (continuous_prod_of_discrete_left.mpr (fun i => (face i).continuous)).subtype_mk _⟩

theorem faceQuot_surjective (n : ℕ) : Function.Surjective (faceQuot n) := by
  intro s
  obtain ⟨i,hi⟩ := s.2
  exact ⟨(i,drop i s.1 hi),Subtype.ext (face_drop i s.1 hi)⟩

theorem faceQuot_isQuotientMap (n : ℕ) : IsQuotientMap (faceQuot n) :=
  IsQuotientMap.of_surjective_continuous (faceQuot_surjective n) (faceQuot n).continuous

universe u
variable {Y : Type u} [TopologicalSpace Y]

def glueFaces {n : ℕ} (h : Fin (n+2) → C(Simplex n,Y))
    (hh : ∀ i j a b, face i a = face j b → h i a = h j b) : C(Boundary (n+1),Y) :=
  (faceQuot_isQuotientMap n).lift
    ⟨fun z => h z.1 z.2,continuous_prod_of_discrete_left.mpr (fun i => (h i).continuous)⟩
    (fun a b hab => hh a.1 b.1 a.2 b.2 (congrArg Subtype.val hab))

@[simp] theorem glueFaces_face {n : ℕ} (h : Fin (n+2) → C(Simplex n,Y))
    (hh : ∀ i j a b, face i a = face j b → h i a = h j b)
    (i : Fin (n+2)) (a : Simplex n) : glueFaces h hh (faceQuot n (i,a)) = h i a := by
  exact DFunLike.congr_fun ((faceQuot_isQuotientMap n).lift_comp
    (⟨fun z => h z.1 z.2,continuous_prod_of_discrete_left.mpr (fun i => (h i).continuous)⟩ :
      C(Fin (n+2) × Simplex n,Y))
    (fun a b hab => hh a.1 b.1 a.2 b.2 (congrArg Subtype.val hab))) (i,a)

end SimplexBoundary

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SimplexHomotopy
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

namespace SimplexBoundary
open Set Topology Metric
open scoped unitInterval

lemma face_injective {n : ℕ} (i : Fin (n+2)) : Function.Injective (face i) := by
  intro a b h
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro j
  simpa only [face_succAbove] using congrArg (fun s : Simplex (n+1) => s.weights (i.succAbove j)) h

lemma face_face {n : ℕ} (i : Fin (n+3)) (j : Fin (n+2)) (s : Simplex n) :
    face (i.succAbove j) (face (j.predAbove i) s) = face i (face j s) := by
  change Convexity.StdSimplex.map (i.succAbove j).succAbove (Convexity.StdSimplex.map (j.predAbove i).succAbove s) =
    Convexity.StdSimplex.map i.succAbove (Convexity.StdSimplex.map j.succAbove s)
  rw [Convexity.StdSimplex.map_map, Convexity.StdSimplex.map_map]
  congr 1
  funext k
  exact Fin.succAbove_succAbove_succAbove_predAbove i j k

theorem face_overlap {n : ℕ} {i j : Fin (n+3)} (hij : i ≠ j)
    {a b : Simplex (n+1)} (h : face i a = face j b) :
    ∃ (k : Fin (n+2)) (s : Simplex n), j = i.succAbove k ∧
      a = face k s ∧ b = face (k.predAbove i) s := by
  obtain ⟨k,hk⟩ : ∃ k, j = i.succAbove k := by
    rcases Fin.eq_self_or_eq_succAbove i j with h' | h'
    · exact False.elim (hij h'.symm)
    · exact h'
  subst j
  have ha : a.weights k = 0 := by
    have he := congrArg (fun s : Simplex (n+2) => s.weights (i.succAbove k)) h
    simpa only [face_succAbove,face_zero] using he
  let s := drop k a ha
  have has : face k s = a := face_drop _ _ _
  refine ⟨k,s,rfl,has.symm,?_⟩
  apply (face_injective (i.succAbove k))
  rw [face_face,has]
  exact h.symm

universe u
variable {Y : Type u} [TopologicalSpace Y]

def glueHomotopies {n : ℕ} (h : Fin (n+2) → C(I × Simplex n,Y))
    (hh : ∀ t i j a b, face i a = face j b → h i (t,a) = h j (t,b)) :
    C(I × Boundary (n+1),Y) :=
  let h' : Fin (n+2) → C(Simplex n,C(I,Y)) := fun i => ((h i).comp ⟨Prod.swap,continuous_swap⟩).curry
  let b := glueFaces h' (by
    intro i j a b hab
    apply ContinuousMap.ext
    intro t
    exact hh t i j a b hab)
  b.uncurry.comp ⟨Prod.swap,continuous_swap⟩

@[simp] theorem glueHomotopies_face {n : ℕ} (h : Fin (n+2) → C(I × Simplex n,Y))
    (hh : ∀ t i j a b, face i a = face j b → h i (t,a) = h j (t,b))
    (i : Fin (n+2)) (a : Simplex n) (t : I) :
    glueHomotopies h hh (t,faceQuot n (i,a)) = h i (t,a) := by
  unfold glueHomotopies
  dsimp only [ContinuousMap.comp_apply,ContinuousMap.coe_mk,Prod.swap,ContinuousMap.uncurry,Function.uncurry]
  rw [glueFaces_face]
  rfl

end SimplexBoundary

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSphereCycle
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

namespace BasedSimplex
open Set Topology Metric
open scoped unitInterval
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ} {x : X}

def Space (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X) :=
  {f : C(Std n,X) // ∀ s ∈ Boundary n, f s = x}

instance instFunLikeSpaceStd : FunLike (Space n X x) (Std n) X where
  coe f := f.1
  coe_injective := fun _ _ h => Subtype.ext (ContinuousMap.ext (congrFun h))

@[ext] theorem ext {f g : Space n X x} (h : ∀ s, f s = g s) : f = g :=
  DFunLike.ext _ _ h

def cubeEquiv (n : ℕ) : (Fin n → I) ≃ₜ Std n :=
  (CubeDisk.homeomorph n).trans (SimplexDisk.diskEquiv n).symm

lemma cubeEquiv_boundary {n : ℕ} (v : Fin n → I) :
    cubeEquiv n v ∈ Boundary n ↔ v ∈ Cube.boundary (Fin n) := by
  change (∃ j, (cubeEquiv n v).weights j = 0) ↔ _
  rw [← SimplexDisk.diskEquiv_boundary_iff]
  change ‖(SimplexDisk.diskEquiv n ((SimplexDisk.diskEquiv n).symm (CubeDisk.toDisk n v))).1‖ = 1 ↔ _
  rw [Homeomorph.apply_symm_apply]
  exact ⟨fun h => by simpa only [CubeDisk.toCube_toDisk] using
    CubeDisk.boundary_of_norm_eq_one (CubeDisk.toDisk n v) h,
    CubeDisk.norm_eq_one_of_boundary v⟩

def loop (f : Space n X x) : GenLoop (Fin n) X x :=
  ⟨f.1.comp ⟨cubeEquiv n,(cubeEquiv n).continuous⟩,
    fun v hv => f.2 _ ((cubeEquiv_boundary v).mpr hv)⟩

def ofLoop (f : GenLoop (Fin n) X x) : Space n X x :=
  ⟨f.1.comp ⟨(cubeEquiv n).symm,(cubeEquiv n).symm.continuous⟩,
    fun s hs => f.2 _ ((cubeEquiv_boundary _).mp (by change cubeEquiv n ((cubeEquiv n).symm s) ∈ Boundary n; simpa only [Homeomorph.apply_symm_apply] using hs))⟩

@[simp] lemma loop_ofLoop (f : GenLoop (Fin n) X x) : loop (ofLoop f) = f := by
  ext v
  change f ((cubeEquiv n).symm (cubeEquiv n v)) = f v
  rw [Homeomorph.symm_apply_apply]

@[simp] lemma ofLoop_loop (f : Space n X x) : ofLoop (loop f) = f := by
  ext v
  change f (cubeEquiv n ((cubeEquiv n).symm v)) = f v
  rw [Homeomorph.apply_symm_apply]

def homotopyClass (f : Space n X x) : HomotopyGroup (Fin n) X x := ⟦loop f⟧

def const (n : ℕ) (x : X) : Space n X x := ⟨ContinuousMap.const _ x,fun _ _ => rfl⟩

@[simp] lemma loop_const (n : ℕ) (x : X) : loop (const n x) = GenLoop.const := rfl

lemma class_homotopic {f g : Space n X x} (H : f.1.HomotopyRel g.1 (Boundary n)) :
    homotopyClass f = homotopyClass g := by
  apply Quotient.sound
  refine ⟨?_⟩
  refine
  { toHomotopy :=
    { toFun := fun z => H (z.1,cubeEquiv n z.2)
      continuous_toFun := H.continuous.comp
        (continuous_fst.prodMk ((cubeEquiv n).continuous.comp continuous_snd))
      map_zero_left := fun z => H.apply_zero _
      map_one_left := fun z => H.apply_one _ },
    prop' := ?_ }
  intro t s hs
  exact H.eq_fst t ((cubeEquiv_boundary s).mpr hs)

end BasedSimplex

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_DuffySimplex
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
namespace DuffySimplex

def cone {n : ℕ} (t : I) (s : Std n) : Std (n+1) where
  weights := Finsupp.equivFunOnFinite.symm (Fin.cons (t:ℝ) (fun i => (1-t:ℝ)*s.weights i))
  nonneg := by
    intro i
    induction i using Fin.cases with
    | zero => exact t.2.1
    | succ i => exact mul_nonneg (sub_nonneg.mpr t.2.2) (s.weights_nonneg i)
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change ∑ i : Fin (n+2), Fin.cons (t:ℝ) (fun i => (1-t:ℝ)*s.weights i) i = 1
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,← Finset.mul_sum,s.total_of_fintype,mul_one]
    ring

@[simp] lemma cone_zero {n : ℕ} (t : I) (s : Std n) : (cone t s).weights 0 = t := rfl
@[simp] lemma cone_succ {n : ℕ} (t : I) (s : Std n) (i : Fin (n+1)) :
    (cone t s).weights i.succ = (1-t:ℝ)*s.weights i := rfl

lemma continuous_cone (n : ℕ) : Continuous (fun z : I × Std n => cone z.1 z.2) := by
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+2))).continuous_iff.mpr
  apply continuous_pi
  intro i
  induction i using Fin.cases with
  | zero => exact continuous_subtype_val.comp continuous_fst
  | succ i =>
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((Convexity.StdSimplex.continuous_weights_apply ℝ i).comp continuous_snd)

def toSimplex : ∀ n, C((Fin n → I),Std n)
  | 0 => ContinuousMap.const _ (Convexity.StdSimplex.single (0 : Fin 1))
  | n+1 => ⟨fun t => cone (t 0) (toSimplex n (fun i => t i.succ)),
      by
        have h : Continuous (fun t : Fin (n+1) → I =>
            (t 0,toSimplex n (fun i => t i.succ))) :=
          (continuous_apply 0).prodMk ((toSimplex n).continuous.comp
            (continuous_pi (fun i => continuous_apply i.succ)))
        exact (continuous_cone n).comp h⟩

@[simp] lemma toSimplex_succ_zero (n : ℕ) (t : Fin (n+1) → I) :
    (toSimplex (n+1) t).weights 0 = t 0 := rfl
@[simp] lemma toSimplex_succ_succ (n : ℕ) (t : Fin (n+1) → I) (i : Fin (n+1)) :
    (toSimplex (n+1) t).weights i.succ =
      (1-t 0:ℝ)*(toSimplex n (fun j => t j.succ)).weights i := rfl

lemma simplex_coordinate_le_one {n : ℕ} (s : Std n) (i : Fin (n+1)) : s.weights i ≤ 1 := by
  have h := Finset.single_le_sum (fun j _ => s.weights_nonneg j) (Finset.mem_univ i)
  rwa [s.total_of_fintype] at h

lemma tail_sum {n : ℕ} (s : Std (n+1)) : ∑ i : Fin (n+1), s.weights i.succ = 1-s.weights 0 := by
  have h := s.total_of_fintype
  rw [Fin.sum_univ_succ] at h
  linarith

def tail {n : ℕ} (s : Std (n+1)) (h : s.weights 0 ≠ 1) : Std n where
  weights := Finsupp.equivFunOnFinite.symm (fun i => s.weights i.succ/(1-s.weights 0))
  nonneg := by
    intro i
    exact div_nonneg (s.weights_nonneg _) (sub_nonneg.mpr (simplex_coordinate_le_one s 0))
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change ∑ i : Fin (n+1), s.weights i.succ/(1-s.weights 0) = 1
    rw [← Finset.sum_div,tail_sum,div_self (sub_ne_zero.mpr (Ne.symm h))]

lemma cone_tail {n : ℕ} (s : Std (n+1)) (h : s.weights 0 ≠ 1) :
    cone ⟨s.weights 0,s.weights_nonneg 0,simplex_coordinate_le_one s 0⟩ (tail s h) = s := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  induction i using Fin.cases with
  | zero => rfl
  | succ i =>
    change (1-s.weights 0)*(s.weights i.succ/(1-s.weights 0)) = s.weights i.succ
    exact mul_div_cancel₀ _ (sub_ne_zero.mpr (Ne.symm h))

lemma coordinate_zero_of_head_one {n : ℕ} (s : Std (n+1)) (h : s.weights 0 = 1)
    (i : Fin (n+1)) : s.weights i.succ = 0 := by
  have ht := tail_sum s
  rw [h,sub_self] at ht
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => s.weights_nonneg j.succ)).mp ht i (Finset.mem_univ i)

lemma cone_one {n : ℕ} (s : Std (n+1)) (h : s.weights 0 = 1) (v : Std n) :
    cone 1 v = s := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  induction i using Fin.cases with
  | zero => exact h.symm
  | succ i => simp [coordinate_zero_of_head_one s h i]

lemma surjective (n : ℕ) : Function.Surjective (toSimplex n) := by
  induction n with
  | zero =>
    intro s
    exact ⟨Fin.elim0,@Subsingleton.elim _ (inferInstanceAs (Subsingleton (Convexity.StdSimplex ℝ (Fin 1)))) _ _⟩
  | succ n ih =>
    intro s
    by_cases h : s.weights 0 = 1
    · refine ⟨Fin.cons 1 (fun _ => 0),?_⟩
      exact cone_one s h _
    · obtain ⟨v,hv⟩ := ih (tail s h)
      refine ⟨Fin.cons ⟨s.weights 0,s.weights_nonneg _,simplex_coordinate_le_one s 0⟩ v,?_⟩
      change cone _ (toSimplex n v) = s
      rw [hv]
      exact cone_tail s h

lemma isQuotientMap (n : ℕ) : IsQuotientMap (toSimplex n) :=
  IsQuotientMap.of_surjective_continuous (surjective n) (toSimplex n).continuous

lemma boundary_iff : ∀ n (t : Fin n → I),
    (∃ i, (toSimplex n t).weights i = 0) ↔ t ∈ Cube.boundary (Fin n)
  | 0, t => by simp [toSimplex,Cube.boundary]
  | n+1, t => by
    constructor
    · rintro ⟨i,hi⟩
      induction i using Fin.cases with
      | zero => exact ⟨0,Or.inl (Subtype.ext hi)⟩
      | succ i =>
        rw [toSimplex_succ_succ,mul_eq_zero] at hi
        rcases hi with h | h
        · exact ⟨0,Or.inr (Subtype.ext (sub_eq_zero.mp h).symm)⟩
        · obtain ⟨j,hj⟩ := (boundary_iff n (fun j => t j.succ)).mp ⟨i,h⟩
          exact ⟨j.succ,hj⟩
    · rintro ⟨i,hi⟩
      induction i using Fin.cases with
      | zero =>
        rcases hi with h | h
        · exact ⟨0,by simp [h]⟩
        · refine ⟨(0 : Fin (n+1)).succ,?_⟩
          rw [toSimplex_succ_succ,h]
          simp
      | succ i =>
        obtain ⟨j,hj⟩ := (boundary_iff n (fun j => t j.succ)).mpr ⟨i,hi⟩
        exact ⟨j.succ,by simp [hj]⟩

lemma injective_off_boundary : ∀ n {v w : Fin n → I},
    toSimplex n v = toSimplex n w → v ∉ Cube.boundary (Fin n) → v = w
  | 0, v, w, h, hv => Subsingleton.elim _ _
  | n+1, v, w, h, hv => by
    have h₀ : v 0 = w 0 := Subtype.ext (congrArg (fun s : Std (n+1) => s.weights 0) h)
    have hneq : (1-v 0:ℝ) ≠ 0 := by
      intro hz
      apply hv
      exact ⟨0,Or.inr (Subtype.ext (sub_eq_zero.mp hz).symm)⟩
    have htail : toSimplex n (fun i => v i.succ) = toSimplex n (fun i => w i.succ) := by
      apply Convexity.StdSimplex.ext
      apply Finsupp.ext
      intro i
      have hi := congrArg (fun s : Std (n+1) => s.weights i.succ) h
      simp only [toSimplex_succ_succ,← h₀] at hi
      exact mul_left_cancel₀ hneq hi
    have hv' : (fun i => v i.succ) ∉ Cube.boundary (Fin n) := by
      rintro ⟨i,hi⟩
      exact hv ⟨i.succ,hi⟩
    have hh := injective_off_boundary n htail hv'
    funext i
    induction i using Fin.cases with
    | zero => exact h₀
    | succ i => exact congrFun hh i

end DuffySimplex

namespace DuffyBased
open DuffySimplex
open Set Topology
open scoped unitInterval
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ} {x : X}

def loop (f : BasedSimplex.Space n X x) : GenLoop (Fin n) X x :=
  ⟨f.1.comp (toSimplex n),fun v hv => f.2 _ ((boundary_iff n v).mpr hv)⟩

lemma loop_fiber (p : GenLoop (Fin n) X x) {v w : Fin n → I}
    (h : toSimplex n v = toSimplex n w) : p v = p w := by
  by_cases hv : v ∈ Cube.boundary (Fin n)
  · have hw : w ∈ Cube.boundary (Fin n) :=
      (boundary_iff n w).mp (h ▸ (boundary_iff n v).mpr hv)
    exact (p.2 v hv).trans (p.2 w hw).symm
  · exact congrArg p (injective_off_boundary n h hv)

def ofLoop (p : GenLoop (Fin n) X x) : BasedSimplex.Space n X x :=
  ⟨(isQuotientMap n).lift p.1 (fun _ _ h => loop_fiber p h),by
    intro s hs
    obtain ⟨t,rfl⟩ := surjective n s
    have he := DFunLike.congr_fun ((isQuotientMap n).lift_comp p.1
      (fun _ _ h => loop_fiber p h)) t
    exact he.trans (p.2 t ((boundary_iff n t).mp hs))⟩

@[simp] theorem ofLoop_apply (p : GenLoop (Fin n) X x) (v : Fin n → I) :
    ofLoop p (toSimplex n v) = p v :=
  DFunLike.congr_fun ((isQuotientMap n).lift_comp p.1 (fun _ _ h => loop_fiber p h)) v

@[simp] theorem loop_ofLoop (p : GenLoop (Fin n) X x) : loop (ofLoop p) = p := by
  ext v
  exact ofLoop_apply p v

@[simp] theorem ofLoop_loop (f : BasedSimplex.Space n X x) : ofLoop (loop f) = f := by
  ext s
  obtain ⟨v,rfl⟩ := surjective n s
  exact ofLoop_apply (loop f) v

def homotopyClass (f : BasedSimplex.Space n X x) : HomotopyGroup.Pi n X x :=
  Quotient.mk _ (loop f)

end DuffyBased

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_DuffyTriangle
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
namespace DuffyTriangle
open Set Topology
open scoped unitInterval
open DuffySimplex SimplexBoundary

lemma cone_face {n : ℕ} (t : I) (i : Fin (n+2)) (s : Std n) :
    cone t (face i s) = face i.succ (cone t s) := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro coordinate
  rcases Fin.eq_self_or_eq_succAbove i.succ coordinate with rfl | ⟨k,rfl⟩
  · rw [cone_succ,face_zero,face_zero,mul_zero]
  · rw [face_succAbove]
    induction k using Fin.cases with
    | zero => rw [Fin.succ_succAbove_zero,cone_zero,cone_zero]
    | succ k => rw [Fin.succ_succAbove_succ,cone_succ,face_succAbove,cone_succ]

def edge : ∀ n, C((Fin n → I) × Std 1,Std (n+1))
  | 0 => ⟨Prod.snd,continuous_snd⟩
  | n+1 => ⟨fun z => cone (z.1 0) (edge n ((fun i => z.1 i.succ),z.2)),by
      have h : Continuous (fun z : (Fin (n+1) → I) × Std 1 =>
          (z.1 0,edge n ((fun i => z.1 i.succ),z.2))) :=
        ((continuous_apply 0).comp continuous_fst).prodMk
          ((edge n).continuous.comp ((continuous_pi (fun i =>
            (continuous_apply i.succ).comp continuous_fst)).prodMk continuous_snd))
      exact (continuous_cone (n+1)).comp h⟩

def triangle : ∀ n, C((Fin n → I) × Std 2,Std (n+2))
  | 0 => ⟨Prod.snd,continuous_snd⟩
  | n+1 => ⟨fun z => cone (z.1 0) (triangle n ((fun i => z.1 i.succ),z.2)),by
      have h : Continuous (fun z : (Fin (n+1) → I) × Std 2 =>
          (z.1 0,triangle n ((fun i => z.1 i.succ),z.2))) :=
        ((continuous_apply 0).comp continuous_fst).prodMk
          ((triangle n).continuous.comp ((continuous_pi (fun i =>
            (continuous_apply i.succ).comp continuous_fst)).prodMk continuous_snd))
      exact (continuous_cone (n+2)).comp h⟩

lemma triangle_face : ∀ n (t : Fin n → I) (i : Fin 3) (s : Std 1),
    triangle n (t,face i s) = face (lastFace n i) (edge n (t,s))
  | 0,t,i,s => rfl
  | n+1,t,i,s => by
    change cone (t 0) (triangle n ((fun j => t j.succ),face i s)) =
      face (lastFace n i).succ (cone (t 0) (edge n ((fun j => t j.succ),s)))
    rw [triangle_face,cone_face]

lemma edge_cube : ∀ n (t : Fin n → I) (a : I),
    edge n (t,toSimplex 1 (fun _ => a)) = toSimplex (n+1) (Fin.snoc t a)
  | 0,t,a => rfl
  | n+1,t,a => by
    change cone (t 0) (edge n ((fun i => t i.succ),toSimplex 1 (fun _ => a))) =
      cone ((Fin.snoc t a : Fin (n+2) → I) 0) (toSimplex (n+1) (fun i => (Fin.snoc t a : Fin (n+2) → I) i.succ))
    rw [edge_cube,Fin.snoc_apply_zero]
    congr 2
    have ht : t = Fin.cons (t 0) (fun i => t i.succ) := (Fin.cons_self_tail t).symm
    rw [ht,← Fin.cons_snoc_eq_snoc_cons]
    rfl

def DoubleBoundary (n : ℕ) : Set (Std n) := {s | ∃ i j, i ≠ j ∧ s.1 i = 0 ∧ s.1 j = 0}

lemma doubleBoundary_cone {n : ℕ} (t : I) (s : Std n) (hs : s ∈ DoubleBoundary n) :
    cone t s ∈ DoubleBoundary (n+1) := by
  obtain ⟨i,j,hij,hi,hj⟩ := hs
  exact ⟨i.succ,j.succ,fun h => hij (Fin.succ_inj.mp h),by simp [hi],by simp [hj]⟩

lemma doubleBoundary_cone_one {n : ℕ} (s : Std (n+1)) : cone 1 s ∈ DoubleBoundary (n+2) := by
  refine ⟨(0 : Fin (n+2)).succ,(1 : Fin (n+2)).succ,?_,?_,?_⟩
  · intro h
    have hh := Fin.succ_inj.mp h
    have hh' := congrArg Fin.val hh
    simp only [Fin.val_zero,Fin.val_one] at hh'
    omega
  · rw [cone_succ]; simp
  · rw [cone_succ]; simp

universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

lemma triangle_boundary : ∀ n (F : C(Std (n+2),X))
    (_ : ∀ s ∈ DoubleBoundary (n+2), F s = x)
    (_ : ∀ i : Fin (n+3), i.val < n → F.comp (face i) = ContinuousMap.const _ x)
    (t : Fin n → I), t ∈ Cube.boundary (Fin n) → ∀ s, F (triangle n (t,s)) = x
  | 0,F,h₂,he,t,ht,s => by obtain ⟨i,_⟩ := ht; exact Fin.elim0 i
  | n+1,F,h₂,he,t,ht,s => by
    obtain ⟨i,hi⟩ := ht
    induction i using Fin.cases with
    | zero =>
      rcases hi with hi | hi
      · change F (cone (t 0) (triangle n ((fun j => t j.succ),s))) = x
        have hz : (cone (t 0) (triangle n ((fun j => t j.succ),s))).1 0 = 0 := by simp [hi]
        rw [← face_drop 0 _ hz]
        exact DFunLike.congr_fun (he 0 (by simp)) _
      · change F (cone (t 0) (triangle n ((fun j => t j.succ),s))) = x
        rw [hi]
        exact h₂ _ (doubleBoundary_cone_one _)
    | succ i =>
      let G : C(Std (n+2),X) := F.comp ⟨fun s => cone (t 0) s,
        (continuous_cone (n+2)).comp (continuous_const.prodMk continuous_id)⟩
      apply triangle_boundary n G
      · intro v hv
        exact h₂ _ (doubleBoundary_cone (t 0) v hv)
      · intro j hj
        ext a
        change F (cone (t 0) (face j a)) = x
        rw [cone_face]
        exact DFunLike.congr_fun (he j.succ (by simpa only [Fin.val_succ] using Nat.succ_lt_succ hj)) _
      · exact ⟨i,hi⟩

def looped (n : ℕ) (F : C(Std (n+2),X))
    (h₂ : ∀ s ∈ DoubleBoundary (n+2), F s = x)
    (he : ∀ i : Fin (n+3), i.val < n → F.comp (face i) = ContinuousMap.const _ x) :
    C(Std 2,GenLoop (Fin n) X x) :=
  let K : C(Std 2 × (Fin n → I),X) := (F.comp (triangle n)).comp ⟨Prod.swap,continuous_swap⟩
  ⟨fun s => ⟨K.curry s,fun t ht => triangle_boundary n F h₂ he t ht s⟩,
    K.curry.continuous.subtype_mk _⟩

@[simp] lemma looped_apply (n : ℕ) (F : C(Std (n+2),X))
    (h₂ : ∀ s ∈ DoubleBoundary (n+2), F s = x)
    (he : ∀ i : Fin (n+3), i.val < n → F.comp (face i) = ContinuousMap.const _ x)
    (s : Std 2) (t : Fin n → I) : looped n F h₂ he s t = F (triangle n (t,s)) := rfl

end DuffyTriangle

namespace TrianglePath
open Set Topology DuffySimplex SimplexBoundary
open scoped unitInterval

lemma duffy_one_zero : toSimplex 1 (fun _ => (0 : I)) = Convexity.StdSimplex.single 1 := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro coordinate
  fin_cases coordinate <;> norm_num [toSimplex,cone,Finsupp.single_apply]

lemma duffy_one_one : toSimplex 1 (fun _ => (1 : I)) = Convexity.StdSimplex.single 0 := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro coordinate
  fin_cases coordinate <;> norm_num [toSimplex,cone,Finsupp.single_apply]

lemma face_vertex {n : ℕ} (i : Fin (n+2)) (j : Fin (n+1)) :
    face i (Convexity.StdSimplex.single j) = Convexity.StdSimplex.single (i.succAbove j) :=
  Convexity.StdSimplex.map_single _ _

def edgePath (i : Fin 3) :
    Path (Convexity.StdSimplex.single (i.succAbove 1) : Std 2)
      (Convexity.StdSimplex.single (i.succAbove 0)) where
  toFun a := face i (toSimplex 1 (fun _ => a))
  continuous_toFun := (face i).continuous.comp ((toSimplex 1).continuous.comp
    (continuous_pi (fun _ => continuous_id)))
  source' := by rw [duffy_one_zero,face_vertex]
  target' := by rw [duffy_one_one,face_vertex]

lemma edgePath_add : ((edgePath 0).trans (edgePath 2)).Homotopic (edgePath 1) := by
  let : ContractibleSpace (closedBall (0 : Fin 2 → ℝ) 1) :=
    (convex_closedBall (0 : Fin 2 → ℝ) 1).contractibleSpace ⟨0,by simp⟩
  let : ContractibleSpace (Std 2) := (SimplexDisk.diskEquiv 2).contractibleSpace
  exact SimplyConnectedSpace.paths_homotopic _ _

universe u
variable {Y : Type u} [TopologicalSpace Y] {y : Y}

def mappedEdge (F : C(Std 2,Y)) (hF : ∀ i : Fin 3, F (Convexity.StdSimplex.single i) = y)
    (i : Fin 3) : Path y y where
  toFun a := F (edgePath i a)
  continuous_toFun := F.continuous.comp (edgePath i).continuous
  source' := (congrArg F (edgePath i).source).trans (hF _)
  target' := (congrArg F (edgePath i).target).trans (hF _)

lemma mappedEdge_add (F : C(Std 2,Y)) (hF : ∀ i : Fin 3, F (Convexity.StdSimplex.single i) = y) :
    ((mappedEdge F hF 0).trans (mappedEdge F hF 2)).Homotopic (mappedEdge F hF 1) := by
  obtain ⟨H⟩ := edgePath_add.map F
  refine ⟨{
    toHomotopy := {
      toContinuousMap := H.toContinuousMap
      map_zero_left := ?_
      map_one_left := ?_ }
    prop' := ?_ }⟩
  · intro a
    exact (H.apply_zero a).trans (congrArg (fun p => p a)
      (Path.map_trans (edgePath 0) (edgePath 2) F.continuous))
  · intro a
    exact H.apply_one a
  · intro t a ha
    exact (H.eq_fst t ha).trans (congrArg (fun p => p a)
      (Path.map_trans (edgePath 0) (edgePath 2) F.continuous))

end TrianglePath

namespace DuffyTriangle
open Set Topology DuffySimplex SimplexBoundary
open scoped unitInterval

lemma triangle_doubleBoundary : ∀ n (t : Fin n → I) (s : Std 2),
    s ∈ DoubleBoundary 2 → triangle n (t,s) ∈ DoubleBoundary (n+2)
  | 0,_,_,hs => hs
  | n+1,_,_,hs => doubleBoundary_cone _ _ (triangle_doubleBoundary n _ _ hs)

lemma vertex_doubleBoundary (i : Fin 3) : Convexity.StdSimplex.single (R := ℝ) i ∈ DoubleBoundary 2 := by
  fin_cases i
  · exact ⟨1,2,by decide,by simp,by simp⟩
  · exact ⟨0,2,by decide,by simp,by simp⟩
  · exact ⟨0,1,by decide,by simp,by simp⟩

universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

lemma looped_vertex (n : ℕ) (F : C(Std (n+2),X))
    (h₂ : ∀ s ∈ DoubleBoundary (n+2), F s = x)
    (he : ∀ i : Fin (n+3), i.val < n → F.comp (face i) = ContinuousMap.const _ x)
    (i : Fin 3) : looped n F h₂ he (Convexity.StdSimplex.single i) = GenLoop.const := by
  ext t
  exact h₂ _ (triangle_doubleBoundary n t _ (vertex_doubleBoundary i))

end DuffyTriangle

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_LoopPath
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

namespace SimplexAddition
open Set Topology DuffySimplex SimplexBoundary DuffyTriangle
open scoped unitInterval
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}

def basedFace (F : C(Std (n+2),X)) (h₂ : ∀ s ∈ DoubleBoundary (n+2), F s = x)
    (i : Fin (n+3)) : BasedSimplex.Space (n+1) X x :=
  ⟨F.comp (face i),by
    rintro s ⟨j,hj⟩
    apply h₂
    refine ⟨i,i.succAbove j,?_,face_zero i s,?_⟩
    · exact (Fin.succAbove_ne i j).symm
    · exact (face_succAbove i s j).trans hj⟩

lemma loop_face (F : C(Std (n+2),X)) (h₂ : ∀ s ∈ DoubleBoundary (n+2), F s = x)
    (he : ∀ i : Fin (n+3), i.val < n → F.comp (face i) = ContinuousMap.const _ x)
    (i : Fin 3) : DuffyBased.loop (basedFace F h₂ (lastFace n i)) =
      LoopPath.fromPath (TrianglePath.mappedEdge (looped n F h₂ he) (looped_vertex n F h₂ he) i) := by
  ext t
  change F (face (lastFace n i) (toSimplex (n+1) t)) =
    F (triangle n (Fin.init t,face i (toSimplex 1 (fun _ => t (Fin.last n)))))
  rw [triangle_face,edge_cube,Fin.snoc_init_self]

theorem three_face (F : C(Std (n+2),X)) (h₂ : ∀ s ∈ DoubleBoundary (n+2), F s = x)
    (he : ∀ i : Fin (n+3), i.val < n → F.comp (face i) = ContinuousMap.const _ x) :
    DuffyBased.homotopyClass (basedFace F h₂ (lastFace n 1)) =
      DuffyBased.homotopyClass (basedFace F h₂ (lastFace n 2)) *
        DuffyBased.homotopyClass (basedFace F h₂ (lastFace n 0)) := by
  let p := DuffyBased.loop (basedFace F h₂ (lastFace n 0))
  let q := DuffyBased.loop (basedFace F h₂ (lastFace n 2))
  have hrel : GenLoop.Homotopic (DuffyBased.loop (basedFace F h₂ (lastFace n 1)))
      (GenLoop.transAt (Fin.last n) p q) := by
    obtain ⟨H⟩ := TrianglePath.mappedEdge_add (looped n F h₂ he) (looped_vertex n F h₂ he)
    dsimp only [p,q]
    rw [loop_face F h₂ he 0,loop_face F h₂ he 1,loop_face F h₂ he 2,← LoopPath.fromPath_trans]
    exact ⟨(LoopPath.fromHomotopy H).symm⟩
  exact (Quotient.sound hrel).trans
    (HomotopyGroup.mul_spec (i := Fin.last n) (p := q) (q := p)).symm

end SimplexAddition

namespace SimplexHorn
open Set Topology
open SimplexBoundary
variable {n : ℕ}

lemma continuous_minimum (i : Fin (n+2)) : Continuous (minimum i) :=
  Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun j _ => Convexity.StdSimplex.continuous_weights_apply ℝ (i.succAbove j))

def retract (i : Fin (n+2)) (s : Std (n+1)) : Std (n+1) where
  weights := Finsupp.equivFunOnFinite.symm (fun coordinate =>
    if coordinate = i then s.1 i + (n+1:ℕ)*minimum i s else s.1 coordinate-minimum i s)
  nonneg := by
    intro coordinate
    change 0 ≤ if coordinate = i then s.1 i + (n+1:ℕ)*minimum i s
      else s.1 coordinate-minimum i s
    split_ifs with coordinate_eq
    · exact add_nonneg (s.weights_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (minimum_nonneg i s))
    · obtain ⟨other,rfl⟩ := Fin.exists_succAbove_eq coordinate_eq
      exact sub_nonneg.mpr (minimum_le i s other)
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change (∑ coordinate : Fin (n+2), if coordinate = i then s.1 i + (n+1:ℕ)*minimum i s
      else s.1 coordinate-minimum i s) = 1
    rw [Fin.sum_univ_succAbove _ i]
    simp only [ite_true,Fin.succAbove_ne,ite_false,Finset.sum_sub_distrib,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have total_eq := s.total_of_fintype
    rw [Fin.sum_univ_succAbove _ i] at total_eq
    convert total_eq using 1
    all_goals try with_reducible_and_instances rfl
    ring

@[simp] lemma retract_self (i : Fin (n+2)) (s : Std (n+1)) :
    (retract i s).1 i = s.1 i+(n+1:ℕ)*minimum i s := by simp [retract]

@[simp] lemma retract_succAbove (i : Fin (n+2)) (s : Std (n+1)) (j : Fin (n+1)) :
    (retract i s).1 (i.succAbove j) = s.1 (i.succAbove j)-minimum i s := by simp [retract]

lemma retract_mem (i : Fin (n+2)) (s : Std (n+1)) :
    ∃ j, j ≠ i ∧ (retract i s).1 j = 0 := by
  obtain ⟨j,hj⟩ := minimum_attained i s
  exact ⟨i.succAbove j,Fin.succAbove_ne _ _,by rw [retract_succAbove,hj,sub_self]⟩

@[simp] lemma retract_fix (i : Fin (n+2)) (s : Horn i) : retract i s.1 = s.1 := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro coordinate
  simp [retract,minimum_eq_zero i s]
  intro h
  rw [h]

lemma continuous_retract (i : Fin (n+2)) : Continuous (retract i) := by
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+2))).continuous_iff.mpr
  apply continuous_pi
  intro j
  change Continuous (fun s : Std (n+1) =>
    if j = i then s.1 i+(n+1:ℕ)*minimum i s else s.1 j-minimum i s)
  split_ifs with h
  · exact (Convexity.StdSimplex.continuous_weights_apply ℝ i).add
      (continuous_const.mul (continuous_minimum i))
  · exact (Convexity.StdSimplex.continuous_weights_apply ℝ j).sub (continuous_minimum i)

def retraction (i : Fin (n+2)) : C(Std (n+1),Horn i) :=
  ⟨fun s => ⟨retract i s,retract_mem i s⟩,(continuous_retract i).subtype_mk _⟩

def quotient (i : Fin (n+2)) : C(Faces i × Std n,Horn i) :=
  ⟨fun z => ⟨face z.1.1 z.2,⟨z.1.1,z.1.2,face_zero _ _⟩⟩,
    (continuous_prod_of_discrete_left.mpr (fun j => (face j.1).continuous)).subtype_mk _⟩

lemma quotient_surjective (i : Fin (n+2)) : Function.Surjective (quotient i) := by
  intro s
  obtain ⟨j,hji,hj⟩ := s.2
  exact ⟨(⟨j,hji⟩,drop j s.1 hj),Subtype.ext (face_drop j s.1 hj)⟩

lemma quotient_isQuotientMap (i : Fin (n+2)) : IsQuotientMap (quotient i) :=
  IsQuotientMap.of_surjective_continuous (quotient_surjective i) (quotient i).continuous

universe u
variable {X : Type u} [TopologicalSpace X]

def glue (i : Fin (n+2)) (f : Faces i → C(Std n,X))
    (hf : ∀ (j k : Faces i) (a b : Std n), face j.1 a = face k.1 b → f j a = f k b) : C(Horn i,X) :=
  (quotient_isQuotientMap i).lift
    ⟨fun z => f z.1 z.2,continuous_prod_of_discrete_left.mpr (fun j => (f j).continuous)⟩
    (fun a b hab => hf a.1 b.1 a.2 b.2 (congrArg Subtype.val hab))

@[simp] lemma glue_face (i : Fin (n+2)) (f : Faces i → C(Std n,X))
    (hf : ∀ (j k : Faces i) (a b : Std n), face j.1 a = face k.1 b → f j a = f k b)
    (j : Faces i) (a : Std n) : glue (n := n) (X := X) i f hf (quotient (n := n) i (j,a)) = f j a :=
  DFunLike.congr_fun ((quotient_isQuotientMap i).lift_comp
    (⟨fun z => f z.1 z.2,continuous_prod_of_discrete_left.mpr (fun j => (f j).continuous)⟩ :
      C(Faces i × Std n,X))
    (fun a b hab => hf a.1 b.1 a.2 b.2 (congrArg Subtype.val hab))) (j,a)

def fill (i : Fin (n+2)) (f : Faces i → C(Std n,X))
    (hf : ∀ (j k : Faces i) (a b : Std n), face j.1 a = face k.1 b → f j a = f k b) : C(Std (n+1),X) :=
  (glue (n := n) (X := X) i f hf).comp (retraction i)

@[simp] lemma fill_face (i : Fin (n+2)) (f : Faces i → C(Std n,X))
    (hf : ∀ (j k : Faces i) (a b : Std n), face j.1 a = face k.1 b → f j a = f k b)
    (j : Faces i) : (fill (n := n) (X := X) i f hf).comp (face j.1) = f j := by
  ext a
  have h : retraction i (face j.1 a) = quotient (n := n) i (j,a) := by
    apply Subtype.ext
    exact retract_fix i (quotient (n := n) i (j,a))
  exact (congrArg (glue (n := n) (X := X) i f hf) h).trans (glue_face i f hf j a)

end SimplexHorn

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
namespace BasedHorn
open Set Topology DuffySimplex SimplexBoundary DuffyTriangle SimplexAddition
open scoped unitInterval
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}

lemma face_compatible (i : Fin (n+3)) (f : SimplexHorn.Faces i → BasedSimplex.Space (n+1) X x) :
    ∀ (j k : SimplexHorn.Faces i) (a b : Std (n+1)),
      face j.1 a = face k.1 b → (f j).1 a = (f k).1 b := by
  intro j k a b hab
  by_cases hjk : j = k
  · subst k
    exact congrArg (f j).1 (face_injective j.1 hab)
  have hv : j.1 ≠ k.1 := fun h => hjk (Subtype.ext h)
  obtain ⟨l,s,_,rfl,rfl⟩ := face_overlap hv hab
  exact ((f j).2 _ ⟨l,face_zero l s⟩).trans ((f k).2 _ ⟨_,face_zero _ s⟩).symm

def fill (i : Fin (n+3)) (f : SimplexHorn.Faces i → BasedSimplex.Space (n+1) X x) :
    C(Std (n+2),X) := SimplexHorn.fill i (fun j => (f j).1) (face_compatible i f)

lemma fill_face (i : Fin (n+3)) (f : SimplexHorn.Faces i → BasedSimplex.Space (n+1) X x)
    (j : SimplexHorn.Faces i) : (fill i f).comp (face j.1) = (f j).1 :=
  SimplexHorn.fill_face i (fun j => (f j).1) (face_compatible i f) j

lemma fill_doubleBoundary (i : Fin (n+3)) (f : SimplexHorn.Faces i → BasedSimplex.Space (n+1) X x) :
    ∀ s ∈ DoubleBoundary (n+2), fill i f s = x := by
  rintro s ⟨j,k,hjk,hj,hk⟩
  have swap : ∀ (j k : Fin (n+3)), j ≠ k → s.1 j = 0 → s.1 k = 0 → j ≠ i → fill i f s = x := by
    intro j k hjk hj hk hji
    let a := drop j s hj
    have ha : a ∈ BasedSimplex.Boundary (n+1) := by
      obtain ⟨l,hl⟩ := Fin.exists_succAbove_eq hjk.symm
      exact ⟨l,by change s.1 (j.succAbove l) = 0; rw [hl,hk]⟩
    rw [← face_drop j s hj]
    exact (DFunLike.congr_fun (fill_face i f ⟨j,hji⟩) a).trans ((f ⟨j,hji⟩).2 a ha)
  by_cases hji : j = i
  · exact swap k j hjk.symm hk hj (by intro hki; exact hjk (hji.trans hki.symm))
  · exact swap j k hjk hj hk hji

def pairFaces (f g : BasedSimplex.Space (n+1) X x) :
    SimplexHorn.Faces (lastFace n 1) → BasedSimplex.Space (n+1) X x := fun j =>
  if j.1 = lastFace n 0 then f else if j.1 = lastFace n 2 then g else BasedSimplex.const (n+1) x

def pairFill (f g : BasedSimplex.Space (n+1) X x) : C(Std (n+2),X) :=
  fill (lastFace n 1) (pairFaces f g)

lemma pairFill_doubleBoundary (f g : BasedSimplex.Space (n+1) X x) :
    ∀ s ∈ DoubleBoundary (n+2), pairFill f g s = x := fill_doubleBoundary _ _

lemma pairFill_early (f g : BasedSimplex.Space (n+1) X x) :
    ∀ i : Fin (n+3), i.val < n → (pairFill f g).comp (face i) = ContinuousMap.const _ x := by
  intro i hi
  have hne (j : Fin 3) : i ≠ lastFace n j := by
    intro h
    have hv := congrArg Fin.val h
    rw [lastFace_val] at hv
    omega
  change (fill _ _).comp (face i) = _
  rw [fill_face _ _ ⟨i,hne 1⟩]
  simp [pairFaces,hne,BasedSimplex.const]

lemma pairFill_left (f g : BasedSimplex.Space (n+1) X x) :
    basedFace (pairFill f g) (pairFill_doubleBoundary f g) (lastFace n 0) = f := by
  apply Subtype.ext
  change (fill _ _).comp (face _) = _
  rw [fill_face _ _ ⟨lastFace n 0,fun h => by have := lastFace_injective n h; contradiction⟩]
  simp [pairFaces]

lemma pairFill_right (f g : BasedSimplex.Space (n+1) X x) :
    basedFace (pairFill f g) (pairFill_doubleBoundary f g) (lastFace n 2) = g := by
  apply Subtype.ext
  change (fill _ _).comp (face _) = _
  rw [fill_face _ _ ⟨lastFace n 2,fun h => by have := lastFace_injective n h; contradiction⟩]
  have hne : lastFace n 2 ≠ lastFace n 0 := fun h => by have := lastFace_injective n h; contradiction
  simp [pairFaces,hne]

def product (f g : BasedSimplex.Space (n+1) X x) : BasedSimplex.Space (n+1) X x :=
  basedFace (pairFill g f) (pairFill_doubleBoundary g f) (lastFace n 1)

lemma product_class (f g : BasedSimplex.Space (n+1) X x) :
    DuffyBased.homotopyClass (product f g) = DuffyBased.homotopyClass f * DuffyBased.homotopyClass g := by
  exact (three_face _ (pairFill_doubleBoundary g f) (pairFill_early g f)).trans
    (by rw [pairFill_right,pairFill_left])

end BasedHorn

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_AscendingHNN
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct
open _root_.CategoryTheory
namespace AscendingHNN
section

variable {U : Type*} [Group U] (f : U →* U) (hf : Function.Injective f)

lemma embed_mul_stable_pow (u : U) (n : ℕ) :
    embed f hf u * (stable f hf)^n =
      (stable f hf)^n * embed f hf ((f : U → U)^[n] u) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,← mul_assoc,ih,mul_assoc,embed_mul_stable,← mul_assoc,← pow_succ,
      Function.iterate_succ_apply']

lemma expand_normal (p q n : ℕ) (u : U) :
    (stable f hf)^p * embed f hf u * ((stable f hf)^q)⁻¹ =
      (stable f hf)^(p+n) * embed f hf ((f : U → U)^[n] u) *
        ((stable f hf)^(q+n))⁻¹ := by
  calc
    _ = (stable f hf)^p * (embed f hf u * (stable f hf)^n) *
        ((stable f hf)^n)⁻¹ * ((stable f hf)^q)⁻¹ := by group
    _ = _ := by rw [embed_mul_stable_pow,pow_add,pow_add]; group

theorem normal_form (j : Torus f hf) :
    ∃ p q : ℕ, ∃ u : U, j = (stable f hf)^p * embed f hf u * ((stable f hf)^q)⁻¹ := by
  induction j using HNNExtension.induction_on with
  | of u => exact ⟨0,0,u,by simp [embed]⟩
  | t => exact ⟨0,1,1,by simp [stable]⟩
  | mul x y hx hy =>
    obtain ⟨p,q,u,rfl⟩ := hx
    obtain ⟨r,s,v,rfl⟩ := hy
    refine ⟨p+r,s+q,((f : U → U)^[r] u)*((f : U → U)^[q] v),?_⟩
    conv_lhs => lhs; rw [expand_normal f hf p q r u]
    conv_lhs => rhs; rw [expand_normal f hf r s q v]
    rw [map_mul,show q+r=r+q by omega]
    group
  | inv x hx =>
    obtain ⟨p,q,u,rfl⟩ := hx
    refine ⟨q,p,u⁻¹,?_⟩
    rw [map_inv]
    group

end

open _root_.CategoryTheory

end AscendingHNN

namespace AscendingHNN

variable {U V : Type*} [Group U] [Group V]
variable (f : U →* U) (hf : Function.Injective f)

variable (i : U →* V) (t : V) (ht : ∀ u, i u*t=t*i (f u))

lemma evaluation_normal (a b : ℕ) (u : U) :
    evaluation f hf i t ht ((stable f hf)^a * embed f hf u * ((stable f hf)^b)⁻¹) =
      t^a * i u * (t^b)⁻¹ := by
  simp only [map_mul,map_inv,map_pow,evaluation_embed,evaluation_stable]

lemma evaluation_injective (hi : Function.Injective i) (β : V →* Multiplicative ℤ)
    (hβi : ∀ u, β (i u)=1) (hβt : β t=Multiplicative.ofAdd 1) :
    Function.Injective (evaluation f hf i t ht) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  obtain ⟨a,b,u,rfl⟩ := normal_form f hf g
  rw [evaluation_normal] at hg
  have hb := congrArg (fun v => Multiplicative.toAdd (β v)) hg
  simp only [map_mul,map_pow,map_inv,hβi,hβt,mul_one,map_one] at hb
  have hab : a=b := by
    simp only [toAdd_mul,toAdd_pow,
      toAdd_inv,toAdd_ofAdd,toAdd_one,
      nsmul_eq_mul,mul_one] at hb
    omega
  subst b
  have hu : u=1 := hi (by
    apply mul_left_cancel (a := t^a)
    apply mul_right_cancel (b := (t^a)⁻¹)
    simpa only [map_one,mul_one,mul_inv_cancel] using hg)
  simp [hu]

lemma evaluation_surjective
    (h : ∀ v : V, ∃ a b : ℕ, ∃ u, v=t^a*i u*(t^b)⁻¹) :
    Function.Surjective (evaluation f hf i t ht) := by
  intro v
  obtain ⟨a,b,u,rfl⟩ := h v
  exact ⟨(stable f hf)^a*embed f hf u*((stable f hf)^b)⁻¹,evaluation_normal f hf i t ht a b u⟩

end AscendingHNN

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SequentialLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace SequentialAction

open SequentialLimit

variable {U X : Type*} [Group U] [MulAction U X]
variable (f : U →* U) (s : X → X) (heq : ∀ g x, s (g • x) = f g • s x)

lemma shift_equivariant (g : Limit f) (x : Limit s) :
    shift s (act f s heq g x) = act f s heq (shiftGroup f g) (shift s x) := by
  obtain ⟨i,g,x,rfl,rfl⟩ := pair_rep f s g x
  simp only [act_of, shift_of, shiftGroup_of]

end SequentialAction

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_AscendingTorus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory MonoidalCategory _root_.Representation TensorProduct
open _root_.CategoryTheory
namespace AscendingTorus

open Monoid.Coprod Multiplicative

universe u

variable {U : Type u} [Group U]

variable {V : Type*} [Group V]

variable {P : Type*} [Group P]

def interleaveEquiv (a : U →* P) (b : P →* U) :
    Torus (b.comp a) ≃* Torus (a.comp b) where
  toFun := interleaveForward a b
  invFun := interleaveBackward a b
  left_inv x := DFunLike.congr_fun (interleaveBackward_forward a b) x
  right_inv x := DFunLike.congr_fun (interleaveForward_backward a b) x
  map_mul' := map_mul (interleaveForward a b)

end AscendingTorus

namespace AscendingHNN
variable {U : Type*} [Group U] (f : U →* U) (hf : Function.Injective f)

lemma from_to_presentation : (fromPresentation f hf).comp (toPresentation f hf)=MonoidHom.id _ := by
  apply hom_ext
  · intro u; simp
  · simp

lemma to_from_presentation : (toPresentation f hf).comp (fromPresentation f hf)=MonoidHom.id _ := by
  apply AscendingTorus.hom_ext
  · ext u; simp
  · simp

def presentationEquiv : Torus f hf ≃* AscendingTorus.Torus f where
  toFun := toPresentation f hf
  invFun := fromPresentation f hf
  left_inv g := DFunLike.congr_fun (from_to_presentation f hf) g
  right_inv g := DFunLike.congr_fun (to_from_presentation f hf) g
  map_mul' := (toPresentation f hf).map_mul

end AscendingHNN

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TorusAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
section
open scoped commutatorElement
namespace TorusAction
open SequentialLimit SequentialAction AscendingHNN
variable {U X : Type*} [Group U] [MulAction U X]
variable (f : U →* U) (hf : Function.Injective f)
variable (s : X → X) (heq : ∀ g x, s (g • x) = f g • s x)

lemma basePerm_apply (g : U) (x : Limit s) :
    basePerm f s heq g x = act f s heq (of f 0 g) x := rfl

lemma base_shift (g : U) :
    basePerm f s heq g * shift s = shift s * basePerm f s heq (f g) := by
  ext x
  have h := shift_equivariant f s heq (of f 0 (f g)) x
  simpa only [shiftGroup_of,of_succ,Equiv.Perm.mul_apply,basePerm_apply] using h.symm

lemma inverse_shift_base (g : U) :
    (shift s)⁻¹ * basePerm f s heq g = basePerm f s heq (f g) * (shift s)⁻¹ := by
  calc
    _ = (shift s)⁻¹ * (basePerm f s heq g * shift s) * (shift s)⁻¹ := by group
    _ = _ := by rw [base_shift]; group

def representation : Torus f hf →* Equiv.Perm (Limit s) :=
  HNNExtension.lift (basePerm f s heq) (shift s)⁻¹
    (fun a => inverse_shift_base f s heq a)

@[simp] lemma representation_embed (g : U) :
    representation f hf s heq (embed f hf g) = basePerm f s heq g := by
  exact HNNExtension.lift_of _ _ _ g

@[simp] lemma representation_stable :
    representation f hf s heq (stable f hf) = shift s := by
  change (HNNExtension.lift (basePerm f s heq) (shift s)⁻¹
    (fun a : (⊤ : Subgroup U) => inverse_shift_base f s heq a)) HNNExtension.t⁻¹ = _
  rw [map_inv]
  exact (congrArg Inv.inv (HNNExtension.lift_t _ _ _)).trans (inv_inv _)

end TorusAction

end

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_AscendingHNNInnerTwist
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
namespace AscendingHNN
variable {U : Type*} [Group U] (f : U →* U) (hf : Function.Injective f) (a : U)

include hf in
lemma innerTwist_injective : Function.Injective (innerTwist f a) :=
  (MulAut.conj a).injective.comp hf

lemma changed_stable_relation (u : U) :
    embed f hf u * (stable f hf * (embed f hf a)⁻¹) =
      (stable f hf * (embed f hf a)⁻¹) * embed f hf (innerTwist f a u) := by
  simp only [innerTwist_apply,map_mul,map_inv]
  rw [← mul_assoc,embed_mul_stable]
  group

def changeStableHom : Torus (innerTwist f a) (innerTwist_injective f hf a) →* Torus f hf :=
  evaluation (innerTwist f a) (innerTwist_injective f hf a)
    (embed f hf) (stable f hf * (embed f hf a)⁻¹) (changed_stable_relation f hf a)

lemma restored_stable_relation (u : U) :
    embed (innerTwist f a) (innerTwist_injective f hf a) u *
      (stable (innerTwist f a) (innerTwist_injective f hf a) *
        embed (innerTwist f a) (innerTwist_injective f hf a) a) =
    (stable (innerTwist f a) (innerTwist_injective f hf a) *
        embed (innerTwist f a) (innerTwist_injective f hf a) a) *
      embed (innerTwist f a) (innerTwist_injective f hf a) (f u) := by
  rw [← mul_assoc,embed_mul_stable]
  simp only [innerTwist_apply,map_mul,map_inv]
  group

def restoreStableHom : Torus f hf →* Torus (innerTwist f a) (innerTwist_injective f hf a) :=
  evaluation f hf (embed (innerTwist f a) (innerTwist_injective f hf a))
    (stable (innerTwist f a) (innerTwist_injective f hf a) *
      embed (innerTwist f a) (innerTwist_injective f hf a) a)
    (restored_stable_relation f hf a)

@[simp] lemma changeStableHom_embed (u : U) :
    changeStableHom f hf a (embed (innerTwist f a) (innerTwist_injective f hf a) u) =
    embed f hf u := evaluation_embed _ _ _ _ _ _

@[simp] lemma changeStableHom_stable :
    changeStableHom f hf a (stable (innerTwist f a) (innerTwist_injective f hf a)) =
    stable f hf * (embed f hf a)⁻¹ := evaluation_stable _ _ _ _ _

@[simp] lemma restoreStableHom_embed (u : U) :
    restoreStableHom f hf a (embed f hf u) =
    embed (innerTwist f a) (innerTwist_injective f hf a) u := evaluation_embed _ _ _ _ _ _

@[simp] lemma restoreStableHom_stable :
    restoreStableHom f hf a (stable f hf) =
    stable (innerTwist f a) (innerTwist_injective f hf a) *
      embed (innerTwist f a) (innerTwist_injective f hf a) a := evaluation_stable _ _ _ _ _

lemma change_restore : (changeStableHom f hf a).comp (restoreStableHom f hf a) = MonoidHom.id _ := by
  apply hom_ext
  · intro u
    simp
  · simp

lemma restore_change : (restoreStableHom f hf a).comp (changeStableHom f hf a) = MonoidHom.id _ := by
  apply hom_ext
  · intro u
    simp
  · simp

def changeStableEquiv : Torus (innerTwist f a) (innerTwist_injective f hf a) ≃* Torus f hf where
  toFun := changeStableHom f hf a
  invFun := restoreStableHom f hf a
  left_inv g := DFunLike.congr_fun (restore_change f hf a) g
  right_inv g := DFunLike.congr_fun (change_restore f hf a) g
  map_mul' := (changeStableHom f hf a).map_mul

end AscendingHNN

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_PrefixProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace BinaryPrefixOperators.Arithmetic
variable (K : Type*) [CommRing K]

noncomputable section

theorem deletion_insertion (w u : Word) :
    deletion K w * insertion K u =
      if u.take w.length = w then insertion K (u.drop w.length) else
        if w.take u.length = u then deletion K (w.drop u.length) else 0 := by
  induction w generalizing u with
  | nil => simp
  | cons i w ih =>
    cases u with
    | nil => simp
    | cons j u =>
      have hh : (deletion K w * r K i) * (l K j * insertion K u) =
          deletion K w * (r K i * l K j) * insertion K u := by simp [mul_assoc]
      rw [deletion_cons, prefix_cons, hh, r_l]
      by_cases hij : i=j
      · subst j
        simp only [List.length_cons, List.take_succ_cons,
          List.drop_succ_cons, List.cons.injEq, true_and]
        exact ih u
      · simp [hij, Ne.symm hij]

theorem deletion_insertion_cancel (w u : Word) :
    deletion K w * insertion K u = (cancel w u).elim 0 (replacement K) := by
  rw [deletion_insertion]
  unfold cancel
  split
  · simp [replacement]
  · split <;> simp [replacement]

end

end BinaryPrefixOperators.Arithmetic

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_PrefixNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace BinaryPrefixOperators.Arithmetic

namespace Lists
variable {K : Type*} [CommRing K]

variable [Primcodable K] [Finite K]

 theorem primrec_product : Primrec₂ (product (K:=K)) := by
  unfold product
  apply Primrec.list_flatMap Primrec.fst
  change Primrec (fun p : (Poly K × Poly K) × (K × Pair) => p.1.2.flatMap (mulTerm p.2))
  apply Primrec.list_flatMap (Primrec.snd.comp Primrec.fst)
  exact (primrec_mulTerm.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

end Lists
end BinaryPrefixOperators.Arithmetic

end OAI
end


