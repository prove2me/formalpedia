-- Prove2me | Definitions.Def_OAIQ66So017
-- name    : OAIQ66So017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:22:44.66936+00:00
-- url     : https://prove2.me/theorems/d2328e09-a0fc-476b-846e-0b82bc25ed2c
-- title:
--   Definitions bundle OAIQ66So017 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 217 declarations of OpenAI's Lean: 63 definitions and 154 theorems. The definitions and types are `OAI.BoundaryValue.boundary`, `OAI.BoundaryValue.value`, `OAI.CWCellular.SkeletalMap.absoluteMap`, `OAI.CWCellular.SkeletalMap.cellMap`, `OAI.CWCellular.SkeletalMap.relativeMap`, `OAI.CWCellular.absolute`, `OAI.CWCellular.cell`, `OAI.CWCellular.relative`, `OAI.CWSkeletalHomology.complex`, `OAI.CWSkeletalHomology.oneDisk`, `OAI.DiskHomology.Boundary`, `OAI.DuffyBased.cylinder`, `OAI.DuffyBased.homotopy`, `OAI.DuffyBased.homotopyOfLoop`, `OAI.DuffyHurewicz.hom`, `OAI.DuffyHurewicz.value`, `OAI.HornElimination.earlyFace`, `OAI.HornElimination.family`, `OAI.HornElimination.higher`, `OAI.HornElimination.newFaces`, `OAI.HornElimination.pivot`, `OAI.HornElimination.pivotFace`, `OAI.HornElimination.pivotFamily`, `OAI.HornElimination.replacement`, `OAI.HornElimination.replacementFace`, `OAI.HornElimination.side`, `OAI.HurewiczConstruction.canonical`, `OAI.HurewiczNormalized.cycle`, `OAI.HurewiczNormalized.cycleClassHom`, `OAI.HurewiczNormalized.homologyClass`, `OAI.RelativeChains.complex`, `OAI.RelativeChains.inclusion`, `OAI.RelativeChains.map`, `OAI.RelativeChains.pointChange`, `OAI.RelativeChains.projection`, `OAI.RelativeChains.quotientMap`, `OAI.RelativeChains.sequence`, `OAI.RelativeChains.sequenceMap`, `OAI.RotationClass.blend`, `OAI.RotationClass.permute` and 23 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `FiniteCompiler_UniformControl`, `FiniteType_BasedHorn`, `FiniteType_BoundaryValue`, `FiniteType_BoundaryValueBoundarySplit`, `FiniteType_CWCellular`, `FiniteType_ChainShortExact`, `FiniteType_DiskHEP`, `FiniteType_DiskSigmaCollar`, `FiniteType_DuffySimplex`, `FiniteType_HornElimination`, `FiniteType_QuotientComplex`, `FiniteType_RelativeChains`, `FiniteType_RelativeChainsEmptyProjectionQuasiIso`, `FiniteType_RepresentationKilling`, `FiniteType_SimplexHomotopy`, `FiniteType_SimplexRotation`, `FiniteType_SimplexSign`, `FiniteType_SingularExcision`, `FiniteType_SingularSigma`, `FiniteType_SingularSigmaSingleMerge`, `FiniteType_SingularSphereCycle`, `FiniteType_SingularSubdivision`, `FiniteType_SingularSubdivisionIterate`, `FiniteType_SingularSubdivisionIterateApplyComm`, `FiniteType_SingularSupport`, `SimpleOvergroups_PrefixProduct`.
--
--   **Imports.** It imports the bundles `OAIQ66So010`, `OAIQ66So011` and `OAIQ66So012` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So023`, `OAIQ66So024` and `OAIQ66So025`; the proof of `OAI_StageGeometry_localGroup_overgroup_of_binary_ring_data`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So010
import Definitions.Def_OAIQ66So011
import Definitions.Def_OAIQ66So012

section
-- module Solutions.OAIQ066_SO.FiniteCompiler_UniformControl
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform validation, simulation, and finite control.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open Simulator

variable {S Q Q' H C : Type*}

variable [Fintype S] [Primcodable Q]
theorem primrec_simCode : Primrec (simCode (S := S) (Q := Q)) := Primrec.of_equiv

end FiniteAlgebraicEnvelopes.Compiler.HeadCodec

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSubdivision
attribute [-instance] _root_.OAI.ConvexSimplex.stdMetricSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
namespace SingularSubdivision
section
open _root_.CategoryTheory AlgebraicTopology Limits ConvexSimplex AffineRealization

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

lemma subdiv_comm (n : ℕ) :
    subdiv (X := X) (n+1) ≫ (SingularChains.chains X).d (n+1) n =
      (SingularChains.chains X).d (n+1) n ≫ subdiv n := by
  apply SingularChains.hom_ext
  intro f
  rw [generator_subdiv_assoc, (SingularChains.map f).comm]
  rw [← Category.assoc ((realize (n+1)).f (n+1)),(realize (n+1)).comm]
  simp only [Category.assoc]
  rw [simplexChain_boundary_assoc,SingularChains.generator_boundary_assoc]
  simp only [Preadditive.sum_comp,Preadditive.zsmul_comp,generator_subdiv]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [Category.assoc]
  rw [realize_face_assoc]
  congr 2
  rw [SingularChains.map_comp,HomologicalComplex.comp_f]

def subdivision : SingularChains.chains X ⟶ SingularChains.chains X :=
  ChainComplex.ofHom subdiv subdiv_comm

end

open _root_.CategoryTheory AlgebraicTopology Limits ConvexSimplex AffineRealization
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

lemma prism_boundary (n : ℕ) :
    prism (X := X) (n+1) ≫ (SingularChains.chains X).d (n+2) (n+1) =
      𝟙 _ - subdiv (n+1) - (SingularChains.chains X).d (n+1) n ≫ prism n := by
  apply SingularChains.hom_ext
  intro f
  rw [generator_prism_assoc,(SingularChains.map f).comm]
  rw [← Category.assoc ((realize (n+1)).f (n+2)),(realize (n+1)).comm]
  simp only [Category.assoc]
  rw [prismChain_boundary_assoc]
  simp only [Preadditive.sub_comp,Preadditive.comp_sub,Category.comp_id,
    Preadditive.sum_comp,Preadditive.zsmul_comp,Category.assoc]
  rw [generator_realize_assoc,basis_affine,SingularChains.generator_map,ContinuousMap.comp_id,
    generator_subdiv,SingularChains.generator_boundary_assoc]
  simp only [Preadditive.sum_comp,Preadditive.zsmul_comp,generator_prism]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [realize_face_assoc]
  rw [SingularChains.map_comp,HomologicalComplex.comp_f]

end SingularSubdivision

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSupport
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
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

lemma gen_mem {P : C(Std n,X) → Prop} (f : C(Std n,X)) (hf : P f) : gen f ∈ span P :=
  Submodule.subset_span ⟨f,hf,rfl⟩

lemma span_mono {P Q : C(Std n,X) → Prop} (h : ∀ f, P f → Q f) : span P ≤ span Q := by
  apply Submodule.span_le.mpr
  rintro _ ⟨f,hf,rfl⟩
  exact gen_mem f (h f hf)

lemma map_mem {P : C(Std n,X) → Prop} {A : ModuleCat ℤ} {S : Submodule ℤ A}
    (g : (chains X).X n ⟶ A) (hg : ∀ f, P f → g (gen f) ∈ S)
    {c : (chains X).X n} (hc : c ∈ span P) : g c ∈ S := by
  induction hc using Submodule.span_induction with
  | mem x hx => obtain ⟨f,hf,rfl⟩ := hx; exact hg f hf
  | zero => simp
  | add x y hx hy ihx ihy => simpa using S.add_mem ihx ihy
  | smul a x hx ih => simpa using S.smul_mem a ih

end SingularSupport

namespace SmallChains
open Set _root_.CategoryTheory AlgebraicTopology Limits SingularChains
variable {X : Type} [TopologicalSpace X] {ι : Type} (U : ι → Set X)

def group (n : ℕ) : Submodule ℤ ((chains X).X n) := SingularSupport.span (Small U)

lemma gen_mem {n : ℕ} (f : C(Std n,X)) (hf : Small U f) : SingularSupport.gen f ∈ group U n :=
  SingularSupport.gen_mem f hf

lemma boundary_mem {n : ℕ} {c : (chains X).X (n+1)} (hc : c ∈ group U (n+1)) :
    (chains X).d (n+1) n c ∈ group U n := by
  apply SingularSupport.map_mem _ _ hc
  intro f hf
  rw [SingularSupport.boundary_gen]
  apply Submodule.sum_mem
  intro i _
  apply AddSubgroup.zsmul_mem (group U n).toAddSubgroup
  exact gen_mem U _ (small_comp U f hf (face i))

lemma realize_mem {n m : ℕ} (f : C(Std n,X)) (hf : Small U f)
    (c : (AffineChains.chains (Std n)).X m) :
    (map f).f m ((AffineRealization.realize n).f m c) ∈ group U m := by
  let g := (AffineRealization.realize n).f m ≫ (map f).f m
  apply AffineSupport.induction_on ((group U m).comap g.hom) _ c
  intro v
  change (AffineChains.generator v ≫ g) 1 ∈ group U m
  change (AffineChains.generator v ≫ (AffineRealization.realize n).f m ≫ (map f).f m) 1 ∈ group U m
  rw [AffineRealization.generator_realize_assoc,generator_map]
  exact gen_mem U _ (small_comp U f hf (ConvexSimplex.affine v))

lemma subdiv_mem {n : ℕ} {c : (chains X).X n} (hc : c ∈ group U n) :
    SingularSubdivision.subdiv n c ∈ group U n := by
  apply SingularSupport.map_mem _ _ hc
  intro f hf
  change (generator f ≫ SingularSubdivision.subdiv n) 1 ∈ group U n
  rw [SingularSubdivision.generator_subdiv]
  exact realize_mem U f hf (SingularSubdivision.simplexChain n 1)

lemma prism_mem {n : ℕ} {c : (chains X).X n} (hc : c ∈ group U n) :
    SingularSubdivision.prism n c ∈ group U (n+1) := by
  apply SingularSupport.map_mem _ _ hc
  intro f hf
  change (generator f ≫ SingularSubdivision.prism n) 1 ∈ group U (n+1)
  rw [SingularSubdivision.generator_prism]
  exact realize_mem U f hf (SingularSubdivision.prismChain n 1)

end SmallChains

namespace SubdivisionMesh
section
open Set Topology _root_.CategoryTheory ConvexSimplex AffineSupport
variable {N n m : ℕ}

def MeshLe (D : ℝ) (v : Fin (n+1) → Std N) : Prop := ∀ i j, dist (v i) (v j) ≤ D

def Good (v : Fin (n+1) → Std N) (D : ℝ) (w : Fin (m+1) → Std N) : Prop :=
  InHull v w ∧ MeshLe D w

lemma center_dist_hull (v : Fin (n+1) → Std N) {D : ℝ} (hD : 0 ≤ D) (hv : MeshLe D v)
    {w : Std N} (hw : (w.weights : Fin (N+1) → ℝ) ∈
      convexHull ℝ (range (fun j => ((v j).weights : Fin (N+1) → ℝ)))) :
    dist (center v) w ≤ AffineMesh.ratio n * D := by
  change dist ((center v).weights : Fin (N+1) → ℝ) w.weights ≤ _
  rw [center_coe,Finsupp.coe_smul,Finsupp.coe_finsetSum]
  exact AffineMesh.center_dist_hull (fun vertex => ((v vertex).weights : Fin (N+1) → ℝ))
    hD (fun first second => hv first second) hw

lemma good_cone (v : Fin (n+2) → Std N) (i : Fin (n+2)) {D : ℝ} (hD : 0 ≤ D)
    (hv : MeshLe D v) (w : Fin (n+1) → Std N)
    (hw : Good (v ∘ i.succAbove) (AffineMesh.ratio n * D) w) :
    Good v (AffineMesh.ratio (n+1) * D) (Fin.cons (center v) w) := by
  constructor
  · intro j
    induction j using Fin.cases with
    | zero => exact center_hull v
    | succ j => exact hull_face_subset v i (hw.1 j)
  · intro j k
    induction j using Fin.cases with
    | zero =>
      induction k using Fin.cases with
      | zero => simpa using mul_nonneg (AffineMesh.ratio_nonneg (n+1)) hD
      | succ k => exact center_dist_hull v hD hv (hull_face_subset v i (hw.1 k))
    | succ j =>
      induction k using Fin.cases with
      | zero => simpa only [Fin.cons_succ,Fin.cons_zero,dist_comm] using
          center_dist_hull v hD hv (hull_face_subset v i (hw.1 j))
      | succ k => exact (hw.2 j k).trans (mul_le_mul_of_nonneg_right
          (AffineMesh.ratio_mono (Nat.le_succ n)) hD)

theorem subdiv_mesh (n : ℕ) (v : Fin (n+1) → Std N) {D : ℝ} (hD : 0 ≤ D) (hv : MeshLe D v) :
    AffineChains.subdiv (@center N) n (gen v) ∈ span (Good v (AffineMesh.ratio n * D)) := by
  induction n with
  | zero =>
    rw [AffineChains.subdiv_zero]
    apply gen_mem
    constructor
    · exact hull_self v
    · intro i j
      have hij : i = j := by omega
      simp [hij,AffineMesh.ratio]
  | succ n ih =>
    rw [subdiv_gen]
    apply Submodule.sum_mem
    intro i _
    apply AddSubgroup.zsmul_mem (span (Good v (AffineMesh.ratio (n+1) * D))).toAddSubgroup
    apply map_mem (P := Good (v ∘ i.succAbove) (AffineMesh.ratio n * D))
      (AffineChains.cone (center v) n)
    · intro w hw
      rw [cone_gen]
      exact gen_mem _ (good_cone v i hD hv w hw)
    · exact ih (v ∘ i.succAbove) (fun j k => hv _ _)

end

open Set Topology _root_.CategoryTheory ConvexSimplex AffineSupport
variable {N n : ℕ}

lemma subdiv_mem {D : ℝ} (hD : 0 ≤ D) {c : (AffineChains.chains (Std N)).X n}
    (hc : c ∈ span (MeshLe D)) :
    AffineChains.subdiv (@center N) n c ∈ span (MeshLe (AffineMesh.ratio n * D)) := by
  apply map_mem _ _ hc
  intro v hv
  exact span_mono (fun _ h => h.2) (subdiv_mesh n v hD hv)

lemma iterate_mesh {D : ℝ} (hD : 0 ≤ D) {c : (AffineChains.chains (Std N)).X n}
    (hc : c ∈ span (MeshLe D)) (k : ℕ) :
    iterate N n k c ∈ span (MeshLe (AffineMesh.ratio n ^ k * D)) := by
  induction k with
  | zero => simpa [iterate] using hc
  | succ k ih =>
    have h := subdiv_mem (mul_nonneg (pow_nonneg (AffineMesh.ratio_nonneg _) _) hD) ih
    simpa [iterate,pow_succ,mul_assoc,mul_left_comm,mul_comm] using h

lemma basis_mesh (n : ℕ) : MeshLe 2 (AffineRealization.basis n) := by
  intro i j
  change dist ((AffineRealization.basis n i).weights : Fin (n+1) → ℝ)
    (AffineRealization.basis n j).weights ≤ 2
  apply (Metric.dist_le_diam_of_mem
    (Convexity.StdSimplex.isBounded_range_toFun_comp_weights (Fin (n+1)))
    (mem_range_self (AffineRealization.basis n i))
    (mem_range_self (AffineRealization.basis n j))).trans
  exact (Convexity.StdSimplex.diam_range_toFun_comp_weights_subset_closedBall
    (Fin (n+1))).trans (by norm_num)

end SubdivisionMesh

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSubdivisionIterate
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
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

lemma iterate_generator {n : ℕ} (f : C(Std n,X)) (k : ℕ) :
    SingularChains.generator f ≫ iterate X n k =
      AffineChains.generator (basis n) ≫ SubdivisionMesh.iterate n n k ≫
        (realize n).f n ≫ (SingularChains.map f).f n := by
  rw [realize_iterate_assoc,iterate_map]
  simp only [← Category.assoc,generator_realize,basis_affine,SingularChains.generator_map,
    ContinuousMap.comp_id]

end SingularSubdivision

namespace SmallChains
section
open Set Topology Filter _root_.CategoryTheory ConvexSimplex AffineRealization
variable {X : Type} [TopologicalSpace X] {ι : Type} (U : ι → Set X)

lemma affine_small {n m : ℕ} (f : C(Std n,X)) {δ : ℝ} {i : ι}
    (v : Fin (m+1) → Std n) (hv : SubdivisionMesh.MeshLe δ v)
    (hi : Metric.closedBall (v 0) δ ⊆ f ⁻¹' U i) : Small U (f.comp (affine v)) := by
  refine ⟨i,?_⟩
  rintro _ ⟨s,rfl⟩
  apply hi
  change dist (affine v s) (v 0) ≤ δ
  change dist ((affine v s).weights : Fin (n+1) → ℝ) (v 0).weights ≤ δ
  simp only [affine_coe,Finsupp.coe_finsetSum,Finsupp.coe_smul]
  apply AffineMesh.hull_dist _ (by simpa using hv 0 0) (fun i j => hv i j)
  · exact AffineSimplex.simplex_mem_hull _ _
  · exact subset_convexHull ℝ _ (mem_range_self 0)

def eventuallySmall (n : ℕ) : Submodule ℤ ((SingularChains.chains X).X n) where
  carrier := {c | ∀ᶠ k in atTop, SingularSubdivision.iterate X n k c ∈ group U n}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    filter_upwards [hx,hy] with k hx hy
    simpa using (group U n).add_mem hx hy
  smul_mem' := by
    intro a c hc
    filter_upwards [hc] with k hc
    simpa using (group U n).smul_mem a hc

lemma iterate_mem {n : ℕ} {c : (SingularChains.chains X).X n} (hc : c ∈ group U n) (k : ℕ) :
    SingularSubdivision.iterate X n k c ∈ group U n := by
  induction k with
  | zero => simpa [SingularSubdivision.iterate] using hc
  | succ k ih => exact subdiv_mem U ih

end

open _root_.CategoryTheory SingularChains

end SmallChains

namespace SingularSubdivision
open _root_.CategoryTheory SingularChains
variable {X : Type} [TopologicalSpace X]

lemma iterate_comm (n m k : ℕ) :
    iterate X n k ≫ (chains X).d n m = (chains X).d n m ≫ iterate X m k := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    change (iterate X n k ≫ subdivision.f n) ≫ _ = _ ≫ (iterate X m k ≫ subdivision.f m)
    rw [Category.assoc,subdivision.comm,← Category.assoc,ih,Category.assoc]

def sumPrism (X : Type) [TopologicalSpace X] (n k : ℕ) :
    (chains X).X n ⟶ (chains X).X (n+1) :=
  match k with
  | 0 => 0
  | k+1 => sumPrism X n k + iterate X n k ≫ prism n

lemma sumPrism_zero (k : ℕ) : sumPrism X 0 k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [sumPrism,ih]

lemma iterate_zero (k : ℕ) : iterate X 0 k = 𝟙 _ := by
  induction k with
  | zero => rfl
  | succ k ih => simp [iterate,ih]

lemma sumPrism_boundary (n k : ℕ) :
    sumPrism X (n+1) k ≫ (chains X).d (n+2) (n+1) = 𝟙 _ - iterate X (n+1) k -
      (chains X).d (n+1) n ≫ sumPrism X n k := by
  induction k with
  | zero => simp [sumPrism,iterate]
  | succ k ih =>
    rw [sumPrism,Preadditive.add_comp,Category.assoc,prism_boundary,ih]
    simp only [Preadditive.comp_sub,Preadditive.comp_add,Category.comp_id,iterate,
      sumPrism,← Category.assoc]
    rw [iterate_comm]
    abel

end SingularSubdivision

namespace SmallChains
open _root_.CategoryTheory SingularChains
variable {X : Type} [TopologicalSpace X] {ι : Type} (U : ι → Set X)

lemma sumPrism_mem {n : ℕ} {c : (chains X).X n} (hc : c ∈ group U n) (k : ℕ) :
    SingularSubdivision.sumPrism X n k c ∈ group U (n+1) := by
  induction k with
  | zero => exact (group U (n+1)).zero_mem
  | succ k ih =>
    apply (group U (n+1)).add_mem ih
    exact prism_mem U (iterate_mem U hc k)

end SmallChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSubdivisionIterateApplyComm
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
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

lemma cut_mem (P : C(Std n,X) → Prop) (c : (chains X).X n) : cut P c ∈ span P := by
  apply induction_on ((span P).comap (cut P).hom) _ c
  intro f
  change cut P (gen f) ∈ span P
  rw [cut_gen]
  split_ifs with hf
  · exact gen_mem f hf
  · exact Submodule.zero_mem _

lemma cut_eq {P : C(Std n,X) → Prop} {c : (chains X).X n} (hc : c ∈ span P) : cut P c = c := by
  induction hc using Submodule.span_induction with
  | mem c hc => obtain ⟨f,hf,rfl⟩ := hc; simp [hf]
  | zero => exact map_zero _
  | add c d hc hd ihc ihd => simp only [map_add,ihc,ihd]
  | smul a c hc ih =>
    simpa only [ih] using (cut P).hom.map_smul a c

end SingularSupport

namespace SingularSubspace
open Classical
open Set _root_.CategoryTheory AlgebraicTopology Limits SingularChains
variable {X : Type} [TopologicalSpace X] (A : Set X)

def group (n : ℕ) : Submodule ℤ ((chains X).X n) := SingularSupport.span (Within A)

lemma inclusion_liftChain (n : ℕ) : (map (inclusionMap A)).f n ≫ lift A n = 𝟙 _ := by
  apply SingularChains.hom_ext
  intro f
  rw [generator_map_assoc,generator_lift,dite_eq_left (within_inclusion A f),lift_inclusion,Category.comp_id]

lemma liftChain_inclusion (n : ℕ) : lift A n ≫ (map (inclusionMap A)).f n = SingularSupport.cut (Within A) := by
  apply SingularChains.hom_ext
  intro f
  rw [generator_lift_assoc]
  by_cases hf : Within A f
  · rw [dite_eq_left hf,generator_map,inclusion_lift,SingularSupport.cut,generator_desc,ite_eq_left hf]
  · rw [dite_eq_right hf,zero_comp,SingularSupport.cut,generator_desc,ite_eq_right hf]

lemma inclusion_injective (n : ℕ) : Function.Injective ((map (inclusionMap A)).f n) := by
  apply Function.HasLeftInverse.injective
  refine ⟨lift A n,?_⟩
  intro c
  exact congrArg (fun h : (chains A).X n ⟶ (chains A).X n => h c) (inclusion_liftChain A n)

lemma inclusion_mem (n : ℕ) (c : (chains A).X n) : (map (inclusionMap A)).f n c ∈ group A n := by
  apply SingularSupport.induction_on ((group A n).comap ((map (inclusionMap A)).f n).hom) _ c
  intro f
  change (map (inclusionMap A)).f n (SingularSupport.gen f) ∈ group A n
  rw [SingularSupport.map_gen]
  exact SingularSupport.gen_mem _ (within_inclusion A f)

end SingularSubspace
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_QuotientComplex
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial

namespace SingularSupport
open Classical _root_.CategoryTheory SingularChains
variable {X : Type} [TopologicalSpace X] {n : ℕ}

lemma sub_cut_mem {P Q : C(Std n,X) → Prop} {c : (chains X).X n}
    (hc : c ∈ span (fun f => P f ∨ Q f)) : c - cut P c ∈ span Q := by
  change (𝟙 ((chains X).X n) - cut P : (chains X).X n ⟶ (chains X).X n) c ∈ span Q
  apply map_mem _ _ hc
  intro f hf
  change gen f - cut P (gen f) ∈ span Q
  rw [cut_gen]
  by_cases hp : P f
  · rw [ite_eq_left hp,sub_self]; exact Submodule.zero_mem _
  · rw [ite_eq_right hp,sub_zero]; exact gen_mem f (hf.resolve_left hp)

end SingularSupport

namespace SingularSubspace
open Classical Set _root_.CategoryTheory SingularChains
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

lemma group_eq_small (A : Set X) (n : ℕ) : group A n = SmallChains.group (fun _ : Unit => A) n := by
  unfold group SmallChains.group
  congr 1
  funext f
  exact propext ⟨fun hf => ⟨(),hf⟩,fun ⟨_,hf⟩ => hf⟩

lemma boundary_mem (A : Set X) {n m : ℕ} {c : (chains X).X n} (hc : c ∈ group A n) :
    (chains X).d n m c ∈ group A m := by
  by_cases h : m+1 = n
  · subst n
    rw [group_eq_small] at hc ⊢
    exact SmallChains.boundary_mem _ hc
  · rw [(chains X).shape n m h]
    exact Submodule.zero_mem _

lemma iterate_mem (A : Set X) {n : ℕ} {c : (chains X).X n} (hc : c ∈ group A n) (k : ℕ) :
    SingularSubdivision.iterate X n k c ∈ group A n := by
  rw [group_eq_small] at hc ⊢
  exact SmallChains.iterate_mem _ hc k

lemma sumPrism_mem (A : Set X) {n : ℕ} {c : (chains X).X n} (hc : c ∈ group A n) (k : ℕ) :
    SingularSubdivision.sumPrism X n k c ∈ group A (n+1) := by
  rw [group_eq_small] at hc ⊢
  exact SmallChains.sumPrism_mem _ hc k

lemma map_mem (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : MapsTo f A B)
    {n : ℕ} {c : (chains X).X n} (hc : c ∈ group A n) : (map f).f n c ∈ group B n := by
  apply SingularSupport.map_mem _ _ hc
  intro g hg
  rw [SingularSupport.map_gen]
  apply SingularSupport.gen_mem
  rintro _ ⟨s,rfl⟩
  exact hf (hg (mem_range_self s))

lemma lift_mem (A B : Set X) {n : ℕ} {c : (chains X).X n} (hc : c ∈ group A n) :
    lift B n c ∈ group ((inclusionMap B) ⁻¹' A) n := by
  apply SingularSupport.map_mem _ _ hc
  intro f hf
  change (generator f ≫ lift B n) 1 ∈ _
  rw [generator_lift]
  split_ifs with hb
  · apply SingularSupport.gen_mem
    rintro _ ⟨s,rfl⟩
    exact hf (mem_range_self s)
  · exact Submodule.zero_mem _

lemma lift_inclusion_apply (B : Set X) {n : ℕ} {c : (chains X).X n} (hc : c ∈ group B n) :
    (map (inclusionMap B)).f n (lift B n c) = c := by
  change (lift B n ≫ (map (inclusionMap B)).f n) c = c
  rw [liftChain_inclusion]
  exact SingularSupport.cut_eq hc

lemma inclusion_lift_apply (B : Set X) {n : ℕ} (c : (chains B).X n) :
    lift B n ((map (inclusionMap B)).f n c) = c := by
  exact congrArg (fun h : (chains B).X n ⟶ (chains B).X n => h c) (inclusion_liftChain B n)

lemma inclusion_mem_iff (A B : Set X) {n : ℕ} (c : (chains B).X n) :
    (map (inclusionMap B)).f n c ∈ group A n ↔ c ∈ group ((inclusionMap B) ⁻¹' A) n := by
  constructor
  · intro hc
    simpa only [inclusion_lift_apply] using lift_mem A B hc
  · exact map_mem _ _ _ (fun _ h => h)

end SingularSubspace

namespace RelativeChains
section
open Set _root_.CategoryTheory SingularChains
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def complex (A : Set X) : ChainComplex (ModuleCat ℤ) ℕ :=
  QuotientComplex.complex (chains X) (SingularSubspace.group A)
    (fun _ _ _ hc => SingularSubspace.boundary_mem A hc)

def projection (A : Set X) : chains X ⟶ complex A :=
  QuotientComplex.projection (chains X) (SingularSubspace.group A)
    (fun _ _ _ hc => SingularSubspace.boundary_mem A hc)

lemma projection_surjective (A : Set X) (n : ℕ) : Function.Surjective ((projection A).f n) :=
  QuotientComplex.projection_surjective _ _ _ n

lemma projection_zero_iff (A : Set X) (n : ℕ) (c : (chains X).X n) :
    (projection A).f n c = 0 ↔ c ∈ SingularSubspace.group A n :=
  QuotientComplex.projection_zero_iff _ _ _ n c

@[simp] lemma differential_projection (A : Set X) (n m : ℕ) (c : (chains X).X n) :
    (complex A).d n m ((projection A).f n c) = (projection A).f m ((chains X).d n m c) := rfl

def map (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : MapsTo f A B) : complex A ⟶ complex B :=
  QuotientComplex.map _ _ (SingularChains.map f) (fun _ _ hc => SingularSubspace.map_mem A B f hf hc)

@[simp] lemma map_projection (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : MapsTo f A B)
    (n : ℕ) (c : (chains X).X n) :
    (map A B f hf).f n ((projection A).f n c) = (projection B).f n ((SingularChains.map f).f n c) := rfl

def inclusion (A B : Set X) : complex ((SingularSubspace.inclusionMap B) ⁻¹' A) ⟶ complex A :=
  map _ _ (SingularSubspace.inclusionMap B) (fun _ h => h)

end

open Set _root_.CategoryTheory SingularChains SingularSubdivision
variable {X : Type} [TopologicalSpace X]

lemma projection_eq_iff (A : Set X) (n : ℕ) (c d : (chains X).X n) :
    (projection A).f n c = (projection A).f n d ↔ c - d ∈ SingularSubspace.group A n := by
  rw [← sub_eq_zero,← map_sub,projection_zero_iff]

lemma inclusion_projection (A B : Set X) (n : ℕ) (c : (chains B).X n) :
    (inclusion A B).f n ((projection ((SingularSubspace.inclusionMap B) ⁻¹' A)).f n c) =
      (projection A).f n ((SingularChains.map (SingularSubspace.inclusionMap B)).f n c) := rfl

lemma inclusion_injective (A B : Set X) (n : ℕ) : Function.Injective ((inclusion A B).f n) := by
  intro c d h
  obtain ⟨c,rfl⟩ := projection_surjective _ n c
  obtain ⟨d,rfl⟩ := projection_surjective _ n d
  rw [inclusion_projection,inclusion_projection,projection_eq_iff,← map_sub,
    SingularSubspace.inclusion_mem_iff] at h
  exact (projection_eq_iff _ n c d).mpr h

lemma cycle_difference (A : Set X) (n k : ℕ) (c : (chains X).X n)
    (hc : (chains X).d n (n-1) c ∈ SingularSubspace.group A (n-1)) :
    (complex A).d (n+1) n ((projection A).f (n+1) (sumPrism X n k c)) =
      (projection A).f n c - (projection A).f n (iterate X n k c) := by
  rw [differential_projection]
  cases n with
  | zero => simp [sumPrism_zero,iterate_zero]
  | succ n =>
    have h := congrArg (fun h : (chains X).X (n+1) ⟶ (chains X).X (n+1) => h c)
      (sumPrism_boundary n k)
    change (chains X).d (n+2) (n+1) (sumPrism X (n+1) k c) =
      c - iterate X (n+1) k c - sumPrism X n k ((chains X).d (n+1) n c) at h
    rw [h,map_sub,map_sub]
    have hz : (projection A).f (n+1) (sumPrism X n k ((chains X).d (n+1) n c)) = 0 :=
      (projection_zero_iff A _ _).mpr (SingularSubspace.sumPrism_mem A hc k)
    rw [hz,sub_zero]

lemma iterate_projection_eq (A : Set X) (n k : ℕ) {c d : (chains X).X n}
    (h : (projection A).f n c = (projection A).f n d) :
    (projection A).f n (iterate X n k c) = (projection A).f n (iterate X n k d) := by
  apply (projection_eq_iff A n _ _).mpr
  rw [← map_sub]
  exact SingularSubspace.iterate_mem A ((projection_eq_iff A n _ _).mp h) k

end RelativeChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularExcision
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial

namespace RelativeChains
open Set _root_.CategoryTheory SingularChains SingularSubdivision
variable {X : Type} [TopologicalSpace X]

lemma inclusion_d (A B : Set X) (n m : ℕ)
    (c : (complex ((SingularSubspace.inclusionMap B) ⁻¹' A)).X n) :
    (inclusion A B).f m ((complex ((SingularSubspace.inclusionMap B) ⁻¹' A)).d n m c) =
      (complex A).d n m ((inclusion A B).f n c) :=
  (congrArg (fun h : (complex ((SingularSubspace.inclusionMap B) ⁻¹' A)).X n ⟶ (complex A).X m => h c)
    ((inclusion A B).comm n m)).symm

end RelativeChains

namespace SingularExcision
open Set _root_.CategoryTheory SingularChains SingularSubdivision RelativeChains HomologicalComplex
variable {X : Type} [TopologicalSpace X]

abbrev scInclusion (A B : Set X) (n : ℕ) :
    (RelativeChains.complex ((SingularSubspace.inclusionMap B) ⁻¹' A)).sc' (n+1) n (n-1) ⟶
      (RelativeChains.complex A).sc' (n+1) n (n-1) :=
  (shortComplexFunctor' (ModuleCat ℤ) (ComplexShape.down ℕ) (n+1) n (n-1)).map (inclusion A B)

end SingularExcision

namespace RelativeChains
open Set _root_.CategoryTheory HomologicalComplex SingularChains
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def sequence (A : Set X) : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (SingularChains.map (SingularSubspace.inclusionMap A)) (projection A) (by
    ext n c
    change (projection A).f n ((SingularChains.map (SingularSubspace.inclusionMap A)).f n c) = 0
    exact (projection_zero_iff A n _).mpr (SingularSubspace.inclusion_mem A n c))

theorem shortExact (A : Set X) : (sequence A).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro c hc
    change (projection A).f n c = 0 at hc
    have hmem := (projection_zero_iff A n c).mp hc
    refine ⟨SingularSubspace.lift A n c,?_⟩
    exact SingularSubspace.lift_inclusion_apply A hmem
  · exact (ModuleCat.mono_iff_injective _).mpr (SingularSubspace.inclusion_injective A n)
  · exact (ModuleCat.epi_iff_surjective _).mpr (projection_surjective A n)

def sequenceMap (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : MapsTo f A B) : sequence A ⟶ sequence B where
  τ₁ := SingularChains.map (restrictMap A B f hf)
  τ₂ := SingularChains.map f
  τ₃ := map A B f hf
  comm₁₂ := by
    change SingularChains.map (restrictMap A B f hf) ≫ SingularChains.map (SingularSubspace.inclusionMap B) =
      SingularChains.map (SingularSubspace.inclusionMap A) ≫ SingularChains.map f
    rw [← SingularChains.map_comp,← SingularChains.map_comp]
    rfl
  comm₂₃ := by
    ext n c
    rfl

lemma map_quasiIso (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : MapsTo f A B)
    (hfa : QuasiIso (SingularChains.map (restrictMap A B f hf)))
    (hfX : QuasiIso (SingularChains.map f)) : QuasiIso (map A B f hf) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (sequenceMap A B f hf)
    (shortExact A) (shortExact B) hfa hfX

end RelativeChains

namespace SingularChains
open _root_.CategoryTheory AlgebraicTopology HomologicalComplex
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

lemma map_iso (e : X ≃ₜ Y) : IsIso (map (e : C(X,Y))) := by
  refine ⟨⟨map (e.symm : C(Y,X)),?_,?_⟩⟩ <;> rw [← map_comp]
  · convert map_id (X := X) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext x
    exact e.symm_apply_apply x
  · convert map_id (X := Y) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext x
    exact e.apply_symm_apply x

end SingularChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_RelativeChains
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
namespace RelativeChains
open Set _root_.CategoryTheory HomologicalComplex SingularChains
variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

lemma map_id (A : Set X) : map A A (ContinuousMap.id X) (fun _ h => h) = 𝟙 _ := by
  ext n c
  obtain ⟨c,rfl⟩ := projection_surjective A n c
  erw [map_projection]
  rw [SingularChains.map_id]
  rfl

lemma map_comp (A : Set X) (B : Set Y) (D : Set Z) (f : C(X,Y)) (g : C(Y,Z))
    (hf : MapsTo f A B) (hg : MapsTo g B D) :
    map A B f hf ≫ map B D g hg = map A D (g.comp f) (hg.comp hf) := by
  ext n c
  obtain ⟨c,rfl⟩ := projection_surjective A n c
  change (map B D g hg).f n ((map A B f hf).f n ((projection A).f n c)) = _
  simp only [map_projection,SingularChains.map_comp]
  rfl

lemma homeomorph_quasiIso (A : Set X) (B : Set Y) (e : X ≃ₜ Y) (he : ∀ x,x ∈ A ↔ e x ∈ B) :
    QuasiIso (map A B (e : C(X,Y)) (fun x hx => (he x).mp hx)) := by
  apply map_quasiIso
  · have eqr : restrictMap A B (e : C(X,Y)) (fun x hx => (he x).mp hx) = ((e.subtype he) : C(A,B)) := rfl
    rw [eqr]
    let := SingularChains.map_iso (e.subtype he)
    infer_instance
  · let := SingularChains.map_iso e
    infer_instance

end RelativeChains

open Set Topology Metric

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_DiskSigmaCollar
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric

namespace RelativeChains
open Set _root_.CategoryTheory HomologicalComplex SingularChains
variable {X : Type} [TopologicalSpace X]

def quotientMap {D A : Set X} (h : D ⊆ A) : complex D ⟶ complex A :=
  map D A (ContinuousMap.id X) h

@[simp] lemma quotientMap_projection {D A : Set X} (h : D ⊆ A) (n : ℕ) (c : (chains X).X n) :
    (quotientMap h).f n ((projection D).f n c) = (projection A).f n c := by
  erw [quotientMap,map_projection,SingularChains.map_id]
  rfl

end RelativeChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ChainShortExact
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric

namespace SingularSubspace
open Set _root_.CategoryTheory SingularChains
variable {X : Type} [TopologicalSpace X]

lemma constant_fixed (x : X) {n : ℕ} {c : (chains X).X n}
    (hc : c ∈ group ({x} : Set X) n) : (map (ContinuousMap.const X x)).f n c = c := by
  apply sub_eq_zero.mp
  change c ∈ LinearMap.ker (((map (ContinuousMap.const X x)).f n).hom - LinearMap.id)
  apply SingularSupport.map_mem (𝟙 _) _ hc
  intro f hf
  change (map (ContinuousMap.const X x)).f n (SingularSupport.gen f) - SingularSupport.gen f = 0
  rw [SingularSupport.map_gen]
  apply sub_eq_zero.mpr
  congr 1
  ext z
  exact (hf (mem_range_self z)).symm

end SingularSubspace

namespace RelativeChains
open Set _root_.CategoryTheory HomologicalComplex SingularChains
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def pointChange (x y : X) : complex ({x} : Set X) ⟶ complex ({y} : Set X) :=
  QuotientComplex.map _ _ (𝟙 _ - SingularChains.map (ContinuousMap.const X x)) (by
    intro n c hc
    change c - (SingularChains.map (ContinuousMap.const X x)).f n c ∈ SingularSubspace.group {y} n
    rw [SingularSubspace.constant_fixed x hc,sub_self]
    exact Submodule.zero_mem _)

@[simp] lemma pointChange_projection (x y : X) (n : ℕ) (c : (chains X).X n) :
    (pointChange x y).f n ((projection ({x} : Set X)).f n c) =
      (projection ({y} : Set X)).f n (c - (SingularChains.map (ContinuousMap.const X x)).f n c) := rfl

end RelativeChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_RelativeChainsEmptyProjectionQuasiIso
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric

namespace DiskHomology
open Set Metric _root_.CategoryTheory HomologicalComplex
variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Boundary : Set (Disk E) := (SingularSubspace.inclusionMap (closedBall (0 : E) 1)) ⁻¹' sphere (0 : E) 1

end DiskHomology

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSigma
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric
namespace SingularSigma
open Set _root_.CategoryTheory HomologicalComplex SingularChains
attribute [-instance] AddCommGroup.toIntModule
variable {ι X : Type} [TopologicalSpace X]

variable (ι) (A : Set X)

def inclPair (i : ι) : RelativeChains.complex A ⟶ RelativeChains.complex (subset ι A) :=
  RelativeChains.map A (subset ι A) (incl i) (fun _ h => h)

def merge : FinsuppHomology.complex ι (RelativeChains.complex A) ⟶ RelativeChains.complex (subset ι A) where
  f n := FinsuppHomology.sumMap ι (fun i => (inclPair ι A i).f n)
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro i x
    change (RelativeChains.complex (subset ι A)).d n m
      (FinsuppHomology.sumMap ι (fun i => (inclPair ι A i).f n) (Finsupp.single i x)) =
      FinsuppHomology.sumMap ι (fun i => (inclPair ι A i).f m)
        (Finsupp.mapRange ((RelativeChains.complex A).d n m).hom (map_zero _) (Finsupp.single i x))
    rw [FinsuppHomology.sumMap_single,Finsupp.mapRange_single,FinsuppHomology.sumMap_single]
    exact congrArg (fun f => f x) ((inclPair ι A i).comm n m)

@[simp] lemma merge_single (n : ℕ) (i : ι) (x : (RelativeChains.complex A).X n) :
    (merge ι A).f n (Finsupp.single i x) = (inclPair ι A i).f n x := by
  exact FinsuppHomology.sumMap_single _ _ _ _

attribute [instance] AddCommGroup.toIntModule
end SingularSigma

namespace CWSkeletalHomology
attribute [-instance] AddCommGroup.toIntModule
open Set Topology Metric CWExtension _root_.CategoryTheory HomologicalComplex
variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

abbrev complex (n : ℕ) := RelativeChains.complex (CWCollar.lower (C := C) n)

attribute [instance] AddCommGroup.toIntModule
end CWSkeletalHomology

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CWCellular
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric
namespace CWCellular
open Set Topology CWExtension _root_.CategoryTheory HomologicalComplex
variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

abbrev absolute (n : ℕ) := SingularChains.chains (Skel C n)
abbrev relative (n : ℕ) := CWSkeletalHomology.complex (C := C) n

abbrev cell (n : ℕ) := (relative (C := C) n).homology n

end CWCellular

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_DiskHEP
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
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

def boundaryEquiv (n : ℕ) : Boundary n ≃ₜ DiskHEP.Boundary n where
  toFun s := ⟨(SimplexDisk.diskEquiv n s.1).1,by
    rw [mem_sphere,dist_zero_right]
    exact (SimplexDisk.diskEquiv_boundary_iff s.1).mpr s.2⟩
  invFun v := ⟨(SimplexDisk.diskEquiv n).symm ⟨v.1,sphere_subset_closedBall v.2⟩,by
    apply (SimplexDisk.diskEquiv_boundary_iff _).mp
    rw [Homeomorph.apply_symm_apply]
    simpa only [mem_sphere,dist_zero_right] using v.2⟩
  left_inv s := by
    apply Subtype.ext
    exact (SimplexDisk.diskEquiv n).symm_apply_apply s.1
  right_inv v := by
    apply Subtype.ext
    exact congrArg (fun z : DiskHEP.Disk n => z.1)
      ((SimplexDisk.diskEquiv n).apply_symm_apply ⟨v.1,sphere_subset_closedBall v.2⟩)
  continuous_toFun :=
    (continuous_subtype_val.comp ((SimplexDisk.diskEquiv n).continuous.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    ((SimplexDisk.diskEquiv n).symm.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _

universe u

end SimplexBoundary

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SimplexHomotopy
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
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
namespace SimplexHomotopy
open Set Topology Metric
open scoped unitInterval
open SimplexBoundary
universe u
variable {Y : Type u} [TopologicalSpace Y]

def diskMap {n : ℕ} (f : C(Simplex n,Y)) : C(DiskHEP.Disk n,Y) :=
  f.comp ⟨(SimplexDisk.diskEquiv n).symm,(SimplexDisk.diskEquiv n).symm.continuous⟩

def sideMap {n : ℕ} (h : C(I × Boundary n,Y)) : C(I × DiskHEP.Boundary n,Y) :=
  h.comp ⟨fun z => (z.1,(boundaryEquiv n).symm z.2),
    continuous_fst.prodMk ((boundaryEquiv n).symm.continuous.comp continuous_snd)⟩

lemma boundary_compat_forward {n : ℕ} (b : Boundary n) :
    SimplexDisk.diskEquiv n b.1 = DiskHEP.boundaryInclusion n (boundaryEquiv n b) := rfl

lemma sideMap_time {n : ℕ} (f : C(Simplex n,Y)) (h : C(I × Boundary n,Y)) (t : I)
    (ht : ∀ b, h (t,b) = f b.1) (b : DiskHEP.Boundary n) :
    sideMap h (t,b) = diskMap f (DiskHEP.boundaryInclusion n b) := ht _

theorem exists_extension {n : ℕ} (f : C(Simplex n,Y)) (h : C(I × Boundary n,Y))
    (h0 : ∀ b, h (0,b) = f b.1) :
    ∃ F : C(I × Simplex n,Y), (∀ s, F (0,s) = f s) ∧
      ∀ t b, F (t,b.1) = h (t,b) := by
  let hd := sideMap_time f h 0 h0
  let K := DiskHEP.extend (diskMap f) (sideMap h) hd
  let F : C(I × Simplex n,Y) := K.comp
    ⟨fun z => (z.1,SimplexDisk.diskEquiv n z.2),
      continuous_fst.prodMk ((SimplexDisk.diskEquiv n).continuous.comp continuous_snd)⟩
  refine ⟨F,?_,?_⟩
  · intro s
    change DiskHEP.extend _ _ hd (0,SimplexDisk.diskEquiv n s) = _
    rw [DiskHEP.extend_zero]
    exact congrArg f ((SimplexDisk.diskEquiv n).symm_apply_apply s)
  · intro t b
    change DiskHEP.extend _ _ hd (t,SimplexDisk.diskEquiv n b.1) = _
    rw [boundary_compat_forward,DiskHEP.extend_side]
    exact congrArg h (Prod.ext rfl ((boundaryEquiv n).symm_apply_apply b))

end SimplexHomotopy

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSphereCycle
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
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
namespace SingularSphereCycle
open Set Topology _root_.CategoryTheory AlgebraicTopology
open scoped Simplicial
open SphereQuotient

def collapse (n : ℕ) : C(Convexity.StdSimplex ℝ (Fin (n+1)), Boundary (n+1)) :=
  (quotient n).comp ⟨SimplexDisk.diskEquiv n,(SimplexDisk.diskEquiv n).continuous⟩

lemma collapse_face (n : ℕ) (i : Fin (n+2)) (s : Convexity.StdSimplex ℝ (Fin (n+1))) :
    collapse (n+1) (Convexity.StdSimplex.map i.succAbove s) = pole (n+1) :=
  quotient_boundary _ (SimplexDisk.diskEquiv_boundary _ i (face_zero i s))

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def simplex {n : ℕ} (f : C(Convexity.StdSimplex ℝ (Fin (n+1)),X)) :
    (TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.of X) _).symm
    (f.comp ⟨OAI.SingularChains.stdBridge _,(OAI.SingularChains.stdBridge _).continuous⟩)

lemma simplex_face {n : ℕ} (f : C(Convexity.StdSimplex ℝ (Fin (n+2)),X)) (i : Fin (n+2)) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i (simplex f) =
      simplex (f.comp ⟨Convexity.StdSimplex.map i.succAbove,
        Convexity.StdSimplex.continuous_map ℝ _⟩) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of X) _).injective
  ext x
  change f (OAI.SingularChains.stdBridge _ (OAI.SStd.map i.succAbove x)) =
    f (Convexity.StdSimplex.map i.succAbove (OAI.SingularChains.stdBridge _ x))
  congr 1
  apply Convexity.StdSimplex.ext
  ext k
  simp [OAI.SingularChains.stdBridge, OAI.SStd.equivStdSimplex, OAI.SStd.toStdSimplex,
    OAI.SStd.weights_map, Convexity.StdSimplex.weights_map]

def cycle (n : ℕ) : ModuleCat.of ℤ ℤ ⟶ (chains (Boundary (n+1))).X n :=
  (TopCat.toSSet.obj (TopCat.of (Boundary (n+1)))).ιChainComplex (simplex (collapse n)) -
    (TopCat.toSSet.obj (TopCat.of (Boundary (n+1)))).ιChainComplex
      (simplex (ContinuousMap.const _ (pole n)))

lemma cycle_d_succ (n : ℕ) :
    cycle (n+1) ≫ (chains (Boundary (n+2))).d (n+1) n = 0 := by
  rw [cycle,Preadditive.sub_comp,SSet.ιChainComplex_d,SSet.ιChainComplex_d]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  rw [simplex_face,simplex_face]
  congr 1
  apply ContinuousMap.ext
  intro s
  exact collapse_face n i s

lemma cycle_d (n : ℕ) : cycle n ≫ (chains (Boundary (n+1))).d n (n-1) = 0 := by
  cases n with
  | zero => simp
  | succ n => simpa using cycle_d_succ n

def fundamentalClass (n : ℕ) : (chains (Boundary (n+1))).homology n :=
  ((chains (Boundary (n+1))).liftCycles (cycle n) (n-1) (by cases n <;> simp [ChainComplex.next_nat_zero,ChainComplex.next_nat_succ]) (cycle_d n) ≫
    (chains (Boundary (n+1))).homologyπ n) 1

end SingularSphereCycle

namespace HurewiczConstruction
open Set Topology _root_.CategoryTheory AlgebraicTopology
open SphereQuotient
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

def canonical (n : ℕ) : HomotopyGroup (Fin n) X x → integralHomology n X :=
  map n (SingularSphereCycle.fundamentalClass n)

@[simp] theorem canonical_mk (n : ℕ) (a : GenLoop (Fin n) X x) :
    canonical n ⟦a⟧ = pushforward n (sphereMap a) (SingularSphereCycle.fundamentalClass n) := rfl

end HurewiczConstruction

namespace HurewiczNormalized
section
open Set Topology _root_.CategoryTheory AlgebraicTopology Limits HomologicalComplex
open SingularChains
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {n : ℕ} {x : X}

def cycle (f : BasedSimplex.Space n X x) : ModuleCat.of ℤ ℤ ⟶ (chains X).X n :=
  generator f.1 - generator (ContinuousMap.const _ x)

lemma based_face (f : BasedSimplex.Space (n+1) X x) (i : Fin (n+2)) :
    f.1.comp (face i) = ContinuousMap.const _ x := by
  ext s
  exact f.2 _ ⟨i,SimplexBoundary.face_zero i s⟩

lemma cycle_d (f : BasedSimplex.Space n X x) :
    cycle f ≫ (chains X).d n (n-1) = 0 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [cycle,Preadditive.sub_comp,Nat.add_sub_cancel,generator_boundary,generator_boundary]
    apply sub_eq_zero.mpr
    apply Finset.sum_congr rfl
    intro i _
    rw [based_face]
    rfl

def cycleClassHom {X : Type} [TopologicalSpace X] {n : ℕ}
    (c : ModuleCat.of ℤ ℤ ⟶ (chains X).X n) (hc : c ≫ (chains X).d n (n-1) = 0) :
    ModuleCat.of ℤ ℤ ⟶ (chains X).homology n :=
  (chains X).liftCycles c (n-1)
    (by cases n <;> simp [ChainComplex.next_nat_zero,ChainComplex.next_nat_succ]) hc ≫
      (chains X).homologyπ n

lemma cycleClassHom_map (c : ModuleCat.of ℤ ℤ ⟶ (chains X).X n)
    (hc : c ≫ (chains X).d n (n-1) = 0) (g : C(X,Y)) :
    cycleClassHom c hc ≫ homologyMap (map g) n =
      cycleClassHom (c ≫ (map g).f n)
        (by rw [Category.assoc,(map g).comm,← Category.assoc,hc,zero_comp]) := by
  unfold cycleClassHom
  rw [Category.assoc,homologyπ_naturality,← Category.assoc,liftCycles_comp_cyclesMap]

def homologyClass (f : BasedSimplex.Space n X x) : (chains X).homology n :=
  cycleClassHom (cycle f) (cycle_d f) 1

lemma sphereMap_comp_collapse (f : BasedSimplex.Space n X x) :
    (HurewiczConstruction.sphereMap (BasedSimplex.loop f)).comp
      (SingularSphereCycle.collapse n) = f.1 := by
  ext s
  change HurewiczConstruction.sphereMap (BasedSimplex.loop f)
    (SphereQuotient.sphereQuot n (.inl (SimplexDisk.diskEquiv n s))) = f.1 s
  rw [HurewiczConstruction.sphereMap_apply_quot]
  change f.1 ((SimplexDisk.diskEquiv n).symm
    (CubeDisk.toDisk n (CubeDisk.toCube n (SimplexDisk.diskEquiv n s)))) = f.1 s
  rw [CubeDisk.toDisk_toCube,Homeomorph.symm_apply_apply]

lemma sphereCycle_map (f : BasedSimplex.Space n X x) :
    SingularSphereCycle.cycle n ≫
      (map (HurewiczConstruction.sphereMap (BasedSimplex.loop f))).f n = cycle f := by
  change (generator (SingularSphereCycle.collapse n) -
    generator (ContinuousMap.const _ (SphereQuotient.pole n))) ≫ _ = _
  rw [Preadditive.sub_comp,generator_map,generator_map,sphereMap_comp_collapse]
  unfold cycle
  congr 2
  ext s
  exact HurewiczConstruction.sphereMap_pole _

theorem canonical_simplex (f : BasedSimplex.Space n X x) :
    HurewiczConstruction.canonical n (BasedSimplex.homotopyClass f) = homologyClass f := by
  change (cycleClassHom (SingularSphereCycle.cycle n) (SingularSphereCycle.cycle_d n) ≫
    homologyMap (map (HurewiczConstruction.sphereMap (BasedSimplex.loop f))) n) 1 = _
  rw [cycleClassHom_map]
  simp only [sphereCycle_map,homologyClass]

end

open Set Topology _root_.CategoryTheory AlgebraicTopology Limits HomologicalComplex
open SingularChains

end HurewiczNormalized

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_DuffySimplex
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
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

namespace DuffyBased
open DuffySimplex
open Set Topology
open scoped unitInterval
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ} {x : X}

def homotopy {f g : BasedSimplex.Space n X x}
    (H : f.1.HomotopyRel g.1 (BasedSimplex.Boundary n)) :
    (loop f).1.HomotopyRel (loop g).1 (Cube.boundary (Fin n)) where
  toHomotopy :=
  { toFun := fun z => H (z.1,toSimplex n z.2)
    continuous_toFun := H.continuous.comp
      (continuous_fst.prodMk ((toSimplex n).continuous.comp continuous_snd))
    map_zero_left := fun v => H.apply_zero (toSimplex n v)
    map_one_left := fun v => H.apply_one (toSimplex n v) }
  prop' := fun t v hv => H.eq_fst t ((boundary_iff n v).mpr hv)

def cylinder (n : ℕ) : C(I × (Fin n → I), I × Std n) :=
  ⟨fun z => (z.1,toSimplex n z.2),
    continuous_fst.prodMk ((toSimplex n).continuous.comp continuous_snd)⟩

lemma cylinder_quotient (n : ℕ) : IsQuotientMap (cylinder n) :=
  IsQuotientMap.of_surjective_continuous (by
    rintro ⟨t,s⟩
    obtain ⟨v,rfl⟩ := surjective n s
    exact ⟨(t,v),rfl⟩) (cylinder n).continuous

lemma homotopy_fiber {f g : BasedSimplex.Space n X x}
    (H : (loop f).1.HomotopyRel (loop g).1 (Cube.boundary (Fin n)))
    (v w : I × (Fin n → I)) (h : cylinder n v = cylinder n w) : H v = H w := by
  have ht : v.1 = w.1 := congrArg (fun z : I × Std n => z.1) h
  have hvw : toSimplex n v.2 = toSimplex n w.2 := congrArg Prod.snd h
  by_cases hv : v.2 ∈ Cube.boundary (Fin n)
  · have hw := (boundary_iff n w.2).mp (hvw ▸ (boundary_iff n v.2).mpr hv)
    exact (H.eq_fst _ hv).trans ((loop_fiber (loop f) hvw).trans (H.eq_fst _ hw).symm)
  · exact congrArg H (Prod.ext ht (injective_off_boundary n hvw hv))

def homotopyOfLoop {f g : BasedSimplex.Space n X x}
    (H : (loop f).1.HomotopyRel (loop g).1 (Cube.boundary (Fin n))) :
    f.1.HomotopyRel g.1 (BasedSimplex.Boundary n) := by
  let K : C(I × Std n,X) := (cylinder_quotient n).lift H.toContinuousMap (homotopy_fiber H)
  have hK (t : I) (v : Fin n → I) : K (t,toSimplex n v) = H (t,v) :=
    DFunLike.congr_fun ((cylinder_quotient n).lift_comp H.toContinuousMap (homotopy_fiber H)) (t,v)
  refine
  { toHomotopy :=
    { toContinuousMap := K
      map_zero_left := ?_
      map_one_left := ?_ }
    prop' := ?_ }
  · intro s
    obtain ⟨v,rfl⟩ := surjective n s
    exact (hK 0 v).trans (H.apply_zero v)
  · intro s
    obtain ⟨v,rfl⟩ := surjective n s
    exact (hK 1 v).trans (H.apply_one v)
  · intro t s hs
    obtain ⟨v,rfl⟩ := surjective n s
    exact (hK t v).trans (H.eq_fst t ((boundary_iff n v).mp hs))

lemma class_eq_iff (f g : BasedSimplex.Space n X x) :
    homotopyClass f = homotopyClass g ↔ Nonempty (f.1.HomotopyRel g.1 (BasedSimplex.Boundary n)) := by
  constructor
  · intro h
    obtain ⟨H⟩ := Quotient.exact h
    exact ⟨homotopyOfLoop H⟩
  · rintro ⟨H⟩
    exact Quotient.sound ⟨homotopy H⟩

end DuffyBased

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_BasedHorn
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
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
open SingularChains HurewiczNormalized DuffyTriangle SimplexAddition
variable {X : Type} [TopologicalSpace X] {n : ℕ} {x : X}

lemma alternating_cycle_boundary (F : C(Std (n+2),X))
    (h₂ : ∀ s ∈ DoubleBoundary (n+2), F s = x) :
    (generator F - generator (ContinuousMap.const _ x)) ≫ (chains X).d (n+2) (n+1) =
      ∑ i : Fin (n+3), (-1:ℤ)^i.val • cycle (basedFace F h₂ i) := by
  rw [Preadditive.sub_comp,generator_boundary,generator_boundary,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← smul_sub]
  rfl

lemma cycleClassHom_sum {ι : Type} [Fintype ι]
    (c : ι → (ModuleCat.of ℤ ℤ ⟶ (chains X).X n))
    (hc : ∀ i, c i ≫ (chains X).d n (n-1) = 0) (a : ι → ℤ) :
    cycleClassHom (∑ i, a i • c i) (by simp [Preadditive.sum_comp,hc]) =
      ∑ i, a i • cycleClassHom (c i) (hc i) := by
  have hl : (chains X).liftCycles (∑ i, a i • c i) (n-1)
      (by cases n <;> simp [ChainComplex.next_nat_zero,ChainComplex.next_nat_succ])
      (by simp [Preadditive.sum_comp,hc]) =
      ∑ i, a i • (chains X).liftCycles (c i) (n-1)
        (by cases n <;> simp [ChainComplex.next_nat_zero,ChainComplex.next_nat_succ]) (hc i) := by
    apply (cancel_mono ((chains X).iCycles n)).mp
    simp only [liftCycles_i,Preadditive.sum_comp,Linear.smul_comp]
  exact (congrArg (fun t => t ≫ (chains X).homologyπ n) hl).trans
    (by simp only [Preadditive.sum_comp,Linear.smul_comp,cycleClassHom])

lemma alternating_class_zero (F : C(Std (n+2),X))
    (h₂ : ∀ s ∈ DoubleBoundary (n+2), F s = x) :
    (∑ i : Fin (n+3), (-1:ℤ)^i.val • homologyClass (basedFace F h₂ i)) = 0 := by
  have hb := (chains X).liftCycles_homologyπ_eq_zero_of_boundary
    (∑ i : Fin (n+3), (-1:ℤ)^i.val • cycle (basedFace F h₂ i)) n
    (by simp [ChainComplex.next_nat_succ])
    (generator F - generator (ContinuousMap.const _ x)) (alternating_cycle_boundary F h₂).symm
  change cycleClassHom _ _ = 0 at hb
  rw [cycleClassHom_sum (fun i => cycle (basedFace F h₂ i)) (fun i => cycle_d _) (fun i : Fin (n+3) => (-1:ℤ)^i.val)] at hb
  have hv := congrArg (fun t => t 1) hb
  simpa only [ModuleCat.hom_sum,ModuleCat.hom_smul,ModuleCat.hom_zero,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.zero_apply,homologyClass] using hv

@[simp] lemma homologyClass_const (x : X) (n : ℕ) : homologyClass (BasedSimplex.const n x) = 0 := by
  have hc : cycle (BasedSimplex.const n x) = 0 := sub_self _
  have hh : cycleClassHom (cycle (BasedSimplex.const n x)) (cycle_d _) = 0 := by
    unfold cycleClassHom
    have hl : (chains X).liftCycles (cycle (BasedSimplex.const n x)) (n-1)
        (by cases n <;> simp [ChainComplex.next_nat_zero,ChainComplex.next_nat_succ]) (cycle_d _) = 0 := by
      apply (cancel_mono ((chains X).iCycles n)).mp
      rw [liftCycles_i,zero_comp,hc]
    rw [hl,zero_comp]
  exact congrArg (fun t => t 1) hh

lemma homologyClass_product (f g : BasedSimplex.Space (n+1) X x) :
    homologyClass (BasedHorn.product f g) = homologyClass f + homologyClass g := by
  have h := alternating_class_zero (BasedHorn.pairFill g f) (BasedHorn.pairFill_doubleBoundary g f)
  rw [alternating_three n _ (by
    intro i hi
    have hface : basedFace (BasedHorn.pairFill g f) (BasedHorn.pairFill_doubleBoundary g f) i =
        BasedSimplex.const (n+1) x := Subtype.ext (BasedHorn.pairFill_early g f i hi)
    rw [hface,homologyClass_const])] at h
  rw [BasedHorn.pairFill_left,BasedHorn.pairFill_right] at h
  change (-1:ℤ)^n • (homologyClass g - homologyClass (BasedHorn.product f g) + homologyClass f) = 0 at h
  have hz : homologyClass g - homologyClass (BasedHorn.product f g) + homologyClass f = 0 := by
    have h' := congrArg (fun z => (-1:ℤ)^n • z) h
    have hz₀ : (-1:ℤ)^n • (0 : (chains X).homology (n+1)) = 0 := zsmul_zero _
    have heq : homologyClass g - homologyClass (BasedHorn.product f g) + homologyClass f =
        (-1:ℤ)^n • (0 : (chains X).homology (n+1)) := by
      simpa only [smul_smul,← mul_pow,neg_one_mul,neg_neg,one_pow,one_smul] using h'
    exact heq.trans hz₀
  have he : homologyClass g + homologyClass f = homologyClass (BasedHorn.product f g) :=
    sub_eq_zero.mp (by convert hz using 1; abel)
  exact he.symm.trans (add_comm _ _)

end HurewiczAddition

namespace DuffyHurewicz
open Set Topology _root_.CategoryTheory AlgebraicTopology Limits HomologicalComplex
open SingularChains HurewiczNormalized DuffyBased
variable {X : Type} [TopologicalSpace X] {n : ℕ} {x : X}

lemma homologyClass_homotopic {f g : BasedSimplex.Space n X x}
    (H : f.1.HomotopyRel g.1 (BasedSimplex.Boundary n)) :
    homologyClass f = homologyClass g := by
  rw [← canonical_simplex,← canonical_simplex,BasedSimplex.class_homotopic H]

def value (p : HomotopyGroup.Pi n X x) : (chains X).homology n :=
  Quotient.lift (fun p => homologyClass (ofLoop p)) (by
    intro p q hpq
    apply homologyClass_homotopic
    apply Classical.choice
    apply (class_eq_iff _ _).mp
    change Quotient.mk _ (loop (ofLoop p)) = Quotient.mk _ (loop (ofLoop q))
    simpa only [loop_ofLoop] using Quotient.sound hpq) p

@[simp] lemma value_class (f : BasedSimplex.Space n X x) :
    value (homotopyClass f) = homologyClass f := by
  change homologyClass (ofLoop (loop f)) = _
  rw [ofLoop_loop]

lemma value_mul (p q : HomotopyGroup.Pi (n+1) X x) :
    value (p*q) = value p + value q := by
  induction p using Quotient.inductionOn with
  | h p =>
    induction q using Quotient.inductionOn with
    | h q =>
      have hp : homotopyClass (ofLoop p) = Quotient.mk _ p := congrArg (Quotient.mk _) (loop_ofLoop p)
      have hq : homotopyClass (ofLoop q) = Quotient.mk _ q := congrArg (Quotient.mk _) (loop_ofLoop q)
      rw [← hp,← hq,← BasedHorn.product_class,value_class,value_class,value_class]
      exact HurewiczAddition.homologyClass_product _ _

def hom (n : ℕ) (x : X) : Additive (HomotopyGroup.Pi (n+1) X x) →+ (chains X).homology (n+1) :=
  AddMonoidHom.mk' (fun p => value p.toMul) (fun p q => value_mul p.toMul q.toMul)

@[simp] lemma hom_class (f : BasedSimplex.Space (n+1) X x) :
    hom n x (Additive.ofMul (homotopyClass f)) = homologyClass f := value_class f

end DuffyHurewicz

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SimplexRotation
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
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

lemma continuous_minimum : Continuous (minimum (n:=n)) :=
  Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun i _ => Convexity.StdSimplex.continuous_weights_apply ℝ i)

lemma continuous_radius : Continuous (radius (n:=n)) :=
  continuous_const.sub (continuous_const.mul continuous_minimum)

def perm (p : Equiv.Perm (Fin (n+1))) : C(Std n,Std n) :=
  ⟨fun s => ⟨Finsupp.equivFunOnFinite.symm (fun i => s.weights (p i)),fun i => s.weights_nonneg _,by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    exact (Equiv.sum_comp p s.weights).trans s.total_of_fintype⟩,by
    apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).continuous_iff.mpr
    apply continuous_pi
    intro i
    exact Convexity.StdSimplex.continuous_weights_apply ℝ (p i)⟩

lemma perm_boundary (p : Equiv.Perm (Fin (n+1))) (s : Boundary n) :
    ∃ i, (perm p s.1).weights i = 0 := by
  obtain ⟨i,hi⟩ := s.2
  exact ⟨p.symm i,by simpa [perm] using hi⟩

def mix (p : Equiv.Perm (Fin (n+1))) : C(I × Std n,Std n) :=
  ⟨fun z => ⟨Finsupp.equivFunOnFinite.symm (fun i => (1-z.1:ℝ)*z.2.weights i+(z.1:ℝ)*z.2.weights (p i)),by
    intro i
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr z.1.2.2) (z.2.weights_nonneg i))
      (mul_nonneg z.1.2.1 (z.2.weights_nonneg _)),by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change ∑ i, ((1-z.1:ℝ)*z.2.weights i+(z.1:ℝ)*z.2.weights (p i)) = 1
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
      Equiv.sum_comp,z.2.total_of_fintype]
    ring⟩,by
    apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).continuous_iff.mpr
    apply continuous_pi
    intro i
    change Continuous (fun z : I × Std n => (1-z.1:ℝ)*z.2.weights i+(z.1:ℝ)*z.2.weights (p i))
    have ht : Continuous (fun z : I × Std n => (z.1:ℝ)) := continuous_subtype_val.comp continuous_fst
    have hc (j : Fin (n+1)) : Continuous (fun z : I × Std n => z.2.weights j) :=
      (Convexity.StdSimplex.continuous_weights_apply ℝ j).comp continuous_snd
    exact ((continuous_const.sub ht).mul (hc i)).add (ht.mul (hc (p i)))⟩

@[simp] lemma mix_zero (p : Equiv.Perm (Fin (n+1))) (s : Std n) : mix p (0,s) = s := by
  apply Convexity.StdSimplex.ext; apply Finsupp.ext; intro i; simp [mix]
@[simp] lemma mix_one (p : Equiv.Perm (Fin (n+1))) (s : Std n) : mix p (1,s) = perm p s := by
  apply Convexity.StdSimplex.ext; apply Finsupp.ext; intro i; simp [mix,perm]

lemma mix_radius_pos (p : Equiv.Perm (Fin (n+1))) (hp : ∀ i, p (p (p i)) = i)
    (t : I) (s : Boundary n) : 0 < radius (mix p (t,s.1)) := by
  apply lt_of_le_of_ne (radius_nonneg _)
  intro hz
  have hc := (radius_zero_iff _).mp hz.symm
  let c := minimum (mix p (t,s.1))
  have hid (i : Fin (n+1)) : s.1.weights i = c := by
    have h0 := hc i
    have h1 := hc (p i)
    have h2 := hc (p (p i))
    change (1-t:ℝ)*s.1.weights i+(t:ℝ)*s.1.weights (p i) = c at h0
    change (1-t:ℝ)*s.1.weights (p i)+(t:ℝ)*s.1.weights (p (p i)) = c at h1
    change (1-t:ℝ)*s.1.weights (p (p i))+(t:ℝ)*s.1.weights (p (p (p i))) = c at h2
    rw [hp] at h2
    have hd : (0:ℝ) < (1-t:ℝ)^3+(t:ℝ)^3 := by
      nlinarith [sq_nonneg ((t:ℝ)-1/2)]
    apply (mul_left_cancel₀ (ne_of_gt hd))
    linear_combination (1-t:ℝ)^2*h0 - (t:ℝ)*(1-t)*h1+(t:ℝ)^2*h2
  obtain ⟨i,hi⟩ := s.2
  have hc0 : c = 0 := (hid i).symm.trans hi
  have hs := s.1.total_of_fintype
  simp only [hid,hc0,Finset.sum_const_zero] at hs
  norm_num at hs

def boundaryRotation (p : Equiv.Perm (Fin (n+1))) (hp : ∀ i, p (p (p i)) = i) :
    C(I × Boundary n,Boundary n) :=
  ⟨fun z => radial (mix p (z.1,z.2.1)) (mix_radius_pos p hp z.1 z.2),by
    apply Continuous.subtype_mk
    apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).continuous_iff.mpr
    apply continuous_pi
    intro i
    apply Continuous.div
    · exact ((Convexity.StdSimplex.continuous_weights_apply ℝ i).comp
        ((mix p).continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))).sub
        (continuous_minimum.comp ((mix p).continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))))
    · exact continuous_radius.comp ((mix p).continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
    · intro z
      exact (mix_radius_pos p hp z.1 z.2).ne'⟩

@[simp] lemma boundaryRotation_zero (p : Equiv.Perm (Fin (n+1))) (hp : ∀ i, p (p (p i)) = i)
    (s : Boundary n) : boundaryRotation p hp (0,s) = s := by
  apply Subtype.ext
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  simp [boundaryRotation,radial,mix_zero,radius,minimum_boundary]

@[simp] lemma boundaryRotation_one (p : Equiv.Perm (Fin (n+1))) (hp : ∀ i, p (p (p i)) = i)
    (s : Boundary n) : (boundaryRotation p hp (1,s)).1 = perm p s.1 := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  have hm : minimum (perm p s.1) = 0 := minimum_boundary ⟨_,perm_boundary p s⟩
  simp [boundaryRotation,radial,mix_one,radius,hm]

end SimplexRotation

namespace RotationClass
open Set Topology SimplexRotation
open scoped unitInterval
universe u v
variable {X : Type u} [TopologicalSpace X] {Z : Type v} [TopologicalSpace Z]
variable {n : ℕ} {x : X}

def permute (f : BasedSimplex.Space n X x) (p : Equiv.Perm (Fin (n+1))) :
    BasedSimplex.Space n X x :=
  ⟨f.1.comp (perm p),fun s hs => f.2 _ (perm_boundary p ⟨s,hs⟩)⟩

def blend (a b : C(Z,Std n)) : C(I × Z,Std n) :=
  ⟨fun z => ⟨Finsupp.equivFunOnFinite.symm (fun i => (1-z.1:ℝ)*(a z.2).weights i+(z.1:ℝ)*(b z.2).weights i),by
    intro i
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr z.1.2.2) ((a z.2).weights_nonneg i))
      (mul_nonneg z.1.2.1 ((b z.2).weights_nonneg i)),by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    change ∑ i, ((1-z.1:ℝ)*(a z.2).weights i+(z.1:ℝ)*(b z.2).weights i) = 1
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
      (a z.2).total_of_fintype,(b z.2).total_of_fintype]
    ring⟩,by
    apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).continuous_iff.mpr
    apply continuous_pi
    intro i
    change Continuous (fun z : I × Z => (1-z.1:ℝ)*(a z.2).weights i+(z.1:ℝ)*(b z.2).weights i)
    have ht : Continuous (fun z : I × Z => (z.1:ℝ)) := continuous_subtype_val.comp continuous_fst
    have ha : Continuous (fun z : I × Z => (a z.2).weights i) :=
      (Convexity.StdSimplex.continuous_weights_apply ℝ i).comp (a.continuous.comp continuous_snd)
    have hb : Continuous (fun z : I × Z => (b z.2).weights i) :=
      (Convexity.StdSimplex.continuous_weights_apply ℝ i).comp (b.continuous.comp continuous_snd)
    exact ((continuous_const.sub ht).mul ha).add (ht.mul hb)⟩

@[simp] lemma blend_zero (a b : C(Z,Std n)) (z : Z) : blend a b (0,z) = a z := by
  apply Convexity.StdSimplex.ext; apply Finsupp.ext; intro i; simp [blend]
@[simp] lemma blend_one (a b : C(Z,Std n)) (z : Z) : blend a b (1,z) = b z := by
  apply Convexity.StdSimplex.ext; apply Finsupp.ext; intro i; simp [blend]
lemma blend_eq (a b : C(Z,Std n)) (z : Z) (h : a z = b z) (t : I) :
    blend a b (t,z) = b z := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  change (1-t:ℝ)*(a z).weights i+(t:ℝ)*(b z).weights i = (b z).weights i
  rw [h]
  ring

theorem class_of_boundary_isotopy (f : BasedSimplex.Space n X x)
    (p : Equiv.Perm (Fin (n+1)))
    (B : C(I × Boundary n,Boundary n))
    (h0 : ∀ s, B (0,s) = s)
    (h1 : ∀ s, (B (1,s)).1 = perm p s.1) :
    DuffyBased.homotopyClass f = DuffyBased.homotopyClass (permute f p) := by
  let side : C(I × Boundary n,Std n) := ⟨fun z => (B z).1,continuous_subtype_val.comp B.continuous⟩
  obtain ⟨F,hF0,hFs⟩ := SimplexHomotopy.exists_extension (ContinuousMap.id (Std n)) side
    (fun s => congrArg Subtype.val (h0 s))
  let g : C(Std n,Std n) := F.comp ⟨fun s => (1,s),continuous_const.prodMk continuous_id⟩
  have hg (s : Boundary n) : g s.1 = perm p s.1 := (hFs 1 s).trans (h1 s)
  let fg : BasedSimplex.Space n X x := ⟨f.1.comp g,fun s hs => by
    change f.1 (g s) = x
    rw [hg ⟨s,hs⟩]
    exact f.2 _ (perm_boundary p ⟨s,hs⟩)⟩
  have H : f.1.HomotopyRel fg.1 (BasedSimplex.Boundary n) :=
    { toHomotopy :=
      { toContinuousMap := f.1.comp F
        map_zero_left := fun s => congrArg f.1 (hF0 s)
        map_one_left := fun _ => rfl }
      prop' := by
        intro t s hs
        change f.1 (F (t,s)) = f.1 s
        rw [hFs t ⟨s,hs⟩]
        exact (f.2 _ (B (t,⟨s,hs⟩)).2).trans (f.2 s hs).symm }
  have K : fg.1.HomotopyRel (permute f p).1 (BasedSimplex.Boundary n) :=
    { toHomotopy :=
      { toContinuousMap := f.1.comp (blend g (perm p))
        map_zero_left := fun s => congrArg f.1 (blend_zero g (perm p) s)
        map_one_left := fun s => congrArg f.1 (blend_one g (perm p) s) }
      prop' := by
        intro t s hs
        change f.1 (blend g (perm p) (t,s)) = f.1 (g s)
        rw [blend_eq g (perm p) s (hg ⟨s,hs⟩) t,hg ⟨s,hs⟩] }
  exact (DuffyBased.class_eq_iff _ _).mpr ⟨H.trans K⟩

theorem class_cube (f : BasedSimplex.Space n X x) (p : Equiv.Perm (Fin (n+1)))
    (hp : ∀ i, p (p (p i)) = i) :
    DuffyBased.homotopyClass (permute f p) = DuffyBased.homotopyClass f :=
  (class_of_boundary_isotopy f p (boundaryRotation p hp)
    (boundaryRotation_zero p hp) (boundaryRotation_one p hp)).symm

@[simp] lemma permute_one (f : BasedSimplex.Space n X x) : permute f 1 = f := by
  apply Subtype.ext
  ext s
  change f.1 (perm 1 s) = f.1 s
  congr 1
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro index
  rfl

lemma permute_mul (f : BasedSimplex.Space n X x) (p q : Equiv.Perm (Fin (n+1))) :
    permute (permute f p) q = permute f (q*p) := by
  apply Subtype.ext
  ext s
  change f.1 (perm p (perm q s)) = f.1 (perm (q*p) s)
  rfl

end RotationClass

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SimplexSign
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
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
namespace SimplexSign
open Set Topology SimplexRotation RotationClass DuffySimplex
open scoped unitInterval
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

lemma simplex_lastSwap : ∀ n (t : Fin (n+1) → I),
    perm (lastSwap n) (toSimplex (n+1) t) = toSimplex (n+1) (reverseLast n t)
  | 0,t => by
    apply Convexity.StdSimplex.ext
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp [perm,lastSwap,toSimplex,cone,reverseLast,unitInterval.symm]
  | n+1,t => by
    apply Convexity.StdSimplex.ext
    apply Finsupp.ext
    intro i
    induction i using Fin.cases with
    | zero =>
      change (toSimplex (n+2) t).weights (lastSwap (n+1) 0) = _
      rw [lastSwap_zero,toSimplex_succ_zero,toSimplex_succ_zero,reverseLast_succ_zero]
    | succ i =>
      change (toSimplex (n+2) t).weights (lastSwap (n+1) i.succ) = _
      rw [lastSwap_succ,toSimplex_succ_succ,toSimplex_succ_succ,reverseLast_succ_zero]
      congr 1
      have h := congrArg (fun s : DuffySimplex.Std (n+1) => s.weights i) (simplex_lastSwap n (fun j => t j.succ))
      simpa only [perm,ContinuousMap.coe_mk,Finsupp.coe_equivFunOnFinite_symm,
        reverseLast_succ_succ] using h

lemma class_lastSwap (n : ℕ) (f : BasedSimplex.Space (n+1) X x) :
    DuffyBased.homotopyClass (permute f (lastSwap n)) = (DuffyBased.homotopyClass f)⁻¹ := by
  have h : DuffyBased.loop (permute f (lastSwap n)) = GenLoop.symmAt (Fin.last n) (DuffyBased.loop f) := by
    ext t
    change f.1 (perm (lastSwap n) (toSimplex (n+1) t)) = f.1 _
    rw [simplex_lastSwap]
    congr 2
    funext j
    simp only [reverseLast]
    split_ifs with h
    · rw [h]
    · rfl
  exact (congrArg (Quotient.mk _) h).trans (HomotopyGroup.inv_spec (i:=Fin.last n)).symm

def classStabilizer (n : ℕ) (X : Type u) [TopologicalSpace X] (x : X) :
    Subgroup (Equiv.Perm (Fin (n+1))) where
  carrier := {p | ∀ f : BasedSimplex.Space n X x,
    DuffyBased.homotopyClass (permute f p) = DuffyBased.homotopyClass f}
  one_mem' := fun f => by rw [permute_one]
  mul_mem' := by
    intro p q hp hq f
    rw [← permute_mul,hp,hq]
  inv_mem' := by
    intro p hp f
    have h := hp (permute f p⁻¹)
    rw [permute_mul,mul_inv_cancel,permute_one] at h
    exact h.symm

lemma alternating_le_classStabilizer (n : ℕ) :
    alternatingGroup (Fin (n+1)) ≤ classStabilizer n X x := by
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
  apply (Subgroup.closure_le _).mpr
  intro p hp f
  apply class_cube
  intro i
  have h : p^3 = 1 := hp.orderOf ▸ pow_orderOf_eq_one p
  exact congrArg (fun q : Equiv.Perm (Fin (n+1)) => q i) h

lemma class_even {n : ℕ} (f : BasedSimplex.Space n X x)
    (p : Equiv.Perm (Fin (n+1))) (hp : Equiv.Perm.sign p = 1) :
    DuffyBased.homotopyClass (permute f p) = DuffyBased.homotopyClass f :=
  alternating_le_classStabilizer n (Equiv.Perm.mem_alternatingGroup.mpr hp) f

lemma class_odd {n : ℕ} (f : BasedSimplex.Space (n+1) X x)
    (p : Equiv.Perm (Fin (n+2))) (hp : Equiv.Perm.sign p = -1) :
    DuffyBased.homotopyClass (permute f p) = (DuffyBased.homotopyClass f)⁻¹ := by
  have hs : Equiv.Perm.sign (lastSwap n) = -1 := Equiv.Perm.sign_swap (by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last] at this
    omega)
  have h := class_even f (lastSwap n * p) (by rw [map_mul,hp,hs]; norm_num)
  rw [← permute_mul,class_lastSwap] at h
  exact inv_eq_iff_eq_inv.mp h

lemma class_sign {n : ℕ} (f : BasedSimplex.Space (n+1) X x)
    (p : Equiv.Perm (Fin (n+2))) :
    DuffyBased.homotopyClass (permute f p) =
      (DuffyBased.homotopyClass f)^((Equiv.Perm.sign p : ℤˣ) : ℤ) := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h
  · rw [class_even f p h,h]
    simp
  · rw [class_odd f p h,h]
    simp

end SimplexSign

namespace SimplexVertexMaps
open Set Topology SimplexBoundary
variable {n m k : ℕ}

def vertexMap (f : Fin (n+1) → Fin (m+1)) : C(Simplex n,Simplex m) :=
  ⟨Convexity.StdSimplex.map f,Convexity.StdSimplex.continuous_map ℝ f⟩

@[simp] lemma vertexMap_id : vertexMap (id : Fin (n+1) → Fin (n+1)) = ContinuousMap.id _ := by
  apply ContinuousMap.ext
  intro s
  exact Convexity.StdSimplex.map_id s

lemma vertexMap_comp (f : Fin (n+1) → Fin (m+1)) (g : Fin (m+1) → Fin (k+1)) :
    (vertexMap g).comp (vertexMap f) = vertexMap (g ∘ f) := by
  apply ContinuousMap.ext
  intro s
  exact Convexity.StdSimplex.map_map s f g

lemma vertexMap_perm (p : Equiv.Perm (Fin (n+1))) : vertexMap p = SimplexRotation.perm p.symm := by
  ext s i
  change Finsupp.mapDomain p s.weights i = s.weights (p.symm i)
  simpa only [Equiv.apply_symm_apply] using
    Finsupp.mapDomain_apply p.injective s.weights (p.symm i)

lemma vertexMap_face (p : Equiv.Perm (Fin (n+2))) (i : Fin (n+2)) :
    (vertexMap p).comp (face i) = (face (p i)).comp (vertexMap (FacePermutation.restrict p i)) := by
  change (vertexMap p).comp (vertexMap i.succAbove) =
    (vertexMap (p i).succAbove).comp (vertexMap (FacePermutation.restrict p i))
  rw [vertexMap_comp,vertexMap_comp]
  congr 1
  funext j
  exact (FacePermutation.succAbove_restrict p i j).symm

lemma vertexMap_perm_coordinate (p : Equiv.Perm (Fin (n+1))) (s : Simplex n) (i : Fin (n+1)) :
    (vertexMap p s).weights (p i) = s.weights i := by
  rw [vertexMap_perm]
  simp [SimplexRotation.perm]

lemma vertexMap_perm_doubleBoundary (p : Equiv.Perm (Fin (n+1))) (s : Simplex n)
    (hs : s ∈ DuffyTriangle.DoubleBoundary n) : vertexMap p s ∈ DuffyTriangle.DoubleBoundary n := by
  obtain ⟨i,j,hij,hi,hj⟩ := hs
  exact ⟨p i,p j,p.injective.ne hij,(vertexMap_perm_coordinate p s i).trans hi,
    (vertexMap_perm_coordinate p s j).trans hj⟩

lemma vertexMap_zero_of_notMem_range (f : Fin (n+1) → Fin (m+1)) (i : Fin (m+1))
    (hi : i ∉ Set.range f) (s : Simplex n) : (vertexMap f s).weights i = 0 := by
  exact Finsupp.mapDomain_of_notMem_range s.weights i hi

end SimplexVertexMaps

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_BoundaryValue
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
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
namespace BoundaryValue
section
open Set Topology SimplexBoundary SimplexAddition SimplexVertexMaps
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}

def value (f : BasedSimplex.Space (n+2) X x) : A n X x :=
  Additive.ofMul (DuffyBased.homotopyClass f)

def boundary (F : C(Simplex (n+3),X))
    (h₂ : ∀ s ∈ DuffyTriangle.DoubleBoundary (n+3), F s = x) : A n X x :=
  ∑ i : Fin (n+4), (-1:ℤ)^i.val • value (basedFace F h₂ i)

lemma value_permute (f : BasedSimplex.Space (n+2) X x) (p : Equiv.Perm (Fin (n+3))) :
    value (RotationClass.permute f p) = ((Equiv.Perm.sign p : ℤˣ) : ℤ) • value f :=
  congrArg Additive.ofMul (SimplexSign.class_sign f p)

lemma boundary_permutation (F : C(Simplex (n+3),X))
    (h₂ : ∀ s ∈ DuffyTriangle.DoubleBoundary (n+3), F s = x)
    (p : Equiv.Perm (Fin (n+4))) :
    boundary (F.comp (vertexMap p))
      (fun s hs => h₂ _ (vertexMap_perm_doubleBoundary p s hs)) =
    ((Equiv.Perm.sign p : ℤˣ) : ℤ) • boundary F h₂ := by
  have hf (i : Fin (n+4)) :
      basedFace (F.comp (vertexMap p))
        (fun s hs => h₂ _ (vertexMap_perm_doubleBoundary p s hs)) i =
      RotationClass.permute (basedFace F h₂ (p i)) (FacePermutation.restrict p i).symm := by
    apply Subtype.ext
    change (F.comp (vertexMap p)).comp (face i) = _
    rw [ContinuousMap.comp_assoc,vertexMap_face,← ContinuousMap.comp_assoc,vertexMap_perm]
    rfl
  have hs (i : Fin (n+4)) :
      (-1:ℤ)^i.val * ((Equiv.Perm.sign (FacePermutation.restrict p i) : ℤˣ) : ℤ) =
        ((Equiv.Perm.sign p : ℤˣ) : ℤ) * (-1:ℤ)^(p i).val := by
    exact congrArg (fun z : ℤˣ => (z:ℤ)) (FacePermutation.sign_restrict p i)
  simp only [boundary,hf,value_permute,Equiv.Perm.sign_symm]
  simp_rw [← mul_zsmul,hs,mul_zsmul]
  rw [← Finset.smul_sum]
  exact congrArg (fun z : A n X x => ((Equiv.Perm.sign p : ℤˣ) : ℤ) • z)
    (Equiv.sum_comp p (fun i => (-1:ℤ)^i.val • value (basedFace F h₂ i)))

end

open Set Topology SimplexBoundary SimplexAddition SimplexVertexMaps DuffyTriangle
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}

@[simp] lemma value_const : value (BasedSimplex.const (n+2) x) = 0 := by
  rfl

lemma boundary_three (F : C(Simplex (n+3),X))
    (h₂ : ∀ s ∈ DoubleBoundary (n+3), F s = x)
    (he : ∀ i : Fin (n+4), i.val < n+1 → F.comp (face i) = ContinuousMap.const _ x) :
    boundary F h₂ = 0 := by
  unfold boundary
  rw [HurewiczAddition.alternating_three (n+1) _ (by
    intro i hi
    have hf : basedFace F h₂ i = BasedSimplex.const (n+2) x := Subtype.ext (he i hi)
    rw [hf,value_const])]
  have h := congrArg Additive.ofMul (SimplexAddition.three_face F h₂ he)
  change value (basedFace F h₂ (lastFace (n+1) 1)) =
    value (basedFace F h₂ (lastFace (n+1) 2)) + value (basedFace F h₂ (lastFace (n+1) 0)) at h
  rw [h]
  have hz : value (basedFace F h₂ (lastFace (n+1) 0)) -
      (value (basedFace F h₂ (lastFace (n+1) 2)) + value (basedFace F h₂ (lastFace (n+1) 0))) +
      value (basedFace F h₂ (lastFace (n+1) 2)) = 0 := by abel
  rw [hz,smul_zero]

lemma boundary_three_at (F : C(Simplex (n+3),X))
    (h₂ : ∀ s ∈ DoubleBoundary (n+3), F s = x) (a : Fin (n+4)) (ha : a.val < n+2)
    (he : ∀ i : Fin (n+4), i ≠ a → i ≠ lastFace (n+1) 1 → i ≠ lastFace (n+1) 2 →
      F.comp (face i) = ContinuousMap.const _ x) : boundary F h₂ = 0 := by
  let p := Equiv.swap a (lastFace (n+1) 0)
  have hp : p (lastFace (n+1) 0) = a := Equiv.swap_apply_right _ _
  have hpfix (j : Fin 3) (hj : 1 ≤ j.val) : p (lastFace (n+1) j) = lastFace (n+1) j := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      have hv := congrArg Fin.val h
      simp only [lastFace_val] at hv
      omega
    · exact fun h => (by have := BasedHorn.lastFace_injective (n+1) h; subst j; simp at hj)
  have hz := boundary_three (F.comp (vertexMap p))
    (fun s hs => h₂ _ (vertexMap_perm_doubleBoundary p s hs)) (by
      intro i hi
      have hineq (j : Fin 3) : i ≠ lastFace (n+1) j := by
        intro h
        have hv := congrArg Fin.val h
        simp only [lastFace_val] at hv
        omega
      have hia : p i ≠ a := by rw [← hp]; exact p.injective.ne (hineq 0)
      have hi1 : p i ≠ lastFace (n+1) 1 := by
        rw [← hpfix 1 (by decide)]
        exact p.injective.ne (hineq 1)
      have hi2 : p i ≠ lastFace (n+1) 2 := by
        rw [← hpfix 2 (by decide)]
        exact p.injective.ne (hineq 2)
      rw [ContinuousMap.comp_assoc,vertexMap_face,← ContinuousMap.comp_assoc,he (p i) hia hi1 hi2]
      rfl)
  rw [boundary_permutation] at hz
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h <;> simpa [h] using hz

end BoundaryValue

namespace SimplexDegeneracy
open Set Topology SimplexBoundary SimplexVertexMaps
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}

def degenerate (f : BasedSimplex.Space n X x) (v : Fin (n+1)) : C(Simplex (n+1),X) :=
  f.1.comp (vertexMap (append v))

lemma degenerate_face_last (f : BasedSimplex.Space n X x) (v : Fin (n+1)) :
    (degenerate f v).comp (face (Fin.last (n+1))) = f.1 := by
  change (f.1.comp (vertexMap (append v))).comp (vertexMap (Fin.last (n+1)).succAbove) = _
  rw [ContinuousMap.comp_assoc,vertexMap_comp,append_face_last,vertexMap_id,ContinuousMap.comp_id]

lemma degenerate_face_const (f : BasedSimplex.Space n X x) (v i : Fin (n+1)) (hiv : i ≠ v) :
    (degenerate f v).comp (face i.castSucc) = ContinuousMap.const _ x := by
  change (f.1.comp (vertexMap (append v))).comp (vertexMap i.castSucc.succAbove) = _
  rw [ContinuousMap.comp_assoc,vertexMap_comp]
  apply ContinuousMap.ext
  intro s
  apply f.2
  refine ⟨i,vertexMap_zero_of_notMem_range _ i ?_ s⟩
  rintro ⟨j,hj⟩
  exact Fin.succAbove_ne i.castSucc j (append_eq v i hiv _ hj)

lemma degenerate_standard_face (f : BasedSimplex.Space n X x) :
    (degenerate f (Fin.last n)).comp (face (Fin.last n).castSucc) = f.1 := by
  change (f.1.comp (vertexMap (append (Fin.last n)))).comp (vertexMap (Fin.last n).castSucc.succAbove) = _
  rw [ContinuousMap.comp_assoc,vertexMap_comp,append_face_last_castSucc,vertexMap_id,ContinuousMap.comp_id]

lemma degenerate_twisted_face (f : BasedSimplex.Space (n+1) X x) :
    (degenerate f (Fin.last n).castSucc).comp (face (Fin.last n).castSucc.castSucc) =
      (RotationClass.permute f (SimplexSign.lastSwap n)).1 := by
  change (f.1.comp (vertexMap (append (Fin.last n).castSucc))).comp
    (vertexMap (Fin.last n).castSucc.castSucc.succAbove) = _
  rw [ContinuousMap.comp_assoc,vertexMap_comp,append_face_penult,vertexMap_perm]
  rfl

end SimplexDegeneracy

namespace SimplexHorn
open Set Topology SimplexBoundary
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ}

lemma compatible_of_ordered (hole : Fin (n+3)) (f : Fin (n+3) → C(Simplex (n+1),X))
    (hc : ∀ (i j : Fin (n+2)), i ≤ j → i.castSucc ≠ hole → j.succ ≠ hole →
      (f i.castSucc).comp (face j) = (f j.succ).comp (face i)) :
    ∀ (i j : Faces hole) (a b : Simplex (n+1)), face i.1 a = face j.1 b → f i.1 a = f j.1 b := by
  have aux (i j : Faces hole) (hij : i.1 < j.1) (a b : Simplex (n+1))
      (hab : face i.1 a = face j.1 b) : f i.1 a = f j.1 b := by
    obtain ⟨l,s,hj,rfl,rfl⟩ := face_overlap hij.ne hab
    have hiLast : i.1 ≠ Fin.last (n+2) := ne_of_lt (lt_of_lt_of_le hij (Fin.le_last _))
    let k : Fin (n+2) := i.1.castPred hiLast
    have hk : k.castSucc = i.1 := Fin.castSucc_castPred i.1 hiLast
    have hle : i.1 ≤ l.castSucc := by
      by_contra! h
      rw [Fin.succAbove_of_castSucc_lt _ _ h] at hj
      exact (not_lt_of_ge (le_of_lt h)) (hj ▸ hij)
    have hkl : k ≤ l := by
      rw [← hk] at hle
      exact Fin.castSucc_le_castSucc_iff.mp hle
    rw [Fin.succAbove_of_le_castSucc _ _ hle] at hj
    have hp : l.predAbove i.1 = k := by rw [← hk,Fin.predAbove_castSucc_of_le _ _ hkl]
    rw [hp,← hk, hj]
    exact DFunLike.congr_fun (hc k l hkl (hk ▸ i.2) (hj ▸ j.2)) s
  intro i j a b hab
  rcases lt_trichotomy i.1 j.1 with h | h | h
  · exact aux i j h a b hab
  · have hij : i = j := Subtype.ext h
    subst j
    exact congrArg (f i.1) (face_injective i.1 hab)
  · exact (aux j i h b a hab.symm).symm

end SimplexHorn

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_HornElimination
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
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
namespace HornElimination
open Set Topology SimplexBoundary SimplexAddition SimplexDegeneracy DuffyTriangle
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}
variable (F : C(Simplex (n+3),X)) (h₂ : ∀ s ∈ DoubleBoundary (n+3), F s = x)
variable (a : Fin (n+2))

abbrev earlyFace (i : Fin (n+2)) := basedFace F h₂ i.castSucc.castSucc
abbrev pivotFace := basedFace F h₂ (Fin.last (n+2)).castSucc

def pivotFamily : Fin (n+4) → BasedSimplex.Space (n+2) X x :=
  Fin.lastCases (pivotFace F h₂) (Fin.lastCases (BasedSimplex.const _ x)
    (fun i => if i = a then RotationClass.permute (earlyFace F h₂ i) (SimplexSign.lastSwap (n+1))
      else BasedSimplex.const _ x))

def pivot : C(Simplex (n+3),X) :=
  BasedHorn.fill (Fin.last (n+2)).castSucc (fun j => pivotFamily F h₂ a j.1)

lemma pivot_early (i : Fin (n+2)) :
    (pivot F h₂ a).comp (face i.castSucc.castSucc) =
      if i = a then (RotationClass.permute (earlyFace F h₂ i) (SimplexSign.lastSwap (n+1))).1
      else ContinuousMap.const _ x := by
  have hi : i.castSucc.castSucc ≠ (Fin.last (n+2)).castSucc := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc,Fin.val_last] at hv
    omega
  rw [pivot,BasedHorn.fill_face _ _ ⟨_,hi⟩]
  simp only [pivotFamily, Fin.lastCases_castSucc]
  split_ifs <;> rfl

lemma pivot_last : (pivot F h₂ a).comp (face (Fin.last (n+3))) = (pivotFace F h₂).1 := by
  rw [pivot,BasedHorn.fill_face _ _ ⟨_, (Fin.castSucc_ne_last _).symm⟩]
  simp [pivotFamily]

lemma pivot_double : ∀ s ∈ DoubleBoundary (n+3), pivot F h₂ a s = x :=
  BasedHorn.fill_doubleBoundary _ _

def side (i : Fin (n+2)) : C(Simplex (n+3),X) :=
  if i = a then degenerate (earlyFace F h₂ i) (Fin.last (n+1)).castSucc
  else degenerate (earlyFace F h₂ i) (Fin.last (n+2))

lemma side_last (i : Fin (n+2)) :
    (side F h₂ a i).comp (face (Fin.last (n+3))) = (earlyFace F h₂ i).1 := by
  unfold side
  split_ifs <;> exact degenerate_face_last _ _

lemma side_penult (i : Fin (n+2)) :
    (side F h₂ a i).comp (face (Fin.last (n+2)).castSucc) =
      if i = a then ContinuousMap.const _ x else (earlyFace F h₂ i).1 := by
  unfold side
  split_ifs
  · exact degenerate_face_const _ _ _ (Fin.castSucc_ne_last _).symm
  · exact degenerate_standard_face _

lemma side_prepenult (i : Fin (n+2)) :
    (side F h₂ a i).comp (face (Fin.last (n+1)).castSucc.castSucc) =
      if i = a then (RotationClass.permute (earlyFace F h₂ i) (SimplexSign.lastSwap (n+1))).1
      else ContinuousMap.const _ x := by
  unfold side
  split_ifs
  · exact degenerate_twisted_face _
  · exact degenerate_face_const _ _ _ (Fin.castSucc_ne_last _)

lemma side_small (i : Fin (n+2)) (j : Fin (n+3)) (hj : j.val < n+1) :
    (side F h₂ a i).comp (face j.castSucc) = ContinuousMap.const _ x := by
  unfold side
  split_ifs <;> apply degenerate_face_const <;> intro h <;>
    have hv := congrArg Fin.val h <;> simp only [Fin.val_castSucc,Fin.val_last] at hv <;> omega

def family : Fin (n+5) → C(Simplex (n+3),X) :=
  Fin.lastCases F (Fin.lastCases (ContinuousMap.const _ x)
    (Fin.lastCases (pivot F h₂ a) (side F h₂ a)))

lemma family_ordered (i j : Fin (n+4)) (hij : i ≤ j)
    (hi : i.castSucc ≠ (Fin.last (n+3)).castSucc)
    (hj : j.succ ≠ (Fin.last (n+3)).castSucc) :
    (family F h₂ a i.castSucc).comp (face j) = (family F h₂ a j.succ).comp (face i) := by
  induction i using Fin.lastCases with
  | last => exact (hi rfl).elim
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simp only [family,Fin.lastCases_castSucc,Fin.succ_last,Fin.lastCases_last]
      induction i using Fin.lastCases with
      | last => simpa only [Fin.lastCases_last,pivotFace,basedFace] using pivot_last F h₂ a
      | cast i => simpa only [Fin.lastCases_castSucc,earlyFace,basedFace] using side_last F h₂ a i
    | cast j =>
      induction j using Fin.lastCases with
      | last =>
        apply False.elim
        apply hj
        apply Fin.ext
        rfl
      | cast j =>
        induction i using Fin.lastCases with
        | last =>
          have hval := Fin.le_iff_val_le_val.mp hij
          simp only [Fin.val_castSucc,Fin.val_last] at hval
          omega
        | cast i =>
          induction j using Fin.lastCases with
          | last =>
            have he : (Fin.last (n+1)).castSucc.castSucc.succ = (Fin.last (n+2)).castSucc.castSucc := Fin.ext rfl
            rw [he]
            simp only [family,Fin.lastCases_castSucc,Fin.lastCases_last]
            exact (side_prepenult F h₂ a i).trans (pivot_early F h₂ a i).symm
          | cast j =>
            have he : j.castSucc.castSucc.castSucc.succ = j.succ.castSucc.castSucc.castSucc := Fin.ext rfl
            rw [he]
            simp only [family,Fin.lastCases_castSucc]
            rw [side_small F h₂ a i j.castSucc.castSucc (by simpa only [Fin.val_castSucc] using j.isLt)]
            symm
            apply side_small
            have hval := Fin.le_iff_val_le_val.mp hij
            simp only [Fin.val_castSucc] at hval ⊢
            omega

lemma family_compatible :
    ∀ (i j : SimplexHorn.Faces (Fin.last (n+3)).castSucc) (s t : Simplex (n+3)),
      face i.1 s = face j.1 t → family F h₂ a i.1 s = family F h₂ a j.1 t :=
  SimplexHorn.compatible_of_ordered _ _ (family_ordered F h₂ a)

def higher : C(Simplex (n+4),X) :=
  SimplexHorn.fill (Fin.last (n+3)).castSucc (fun j => family F h₂ a j.1) (family_compatible F h₂ a)

lemma higher_face (i : Fin (n+5)) (hi : i ≠ (Fin.last (n+3)).castSucc) :
    (higher F h₂ a).comp (face i) = family F h₂ a i :=
  SimplexHorn.fill_face _ _ _ ⟨i,hi⟩

end HornElimination

namespace SimplexBoundary
open Set Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}

lemma face_ordered (i j : Fin (n+2)) (hij : i ≤ j) :
    (face i.castSucc).comp (face j) = (face j.succ).comp (face i) := by
  apply ContinuousMap.ext
  intro s
  have h := face_face i.castSucc j s
  rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hij),
    Fin.predAbove_castSucc_of_le _ _ hij] at h
  exact h.symm

lemma face_comp_ordered (H : C(Simplex (n+2),X)) (i j : Fin (n+2)) (hij : i ≤ j) :
    (H.comp (face i.castSucc)).comp (face j) = (H.comp (face j.succ)).comp (face i) := by
  rw [ContinuousMap.comp_assoc,ContinuousMap.comp_assoc,face_ordered i j hij]

lemma doubleBoundary_of_faces (F : C(Simplex (n+2),X))
    (f : Fin (n+3) → BasedSimplex.Space (n+1) X x)
    (hf : ∀ i, F.comp (face i) = (f i).1) : ∀ s ∈ DuffyTriangle.DoubleBoundary (n+2), F s = x := by
  rintro s ⟨i,j,hij,hi,hj⟩
  obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq hij.symm
  rw [← face_drop i s hi]
  have he := DFunLike.congr_fun (hf i) (drop i s hi)
  exact he.trans ((f i).2 _ ⟨k,by change s.1 (i.succAbove k) = 0; rw [hk,hj]⟩)

end SimplexBoundary

namespace HornElimination
open Set Topology SimplexBoundary SimplexAddition SimplexDegeneracy DuffyTriangle
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}
variable (F : C(Simplex (n+3),X)) (h₂ : ∀ s ∈ DoubleBoundary (n+3), F s = x)
variable (a : Fin (n+2))

def replacementFace : BasedSimplex.Space (n+2) X x :=
  basedFace (pivot F h₂ a) (pivot_double F h₂ a) (Fin.last (n+2)).castSucc

def replacement : C(Simplex (n+3),X) :=
  (higher F h₂ a).comp (face (Fin.last (n+3)).castSucc)

lemma replacement_early (i : Fin (n+2)) :
    (replacement F h₂ a).comp (face i.castSucc.castSucc) =
      if i = a then ContinuousMap.const _ x else (earlyFace F h₂ i).1 := by
  have hi : i.castSucc.castSucc ≤ (Fin.last (n+2)).castSucc := by
    exact Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last _)
  have h := face_comp_ordered (higher F h₂ a) i.castSucc.castSucc (Fin.last (n+2)).castSucc hi
  have he : (Fin.last (n+2)).castSucc.succ = (Fin.last (n+3)).castSucc := Fin.ext rfl
  rw [he,higher_face _ _ _ _ (by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc,Fin.val_last] at hv
    omega)] at h
  simp only [family,Fin.lastCases_castSucc] at h
  exact h.symm.trans (side_penult F h₂ a i)

lemma replacement_pivot :
    (replacement F h₂ a).comp (face (Fin.last (n+2)).castSucc) = (replacementFace F h₂ a).1 := by
  have h := face_comp_ordered (higher F h₂ a) (Fin.last (n+2)).castSucc (Fin.last (n+2)).castSucc le_rfl
  have he : (Fin.last (n+2)).castSucc.succ = (Fin.last (n+3)).castSucc := Fin.ext rfl
  rw [he,higher_face _ _ _ _ (by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc,Fin.val_last] at hv
    omega)] at h
  simp only [family,Fin.lastCases_castSucc,Fin.lastCases_last] at h
  exact h.symm

lemma replacement_last :
    (replacement F h₂ a).comp (face (Fin.last (n+3))) = (basedFace F h₂ (Fin.last (n+3))).1 := by
  have h := face_comp_ordered (higher F h₂ a) (Fin.last (n+3)) (Fin.last (n+3)) le_rfl
  rw [Fin.succ_last,higher_face _ _ _ _ (Fin.castSucc_ne_last _).symm] at h
  simpa only [family,Fin.lastCases_last,replacement,basedFace] using h

def newFaces : Fin (n+4) → BasedSimplex.Space (n+2) X x :=
  Fin.lastCases (basedFace F h₂ (Fin.last (n+3)))
    (Fin.lastCases (replacementFace F h₂ a) (fun i => if i = a then BasedSimplex.const _ x else earlyFace F h₂ i))

lemma replacement_faces (i : Fin (n+4)) :
    (replacement F h₂ a).comp (face i) = (newFaces F h₂ a i).1 := by
  induction i using Fin.lastCases with
  | last => simpa only [newFaces,Fin.lastCases_last] using replacement_last F h₂ a
  | cast i =>
    induction i using Fin.lastCases with
    | last => simpa only [newFaces,Fin.lastCases_castSucc,Fin.lastCases_last] using replacement_pivot F h₂ a
    | cast i =>
      rw [replacement_early]
      simp only [newFaces,Fin.lastCases_castSucc]
      split_ifs <;> rfl

lemma replacement_double : ∀ s ∈ DoubleBoundary (n+3), replacement F h₂ a s = x :=
  doubleBoundary_of_faces _ _ (replacement_faces F h₂ a)

lemma new_basedFace (i : Fin (n+4)) :
    basedFace (replacement F h₂ a) (replacement_double F h₂ a) i = newFaces F h₂ a i :=
  Subtype.ext (replacement_faces F h₂ a i)

end HornElimination

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_BoundaryValueBoundarySplit
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
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
namespace BoundaryValue
open Set Topology SimplexBoundary SimplexAddition SimplexVertexMaps DuffyTriangle
universe u
variable {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}

lemma boundary_split (F : C(Simplex (n+3),X))
    (h₂ : ∀ s ∈ DoubleBoundary (n+3), F s = x) :
    boundary F h₂ =
      (∑ i : Fin (n+2), (-1:ℤ)^i.val • value (basedFace F h₂ i.castSucc.castSucc)) +
      (-1:ℤ)^(n+2) • value (basedFace F h₂ (Fin.last (n+2)).castSucc) +
      (-1:ℤ)^(n+3) • value (basedFace F h₂ (Fin.last (n+3))) := by
  rw [boundary,Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  rfl

lemma pivot_boundary_zero (F : C(Simplex (n+3),X))
    (h₂ : ∀ s ∈ DoubleBoundary (n+3), F s = x) (a : Fin (n+2)) :
    boundary (HornElimination.pivot F h₂ a) (HornElimination.pivot_double F h₂ a) = 0 := by
  apply boundary_three_at _ _ a.castSucc.castSucc (by simpa only [Fin.val_castSucc] using a.isLt)
  intro i hi h1 h2
  induction i using Fin.lastCases with
  | last => exact (h2 (Fin.ext (by simp [lastFace_val]))).elim
  | cast i =>
    induction i using Fin.lastCases with
    | last => exact (h1 (Fin.ext (by simp [lastFace_val]))).elim
    | cast i =>
      have hia : i ≠ a := fun h => hi (h ▸ rfl)
      rw [HornElimination.pivot_early,ite_eq_right hia]

lemma replacement_boundary (F : C(Simplex (n+3),X))
    (h₂ : ∀ s ∈ DoubleBoundary (n+3), F s = x) (a : Fin (n+2)) :
    boundary (HornElimination.replacement F h₂ a) (HornElimination.replacement_double F h₂ a) =
      boundary F h₂ := by
  let P := HornElimination.pivot F h₂ a
  let hP := HornElimination.pivot_double F h₂ a
  let R := HornElimination.replacement F h₂ a
  let hR := HornElimination.replacement_double F h₂ a
  have he (i : Fin (n+2)) :
      value (basedFace R hR i.castSucc.castSucc) - value (basedFace F h₂ i.castSucc.castSucc) =
        value (basedFace P hP i.castSucc.castSucc) := by
    have hf := HornElimination.new_basedFace F h₂ a i.castSucc.castSucc
    have hp : basedFace P hP i.castSucc.castSucc =
        if i = a then RotationClass.permute (HornElimination.earlyFace F h₂ i) (SimplexSign.lastSwap (n+1))
        else BasedSimplex.const _ x := by
      by_cases hia : i = a
      · rw [ite_eq_left hia]
        apply Subtype.ext
        simpa only [P,basedFace,ite_eq_left hia] using HornElimination.pivot_early F h₂ a i
      · rw [ite_eq_right hia]
        apply Subtype.ext
        simpa only [P,basedFace,BasedSimplex.const,ite_eq_right hia] using HornElimination.pivot_early F h₂ a i
    dsimp only [HornElimination.newFaces] at hf
    simp only [Fin.lastCases_castSucc] at hf
    change basedFace R hR _ = _ at hf
    rw [hf,hp]
    by_cases hia : i = a
    · simp only [ite_eq_left hia,value_const,zero_sub,value_permute]
      have hsign : Equiv.Perm.sign (SimplexSign.lastSwap (n+1)) = -1 := by
        exact Equiv.Perm.sign_swap (by
          intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_last] at hv
          omega)
      rw [hsign]
      simp only [Units.val_neg,Units.val_one,neg_one_zsmul]

    · simp only [ite_eq_right hia, HornElimination.earlyFace,sub_self,value_const]
  have hs :
      (∑ i : Fin (n+2), (-1:ℤ)^i.val • value (basedFace R hR i.castSucc.castSucc)) -
      (∑ i : Fin (n+2), (-1:ℤ)^i.val • value (basedFace F h₂ i.castSucc.castSucc)) =
      (∑ i : Fin (n+2), (-1:ℤ)^i.val • value (basedFace P hP i.castSucc.castSucc)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [← smul_sub,he])
  have hrp : basedFace R hR (Fin.last (n+2)).castSucc = basedFace P hP (Fin.last (n+2)).castSucc :=
    Subtype.ext (HornElimination.replacement_pivot F h₂ a)
  have hrl : basedFace R hR (Fin.last (n+3)) = basedFace F h₂ (Fin.last (n+3)) :=
    Subtype.ext (HornElimination.replacement_last F h₂ a)
  have hpl : basedFace P hP (Fin.last (n+3)) = basedFace F h₂ (Fin.last (n+2)).castSucc :=
    Subtype.ext (HornElimination.pivot_last F h₂ a)
  have hz := pivot_boundary_zero F h₂ a
  change boundary P hP = 0 at hz
  rw [boundary_split,hpl] at hz
  change boundary R hR = boundary F h₂
  rw [boundary_split,boundary_split,hrp,hrl]
  have hpow : (-1:ℤ)^(n+3) = -((-1:ℤ)^(n+2)) := by rw [pow_succ]; ring
  rw [hpow,neg_smul] at hz
  rw [← hs] at hz
  apply sub_eq_zero.mp
  convert hz using 1; abel

theorem boundary_zero (F : C(Simplex (n+3),X))
    (h₂ : ∀ s ∈ DoubleBoundary (n+3), F s = x) : boundary F h₂ = 0 := by
  have aux : ∀ m k : ℕ, k+m = n+1 → ∀ (F : C(Simplex (n+3),X))
      (h₂ : ∀ s ∈ DoubleBoundary (n+3), F s = x),
      (∀ i : Fin (n+4), i.val < k → F.comp (face i) = ContinuousMap.const _ x) → boundary F h₂ = 0 := by
    intro m
    induction m with
    | zero =>
      intro k hk F h₂ he
      have hk' : k = n+1 := by omega
      subst k
      exact boundary_three F h₂ he
    | succ m ih =>
      intro k hk F h₂ he
      let a : Fin (n+2) := ⟨k,by omega⟩
      let R := HornElimination.replacement F h₂ a
      let hR := HornElimination.replacement_double F h₂ a
      rw [← replacement_boundary F h₂ a]
      apply ih (k+1) (by omega) R hR
      intro i hi
      have hib : i.val < n+2 := by omega
      let j : Fin (n+2) := ⟨i.val,hib⟩
      have hij : j.castSucc.castSucc = i := Fin.ext rfl
      rw [← hij]
      change (HornElimination.replacement F h₂ a).comp (face j.castSucc.castSucc) = _
      rw [HornElimination.replacement_early]
      split_ifs with hja
      · rfl
      · apply he
        have hv : j.val ≠ k := by
          intro hjv
          exact hja (Fin.ext hjv)
        change i.val < k
        change i.val ≠ k at hv
        omega
  exact aux (n+1) 0 (by omega) F h₂ (fun i hi => (Nat.not_lt_zero _ hi).elim)

end BoundaryValue

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_RepresentationKilling
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace RepresentationKilling
attribute [-instance] AddCommGroup.toIntModule
attribute [instance] AddCommGroup.toIntModule
end RepresentationKilling

namespace CWCellular
section
open Set Topology CWExtension _root_.CategoryTheory HomologicalComplex SingularChains
attribute [-instance] AddCommGroup.toIntModule

attribute [instance] AddCommGroup.toIntModule
end

section
open Set Topology CWExtension _root_.CategoryTheory HomologicalComplex SingularChains
attribute [-instance] AddCommGroup.toIntModule

attribute [instance] AddCommGroup.toIntModule
end

open Set Topology CWExtension _root_.CategoryTheory HomologicalComplex
variable {X Y Z : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  [TopologicalSpace Z] [T2Space Z] {C : Set X} {D : Set Y} {E : Set Z}
  [CWComplex C] [CWComplex D] [CWComplex E]

namespace SkeletalMap
variable (f : SkeletalMap C D)

def absoluteMap (n : ℕ) : absolute (C := C) n ⟶ absolute (C := D) n :=
  SingularChains.map (f.onSkel n)

def relativeMap (n : ℕ) : relative (C := C) n ⟶ relative (C := D) n :=
  RelativeChains.map _ _ (f.onSkel (n+1)) (f.lower_maps n)

def cellMap (n : ℕ) : cell (C := C) n ⟶ cell (C := D) n :=
  homologyMap (f.relativeMap n) n

end SkeletalMap
end CWCellular

attribute [-instance] AddCommGroup.toIntModule

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SingularSigmaSingleMerge
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
attribute [-instance] AddCommGroup.toIntModule

namespace CWSkeletalHomology
open Set Topology Metric CWExtension _root_.CategoryTheory HomologicalComplex
variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

lemma oneDisk_maps (n : ℕ) (i : RelCWComplex.cell C n) :
    MapsTo (charSkel n i) (DiskHomology.Boundary (Fin n → ℝ)) (CWCollar.lower (C := C) n) := by
  intro v hv
  apply (CWCollar.radius_eq_one_iff n _).mp
  rw [CWCollar.radius_disk]
  change v.1 ∈ sphere (0 : Fin n → ℝ) 1 at hv
  simpa only [mem_sphere,dist_zero_right] using hv

def oneDisk (n : ℕ) (i : RelCWComplex.cell C n) :
    RelativeChains.complex (DiskHomology.Boundary (Fin n → ℝ)) ⟶ complex (C := C) n :=
  RelativeChains.map _ _ (charSkel n i) (oneDisk_maps n i)

end CWSkeletalHomology

namespace CWCellular.SkeletalMap
open Set Topology CWExtension _root_.CategoryTheory HomologicalComplex
variable {X Y : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  {C : Set X} {D : Set Y} [CWComplex C] [CWComplex D]
variable (f : SkeletalMap C D) (g : ∀ n, RelCWComplex.cell C n → RelCWComplex.cell D n)
  (h : ∀ n i (v : Disk n), f.toMap (RelCWComplex.map n i v) = RelCWComplex.map n (g n i) v)

include h
lemma oneDisk_natural (n : ℕ) (i : RelCWComplex.cell C n) :
    CWSkeletalHomology.oneDisk n i ≫ f.relativeMap n = CWSkeletalHomology.oneDisk n (g n i) := by
  unfold CWSkeletalHomology.oneDisk relativeMap
  rw [RelativeChains.map_comp]
  congr 1
  apply ContinuousMap.ext
  intro v
  exact Subtype.ext (h n i v)

end CWCellular.SkeletalMap

attribute [instance] AddCommGroup.toIntModule

end

namespace CWEquivariant
attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension CWCellular _root_.CategoryTheory HomologicalComplex

attribute [instance] AddCommGroup.toIntModule
end CWEquivariant

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
 theorem replacement_mul (p q : Pair) :
    replacement K p * replacement K q = (multiplyPair p q).elim 0 (replacement K) := by
  have hh : replacement K p * replacement K q =
      insertion K p.1 * (deletion K p.2 * insertion K q.1) * deletion K q.2 := by
    simp [replacement, mul_assoc]
  rw [hh, deletion_insertion_cancel]
  cases h : cancel p.2 q.1 with
  | none => simp [multiplyPair, h]
  | some r => simp [multiplyPair, h, replacement, mul_assoc]
end

namespace Lists
variable {K}

 theorem value_mulTerm (a b : K × Pair) :
    value (mulTerm a b) = (a.1 • replacement K a.2) * (b.1 • replacement K b.2) := by
  rw [smul_mul_smul_comm, replacement_mul]
  cases h : multiplyPair a.2 b.2 <;> simp [mulTerm, h]

 theorem value_product (p q : Poly K) : value (product p q) = value p * value q := by
  induction p with
  | nil => simp [product]
  | cons a p ih =>
    rcases a with ⟨a,v⟩
    simp only [product, List.flatMap_cons, value_append, value_cons, add_mul] at *
    rw [ih]
    congr 1
    clear ih
    induction q with
    | nil => simp
    | cons b q ih =>
      rcases b with ⟨b,w⟩
      simp only [List.flatMap_cons, value_append, value_cons, value_mulTerm, mul_add, ih]

theorem value_surjective : Function.Surjective (value (K:=K)) := by
  intro x
  have hx := x.property
  change x.val ∈ Algebra.adjoin K (Set.range (left K) ∪ Set.range (right K)) at hx
  have hh : ∃ p : Poly K, (value p : Module.End K (Space K)) = x.val := by
    apply Algebra.adjoin_induction (p := fun x _ => ∃ p : Poly K,
      (value p : Module.End K (Space K)) = x) ?_ ?_ ?_ ?_ hx
    · intro x hx
      rcases hx with ⟨i,rfl⟩ | ⟨i,rfl⟩
      · exact ⟨[(1,([i],[]))], by simp [replacement, l]⟩
      · exact ⟨[(1,([],[i]))], by simp [replacement, r]⟩
    · intro a
      exact ⟨[(a,([],[]))], by simp [replacement, Algebra.algebraMap_eq_smul_one]⟩
    · intro x y hx hy hp hq
      obtain ⟨p,rfl⟩ := hp
      obtain ⟨q,rfl⟩ := hq
      exact ⟨p++q, by simp⟩
    · intro x y hx hy hp hq
      obtain ⟨p,rfl⟩ := hp
      obtain ⟨q,rfl⟩ := hq
      exact ⟨product p q, by simp [value_product]⟩
  obtain ⟨p,hp⟩ := hh
  exact ⟨p, Subtype.ext hp⟩

end Lists
end BinaryPrefixOperators.Arithmetic

end OAI
end


