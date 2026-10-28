-- Prove2me | Definitions.Def_OAIQ66So014
-- name    : OAIQ66So014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:17:24.483343+00:00
-- url     : https://prove2.me/theorems/27c8e04d-f701-4049-a475-ad5767b6a500
-- title:
--   Definitions bundle OAIQ66So014 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 157 declarations of OpenAI's Lean: 53 definitions, 1 inductive type or structure, 5 instances and 98 theorems. The definitions and types are `OAI.ListChains.standardTupleMap`, `OAI.OrbitBrown.perm`, `OAI.OrbitBrown.tensorPermIso`, `OAI.OrbitCoefficients.diagonalIso`, `OAI.OrbitCoefficients.diagonalMap`, `OAI.OrbitCoefficients.orbitCosetIso`, `OAI.OrbitCoefficients.orbitInclusion`, `OAI.OrbitCoefficients.orbitProjection`, `OAI.OrbitModule.Presentation.induced`, `OAI.OrbitModule.Presentation.ofBeginning`, `OAI.PosetTransport.Cocycle.Potential`, `OAI.PosetTransport.Cocycle.Trivial`, `OAI.PosetTransport.Cocycle.extension`, `OAI.PosetTransport.Cocycle.extensionLabel`, `OAI.PosetTransport.Cocycle.fullExtension`, `OAI.PosetTransport.Cocycle.linkPotential`, `OAI.PosetTransport.Cocycle.next`, `OAI.PosetTransport.Cocycle.nextEdge`, `OAI.PosetTransport.Cocycle.pull`, `OAI.PosetTransport.Connected`, `OAI.PrefixPermutation.units`, `OAI.ProductFiniteResolution.Beginning.ofComplex`, `OAI.ProductFiniteResolution.cover`, `OAI.ProductFiniteResolution.coverπ`, `OAI.ProductFiniteResolution.degreeIndex`, `OAI.ProductFiniteResolution.differential`, `OAI.ProductFiniteResolution.extendedComplex`, `OAI.ProductFiniteResolution.freeCover`, `OAI.ProductFiniteResolution.fromGenerators`, `OAI.ProductFiniteResolution.kerAsModuleEquiv`, `OAI.ProductFiniteResolution.next`, `OAI.ProductFiniteResolution.resolution`, `OAI.ProductGroupHomology.freePermIso`, `OAI.RegularProductR.relabel`, `OAI.RingExchange.Data.flipMatrix`, `OAI.RingExchange.Data.flipUnit`, `OAI.SequentialLimit.stage`, `OAI.SimpleFInftyOvergroups.BoundedEncoding.ActionCalculus.enlargement`, `OAI.SimpleFInftyOvergroups.BoundedEncoding.NamedAction.Operations.key`, `OAI.SimpleFInftyOvergroups.BoundedEncoding.NamedAction.Operations.test` and 14 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `FiniteType_FiniteIndexRegular`, `FiniteType_FreeTensor`, `FiniteType_InducedFree`, `FiniteType_ListChainsFromTuplesCone`, `FiniteType_PosetTransport`, `FiniteType_PrefixPermutation`, `FiniteType_PresentationGeometry`, `FiniteType_ProductCoefficientAffineShift`, `FiniteType_ProductCriterion`, `FiniteType_ProductFiniteResolution`, `FiniteType_ProductFiniteResolutionBeginningOfComplex`, `FiniteType_RingExchange`, `FiniteType_SequentialLimit`, `FiniteType_SurjectiveTrivialInduction`, `SimpleOvergroups_BoundedContexts`, `SimpleOvergroups_BoundedFamilyTests`, `SimpleOvergroups_CodeEmbedding`, `SimpleOvergroups_CommonCompiler`, `SimpleOvergroups_ContextualTables`, `SimpleOvergroups_ContractedNormalForms`, `SimpleOvergroups_EffectiveActions`, `SimpleOvergroups_EffectiveFold`, `SimpleOvergroups_EffectiveTables`, `SimpleOvergroups_FamilyTables`, `SimpleOvergroups_MatrixEffective`, `SimpleOvergroups_NamedActions`, `SimpleOvergroups_PlanEffective`, `SimpleOvergroups_TruncatedAction`, `SimpleOvergroups_TruncatedAlgebra`, `SimpleOvergroups_TruncatedArrays`, `SimpleOvergroups_TruncatedMatrix`.
--
--   **Imports.** It imports the bundles `OAIQ66So000`, `OAIQ66So001`, `OAIQ66So002`, `OAIQ66So003`, `OAIQ66So004`, `OAIQ66So005`, `OAIQ66So006`, `OAIQ66So007` and `OAIQ66So008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So019` and `OAIQ66So020`; the statements `OAI_TwistedBrin_Basis_CutBasis_simplex_stabilizer_products`, `OAI_TwistedBrin_Basis_CutBasis_sublevel_exact` and `OAI_TwistedBrin_localGroup_geometric_of_torus_models`; the proof of `OAI.ListChains.controlled_commuting_additivity`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So000
import Definitions.Def_OAIQ66So001
import Definitions.Def_OAIQ66So002
import Definitions.Def_OAIQ66So003
import Definitions.Def_OAIQ66So004
import Definitions.Def_OAIQ66So005
import Definitions.Def_OAIQ66So006
import Definitions.Def_OAIQ66So007
import Definitions.Def_OAIQ66So008

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometry
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Topology

noncomputable section

namespace PresentationGeometry

namespace Rose

instance point_finiteType : RelCWComplex.FiniteType (univ : Set Point) where
  finite_cell n := by
    cases n with
    | zero => change Finite (univ : Set Point); infer_instance
    | succ n => change Finite PEmpty; infer_instance

theorem point_dimension (n : ℕ) (i : RelCWComplex.cell (univ : Set Point) n) : n < 1 := by
  cases n with
  | zero => omega
  | succ n => exact PEmpty.elim i

end Rose

end PresentationGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductFiniteResolution
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.PartialResolution.complex_projective _root_.OAI.PartialResolution.obj_projective _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ProductFiniteResolution

open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidAlgebra

variable {k G : Type} [CommRing k] [Group G]

def fromGenerators {α : Type} (C : Rep k G) (s : α → C.ρ.asModule) :
    Rep.free k G α ⟶ C :=
  repMap ((Representation.freeAsModuleBasis k G α).constr k s)

lemma fromGenerators_surjective {α : Type} (C : Rep k G)
    (s : α → C.ρ.asModule) (hs : Submodule.span k[G] (Set.range s) = ⊤) :
    Function.Surjective (fromGenerators C s).hom := by
  have hr : LinearMap.range (ProductCriterion.moduleMap (fromGenerators C s)) = ⊤ := by
    rw [fromGenerators, moduleMap_repMap, Module.Basis.constr_range, hs]
  have h := LinearMap.range_eq_top.mp hr
  intro x
  obtain ⟨y, hy⟩ := h (C.ρ.asModuleEquiv.symm x)
  exact ⟨(Rep.free k G α).ρ.asModuleEquiv y, congrArg C.ρ.asModuleEquiv hy⟩

noncomputable def freeCover (C : Rep k G) : FreeCover C := by
  classical
  by_cases h : Module.Finite k[G] C.ρ.asModule
  · letI := h
    let n := Classical.choose (Module.Finite.exists_fin (R := k[G]) (M := C.ρ.asModule))
    have hn := Classical.choose_spec (Module.Finite.exists_fin (R := k[G]) (M := C.ρ.asModule))
    let s := Classical.choose hn
    have hs := Classical.choose_spec hn
    exact ⟨Fin n, fromGenerators C s, fromGenerators_surjective C s hs,
      fun _ => inferInstance⟩
  · exact ⟨C.ρ.asModule, fromGenerators C id,
      fromGenerators_surjective C id (by simp), fun hf => False.elim (h hf)⟩

abbrev cover (C : Rep k G) : Rep k G := Rep.free k G (freeCover C).ι
abbrev coverπ (C : Rep k G) : cover C ⟶ C := (freeCover C).π

instance coverπ_epi (C : Rep k G) : Epi (coverπ C) :=
  (Rep.epi_iff_surjective _).mpr (freeCover C).surjective

instance cover_projective (C : Rep k G) : Projective (cover C) := by
  dsimp [cover]
  infer_instance

def kerAsModuleEquiv {C D : Rep k G} (f : C ⟶ D) :
    (kerRep f).ρ.asModule ≃ₗ[k[G]] (ProductCriterion.moduleMap f).ker :=
  LinearEquiv.ofBijective
    ((ProductCriterion.moduleMap (kerι f)).codRestrict _ (fun x => by
      change ProductCriterion.moduleMap f (ProductCriterion.moduleMap (kerι f) x) = 0
      exact congrArg D.ρ.asModuleEquiv.symm ((kerRep f).ρ.asModuleEquiv x).property))
    (by
      constructor
      · intro x y h
        apply (kerRep f).ρ.asModuleEquiv.injective
        apply Subtype.ext
        exact congrArg C.ρ.asModuleEquiv (Subtype.ext_iff.mp h)
      · intro y
        refine ⟨(kerRep f).ρ.asModuleEquiv.symm
          ⟨C.ρ.asModuleEquiv y.val, ?_⟩, ?_⟩
        · exact congrArg D.ρ.asModuleEquiv y.property
        · apply Subtype.ext
          rfl)

abbrev next {C D : Rep k G} (f : C ⟶ D) := cover (kerRep f)

def differential {C D : Rep k G} (f : C ⟶ D) : next f ⟶ C :=
  coverπ (kerRep f) ≫ kerι f

@[reassoc (attr := simp)] lemma differential_comp {C D : Rep k G} (f : C ⟶ D) :
    differential f ≫ f = 0 := by simp [differential]

lemma differential_exact {C D : Rep k G} (f : C ⟶ D) :
    (ShortComplex.mk (differential f) f (differential_comp f)).Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k)),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨y, hy⟩ := (freeCover (kerRep f)).surjective ⟨x, hx⟩
  refine ⟨y, ?_⟩
  exact congrArg Subtype.val hy

attribute [instance] Beginning.finite₀ Beginning.finite₁ Beginning.finite₂ Beginning.epi_ε

variable {Z : Rep k G} (B : Beginning Z)

def extendedComplex : ChainComplex (Rep k G) ℕ :=
  ChainComplex.mk (Rep.free k G B.α₀) (Rep.free k G B.α₁) (Rep.free k G B.α₂)
    B.d₁ B.d₂ B.d₂_d₁ (fun S => ⟨next S.f, differential S.f, differential_comp S.f⟩)

@[simp] lemma extendedComplex_d_1_0 : (extendedComplex B).d 1 0 = B.d₁ := by
  simp [extendedComplex]

@[simp] lemma extendedComplex_d_2_1 : (extendedComplex B).d 2 1 = B.d₂ := by
  simp [extendedComplex]

lemma extendedComplex_exactAt_succ (n : ℕ) : (extendedComplex B).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)]
  change (ShortComplex.mk _ _ ((extendedComplex B).d_comp_d (n + 2) (n + 1) n)).Exact
  erw [← ChainComplex.mkAux_eq_shortComplex_mk_d_comp_d
    (Rep.free k G B.α₀) (Rep.free k G B.α₁) (Rep.free k G B.α₂)
    B.d₁ B.d₂ B.d₂_d₁
    (fun S => ⟨next S.f, differential S.f, differential_comp S.f⟩) n]
  cases n with
  | zero => exact B.exact₁
  | succ n => exact differential_exact (k := k) (G := G) _

instance extendedComplex_projective (n : ℕ) : Projective ((extendedComplex B).X n) := by
  obtain (_ | _ | _ | n) := n <;> apply Rep.free_projective

def resolution : ProjectiveResolution Z where
  complex := extendedComplex B
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨B.ε, by
    rw [extendedComplex_d_1_0]; exact B.d₁_ε⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2 ⟨B.exact₀, B.epi_ε⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by
            simp only [Iso.refl_hom, extendedComplex]
            change 𝟙 (Rep.free k G B.α₁) ≫ B.d₁ = B.d₁ ≫ 𝟙 (Rep.free k G B.α₀)
            simp)
          (by
            change 𝟙 (Rep.free k G B.α₀) ≫ B.ε = B.ε ≫ 𝟙 Z
            simp)
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact extendedComplex_exactAt_succ B n
      · apply ChainComplex.exactAt_succ_single_obj⟩

def degreeIndex : ℕ → Type
  | 0 => B.α₀
  | 1 => B.α₁
  | 2 => B.α₂
  | n + 3 => (freeCover (kerRep ((extendedComplex B).d (n + 2) (n + 1)))).ι

end ProductFiniteResolution

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_FreeTensor
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ListChains

variable (G : Type*)

lemma head_mem_vertices (s : Simplex G) : s.1 ∈ vertices G s := Or.inl rfl

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ListChainsFromTuplesCone
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory
namespace ListChains
section
variable (G : Type)

lemma tuple_single_as_cone (n : ℕ) (c : Fin (n+2) → G) (r : ℤ) :
    Finsupp.single c r = ControlledChains.cone G (c 0) n
      (Finsupp.single (fun i => c i.succ) r) := by
  rw [ControlledChains.cone_single]
  congr 1
  exact (Fin.cons_self_tail c).symm

end

open _root_.CategoryTheory

end ListChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductCoefficientAffineShift
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.CategoryTheory

namespace ListChains
open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
variable (G I C : Type) [Group G]

def standardTupleMap (f : G →* G) (n : ℕ) :
    MonoidAlgebra ℤ (Fin (n+1) → G) →ₗ[ℤ] MonoidAlgebra ℤ (Fin (n+1) → G) :=
  (MonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap.comp
    ((ControlledChains.mapChain G f n).comp (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap)

end ListChains

open _root_.CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_FiniteIndexRegular
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RegularProductR
open _root_.CategoryTheory _root_.OAI.CategoryTheory
variable {G H : Type} [Group G] [Group H] (e : G ≃* H) (I : Type)
noncomputable def relabel : Module ℤ G I ≃ₗ[ℤ] Module ℤ H I :=
  LinearEquiv.piCongrRight (fun _ => Finsupp.domLCongr (R := ℤ) e.toEquiv)

end RegularProductR

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_InducedFree
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation

namespace OrbitModule
open scoped MonoidalCategory
variable {k G : Type} [CommRing k] [Group G]
attribute [instance] Presentation.finiteα Presentation.finiteβ Presentation.epi

def Presentation.induced {H : Type} [Group H] (φ : G →* H) {C : Rep k G}
    (P : Presentation C) : Presentation (Rep.ind φ C) := by
  let F := Rep.indFunctor k φ
  let e0 := InducedFree.iso (k := k) φ P.α
  let e1 := InducedFree.iso (k := k) φ P.β
  have hS := P.exact.map_of_epi_of_preservesCokernel F P.epi inferInstance
  exact {
    α := P.α
    β := P.β
    d := e1.inv ≫ F.map P.d ≫ e0.hom
    ε := e0.inv ≫ F.map P.ε
    w := by simp only [Category.assoc,Iso.hom_inv_id_assoc,← Functor.map_comp,P.w,Functor.map_zero,comp_zero]
    exact := by
      let E := (ShortComplex.mk P.d P.ε P.w).map F
      let D := ShortComplex.mk (e1.inv ≫ F.map P.d ≫ e0.hom) (e0.inv ≫ F.map P.ε)
        (by simp only [Category.assoc,Iso.hom_inv_id_assoc,← Functor.map_comp,P.w,Functor.map_zero,comp_zero])
      let iso : E ≅ D := ShortComplex.isoMk e1 e0 (Iso.refl _)
        (by change e1.hom ≫ e1.inv ≫ F.map P.d ≫ e0.hom = F.map P.d ≫ e0.hom
            simp only [Iso.hom_inv_id_assoc])
        (by change e0.hom ≫ e0.inv ≫ F.map P.ε = F.map P.ε ≫ 𝟙 _
            simp only [Iso.hom_inv_id_assoc,Category.comp_id])
      exact (ShortComplex.exact_iff_of_iso iso).mp hS }

variable (G) in
def Presentation.ofBeginning (B : ProductFiniteResolution.Beginning (Rep.trivial k G k)) :
    Presentation (Rep.trivial k G k) where
  α := B.α₀
  β := B.α₁
  d := B.d₁
  ε := B.ε
  w := B.d₁_ε
  exact := B.exact₀
end OrbitModule

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SequentialLimit
attribute [-instance] _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace SequentialLimit

variable {X Y : Type*}

lemma of_injective (s : X → X) (hs : Function.Injective s) (i : ℕ) :
    Function.Injective (of s i) :=
  DirectLimit.mk_injective (transition s) (fun _ _ _ => hs.iterate _) i

instance limitCountable (s : X → X) [Countable X] : Countable (Limit s) :=
  inferInstanceAs (Countable (Quotient (DirectLimit.setoid (transition s))))

def stage (s : X → X) (i : ℕ) : Set (Limit s) := Set.range (of s i)

end SequentialLimit

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PrefixPermutation
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace PrefixPermutation
variable {R Y : Type*} [Ring R] [DecidableEq Y]
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y z, T y*S z=if y=z then e else 0)
variable (hSe : ∀ y, S y*e=S y)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (x : ι → Y) (hx : Function.Injective x)

include hTS hSe hx in
lemma partial_mul (σ τ : Equiv.Perm ι) :
    matrixPart S T x σ*matrixPart S T x τ=matrixPart S T x (σ*τ) := by
  classical
  unfold matrixPart
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have heq (i : ι) : S (x (σ i))*T (x i)*(S (x (τ j))*T (x j))=
      if i=τ j then S (x (σ (τ j)))*T (x j) else 0 := by
    rw [mul_assoc,← mul_assoc (T (x i)),hTS]
    by_cases h : i=τ j
    · subst i; simp [← mul_assoc,hSe]
    · rw [ite_eq_right (fun he => h (hx he)),zero_mul,mul_zero,ite_eq_right h]
  simp_rw [heq]
  simp

include hTS hSe hx in
lemma support_mul (σ : Equiv.Perm ι) : support S T x*matrixPart S T x σ=matrixPart S T x σ := by
  simpa only [partial_one,one_mul] using partial_mul e S T hTS hSe x hx 1 σ

include hTS hSe hx in
lemma mul_support (σ : Equiv.Perm ι) : matrixPart S T x σ*support S T x=matrixPart S T x σ := by
  simpa only [partial_one,mul_one] using partial_mul e S T hTS hSe x hx σ 1

include hTS hSe hx in
lemma support_idempotent : support S T x*support S T x=support S T x := by
  simpa only [partial_one] using support_mul e S T hTS hSe x hx 1

include hTS hSe hx in
lemma value_mul (σ τ : Equiv.Perm ι) : value S T x (σ*τ)=value S T x σ*value S T x τ := by
  have hpp := support_idempotent e S T hTS hSe x hx
  have hpτ := support_mul e S T hTS hSe x hx τ
  have hσp := mul_support e S T hTS hSe x hx σ
  have hστ := partial_mul e S T hTS hSe x hx σ τ
  unfold value
  noncomm_ring [hpp,hpτ,hσp,hστ]

def units : Equiv.Perm ι →* Rˣ where
  toFun σ := {
    val := value S T x σ
    inv := value S T x σ⁻¹
    val_inv := by rw [← value_mul e S T hTS hSe x hx,mul_inv_cancel,value_one]
    inv_val := by rw [← value_mul e S T hTS hSe x hx,inv_mul_cancel,value_one] }
  map_one' := Units.ext (value_one S T x)
  map_mul' σ τ := Units.ext (value_mul e S T hTS hSe x hx σ τ)

end PrefixPermutation

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_RingExchange
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace RingExchange.Data
variable {R : Type*} [Ring R] (D : RingExchange.Data R)

def flipMatrix : Matrix (Fin 2) (Fin 2) R := !![1-D.F,D.a; D.b,1-D.E]

lemma flipMatrix_square : D.flipMatrix * D.flipMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flipMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    simp only [sub_mul, mul_sub, one_mul, mul_one, D.FF, D.EE, D.Fa, D.aE,
      D.bF, D.Eb, D.ab, D.ba]
    abel

def flipUnit : (Matrix (Fin 2) (Fin 2) R)ˣ :=
  ⟨D.flipMatrix,D.flipMatrix,D.flipMatrix_square,D.flipMatrix_square⟩

lemma flip_bad_row (η : R →ₙ+* R) (hE : ∀ x, D.E*η x=η x) (x : R) (j : Fin 2) :
    D.flipMatrix 1 j * η x=0 := by
  have hb : D.b*η x=0 := by rw [← hE x,← mul_assoc,D.bE,zero_mul]
  fin_cases j <;> simp [flipMatrix,sub_mul,hE,hb]

lemma flip_bad_col (η : R →ₙ+* R) (hE : ∀ x, η x*D.E=η x) (x : R) (j : Fin 2) :
    η x * D.flipMatrix j 1=0 := by
  have ha : η x*D.a=0 := by rw [← hE x,mul_assoc,D.Ea,mul_zero]
  fin_cases j <;> simp [flipMatrix,mul_sub,hE,ha]

end RingExchange.Data

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductCriterion
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonoidalCategory
namespace ProductBrown
attribute [-instance] AddCommGroup.toIntModule
end ProductBrown

open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace OrbitCoefficients
variable {k G V W : Type} [CommRing k] [Group G] [MulAction G V] [MulAction G W]
variable (A : Rep k G)

local instance (V : Type) [MulAction G V] : CoeFun (FunctionalTree.diagonalRep (V := V) A) (fun _ => V → A) :=
  ⟨fun x => @DFunLike.coe (V →₀ A) V (fun _ => A) inferInstance x⟩

lemma diagonal_apply (g : G) (z : V →₀ A) (v : V) :
    ((FunctionalTree.diagonalRep (V := V) A).ρ g z : V →₀ A) v = A.ρ g (z (g⁻¹ • v)) := by
  classical
  change FunctionalTree.diagonalAction A g z v = _
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add,Finsupp.add_apply,hx,hy]
  | single x a =>
    rw [FunctionalTree.diagonalAction_single]
    by_cases h : g • x = v
    · have h' : x = g⁻¹ • v := by rw [← h,inv_smul_smul]
      simp [h']
    · have h' : x ≠ g⁻¹ • v := by intro h'; apply h; rw [h',smul_inv_smul]
      simp [h,h']

def diagonalMap (f : V → W) (hf : ∀ (g : G) (v : V), f (g • v) = g • f v) :
    FunctionalTree.diagonalRep (V := V) A ⟶ FunctionalTree.diagonalRep (V := W) A :=
  Rep.ofHom ⟨Finsupp.lmapDomain A k f,by
    intro g
    apply Finsupp.lhom_ext
    intro v a
    simp [hf]⟩

@[simp] lemma diagonalMap_single (f : V → W) (hf : ∀ (g : G) (v : V), f (g • v) = g • f v) (v : V) (a : A) :
    diagonalMap A f hf (Finsupp.single v a) = Finsupp.single (f v) a := by
  change Finsupp.mapDomain f (Finsupp.single v a) = _
  exact Finsupp.mapDomain_single

def diagonalIso (e : V ≃ W) (he : ∀ (g : G) (v : V), e (g • v) = g • e v) :
    FunctionalTree.diagonalRep (V := V) A ≅ FunctionalTree.diagonalRep (V := W) A := by
  have hi (g : G) (w : W) : e.symm (g • w) = g • e.symm w := by
    apply e.injective
    rw [e.apply_symm_apply,he,e.apply_symm_apply]
  exact {
    hom := diagonalMap A e he
    inv := diagonalMap A e.symm hi
    hom_inv_id := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply Finsupp.lhom_ext
      intro v a
      change diagonalMap A e.symm hi (diagonalMap A e he (Finsupp.single v a)) = Finsupp.single v a
      simp only [diagonalMap_single,e.symm_apply_apply]
      rfl
    inv_hom_id := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply Finsupp.lhom_ext
      intro v a
      change diagonalMap A e he (diagonalMap A e.symm hi (Finsupp.single v a)) = Finsupp.single v a
      simp only [diagonalMap_single,e.apply_symm_apply]
      rfl }

variable (j : Orbits (G := G) V)

def orbitInclusion : FunctionalTree.diagonalRep (V := j.orbit) A ⟶
    FunctionalTree.diagonalRep (V := V) A := diagonalMap A Subtype.val (fun _ _ => rfl)

def orbitProjection : FunctionalTree.diagonalRep (V := V) A ⟶
    FunctionalTree.diagonalRep (V := j.orbit) A :=
  Rep.ofHom ⟨Finsupp.lsubtypeDomain j.orbit,by
    intro g
    apply LinearMap.ext
    intro z
    apply Finsupp.ext
    intro v
    change ((FunctionalTree.diagonalRep (V := V) A).ρ g z : V →₀ A) v.val =
      ((FunctionalTree.diagonalRep (V := j.orbit) A).ρ g (Finsupp.subtypeDomain _ z) : j.orbit →₀ A) v
    rw [diagonal_apply,diagonal_apply]
    rfl⟩

def orbitCosetIso : CosetInduction.cosetRep (MulAction.stabilizer G j.out) A ≅
    FunctionalTree.diagonalRep (V := j.orbit) A := by
  let e0 := (MulAction.orbitEquivQuotientStabilizer G j.out).symm
  let e1 : MulAction.orbit G j.out ≃ j.orbit :=
    Equiv.setCongr (MulAction.orbitRel.Quotient.orbit_eq_orbit_out j Quotient.out_eq').symm
  exact diagonalIso A (e0.trans e1) (fun g q => Subtype.ext (orbitCoset_equivariant j g q))

end OrbitCoefficients

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductFiniteResolutionBeginningOfComplex
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace ProductFiniteResolution
variable {k G : Type} [CommRing k] [Group G]
def Beginning.ofComplex (C : ChainComplex (Rep k G) ℕ)
    (ε : C.X 0 ⟶ Rep.trivial k G k) [Epi ε]
    (w : C.d 1 0 ≫ ε = 0) (he0 : (ShortComplex.mk (C.d 1 0) ε w).Exact)
    (he1 : C.ExactAt 1) (α : ℕ → Type) [∀ n, Finite (α n)]
    (e : ∀ n, C.X n ≅ Rep.free k G (α n)) : Beginning (Rep.trivial k G k) where
  α₀ := α 0
  α₁ := α 1
  α₂ := α 2
  d₁ := (e 1).inv ≫ C.d 1 0 ≫ (e 0).hom
  d₂ := (e 2).inv ≫ C.d 2 1 ≫ (e 1).hom
  ε := (e 0).inv ≫ ε
  d₂_d₁ := by simp only [Category.assoc,Iso.hom_inv_id_assoc,← Category.assoc (C.d 2 1),
    C.d_comp_d,zero_comp,comp_zero]
  d₁_ε := by simp only [Category.assoc,Iso.hom_inv_id_assoc,w,comp_zero]
  exact₁ := by
    have he := (HomologicalComplex.exactAt_iff' C 2 1 0 (by simp) (by simp)).mp he1
    apply (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk (e 2) (e 1) (e 0)
      ((e 2).hom_inv_id_assoc (C.d 2 1 ≫ (e 1).hom))
      ((e 1).hom_inv_id_assoc (C.d 1 0 ≫ (e 0).hom)))).mp he
  exact₀ := by
    let E := ShortComplex.mk (C.d 1 0) ε w
    let F := ShortComplex.mk ((e 1).inv ≫ C.d 1 0 ≫ (e 0).hom) ((e 0).inv ≫ ε)
      (by simp only [Category.assoc,Iso.hom_inv_id_assoc,w,comp_zero])
    let iso : E ≅ F := ShortComplex.isoMk (e 1) (e 0) (Iso.refl _)
      (by dsimp [E,F]; simp only [Iso.hom_inv_id_assoc])
      (by dsimp [E,F]; simp only [Iso.hom_inv_id_assoc,Category.comp_id])
    exact (ShortComplex.exact_iff_of_iso iso).mp he0

end ProductFiniteResolution

namespace OrbitBrown
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
attribute [-instance] AddCommGroup.toIntModule
variable {G V I : Type} [Group G] [MulAction G V]
abbrev perm (G V : Type) [Group G] [MulAction G V] :=
  FunctionalTree.diagonalRep (V := V) (Rep.trivial ℤ G ℤ)

@[simp] lemma perm_single (g : G) (v : V) (r : ℤ) :
    (perm G V).ρ g (Finsupp.single v r) = Finsupp.single (g • v) r := by
  rw [FunctionalTree.diagonalRep_single]
  rfl

variable (A : Rep ℤ G) in
def tensorPermIso : A ⊗ perm G V ≅ FunctionalTree.diagonalRep (V := V) A := by
  classical
  exact Rep.mkIso (Representation.Equiv.mk (((TensorProduct.comm ℤ A (V →₀ ℤ)).trans (TensorProduct.finsuppScalarLeft ℤ A V))) (fun g => by
    apply TensorProduct.ext
    apply DFunLike.ext
    intro a
    apply Finsupp.lhom_ext
    intro v r
    change ((TensorProduct.comm ℤ A (V →₀ ℤ)).trans (TensorProduct.finsuppScalarLeft ℤ A V))
      (A.ρ g a ⊗ₜ[ℤ] ((perm G V).ρ g (Finsupp.single v r))) =
      (FunctionalTree.diagonalRep (V := V) A).ρ g
        (((TensorProduct.comm ℤ A (V →₀ ℤ)).trans (TensorProduct.finsuppScalarLeft ℤ A V)) (a ⊗ₜ[ℤ] Finsupp.single v r))
    rw [perm_single]
    simp only [LinearEquiv.trans_apply, TensorProduct.comm_tmul, TensorProduct.finsuppScalarLeft_apply_tmul]
    rw [Finsupp.sum_single_index (by
      exact (congrArg (Finsupp.single (g • v)) (Module.zero_smul (R := ℤ) ((A.ρ g) a))).trans (Finsupp.single_zero _)), Finsupp.sum_single_index (by
      exact (congrArg (Finsupp.single v) (Module.zero_smul (R := ℤ) a)).trans (Finsupp.single_zero _))]
    rw [FunctionalTree.diagonalRep_single]
    exact congrArg (Finsupp.single (g • v)) ((A.ρ g).map_smul r a).symm))

end OrbitBrown

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SurjectiveTrivialInduction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace SurjectiveTrivialInduction
open _root_.CategoryTheory _root_.OAI.CategoryTheory _root_.Representation _root_.OAI.Representation
attribute [-instance] AddCommGroup.toIntModule
end SurjectiveTrivialInduction

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
namespace ProductGroupHomology
section
attribute [-instance] AddCommGroup.toIntModule
variable {G H α : Type} [Group G] [Group H]

variable (G H α) in
def freePermIso : Rep.res (MonoidHom.fst G H) (Rep.free ℤ G α) ≅ OrbitBrown.perm (G × H) (α × G) := by
  classical
  let e : (α →₀ MonoidAlgebra ℤ G) ≃ₗ[ℤ] ((α × G) →₀ ℤ) :=
    (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv ℤ)).trans (Finsupp.curryLinearEquiv ℤ).symm
  apply Rep.mkIso (Representation.Equiv.mk e ?_)
  intro g
  apply Finsupp.lhom_ext
  intro a b
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp only [Finsupp.single_zero,map_zero]
  | add x y hx hy => simp only [Finsupp.single_add,map_add,hx,hy]
  | single h r =>
    change e ((Rep.free ℤ G α).ρ g.1 (Finsupp.single a (.single h r))) =
      (OrbitBrown.perm (G × H) (α × G)).ρ g (e (Finsupp.single a (.single h r)))
    rw [Representation.free_single_single]
    have hs (h : G) : e (Finsupp.single a (.single h r)) = Finsupp.single (a,h) r := by
      ext x
      simp [e,Finsupp.single_apply]
    rw [hs,hs,OrbitBrown.perm_single]
    rfl

open scoped MonoidalCategory
end

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
attribute [-instance] AddCommGroup.toIntModule
end ProductGroupHomology

attribute [instance] AddCommGroup.toIntModule

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PosetTransport
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace PosetTransport
section
universe u v w
variable {P : Type u} [Preorder P] {Q : Type v} [Preorder Q]
variable {H : Type w} [Group H]
namespace Cocycle
variable (c : Cocycle P H)
def Potential (v : P → H) : Prop := ∀ {x y}, (h : x ≤ y) → v x * c.edge h = v y
def Trivial : Prop := ∃ v : P → H, c.Potential v
def pull (f : Q →o P) : Cocycle Q H where
  edge h := c.edge (f.monotone h)
  refl x := c.refl (f x)
  comp h k := c.comp (f.monotone h) (f.monotone k)
end Cocycle

def Connected (P : Type u) [Preorder P] : Prop :=
  ∀ x y : P, Relation.ReflTransGen Adj x y

section RankBelow
variable {R : Type*} [PartialOrder R]

namespace Cocycle
variable (r : R → ℕ) (hr : StrictMono r) (m : ℕ) (c : Cocycle (rankBelow r m) H)
variable (hlink : ∀ a, r a = m+1 → ∀ d : Cocycle (Set.Iio a) H, d.Trivial)
noncomputable def linkPotential (a : R) (ha : r a = m+1) : Set.Iio a → H :=
  (hlink a ha (c.pull (linkBelow r hr m a ha))).choose
lemma linkPotential_spec (a : R) (ha : r a = m+1) :
    (c.pull (linkBelow r hr m a ha)).Potential (linkPotential r hr m c hlink a ha) :=
  (hlink a ha (c.pull (linkBelow r hr m a ha))).choose_spec

noncomputable def nextEdge {x y : rankBelow r (m+1)} (h : x ≤ y) : H := by
  classical
  exact if hy : r y.val ≤ m then
    c.edge (x := ⟨x.val,(hr.monotone h).trans hy⟩) (y := ⟨y.val,hy⟩) h
  else if he : x = y then 1
  else (linkPotential r hr m c hlink y.val (by
    have hh := y.property; change r y.val ≤ m+1 at hh; omega)
    ⟨x.val,lt_of_le_of_ne h (fun hv => he (Subtype.ext hv))⟩)⁻¹

lemma nextEdge_old {x y : rankBelow r (m+1)} (h : x ≤ y) (hy : r y.val ≤ m) :
    nextEdge r hr m c hlink h =
      c.edge (x := ⟨x.val,(hr.monotone h).trans hy⟩) (y := ⟨y.val,hy⟩) h := by
  classical
  simp only [nextEdge,dite_eq_left hy]
lemma nextEdge_refl (x : rankBelow r (m+1)) : nextEdge r hr m c hlink (le_refl x) = 1 := by
  classical
  by_cases hx : r x.val ≤ m
  · rw [nextEdge_old r hr m c hlink _ hx]
    exact c.refl _
  · simp [nextEdge,hx]
lemma nextEdge_comp {x y z : rankBelow r (m+1)} (h : x ≤ y) (k : y ≤ z) :
    nextEdge r hr m c hlink h * nextEdge r hr m c hlink k =
      nextEdge r hr m c hlink (h.trans k) := by
  classical
  by_cases hz : r z.val ≤ m
  · have hy : r y.val ≤ m := (hr.monotone k).trans hz
    rw [nextEdge_old r hr m c hlink _ hy,nextEdge_old r hr m c hlink _ hz,
      nextEdge_old r hr m c hlink _ hz]
    exact c.comp _ _
  · by_cases hyz : y = z
    · subst z
      rw [nextEdge_refl,mul_one]
    · have hyz' : y.val < z.val := lt_of_le_of_ne k (fun he => hyz (Subtype.ext he))
      have hyr := hr hyz'
      have hzr := z.property
      change r z.val ≤ m+1 at hzr
      have hze : r z.val = m+1 := by omega
      have hy : r y.val ≤ m := by omega
      have hxz : x ≠ z := fun he => hyz (le_antisymm k (he ▸ h))
      have hv := linkPotential_spec r hr m c hlink z.val hze
        (x := ⟨x.val,lt_of_le_of_lt h hyz'⟩) (y := ⟨y.val,hyz'⟩) h
      rw [nextEdge_old r hr m c hlink _ hy]
      simp only [nextEdge,dite_eq_right hz,dite_eq_right hyz,dite_eq_right hxz]
      apply mul_left_cancel (a := linkPotential r hr m c hlink z.val hze
        ⟨x.val,lt_of_le_of_lt h hyz'⟩)
      rw [← mul_assoc,show linkPotential r hr m c hlink z.val hze
        ⟨x.val,lt_of_le_of_lt h hyz'⟩ * c.edge (x := ⟨x.val,(hr.monotone h).trans hy⟩)
          (y := ⟨y.val,hy⟩) h = linkPotential r hr m c hlink z.val hze ⟨y.val,hyz'⟩ from hv]
      simp only [mul_inv_cancel]

noncomputable def next : Cocycle (rankBelow r (m+1)) H where
  edge h := nextEdge r hr m c hlink h
  refl := nextEdge_refl r hr m c hlink
  comp := nextEdge_comp r hr m c hlink
end Cocycle
end RankBelow

variable {R : Type*} [PartialOrder R]
namespace Cocycle
variable (r : R → ℕ) (hr : StrictMono r) (h : ℕ)
variable (c : Cocycle (rankBelow r h) H)
variable (hlink : ∀ a, h < r a → ∀ d : Cocycle (Set.Iio a) H, d.Trivial)
noncomputable def extension : (k : ℕ) → Cocycle (rankBelow r (h+k)) H
  | 0 => c
  | k+1 => next r hr (h+k) (extension k)
    (fun a ha => hlink a (by omega))
noncomputable def extensionLabel (k : ℕ) {x y : R} (hxy : x ≤ y) (hy : r y ≤ h+k) : H :=
  (extension r hr h c hlink k).edge
    (x := ⟨x,(hr.monotone hxy).trans hy⟩) (y := ⟨y,hy⟩) hxy
lemma extensionLabel_succ (k : ℕ) {x y : R} (hxy : x ≤ y) (hy : r y ≤ h+k) :
    extensionLabel r hr h c hlink (k+1) hxy (Nat.le_trans hy (Nat.le_succ _)) =
      extensionLabel r hr h c hlink k hxy hy := by
  exact nextEdge_old r hr (h+k) _ _
    (x := ⟨x,(hr.monotone hxy).trans (hy.trans (Nat.le_succ _))⟩)
    (y := ⟨y,hy.trans (Nat.le_succ _)⟩) hxy hy
lemma extensionLabel_stable {i j : ℕ} (hij : i ≤ j) {x y : R}
    (hxy : x ≤ y) (hy : r y ≤ h+i) :
    extensionLabel r hr h c hlink j hxy (hy.trans (Nat.add_le_add_left hij h)) =
      extensionLabel r hr h c hlink i hxy hy := by
  induction j,hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    rw [extensionLabel_succ r hr h c hlink j hxy (hy.trans (Nat.add_le_add_left hij h))]
    exact ih

noncomputable def fullExtension : Cocycle R H where
  edge {x y} hxy := extensionLabel r hr h c hlink (r y) hxy (Nat.le_add_left _ _)
  refl x := (extension r hr h c hlink (r x)).refl ⟨x,Nat.le_add_left _ _⟩
  comp {x y z} hxy hyz := by
    have hz : r z ≤ h+r z := Nat.le_add_left _ _
    have hy : r y ≤ h+r y := Nat.le_add_left _ _
    rw [← extensionLabel_stable r hr h c hlink (hr.monotone hyz) hxy hy]
    exact (extension r hr h c hlink (r z)).comp
      (x := ⟨x,(hr.monotone (hxy.trans hyz)).trans hz⟩)
      (y := ⟨y,(hr.monotone hyz).trans hz⟩) (z := ⟨z,hz⟩) hxy hyz
end Cocycle
end

open OrderListChains OrderChains
end PosetTransport

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_TruncatedAlgebra
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding
noncomputable section
open scoped Classical

namespace WordCalculus
variable {M : Type*} [Monoid M] {m : ℕ} (C : WordCalculus M m)
variable (k : Type*) [CommSemiring k]

theorem ball_mono {b c : ℕ} (hbc : b ≤ c) : C.ball k b ≤ C.ball k c := by
  intro p hp w hw
  exact (hp hw).trans hbc

theorem ball_induction {b : ℕ} {P : MonoidAlgebra k M → Prop}
    (hp : ∀ w, C.grade w ≤ b → P (MonoidAlgebra.single w 1))
    (hz : P 0) (ha : ∀ p q, P p → P q → P (p+q))
    (hs : ∀ (a : k) p, P p → P (a • p)) {p : MonoidAlgebra k M}
    (h : p ∈ C.ball k b) : P p := by
  rw [ball, MonoidAlgebra.supported_eq_span_single] at h
  induction h using Submodule.span_induction with
  | mem p h => obtain ⟨w, hw, rfl⟩ := h; exact hp w hw
  | zero => exact hz
  | add p q _ _ hp hq => exact ha p q hp hq
  | smul a p _ hp => exact hs a p hp

theorem mul_mem_ball {p q : MonoidAlgebra k M} {b c : ℕ}
    (hp : p ∈ C.ball k b) (hq : q ∈ C.ball k c) : p*q ∈ C.ball k (b+c) := by
  apply C.ball_induction k (P := fun p => p*q ∈ C.ball k (b+c)) ?_ ?_ ?_ ?_ hp
  · intro u hu
    apply C.ball_induction k (P := fun q => MonoidAlgebra.single u 1*q ∈ C.ball k (b+c))
      ?_ ?_ ?_ ?_ hq
    · intro v hv
      rw [MonoidAlgebra.single_mul_single]
      exact C.single_mem_ball k (by rw [C.grade_mul]; omega) _
    · simp
    · intro x y hx hy
      rw [mul_add]
      exact (C.ball k (b+c)).add_mem hx hy
    · intro a x hx
      rw [mul_smul_comm]
      exact (C.ball k (b+c)).smul_mem a hx
  · simp
  · intro x y hx hy
    rw [add_mul]
    exact (C.ball k (b+c)).add_mem hx hy
  · intro a x hx
    rw [smul_mul_assoc]
    exact (C.ball k (b+c)).smul_mem a hx

@[simp] theorem collect_one : C.collect k 1 = 1 := by
  rw [MonoidAlgebra.one_def, C.collect_single, C.normal_one,
    ite_eq_right (Ne.symm C.omega_ne_one)]

@[simp] theorem collect_omega (a : k) :
    C.collect k (MonoidAlgebra.single C.omega a) = 0 := by
  simp [C.normal_omega]

theorem collect_mem_ball {p : MonoidAlgebra k M} {b : ℕ}
    (hp : p ∈ C.ball k b) (hb : b ≤ m) : C.collect k p ∈ C.ball k b := by
  classical
  apply C.ball_induction k (P := fun p => C.collect k p ∈ C.ball k b) ?_ ?_ ?_ ?_ hp
  · intro w hw
    rw [C.collect_single]
    split
    · exact (C.ball k b).zero_mem
    · exact C.single_mem_ball k ((C.nonincreasing w (hw.trans hb)).trans hw) 1
  · simp
  · intro x y hx hy
    rw [map_add]
    exact (C.ball k b).add_mem hx hy
  · intro a x hx
    rw [map_smul]
    exact (C.ball k b).smul_mem a hx

theorem collect_mul_right {p q : MonoidAlgebra k M} {b c : ℕ}
    (hp : p ∈ C.ball k b) (hq : q ∈ C.ball k c) (hbc : b+c ≤ m) :
    C.collect k (p * C.collect k q) = C.collect k (p*q) := by
  classical
  apply C.ball_induction k
    (P := fun p => C.collect k (p*C.collect k q) = C.collect k (p*q)) ?_ ?_ ?_ ?_ hp
  · intro u hu
    apply C.ball_induction k
      (P := fun q => C.collect k (MonoidAlgebra.single u 1*C.collect k q) =
        C.collect k (MonoidAlgebra.single u 1*q)) ?_ ?_ ?_ ?_ hq
    · intro v hv
      have hvn := C.nonincreasing v (by omega)
      have he := C.context (C.idempotent v (by omega)) u 1
        (by simp only [mul_one, C.grade_mul]; omega)
        (by simp only [mul_one, C.grade_mul]; omega)
      simp only [mul_one] at he
      rw [C.collect_single]
      by_cases hz : C.normal v = C.omega
      · rw [ite_eq_left hz, mul_zero, map_zero, MonoidAlgebra.single_mul_single, C.collect_single]
        have ha : C.normal (u*v) = C.omega := by
          rw [hz] at he
          exact he.symm.trans (by simpa using C.absorbs u 1)
        simp [ha]
      · rw [ite_eq_right hz, MonoidAlgebra.single_mul_single,
          MonoidAlgebra.single_mul_single, C.collect_single, C.collect_single, he]
    · simp
    · intro x y hx hy
      simp only [map_add, mul_add, hx, hy]
    · intro a x hx
      simp only [map_smul, mul_smul_comm, hx]
  · simp
  · intro x y hx hy
    simp only [add_mul, map_add, hx, hy]
  · intro a x hx
    simp only [smul_mul_assoc, map_smul, hx]

theorem collect_mul_left {p q : MonoidAlgebra k M} {b c : ℕ}
    (hp : p ∈ C.ball k b) (hq : q ∈ C.ball k c) (hbc : b+c ≤ m) :
    C.collect k (C.collect k p * q) = C.collect k (p*q) := by
  classical
  apply C.ball_induction k
    (P := fun p => C.collect k (C.collect k p*q) = C.collect k (p*q)) ?_ ?_ ?_ ?_ hp
  · intro u hu
    apply C.ball_induction k
      (P := fun q => C.collect k (C.collect k (MonoidAlgebra.single u 1)*q) =
        C.collect k (MonoidAlgebra.single u 1*q)) ?_ ?_ ?_ ?_ hq
    · intro v hv
      have hun := C.nonincreasing u (by omega)
      have he := C.context (C.idempotent u (by omega)) 1 v
        (by simp only [one_mul, C.grade_mul]; omega)
        (by simp only [one_mul, C.grade_mul]; omega)
      simp only [one_mul] at he
      rw [C.collect_single]
      by_cases hz : C.normal u = C.omega
      · rw [ite_eq_left hz, zero_mul, map_zero, MonoidAlgebra.single_mul_single, C.collect_single]
        have ha : C.normal (u*v) = C.omega := by
          rw [hz] at he
          exact he.symm.trans (by simpa using C.absorbs 1 v)
        simp [ha]
      · rw [ite_eq_right hz, MonoidAlgebra.single_mul_single,
          MonoidAlgebra.single_mul_single, C.collect_single, C.collect_single, he]
    · simp
    · intro x y hx hy
      simp only [mul_add, map_add, hx, hy]
    · intro a x hx
      simp only [mul_smul_comm, map_smul, hx]
  · simp
  · intro x y hx hy
    simp only [map_add, add_mul, hx, hy]
  · intro a x hx
    simp only [map_smul, smul_mul_assoc, hx]

end WordCalculus

end
end SimpleFInftyOvergroups.BoundedEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_TruncatedMatrix
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding.WordCalculus
noncomputable section
open scoped Classical

variable {M : Type*} [Monoid M] {m : ℕ} (C : WordCalculus M m)
variable (k : Type*) [CommRing k]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev MatrixBall (b : ℕ) (A : Matrix ι ι (MonoidAlgebra k M)) :=
  ∀ i j, A i j ∈ C.ball k b
abbrev ColumnBall (b : ℕ) (x : ι → MonoidAlgebra k M) := ∀ i, x i ∈ C.ball k b

def matrixCollect (A : Matrix ι ι (MonoidAlgebra k M)) : Matrix ι ι (MonoidAlgebra k M) :=
  A.map (C.collect k)
def columnCollect (x : ι → MonoidAlgebra k M) : ι → MonoidAlgebra k M :=
  fun i => C.collect k (x i)

@[simp] theorem matrixCollect_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MonoidAlgebra k M)) (i j : ι) :
    C.matrixCollect k A i j = C.collect k (A i j) := rfl
@[simp] theorem columnCollect_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → MonoidAlgebra k M) (i : ι) :
    C.columnCollect k x i = C.collect k (x i) := rfl

@[simp] theorem matrixCollect_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    C.matrixCollect k (1 : Matrix ι ι (MonoidAlgebra k M)) = 1 :=
  Matrix.map_one _ (map_zero _) (C.collect_one k)
@[simp] theorem matrixCollect_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    C.matrixCollect k (0 : Matrix ι ι (MonoidAlgebra k M)) = 0 :=
  Matrix.map_zero _ (map_zero _)
@[simp] theorem columnCollect_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    C.columnCollect k (0 : ι → MonoidAlgebra k M) = 0 := by
  funext i; exact (C.collect k).map_zero

@[simp] theorem matrixBall_one {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ℕ) :
    C.MatrixBall k b (1 : Matrix ι ι (MonoidAlgebra k M)) := by
  intro i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h, C.one_mem_ball]
@[simp] theorem matrixBall_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ℕ) :
    C.MatrixBall k b (0 : Matrix ι ι (MonoidAlgebra k M)) := by
  intro i j; exact (C.ball k b).zero_mem
@[simp] theorem columnBall_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ℕ) :
    C.ColumnBall k b (0 : ι → MonoidAlgebra k M) := by
  intro i; exact (C.ball k b).zero_mem

theorem matrixBall_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι (MonoidAlgebra k M)} {b c : ℕ}
    (hA : C.MatrixBall k b A) (hB : C.MatrixBall k c B) : C.MatrixBall k (b+c) (A*B) := by
  intro i j
  rw [Matrix.mul_apply]
  exact (C.ball k (b+c)).sum_mem (fun l _ => C.mul_mem_ball k (hA i l) (hB l j))

theorem columnBall_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι (MonoidAlgebra k M)} {x : ι → MonoidAlgebra k M}
    {b c : ℕ} (hA : C.MatrixBall k b A) (hx : C.ColumnBall k c x) :
    C.ColumnBall k (b+c) (A.mulVec x) := by
  intro i
  exact (C.ball k (b+c)).sum_mem (fun l _ => C.mul_mem_ball k (hA i l) (hx l))

theorem matrixCollect_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι (MonoidAlgebra k M)} {b : ℕ}
    (hA : C.MatrixBall k b A) (hb : b ≤ m) : C.MatrixBall k b (C.matrixCollect k A) := by
  intro i j; exact C.collect_mem_ball k (hA i j) hb

theorem columnCollect_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    {x : ι → MonoidAlgebra k M} {b : ℕ}
    (hx : C.ColumnBall k b x) (hb : b ≤ m) : C.ColumnBall k b (C.columnCollect k x) := by
  intro i; exact C.collect_mem_ball k (hx i) hb

theorem matrixCollect_mul_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι (MonoidAlgebra k M)} {b c : ℕ}
    (hA : C.MatrixBall k b A) (hB : C.MatrixBall k c B) (hbc : b+c ≤ m) :
    C.matrixCollect k (C.matrixCollect k A * B) = C.matrixCollect k (A*B) := by
  funext i j
  simp only [matrixCollect_apply, Matrix.mul_apply, map_sum]
  apply Finset.sum_congr rfl
  intro l _
  exact C.collect_mul_left k (hA i l) (hB l j) hbc

theorem matrixCollect_mul_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι (MonoidAlgebra k M)} {b c : ℕ}
    (hA : C.MatrixBall k b A) (hB : C.MatrixBall k c B) (hbc : b+c ≤ m) :
    C.matrixCollect k (A * C.matrixCollect k B) = C.matrixCollect k (A*B) := by
  funext i j
  simp only [matrixCollect_apply, Matrix.mul_apply, map_sum]
  apply Finset.sum_congr rfl
  intro l _
  exact C.collect_mul_right k (hA i l) (hB l j) hbc

theorem columnCollect_mulVec_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι (MonoidAlgebra k M)}
    {x : ι → MonoidAlgebra k M} {b c : ℕ}
    (hA : C.MatrixBall k b A) (hx : C.ColumnBall k c x) (hbc : b+c ≤ m) :
    C.columnCollect k ((C.matrixCollect k A).mulVec x) = C.columnCollect k (A.mulVec x) := by
  funext i
  simp only [columnCollect_apply, Matrix.mulVec, dotProduct, matrixCollect_apply, map_sum]
  apply Finset.sum_congr rfl
  intro l _
  exact C.collect_mul_left k (hA i l) (hx l) hbc

theorem columnCollect_mulVec_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι (MonoidAlgebra k M)}
    {x : ι → MonoidAlgebra k M} {b c : ℕ}
    (hA : C.MatrixBall k b A) (hx : C.ColumnBall k c x) (hbc : b+c ≤ m) :
    C.columnCollect k (A.mulVec (C.columnCollect k x)) = C.columnCollect k (A.mulVec x) := by
  funext i
  simp only [columnCollect_apply, Matrix.mulVec, dotProduct, map_sum]
  apply Finset.sum_congr rfl
  intro l _
  exact C.collect_mul_right k (hA i l) (hx l) hbc

def matrixPair (u : (Matrix ι ι (MonoidAlgebra k M))ˣ) :=
  (C.matrixCollect k u.val, C.matrixCollect k u.inv)

def UnitBall (b : ℕ) (u : (Matrix ι ι (MonoidAlgebra k M))ˣ) : Prop :=
  C.MatrixBall k b u.val ∧ C.MatrixBall k b u.inv

@[simp] theorem unitBall_one (b : ℕ) :
    C.UnitBall k b (1 : (Matrix ι ι (MonoidAlgebra k M))ˣ) :=
  ⟨C.matrixBall_one k b, C.matrixBall_one k b⟩

theorem unitBall_inv {u : (Matrix ι ι (MonoidAlgebra k M))ˣ} {b : ℕ}
    (hu : C.UnitBall k b u) : C.UnitBall k b u⁻¹ := ⟨hu.2, hu.1⟩

theorem unitBall_mul {u v : (Matrix ι ι (MonoidAlgebra k M))ˣ} {b c : ℕ}
    (hu : C.UnitBall k b u) (hv : C.UnitBall k c v) : C.UnitBall k (b+c) (u*v) := by
  refine ⟨C.matrixBall_mul k hu.1 hv.1, ?_⟩
  change C.MatrixBall k (b+c) (v.inv * u.inv)
  simpa only [Nat.add_comm] using C.matrixBall_mul k hv.2 hu.2

theorem matrixPair_inv {u v : (Matrix ι ι (MonoidAlgebra k M))ˣ}
    (he : C.matrixPair k u = C.matrixPair k v) : C.matrixPair k u⁻¹ = C.matrixPair k v⁻¹ :=
  Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)

end
end SimpleFInftyOvergroups.BoundedEncoding.WordCalculus

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_TruncatedAction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding
noncomputable section
open scoped Classical

namespace KeyBall
variable {X K : Type*} (C : KeyBall X K) (m : ℕ)

theorem leastCost_spec {k : K} (h : C.Represented m k) :
    C.leastCost m k ≤ m ∧ ∃ x ∈ C.ball (C.leastCost m k), C.key x = k := by
  rw [leastCost, dite_eq_left h]
  exact Nat.find_spec h

theorem leastCost_le {x : X} {b : ℕ} (hx : x ∈ C.ball b) (hb : b ≤ m) :
    C.leastCost m (C.key x) ≤ b := by
  rw [leastCost, dite_eq_left (C.represented_key m hx hb)]
  exact Nat.find_min' _ ⟨hb, x, hx, rfl⟩

variable [Nonempty X]

theorem representative_spec {k : K} (h : C.Represented m k) :
    C.representative m k ∈ C.ball (C.leastCost m k) ∧
      C.key (C.representative m k) = k := by
  have he := (C.leastCost_spec m h).2
  rw [representative, dite_eq_left he]
  exact Classical.choose_spec he

theorem canonical_mem {x : X} {b : ℕ} (hx : x ∈ C.ball b) (hb : b ≤ m) :
    C.canonical m x ∈ C.ball b :=
  C.mono (C.leastCost_le m hx hb)
    (C.representative_spec m (C.represented_key m hx hb)).1

theorem key_canonical {x : X} {b : ℕ} (hx : x ∈ C.ball b) (hb : b ≤ m) :
    C.key (C.canonical m x) = C.key x :=
  (C.representative_spec m (C.represented_key m hx hb)).2

end KeyBall

namespace WordCalculus
variable {M : Type*} [Monoid M] {m : ℕ} (C : WordCalculus M m)
variable (k : Type*) [CommRing k] {ι : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] rawMatrixAction

theorem matrixCollect_product {A B : Matrix ι ι (MonoidAlgebra k M)} {b c : ℕ}
    (hA : C.MatrixBall k b A) (hB : C.MatrixBall k c B) (hbc : b+c ≤ m) :
    C.matrixCollect k (C.matrixCollect k A * C.matrixCollect k B) = C.matrixCollect k (A*B) := by
  rw [C.matrixCollect_mul_left k hA (C.matrixCollect_mem k hB (by omega)) hbc,
    C.matrixCollect_mul_right k hA hB hbc]

theorem columnCollect_product {A : Matrix ι ι (MonoidAlgebra k M)} {x : ι → MonoidAlgebra k M}
    {b c : ℕ} (hA : C.MatrixBall k b A) (hx : C.ColumnBall k c x) (hbc : b+c ≤ m) :
    C.columnCollect k ((C.matrixCollect k A).mulVec (C.columnCollect k x)) =
      C.columnCollect k (A.mulVec x) := by
  rw [C.columnCollect_mulVec_left k hA (C.columnCollect_mem k hx (by omega)) hbc,
    C.columnCollect_mulVec_right k hA hx hbc]

def matrixActionCalculus (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ActionCalculus (Matrix ι ι (MonoidAlgebra k M))ˣ (ι → MonoidAlgebra k M)
      (Matrix ι ι (MonoidAlgebra k M) × Matrix ι ι (MonoidAlgebra k M))
      (ι → MonoidAlgebra k M) m where
  group :=
    { ball := C.UnitBall k
      mono := by
        intro b c hbc u hu
        exact ⟨fun i j => C.ball_mono k hbc (hu.1 i j),
          fun i j => C.ball_mono k hbc (hu.2 i j)⟩
      key := C.matrixPair k }
  point :=
    { ball := C.ColumnBall k
      mono := by
        intro b c hbc x hx i
        exact C.ball_mono k hbc (hx i)
      key := C.columnCollect k }
  one_mem := C.unitBall_one k
  inv_mem := C.unitBall_inv k
  mul_mem := C.unitBall_mul k
  smul_mem := fun hu hx => C.columnBall_mulVec k hu.1 hx
  inv_congr := C.matrixPair_inv k
  mul_congr := by
    intro b c b' c' u v u' v' hu hv hu' hv' hb hb' heu hev
    apply Prod.ext
    · change C.matrixCollect k (u.val*v.val) = C.matrixCollect k (u'.val*v'.val)
      rw [← C.matrixCollect_product k hu.1 hv.1 hb,
        ← C.matrixCollect_product k hu'.1 hv'.1 hb']
      rw [show C.matrixCollect k u.val = C.matrixCollect k u'.val from congrArg Prod.fst heu,
        show C.matrixCollect k v.val = C.matrixCollect k v'.val from congrArg Prod.fst hev]
    · change C.matrixCollect k (v.inv*u.inv) = C.matrixCollect k (v'.inv*u'.inv)
      rw [← C.matrixCollect_product k hv.2 hu.2 (by omega),
        ← C.matrixCollect_product k hv'.2 hu'.2 (by omega)]
      rw [show C.matrixCollect k u.inv = C.matrixCollect k u'.inv from congrArg Prod.snd heu,
        show C.matrixCollect k v.inv = C.matrixCollect k v'.inv from congrArg Prod.snd hev]
  smul_congr := by
    intro b c b' c' u x u' x' hu hx hu' hx' hb hb' heu hex
    change C.columnCollect k (u.val.mulVec x) = C.columnCollect k (u'.val.mulVec x')
    rw [← C.columnCollect_product k hu.1 hx hb, ← C.columnCollect_product k hu'.1 hx' hb']
    rw [show C.matrixCollect k u.val = C.matrixCollect k u'.val from congrArg Prod.fst heu,
      show C.columnCollect k x = C.columnCollect k x' from hex]

end WordCalculus
end
end SimpleFInftyOvergroups.BoundedEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_BoundedContexts
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding.ActionCalculus
variable {V X K L : Type*} [Group V] [MulAction V X] {m : ℕ}
  (C : ActionCalculus V X K L m) [DecidableEq L]

theorem display_step (a : C.Letter) (f t : C.Form) {d : ℕ}
    (hb : a.cost C + f.cost C + t.cost C ≤ d) (hm : 3*d ≤ m) :
    (C.run (C.display (C.step a f)) t).key C =
      (C.step a (C.run (C.display f) t)).key C := by
  cases f with
  | none => simp [display]
  | some p =>
    rcases p with ⟨l,g,r⟩
    cases a with
    | zero => simp [display]
    | pre x => simp only [step,display,List.map_cons,List.cons_append,run_cons]
    | grp h =>
      cases l with
      | nil =>
        simp only [step,display,List.map_nil,List.nil_append,run_cons]
        exact (C.step_multiply h g _).symm
      | cons x l =>
        simp only [step,display,List.map_cons,List.cons_append,run_cons]
        exact congrArg (Form.key C) (C.step_group_pre h x _).symm
    | del y =>
      cases l with
      | nil =>
        simp only [step,display,List.map_nil,List.nil_append,List.reverse_append,
          List.reverse_singleton,List.map_cons,List.map_nil,
          List.singleton_append,run_cons]
        apply (C.step_identity (C.step (.del (C.act (C.inverse g) y))
          (C.run (r.reverse.map .del) t))).trans
        symm
        apply C.step_delete_group y g _ (hm := hm)
        have hc := C.run_cost (r.reverse.map Letter.del) t
        have hr : C.wordCost (r.reverse.map Letter.del) = (r.map WithBound.cost).sum := by
          rw [wordCost_dels,List.map_reverse,List.sum_reverse]
        rw [hr] at hc
        change y.cost + (0+g.cost+(r.map WithBound.cost).sum) + t.cost C ≤ d at hb
        omega
      | cons x l =>
        simp only [step]
        by_cases h : y.key = x.key
        · rw [ite_eq_left h]
          simp only [display,List.map_cons,List.cons_append,run_cons]
          exact congrArg (Form.key C) ((C.step_delete_pre y x _).trans (ite_eq_left h)).symm
        · rw [ite_eq_right h]
          simp only [display,List.map_cons,List.cons_append,run_cons,run_nil,step_zero]
          exact congrArg (Form.key C) ((C.step_delete_pre y x _).trans (ite_eq_right h)).symm

theorem run_display_normalize (w : List C.Letter) (t : C.Form) {d : ℕ}
    (hb : C.wordCost w + t.cost C ≤ d) (hm : 3*d ≤ m) :
    (C.run w t).key C = (C.run (C.display (C.normalize w)) t).key C := by
  induction w with
  | nil =>
    simpa only [normalize,run_nil,display,List.map_nil,List.reverse_nil,List.nil_append,
      run_cons] using (C.step_identity t).symm
  | cons a w ih =>
    have hc := C.normalize_cost w
    have ht : C.wordCost w + t.cost C ≤ d := by simp only [wordCost_cons] at hb; omega
    have he := C.step_congr (a := a) rfl (ih ht)
      (hb := by have := C.run_cost w t; simp only [wordCost_cons] at hb; omega)
      (hb' := by
        have hh := C.run_cost (C.display (C.normalize w)) t
        rw [display_cost] at hh
        simp only [wordCost_cons] at hb
        omega)
    rw [run_cons]
    exact he.trans (C.display_step a (C.normalize w) t
      (by simp only [wordCost_cons] at hb; omega) hm).symm

theorem normalize_right_context {u v b : List C.Letter} {d : ℕ}
    (he : (C.normalize u).key C = (C.normalize v).key C)
    (hu : C.wordCost (u++b) ≤ d) (hv : C.wordCost (v++b) ≤ d) (hm : 3*d ≤ m) :
    (C.normalize (u++b)).key C = (C.normalize (v++b)).key C := by
  have hb := C.normalize_cost b
  have huc := C.normalize_cost u
  have hvc := C.normalize_cost v
  simp only [wordCost_append] at hu hv
  change (C.run (u++b) _).key C = (C.run (v++b) _).key C
  rw [run_append,run_append]
  change (C.run u (C.normalize b)).key C = (C.run v (C.normalize b)).key C
  rw [C.run_display_normalize u (C.normalize b) (by omega) hm,
    C.run_display_normalize v (C.normalize b) (by omega) hm]
  apply C.run_congr (C.display_congr he) rfl
  · rw [display_cost]; omega
  · rw [display_cost]; omega

theorem normalize_context {u v a b : List C.Letter} {d : ℕ}
    (he : (C.normalize u).key C = (C.normalize v).key C)
    (hu : C.wordCost (a++u++b) ≤ d) (hv : C.wordCost (a++v++b) ≤ d) (hm : 3*d ≤ m) :
    (C.normalize (a++u++b)).key C = (C.normalize (a++v++b)).key C := by
  simp only [wordCost_append] at hu hv
  rw [List.append_assoc,List.append_assoc]
  apply C.normalize_left_context (C.normalize_right_context he
    (by simp only [wordCost_append]; omega) (by simp only [wordCost_append]; omega) hm)
  · simp only [wordCost_append]; omega
  · simp only [wordCost_append]; omega

theorem normalize_zero_context {u a b : List C.Letter} {d : ℕ}
    (he : (C.normalize u).key C = none)
    (hu : C.wordCost (a++u++b) ≤ d) (hm : 3*d ≤ m) :
    (C.normalize (a++u++b)).key C = none := by
  have hz : (C.normalize [.zero]).key C = none := rfl
  have hh := C.normalize_context (he.trans hz.symm) hu
    (show C.wordCost (a++[.zero]++b) ≤ d from by
      simp only [wordCost_append,wordCost_cons,wordCost_nil,Letter.cost] at hu ⊢
      omega) hm
  simpa only [normalize,run_append,run_cons,step_zero,run_none,Form.key,
    Option.map_none] using hh

end SimpleFInftyOvergroups.BoundedEncoding.ActionCalculus

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_NamedActions
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding.NamedAction

namespace Operations
variable {G X K L : Type*} (N : Operations G X)

variable [DecidableEq L]

theorem totalStep_cost (kx : X → L) (a : Letter G X) (f : Form G X) :
    N.formCost (N.totalStep kx a f) ≤ N.letterCost a + N.formCost f := by
  cases f with
  | none => simp [formCost]
  | some p =>
    rcases p with ⟨l,g,r⟩
    rcases a with h | (x | y)
    · cases l <;> simp [totalStep,plan,formCost,letterCost,N.cost_mul,N.cost_act] <;> omega
    · simp [totalStep,plan,formCost,letterCost]; omega
    · cases y with
      | none => simp [totalStep,plan,formCost,letterCost]
      | some y =>
        cases l with
        | nil => simp [totalStep,plan,formCost,letterCost,N.cost_one,N.cost_act,N.cost_inv]; omega
        | cons x l =>
          by_cases h : kx y = kx x <;> simp [totalStep,plan,h,formCost,letterCost]; omega

theorem totalRun_cost (kx : X → L) (w : List (Letter G X)) (f : Form G X) :
    N.formCost (N.totalRun kx w f) ≤ N.wordCost w + N.formCost f := by
  induction w with
  | nil => simp
  | cons a w ih =>
    exact (N.totalStep_cost kx a (N.totalRun kx w f)).trans (by rw [wordCost_cons]; omega)

theorem totalNormalize_cost (kx : X → L) (w : List (Letter G X)) :
    N.formCost (N.totalNormalize kx w) ≤ N.wordCost w := by
  simpa [totalNormalize,formCost,N.cost_one] using N.totalRun_cost kx w (some ([],N.one,[]))

end Operations

namespace Interpretation
variable {G X V Y K L : Type*} [Group V] [MulAction V Y] {m : ℕ}
  {N : Operations G X} {C : ActionCalculus V Y K L m} (I : Interpretation N C)

variable [DecidableEq L]

theorem totalTest_context {u v a b : List (Letter G X)} {d : ℕ}
    (h : N.totalTest I.gkey I.xkey u = N.totalTest I.gkey I.xkey v)
    (hu : N.wordCost (a++u++b) ≤ d) (hv : N.wordCost (a++v++b) ≤ d) (hm : 3*d ≤ m) :
    N.totalTest I.gkey I.xkey (a++u++b) = N.totalTest I.gkey I.xkey (a++v++b) := by
  simp only [I.totalTest,List.map_append] at h ⊢
  apply C.normalize_context h (hm := hm)
  · simpa only [← List.map_append,I.word_cost] using hu
  · simpa only [← List.map_append,I.word_cost] using hv

theorem totalTest_zero_context {u a b : List (Letter G X)} {d : ℕ}
    (h : N.totalTest I.gkey I.xkey u = none)
    (hu : N.wordCost (a++u++b) ≤ d) (hm : 3*d ≤ m) :
    N.totalTest I.gkey I.xkey (a++u++b) = none := by
  simp only [I.totalTest,List.map_append] at h ⊢
  exact C.normalize_zero_context h (by simpa only [← List.map_append,I.word_cost] using hu) hm

end Interpretation
end SimpleFInftyOvergroups.BoundedEncoding.NamedAction

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_ContextualTables
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes.Bootstrap Relation

namespace CodeTable
variable {A S Q : Type*} {r : S → S → Prop} [Std.Trichotomous r]
variable (C : DelimiterCode A S) (E : FiniteSearch C) (wf : WellFounded r)
  (q : List A → Option Q) (z : S)

theorem whole_steps (hzero : q [] ≠ none) {n : ℕ} {v : List A} (hv : (C.encode v).length ≤ n) :
    Steps (table C E wf q z n) (C.encode v) (output C wf q z v) := by
  by_cases hn : v = []
  · subst v
    rw [C.encode_nil, output_nil C wf q z hzero]
  by_cases he : output C wf q z v = C.encode v
  · rw [he]
  · exact .single (by simpa using Step.apply ((mem_table C E wf q z).mpr
      ⟨v,hv,hn,he,rfl,rfl⟩) [] [])

end CodeTable
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_FamilyTables
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes.Bootstrap Relation

namespace Families
variable {I S : Type*} {A Q : I → Type*} [Fintype I] [Fintype S]
variable {r : S → S → Prop} [Std.Trichotomous r]
variable (C : ∀ i, DelimiterCode (A i) S) (E : ∀ i, FiniteSearch (C i))
  (wf : WellFounded r) (q : ∀ i, List (A i) → Option (Q i)) (z : S)

noncomputable def table (n : ℕ) : List (List S × List S) :=
  Base.absorption z ++ (Static.letters I).flatMap (fun i => CodeTable.table (C i) (E i) wf (q i) z n)

end Families
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_BoundedFamilyTests
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes Bootstrap BoundedEncoding
noncomputable section
open scoped Classical

structure TestCertificate {A S Q : Type*}
    (C : DelimiterCode A S) (f : List A → Part (Option Q)) (n : ℕ) : Prop where
  total : ∀ w, (C.encode w).length ≤ n → (f w).Dom
  nonzero : Search.value f [] ≠ none
  contextual : CodeTable.Contextual C (Search.value f) n
  ideal : CodeTable.ZeroIdeal C (Search.value f) n

end
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_CodeEmbedding
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes.Bootstrap Relation

namespace CodeTable
variable {A S Q : Type*} {r : S → S → Prop} [Std.Trichotomous r]
variable (C : DelimiterCode A S) (E : FiniteSearch C) (wf : WellFounded r)
  (q : List A → Option Q) (z : S)

 theorem canonical_no_infix (hc : ∀ n, Contextual C q n) (hi : ∀ n, ZeroIdeal C q n)
    {w : List A} (hw : q w ≠ none) {n : ℕ} {u v : List S}
    (hp : (u,v) ∈ table C E wf q z n) :
    ¬ u <:+: C.encode (EncodedCanonical.least C wf q w) := by
  obtain ⟨c,_,hcn,hn,rfl,rfl⟩ := (mem_table C E wf q z).mp hp
  rintro ⟨x,y,he⟩
  obtain ⟨a,b,hab,hx,hy⟩ := C.occurrence_decode hcn he.symm
  have hq : q (a++c++b) = q w := hab ▸ EncodedCanonical.least_class C wf q w
  by_cases hz : q c = none
  · exact hw (hq.symm.trans (hi _ a b c le_rfl hz))
  · have hlt : List.Shortlex r (C.encode (EncodedCanonical.least C wf q c)) (C.encode c) := by
      rcases EncodedCanonical.least_lt_or_eq C wf q c with h | h
      · exact h
      · exact False.elim (hn (by simp [output,hz,h]))
    have hb : (C.encode (a++EncodedCanonical.least C wf q c++b)).length ≤
        (C.encode (a++c++b)).length := by
      have hh := EncodedCanonical.least_length C wf q c
      simp only [DelimiterCode.encode_append,List.length_append]
      omega
    have hclass : q (a++EncodedCanonical.least C wf q c++b) = q w :=
      (hc _ a b _ c hb le_rfl (EncodedCanonical.least_class C wf q c)).trans hq
    apply EncodedCanonical.least_global_min C wf q hclass
    rw [hab]
    simpa only [DelimiterCode.encode_append] using shortlex_context hlt (C.encode a) (C.encode b)

 theorem canonical_irreducible {rs : List (List S × List S)} {n : ℕ}
    (hiso : ∀ p ∈ rs, p ∈ table C E wf q z n ∨ ∃ s ∈ p.1, s ∉ C.alphabet)
    (hc : ∀ k, Contextual C q k) (hi : ∀ k, ZeroIdeal C q k)
    {w : List A} (hw : q w ≠ none) :
    Irreducible (Step rs) (C.encode (EncodedCanonical.least C wf q w)) := by
  apply irreducible_of_no_infix
  intro p hp hif
  rcases hiso p hp with hp | ⟨s,hs,hn⟩
  · exact canonical_no_infix C E wf q z hc hi hw hp hif
  · exact hn (C.mem_alphabet_of_mem_encode (hif.subset hs))

 theorem output_eq_iff (hz : z ∉ C.alphabet) (u v : List A) :
    output C wf q z u = output C wf q z v ↔ q u = q v := by
  constructor
  · intro he
    by_cases hu : q u = none <;> by_cases hv : q v = none
    · exact hu.trans hv.symm
    · have hh : z ∈ C.encode (EncodedCanonical.least C wf q v) := by
        rw [output,ite_eq_left hu,output,ite_eq_right hv] at he
        rw [←he]; simp
      exact False.elim (hz (C.mem_alphabet_of_mem_encode hh))
    · have hh : z ∈ C.encode (EncodedCanonical.least C wf q u) := by
        rw [output,ite_eq_right hu,output,ite_eq_left hv] at he
        rw [he]; simp
      exact False.elim (hz (C.mem_alphabet_of_mem_encode hh))
    · rw [output,ite_eq_right hu,output,ite_eq_right hv] at he
      have h := C.encode_injective he
      exact (EncodedCanonical.least_class C wf q u).symm.trans
        ((congrArg q h).trans (EncodedCanonical.least_class C wf q v))
  · exact output_congr C wf q z
end CodeTable

namespace CodeQuotient
open FiniteAlgebraicEnvelopes.Bootstrap.Quotient
variable {A S M : Type*} [DecidableEq S] [Monoid M]
variable {T : ℕ → Part (List (List S × List S))}
variable (C : DelimiterCode A S)

def codeHom : FreeMonoid A →* Mon T where
  toFun w := present T (C.encode w.toList)
  map_one' := by simp
  map_mul' u v := by simp only [FreeMonoid.toList_mul,DelimiterCode.encode_append,present_append]

variable (e : FreeMonoid A →* M) (he : Function.Surjective e)
  (hc : ∀ u v : List A,present T (C.encode u)=present T (C.encode v) ↔
    e (FreeMonoid.ofList u)=e (FreeMonoid.ofList v))

noncomputable def descendCode : M →* Mon T where
  toFun x := codeHom C (he x).choose
  map_one' := by
    have hx : e (he 1).choose=e 1 := (he 1).choose_spec.trans e.map_one.symm
    exact (hc _ []).mpr hx
  map_mul' x y := by
    change present T (C.encode ((he (x*y)).choose.toList)) =
      present T (C.encode ((he x).choose.toList))*present T (C.encode ((he y).choose.toList))
    rw [←present_append,←DelimiterCode.encode_append]
    apply (hc _ _).mpr
    change e (he (x*y)).choose=e ((he x).choose * (he y).choose)
    rw [e.map_mul,(he (x*y)).choose_spec,(he x).choose_spec,(he y).choose_spec]

omit [DecidableEq S] in
theorem descendCode_apply (w : List A) :
    descendCode C e he hc (e (FreeMonoid.ofList w))=present T (C.encode w) :=
  (hc _ w).mpr (he (e (FreeMonoid.ofList w))).choose_spec

omit [DecidableEq S] in
theorem descendCode_injective : Function.Injective (descendCode C e he hc) := by
  intro x y h
  exact (he x).choose_spec.symm.trans (((hc _ _).mp h).trans (he y).choose_spec)
end CodeQuotient
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_CommonCompiler
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding.WordCalculus
noncomputable section
variable {M N : Type*} [Monoid M] [Monoid N] {m : ℕ}

def retract (C : WordCalculus M m) (r : N →* M) (i : M →* N)
    (hi : ∀ x, r (i x) = x) (grade : N → ℕ)
    (hg1 : grade 1 = 0) (hgm : ∀ x y, grade (x*y) = grade x + grade y)
    (hgi : ∀ x, grade (i x) = C.grade x)
    (hgr : ∀ x, C.grade (r x) ≤ grade x) : WordCalculus N m where
  grade := grade
  grade_one := hg1
  grade_mul := hgm
  omega := i C.omega
  grade_omega := (hgi _).trans C.grade_omega
  omega_ne_one h := C.omega_ne_one (by simpa only [hi, map_one] using congrArg r h)
  normal x := i (C.normal (r x))
  normal_one := by simp only [map_one, C.normal_one]
  normal_omega := by simp only [hi, C.normal_omega]
  nonincreasing x hx := by
    rw [hgi]
    exact (C.nonincreasing _ ((hgr _).trans hx)).trans (hgr _)
  idempotent x hx := by rw [hi, C.idempotent _ ((hgr _).trans hx)]
  context h a b hu hv := by
    have he := congrArg r h
    simp only [hi] at he
    apply congrArg i
    simp only [map_mul]
    apply C.context he (r a) (r b)
    · simpa only [map_mul] using (hgr _).trans hu
    · simpa only [map_mul] using (hgr _).trans hv
  absorbs a b := by simp only [map_mul, hi, C.absorbs]

end
end SimpleFInftyOvergroups.BoundedEncoding.WordCalculus

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_ContractedNormalForms
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Contracted.countableAlgebra _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.SemanticEncoding
noncomputable section
open FiniteAlgebraicEnvelopes
open scoped Classical

namespace NormalPresentation
variable {M K : Type*} [Monoid M] [MonoidWithZero K] (P : NormalPresentation M K)
variable (k : Type*) [CommRing k]

def algebraMap : MonoidAlgebra k M →ₐ[k] Contracted.Algebra k K :=
  (Contracted.quotient k K).comp (MonoidAlgebra.mapDomainAlgHom k k P.q)

@[simp] theorem algebraMap_single (w : M) (c : k) :
    P.algebraMap k (MonoidAlgebra.single w c) = Contracted.basis k K (P.q w) c := by
  simp [algebraMap, Contracted.basis]

end NormalPresentation
end
end SimpleFInftyOvergroups.SemanticEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EffectiveFold
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CoreDeck.action _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace SimpleFInftyOvergroups.EffectiveNames
namespace PartialFold
variable {P A B : Type*} (f : P × A × B → Part B)

variable [Primcodable P] [Primcodable A] [Primcodable B]
variable (hf : Partrec f)

include hf in
theorem partrec_loop : Partrec (loop f) := by
  let S := P × List A × B
  have hh : Computable (fun s : S => s.2.1.head?) :=
    Primrec.list_head?.to_comp.comp (Computable.fst.comp Computable.snd)
  have he : Partrec₂ (fun (s : S) (a : A) =>
      (f (s.1,a,s.2.2)).map (fun c => (Sum.inr (s.1,s.2.1.tail,c) : B ⊕ S))) := by
    have hc : Computable (fun x : S × A => (x.1.1,x.2,x.1.2.2)) :=
      (Computable.fst.comp Computable.fst).pair
        (Computable.snd.pair (Computable.snd.comp (Computable.snd.comp Computable.fst)))
    apply (hf.comp hc).map
    exact (Computable.sumInr.comp
      ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        ((Primrec.list_tail.to_comp.comp
          (Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst)))).pair
          Computable.snd))).to₂
  exact (Partrec.optionCasesOn_right hh
    (Computable.sumInl.comp (Computable.snd.comp Computable.snd)) he).of_eq
    (by intro ⟨p,w,b⟩; cases w <;> rfl)

include hf in
theorem partrec_left : Partrec (fun x : P × List A × B => left f x.1 x.2.1 x.2.2) :=
  (Partrec.fix (partrec_loop f hf)).of_eq (fun ⟨p,w,b⟩ => fix_loop f p w b)

include hf in
theorem partrec_right : Partrec (fun x : P × List A × B => right f x.1 x.2.1 x.2.2) := by
  have hc : Computable (fun x : P × List A × B => (x.1,x.2.1.reverse,x.2.2)) :=
    Computable.fst.pair ((Computable.list_reverse.comp (Computable.fst.comp Computable.snd)).pair
      (Computable.snd.comp Computable.snd))
  exact ((partrec_left f hf).comp hc).of_eq (fun ⟨p,w,b⟩ => (right_eq_left_reverse f p w b).symm)

end PartialFold
end SimpleFInftyOvergroups.EffectiveNames

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EffectiveActions
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace SimpleFInftyOvergroups.BoundedEncoding.NamedAction
open FiniteAlgebraicEnvelopes FiniteAlgebraicEnvelopes.Bootstrap
namespace Operations
variable {G X K L : Type*} (N : Operations G X) [DecidableEq L]

def key (fg : G → Part K) (fx : X → Part L) : Form G X → Part (Result K L)
  | none => Part.some none
  | some (l,g,r) => (fg g).bind fun k =>
      (Effect.traverse fx l).bind fun ls =>
        (Effect.traverse fx r).map fun rs => some (ls,k,rs)

def test (fg : G → Part K) (fx : X → Part L) (w : List (Letter G X)) :
    Part (Result K L) :=
  (N.run fx w (some ([],N.one,[]))).bind (key fg fx)

theorem step_full (fx : X → Part L) (kx : X → L) {d : ℕ}
    (hx : ∀ x, N.xcost x ≤ d → kx x ∈ fx x)
    (a : Letter G X) (f : Form G X) (hb : N.letterCost a + N.formCost f ≤ d) :
    N.totalStep kx a f ∈ N.step fx a f := by
  cases f with
  | none => exact Part.mem_some _
  | some p =>
    rcases p with ⟨l,g,r⟩
    rcases a with h | (x | y)
    · cases l <;> exact Part.mem_some _
    · exact Part.mem_some _
    · cases y with
      | none => exact Part.mem_some _
      | some y =>
        cases l with
        | nil => exact Part.mem_some _
        | cons x l =>
          have hy : N.xcost y ≤ d := by simp only [letterCost,formCost] at hb; omega
          have hh : N.xcost x ≤ d := by
            simp only [letterCost,formCost,List.map_cons,List.sum_cons] at hb; omega
          have ht := compare_full fx kx (hx _ hy) (hx _ hh)
          simpa only [step,plan,totalStep,Sum.elim_inr,Bool.cond_decide] using
            Part.mem_map (fun b => bif b then some (l,g,r) else none) ht

theorem run_full (fx : X → Part L) (kx : X → L) {d : ℕ}
    (hx : ∀ x, N.xcost x ≤ d → kx x ∈ fx x)
    (w : List (Letter G X)) (f : Form G X) (hb : N.wordCost w + N.formCost f ≤ d) :
    N.totalRun kx w f ∈ N.run fx w f := by
  induction w with
  | nil => exact Part.mem_some _
  | cons a w ih =>
    refine Part.mem_bind_iff.mpr ⟨N.totalRun kx w f,ih ?_,N.step_full fx kx hx a _ ?_⟩
    · rw [wordCost_cons] at hb; omega
    · have hc := N.totalRun_cost kx w f
      rw [wordCost_cons] at hb
      omega

omit [DecidableEq L] in
theorem key_full (fg : G → Part K) (fx : X → Part L) (kg : G → K) (kx : X → L)
    {d : ℕ} (hg : ∀ g, N.gcost g ≤ d → kg g ∈ fg g)
    (hx : ∀ x, N.xcost x ≤ d → kx x ∈ fx x)
    (f : Form G X) (hb : N.formCost f ≤ d) : formKey kg kx f ∈ key fg fx f := by
  cases f with
  | none => exact Part.mem_some _
  | some p =>
    rcases p with ⟨l,g,r⟩
    change (l.map N.xcost).sum + N.gcost g + (r.map N.xcost).sum ≤ d at hb
    have hl : l.map kx ∈ Effect.traverse fx l := by
      apply Search.traverse_map
      intro x hm
      apply hx
      have hh : N.xcost x ≤ (l.map N.xcost).sum := List.single_le_sum (by simp) _
        (List.mem_map.mpr ⟨x,hm,rfl⟩)
      omega
    have hr : r.map kx ∈ Effect.traverse fx r := by
      apply Search.traverse_map
      intro x hm
      apply hx
      have hh : N.xcost x ≤ (r.map N.xcost).sum := List.single_le_sum (by simp) _
        (List.mem_map.mpr ⟨x,hm,rfl⟩)
      omega
    exact Part.mem_bind_iff.mpr ⟨_,hg g (by omega),Part.mem_bind_iff.mpr ⟨_,hl,Part.mem_map _ hr⟩⟩

theorem test_full (fg : G → Part K) (fx : X → Part L) (kg : G → K) (kx : X → L)
    {d : ℕ} (hg : ∀ g, N.gcost g ≤ d → kg g ∈ fg g)
    (hx : ∀ x, N.xcost x ≤ d → kx x ∈ fx x)
    (w : List (Letter G X)) (hb : N.wordCost w ≤ d) :
    N.totalTest kg kx w ∈ N.test fg fx w := by
  apply Part.mem_bind_iff.mpr
  refine ⟨N.totalNormalize kx w,?_,N.key_full fg fx kg kx hg hx _ ((N.totalNormalize_cost kx w).trans hb)⟩
  apply N.run_full fx kx hx
  simpa only [formCost,List.map_nil,List.sum_nil,N.cost_one,zero_add,add_zero] using hb

variable {P : Type*} [Primcodable P] [Primcodable G] [Primcodable X]
  [Primcodable K] [Primcodable L]
variable {fg : P → G → Part K} {fx : P → X → Part L}

theorem partrec_run (hn : Computable₂ N.plan) (hx : Partrec₂ fx) :
    Partrec (fun p : P × List (Letter G X) × Form G X => N.run (fx p.1) p.2.1 p.2.2) :=
  (EffectiveNames.PartialFold.partrec_right _ (N.partrec_step hn hx)).of_eq
    (fun ⟨p,w,f⟩ => (N.run_eq_fold p w f).symm)

omit [DecidableEq L] in
theorem partrec_key (hg : Partrec₂ fg) (hx : Partrec₂ fx) :
    Partrec₂ (fun p : P => key (fg p) (fx p)) := by
  let S := P × Form G X
  have hs : Partrec₂ (fun (s : S) (t : List X × G × List X) =>
      (fg s.1 t.2.1).bind fun k =>
        (Effect.traverse (fx s.1) t.1).bind fun ls =>
          (Effect.traverse (fx s.1) t.2.2).map fun rs => some (ls,k,rs)) := by
    have hf : Partrec (fun p : S × (List X × G × List X) => fg p.1.1 p.2.2.1) :=
      hg.comp (Computable.fst.comp Computable.fst)
        (Computable.fst.comp (Computable.snd.comp Computable.snd))
    apply hf.bind
    have hl : Partrec (fun p : (S × (List X × G × List X)) × K =>
        Effect.traverse (fx p.1.1.1) p.1.2.1) :=
      (Effect.partrec_traverse_parameter hx).comp
        (Computable.fst.comp (Computable.fst.comp Computable.fst))
        (Computable.fst.comp (Computable.snd.comp Computable.fst))
    apply hl.bind
    have hr : Partrec (fun p : ((S × (List X × G × List X)) × K) × List L =>
        Effect.traverse (fx p.1.1.1.1) p.1.1.2.2.2) :=
      (Effect.partrec_traverse_parameter hx).comp
        (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)))
        (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
          (Computable.fst.comp Computable.fst))))
    exact (hr.map (Computable.option_some.comp
      ((Computable.snd.comp Computable.fst).pair
        ((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair Computable.snd))).to₂).to₂
  exact (Partrec.optionCasesOn_right Computable.snd (Computable.const none) hs).of_eq
    (by intro ⟨p,f⟩; cases f <;> rfl)

theorem partrec_test (hn : Computable₂ N.plan) (hg : Partrec₂ fg) (hx : Partrec₂ fx) :
    Partrec₂ (fun p : P => N.test (fg p) (fx p)) := by
  have hr : Partrec (fun p : P × List (Letter G X) =>
      N.run (fx p.1) p.2 (some ([],N.one,[]))) :=
    (N.partrec_run hn hx).comp (Computable.fst.pair
      (Computable.snd.pair (Computable.const (some ([],N.one,[])))))
  exact hr.bind ((partrec_key hg hx).comp
    (Computable.fst.comp Computable.fst) Computable.snd).to₂

end Operations
end SimpleFInftyOvergroups.BoundedEncoding.NamedAction

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EffectiveTables
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes FiniteAlgebraicEnvelopes.Bootstrap

namespace CodedProgram
variable {P A S Q : Type*}
  [Primcodable P] [Primcodable A] [Primcodable S] [Primcodable Q]
  [DecidableEq S] [DecidableEq Q]

def compute (words : P → ℕ → List (List A)) (code : P → List A → List S)
    (lt : P → List A → List A → Bool) (z : S)
    (f : P → List A → Part (Option Q)) (p : P) (n : ℕ) :
    Part (List (List S × List S)) :=
  (Effect.traverse (fun w => (f p w).map (w,·)) (words p n)).map
    (Uniform.table (code p) (lt p) z)

end CodedProgram
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_MatrixEffective
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding.WithBound
 theorem ext' {A K : Type*} {B : KeyBall A K} {a b : WithBound B}
    (hv : a.val = b.val) (hc : a.cost = b.cost) : a = b := by
  cases a; cases b; cases hv; cases hc; rfl
end SimpleFInftyOvergroups.BoundedEncoding.WithBound

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_PlanEffective
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding.NamedAction.Operations
variable {G X : Type*} [Primcodable G] [Primcodable X] (N : Operations G X)
attribute [local fun_prop] Primrec
attribute [local fun_prop] Primrec.id Primrec.const Primrec.fst Primrec.snd Primrec.pair Primrec.comp
attribute [local fun_prop] Primrec.option_some Primrec.sumInl Primrec.sumInr
attribute [local fun_prop] primrec_cons primrec_append

 theorem primrec_letterCost (hg : Primrec N.gcost) (hx : Primrec N.xcost) :
    Primrec N.letterCost := by
  have ho : Primrec (fun p : Letter G X × Option X =>
      match p.2 with | none => 0 | some x => N.xcost x) :=
    primrec_match_option Primrec.snd (Primrec.const 0) (hx.comp Primrec.snd).to₂
  have hs : Primrec (fun p : Letter G X × (X ⊕ Option X) =>
      match p.2 with
      | .inl x => N.xcost x
      | .inr o => match o with | none => 0 | some x => N.xcost x) :=
    (primrec_match_sum Primrec.snd (hx.comp Primrec.snd).to₂
      (ho.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂).of_eq
        (fun p => by cases p.2 <;> rfl)
  exact (primrec_match_sum Primrec.id (hg.comp Primrec.snd).to₂ hs.to₂).of_eq
    (fun a => by rcases a with g | (x | y); rfl; rfl; cases y <;> rfl)

 theorem primrec_plan (hm : Primrec₂ N.mul) (hi : Primrec N.inv) (ha : Primrec₂ N.act) :
    Primrec₂ N.plan := by
  have hm' : Primrec (fun p : G × G => N.mul p.1 p.2) := hm
  have ha' : Primrec (fun p : G × X => N.act p.1 p.2) := ha
  let T := Letter G X × Form G X
  let B := List X × G × List X
  let R := Form G X ⊕ (X × X × Form G X)
  have hgrp : Primrec (fun p : (T × B) × G =>
      match p.1.2.1 with
      | [] => (Sum.inl (some ([],N.mul p.2 p.1.2.2.1,p.1.2.2.2)) : Form G X ⊕ (X × X × Form G X))
      | x::l => .inl (some (N.act p.2 x::l,p.1.2.2.1,p.1.2.2.2))) := by
    have h0 : Primrec (fun p : (T × B) × G => (Sum.inl
        (some ([],N.mul p.2 p.1.2.2.1,p.1.2.2.2)) : R)) := by
      dsimp only [B,T,R]
      fun_prop (disch := assumption)
    have hc : Primrec₂ (fun (p : (T × B) × G) (q : X × List X) =>
        (Sum.inl (some (N.act p.2 q.1::q.2,p.1.2.2.1,p.1.2.2.2)) : R)) := by
      change Primrec _
      dsimp only [B,T,R]
      fun_prop (disch := assumption)
    exact (primrec_match_list (f := fun p : (T × B) × G => p.1.2.1)
      (by dsimp only [B,T,R]; fun_prop) h0 hc).of_eq (fun p => by cases p.1.2.1 <;> rfl)
  have hdel : Primrec (fun p : (T × B) × X =>
      match p.1.2.1 with
      | [] => (Sum.inl (some ([],N.one,p.1.2.2.2++[N.act (N.inv p.1.2.2.1) p.2])) :
          Form G X ⊕ (X × X × Form G X))
      | x::l => .inr (p.2,x,some (l,p.1.2.2.1,p.1.2.2.2))) := by
    have h0 : Primrec (fun p : (T × B) × X => (Sum.inl
        (some ([],N.one,p.1.2.2.2++[N.act (N.inv p.1.2.2.1) p.2])) : R)) := by
      dsimp only [B,T,R]
      fun_prop (disch := assumption)
    have hc : Primrec₂ (fun (p : (T × B) × X) (q : X × List X) =>
        (Sum.inr (p.2,q.1,some (q.2,p.1.2.2.1,p.1.2.2.2)) : R)) := by
      change Primrec _
      dsimp only [B,T,R]
      fun_prop
    exact (primrec_match_list (f := fun p : (T × B) × X => p.1.2.1)
      (by dsimp only [B,T,R]; fun_prop) h0 hc).of_eq (fun p => by cases p.1.2.1 <;> rfl)
  have hopt : Primrec (fun p : (T × B) × Option X =>
      match p.2 with
      | none => (Sum.inl none : Form G X ⊕ (X × X × Form G X))
      | some x => match p.1.2.1 with
        | [] => .inl (some ([],N.one,p.1.2.2.2++[N.act (N.inv p.1.2.2.1) x]))
        | z::l => .inr (x,z,some (l,p.1.2.2.1,p.1.2.2.2))) := by
    apply primrec_match_option Primrec.snd (Primrec.const (Sum.inl none))
    exact (hdel.comp (Primrec.fst.comp Primrec.fst |>.pair Primrec.snd)).to₂
  have hnon : Primrec (fun p : (T × B) × (X ⊕ Option X) =>
      match p.2 with
      | .inl x => (Sum.inl (some (x::p.1.2.1,p.1.2.2.1,p.1.2.2.2)) :
          Form G X ⊕ (X × X × Form G X))
      | .inr y => match y with
        | none => .inl none
        | some x => match p.1.2.1 with
          | [] => .inl (some ([],N.one,p.1.2.2.2++[N.act (N.inv p.1.2.2.1) x]))
          | z::l => .inr (x,z,some (l,p.1.2.2.1,p.1.2.2.2))) := by
    have hl : Primrec₂ (fun (p : (T × B) × (X ⊕ Option X)) (x : X) =>
        (Sum.inl (some (x::p.1.2.1,p.1.2.2.1,p.1.2.2.2)) : R)) := by
      change Primrec _
      dsimp only [B,T,R]
      fun_prop
    exact (primrec_match_sum Primrec.snd hl
      (hopt.comp (Primrec.fst.comp Primrec.fst |>.pair Primrec.snd)).to₂).of_eq
        (fun p => by cases p.2 <;> rfl)
  have hs : Primrec (fun p : T × B => N.plan p.1.1 (some p.2)) := by
    apply (Primrec.sumCasesOn (Primrec.fst.comp Primrec.fst)
      (hgrp.to₂) (hnon.to₂)).of_eq
    intro p
    rcases p with ⟨⟨a,f⟩,l,g,r⟩
    rcases a with h | (x|y)
    · cases l <;> rfl
    · rfl
    · cases y with
      | none => rfl
      | some y => cases l <;> rfl
  exact (Primrec.option_casesOn Primrec.snd (Primrec.const (.inl none)) hs.to₂).of_eq
    (fun p => by rcases p with ⟨a,f⟩; cases f <;> rfl)
end SimpleFInftyOvergroups.BoundedEncoding.NamedAction.Operations

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_TruncatedArrays
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding
noncomputable section
open scoped Classical

namespace ActionCalculus
variable {V X K L : Type*} [Group V] [MulAction V X] {m : ℕ}
  (C : ActionCalculus V X K L m) (D : Type*) [Ring D]

theorem algebraCollect_product {p q : MonoidAlgebra D V} {b c : ℕ}
    (hp : C.group.algebraBall D b p) (hq : C.group.algebraBall D c q) (hbc : b+c ≤ m) :
    C.group.algebraCollect D (C.group.algebraCanonical D m p * C.group.algebraCanonical D m q) =
      C.group.algebraCollect D (p*q) := by
  apply C.group.algebra_induction D
    (P := fun p => C.group.algebraCollect D
      (C.group.algebraCanonical D m p * C.group.algebraCanonical D m q) =
      C.group.algebraCollect D (p*q)) ?_ ?_ ?_ hp
  · simp
  · intro u hu a
    apply C.group.algebra_induction D
      (P := fun q => C.group.algebraCollect D
        (C.group.algebraCanonical D m (MonoidAlgebra.single u a) * C.group.algebraCanonical D m q) =
        C.group.algebraCollect D (MonoidAlgebra.single u a*q)) ?_ ?_ ?_ hq
    · simp
    · intro v hv d
      simp only [KeyBall.algebraCanonical_single, MonoidAlgebra.single_mul_single,
        KeyBall.algebraCollect_single]
      have hk := C.mul_congr (C.group.canonical_mem m hu (by omega))
        (C.group.canonical_mem m hv (by omega)) hu hv hbc hbc
        (C.group.key_canonical m hu (by omega)) (C.group.key_canonical m hv (by omega))
      rw [hk]
    · intro x y hx hy
      simp only [map_add, mul_add, hx, hy]
  · intro x y hx hy
    simp only [map_add, add_mul, hx, hy]

theorem algebraCollect_mul_congr {p q p' q' : MonoidAlgebra D V} {b c b' c' : ℕ}
    (hp : C.group.algebraBall D b p) (hq : C.group.algebraBall D c q)
    (hp' : C.group.algebraBall D b' p') (hq' : C.group.algebraBall D c' q')
    (hbc : b+c ≤ m) (hbc' : b'+c' ≤ m)
    (hep : C.group.algebraCollect D p = C.group.algebraCollect D p')
    (heq : C.group.algebraCollect D q = C.group.algebraCollect D q') :
    C.group.algebraCollect D (p*q) = C.group.algebraCollect D (p'*q') := by
  rw [← C.algebraCollect_product D hp hq hbc, ← C.algebraCollect_product D hp' hq' hbc',
    C.group.algebraCanonical_congr D m hep, C.group.algebraCanonical_congr D m heq]

variable [Nonempty X]

theorem arrayCollect_action {p : MonoidAlgebra D V} {x : X →₀ D} {b c : ℕ}
    (hp : C.group.algebraBall D b p) (hx : C.point.arrayBall D c x) (hbc : b+c ≤ m) :
    C.point.arrayCollect D (SourceEnlargement.ringAction (C.group.algebraCanonical D m p)
      (C.point.arrayCanonical D m x)) =
      C.point.arrayCollect D (SourceEnlargement.ringAction p x) := by
  apply C.group.algebra_induction D
    (P := fun p => C.point.arrayCollect D (SourceEnlargement.ringAction (C.group.algebraCanonical D m p)
      (C.point.arrayCanonical D m x)) = C.point.arrayCollect D (SourceEnlargement.ringAction p x))
    ?_ ?_ ?_ hp
  · simp
  · intro v hv a
    apply C.point.array_induction D
      (P := fun x => C.point.arrayCollect D
        (SourceEnlargement.ringAction (C.group.algebraCanonical D m (MonoidAlgebra.single v a))
          (C.point.arrayCanonical D m x)) =
        C.point.arrayCollect D (SourceEnlargement.ringAction (MonoidAlgebra.single v a) x))
      ?_ ?_ ?_ hx
    · simp
    · intro z hz d
      simp only [KeyBall.algebraCanonical_single, KeyBall.arrayCanonical_single,
        SourceEnlargement.ringAction_single, KeyBall.arrayCollect_single]
      have hk := C.smul_congr (C.group.canonical_mem m hv (by omega))
        (C.point.canonical_mem m hz (by omega)) hv hz hbc hbc
        (C.group.key_canonical m hv (by omega)) (C.point.key_canonical m hz (by omega))
      rw [hk]
    · intro x y hx hy
      simp only [map_add, hx, hy]
  · intro p q hp hq
    simp only [map_add]
    change C.point.arrayCollect D
      (SourceEnlargement.ringAction (C.group.algebraCanonical D m p) (C.point.arrayCanonical D m x) +
        SourceEnlargement.ringAction (C.group.algebraCanonical D m q) (C.point.arrayCanonical D m x)) =
      C.point.arrayCollect D (SourceEnlargement.ringAction p x + SourceEnlargement.ringAction q x)
    simp only [map_add, hp, hq]

theorem arrayCollect_action_congr {p p' : MonoidAlgebra D V} {x x' : X →₀ D} {b c b' c' : ℕ}
    (hp : C.group.algebraBall D b p) (hx : C.point.arrayBall D c x)
    (hp' : C.group.algebraBall D b' p') (hx' : C.point.arrayBall D c' x')
    (hbc : b+c ≤ m) (hbc' : b'+c' ≤ m)
    (hep : C.group.algebraCollect D p = C.group.algebraCollect D p')
    (hex : C.point.arrayCollect D x = C.point.arrayCollect D x') :
    C.point.arrayCollect D (SourceEnlargement.ringAction p x) =
      C.point.arrayCollect D (SourceEnlargement.ringAction p' x') := by
  rw [← C.arrayCollect_action D hp hx hbc, ← C.arrayCollect_action D hp' hx' hbc',
    C.group.algebraCanonical_congr D m hep, C.point.arrayCanonical_congr D m hex]

def enlargement :
    ActionCalculus (MonoidAlgebra D V)ˣ (X →₀ D) ((K →₀ D) × (K →₀ D)) (L →₀ D) m where
  group :=
    { ball := fun b v => C.group.algebraBall D b v.val ∧ C.group.algebraBall D b v.inv
      mono := by
        intro b c hbc v hv
        exact ⟨C.group.arrayBall_mono D hbc hv.1, C.group.arrayBall_mono D hbc hv.2⟩
      key := fun v => (C.group.algebraCollect D v.val, C.group.algebraCollect D v.inv) }
  point := C.point.arrays D
  one_mem b := by
    have h : C.group.algebraBall D b 1 := by
      rw [MonoidAlgebra.one_def]
      exact C.group.algebraBall_single D (C.one_mem b) 1
    exact ⟨h,h⟩
  inv_mem := fun h => ⟨h.2,h.1⟩
  mul_mem := by
    intro b c u v hu hv
    refine ⟨C.algebra_mul_mem D hu.1 hv.1, ?_⟩
    change C.group.algebraBall D (b+c) (v.inv*u.inv)
    simpa only [Nat.add_comm] using C.algebra_mul_mem D hv.2 hu.2
  smul_mem := fun hu hx => C.array_action_mem D hu.1 hx
  inv_congr := fun he => Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
  mul_congr := by
    intro b c b' c' u v u' v' hu hv hu' hv' hb hb' heu hev
    apply Prod.ext
    · exact C.algebraCollect_mul_congr D hu.1 hv.1 hu'.1 hv'.1 hb hb'
        (congrArg Prod.fst heu) (congrArg Prod.fst hev)
    · exact C.algebraCollect_mul_congr D hv.2 hu.2 hv'.2 hu'.2 (by omega) (by omega)
        (congrArg Prod.snd hev) (congrArg Prod.snd heu)
  smul_congr := by
    intro b c b' c' u x u' x' hu hx hu' hx' hb hb' heu hex
    exact C.arrayCollect_action_congr D hu.1 hx hu'.1 hx' hb hb' (congrArg Prod.fst heu) hex

theorem unitMap_mem (E : D) (hE : E*E = E) {v : V} {b : ℕ} (hv : v ∈ C.group.ball b) :
    SourceEnlargement.unitMap E hE v ∈ (C.enlargement D).group.ball b := by
  constructor
  · exact C.group.algebraBall_add D (C.group.algebraBall_single D (C.one_mem b) _)
      (C.group.algebraBall_single D hv _)
  · exact C.group.algebraBall_add D (C.group.algebraBall_single D (C.one_mem b) _)
      (C.group.algebraBall_single D (C.inv_mem hv) _)

theorem basis_mem {x : X} {b : ℕ} (hx : x ∈ C.point.ball b) :
    Finsupp.single x (1 : D) ∈ (C.enlargement D).point.ball b :=
  C.point.arrayBall_single D hx 1

end ActionCalculus
end
end SimpleFInftyOvergroups.BoundedEncoding

end OAI
end


