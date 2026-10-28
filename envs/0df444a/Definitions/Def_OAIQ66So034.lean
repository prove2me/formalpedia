-- Prove2me | Definitions.Def_OAIQ66So034
-- name    : OAIQ66So034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:56:47.532439+00:00
-- url     : https://prove2.me/theorems/b1fee28d-f45b-463b-aa48-008fad66547c
-- title:
--   Definitions bundle OAIQ66So034 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 15 declarations of OpenAI's Lean: 12 definitions and 3 theorems. The definitions and types are `OAI.SimpleFInftyOvergroups.SourceModel.data`, `OAI.StageConstruction.limitRepresentation`, `OAI.StageConstruction.stabilizerBlock`, `OAI.StageGeometry.base`, `OAI.StageGeometry.baseEquiv`, `OAI.StageGeometry.changed`, `OAI.StageGeometry.diagramMap`, `OAI.StageGeometry.endomorphism`, `OAI.StageGeometry.endomorphism_injective`, `OAI.StageGeometry.limitAction`, `OAI.StageGeometry.splittings`, `OAI.StageGeometry.transInjective`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: [`FiniteType_AscendingHNNInnerTwist`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/AscendingHNNInnerTwist.lean), [`FiniteType_HomStabilizer`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/HomStabilizer.lean), [`FiniteType_StageConstruction`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/StageConstruction.lean), [`FiniteType_TorusAction`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/TorusAction.lean), [`SimpleOvergroups_SourceProducer`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/SimpleOvergroups/SourceProducer.lean).
--
--   **Imports.** It imports the bundles `OAIQ66So032` and `OAIQ66So033` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.StageGeometry.finite_set_model` and `OAI.StageGeometry.localGroup_geometric_of_binary_ring_data`; the proofs of `OAI.SimpleFInftyOvergroups.main`, `OAI.StageGeometry.finite_set_model`, `OAI.StageGeometry.localGroup_geometric_of_binary_ring_data` and `OAI.StageGeometry.simple_geometric_overgroup_of_binary_ring_data`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So032
import Definitions.Def_OAIQ66So033

section
-- module Solutions.OAIQ066_SO.FiniteType_StageConstruction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.StageConstruction.columnMulAction _root_.OAI.SteinbergFinitePresentation.instFiniteElemFreeGroupRootOptionRelations _root_.OAI.SteinbergFinitePresentation.instFiniteRoot _root_.OAI.SteinbergFinitePresentation.instIsFinitelyPresentedUniversalOfFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace StageConstruction
variable {R : Type*} [Ring R]

variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)

variable {ι : Type*}

def stabilizerBlock (c : ι → R) (a : Q R) (d : R)
    (hc : ∀ i, d*c i=0) :
    Steinberg.Group (Fin 6) R →* fixing (fun i => action a (Pi.single first (c i))) :=
  (((MulAut.conj (a*(exchange d)⁻¹)).toMonoidHom).comp block).codRestrict _ (by
    intro g i
    change action ((a*(exchange d)⁻¹)*block g*(a*(exchange d)⁻¹)⁻¹)
      (action a (Pi.single first (c i)))=action a (Pi.single first (c i))
    simp only [mul_inv_rev,inv_inv,map_mul,map_inv,Equiv.Perm.mul_apply,Equiv.Perm.inv_def]
    rw [Equiv.symm_apply_apply,exchange_fixes d (c i) (hc i),block_fixes]
    have he := exchange_fixes d (c i) (hc i)
    have hei : (action (exchange d)).symm (Pi.single first (c i))=Pi.single first (c i) :=
      (Equiv.symm_apply_eq (action (exchange d))).mpr he.symm
    rw [hei])

end StageConstruction

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TorusAction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
section
open scoped commutatorElement

namespace StageConstruction
variable {R : Type*} [Ring R]

variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
variable {Y W : Type*} [DecidableEq Y] [Group W] [MulAction W Y]
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y z, T y*S z=if y=z then e else 0)
variable (hSe : ∀ y, S y*e=S y)
variable (ρ : W →* Rˣ) (ι : Q R →* W) (point : X R → Y)
variable (hρS : ∀ w y, (ρ w).val*S y=S (w • y))
variable (hpoint : ∀ q x, ι q • point x=point (q • x))
variable (hφ : Function.Injective φ) (hρ : Function.Injective ρ)
variable (hι : Function.Injective ι) (hpt : Function.Injective point)

def limitRepresentation : LimitGroup φ D ρ ι hφ hρ hι →* Equiv.Perm (LimitPoints φ S point) :=
  TorusAction.representation (delta φ D ρ ι) (delta_injective φ D ρ ι hφ hρ hι)
    (sigma φ S point) (fun q x => (transition_equivariant φ D S ρ ι point hρS hpoint q x).symm)

end StageConstruction

end

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_AscendingHNNInnerTwist
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SimpleFInftyOvergroups.SemanticEncoding.IdempotentNames.instFintypeElemSubtypeEndSpaceMemSubalgebraAlgebraIndexOfFinite _root_.OAI.SimpleFInftyOvergroups.SemanticEncoding.IdempotentNames.instPrimcodableElemSubtypeEndSpaceMemSubalgebraAlgebraIndexOfFinite _root_.OAI.SourceEnlargement.Double.action₁ _root_.OAI.SourceEnlargement.Double.action₂ _root_.OAI.SourceEnlargement.Double.orbitAction _root_.OAI.SourceEnlargement.Double.orbitSMul _root_.OAI.SourceEnlargement.Double.smul₁ _root_.OAI.SourceEnlargement.Double.smul₂ _root_.OAI.SourceEnlargement.enlargedAction _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise

namespace StageGeometry
open StageConstruction

variable {R Y W : Type} [Ring R] [Group W] [MulAction W Y]
variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
variable (S : Y → R) (ρ : W →* Rˣ) (ι : Q R →* W) (point : X R → Y)
variable (hρS : ∀ w y, (ρ w).val*S y=S (w • y))
variable (hpoint : ∀ q x, ι q • point x=point (q • x))
variable (hφ : Function.Injective φ) (hρ : Function.Injective ρ)
variable (hι : Function.Injective ι)

abbrev transInjective := delta_injective φ D ρ ι hφ hρ hι
include hρS hpoint in
lemma compatible (q : Q R) (x : X R) :
    shift φ S point (q • x) = trans φ D ρ ι q • shift φ S point x :=
  (transition_equivariant φ D S ρ ι point hρS hpoint q x).symm

variable {J : Type} (z : J → X R) (a : Q R)
variable (ha : ∀ j, a • shift φ S point (z j) = z j)

abbrev changed := TorusStabilizer.changedSubgroup
  (trans φ D ρ ι) (transInjective φ D ρ ι hφ hρ hι)
  (shift φ S point) (compatible φ D S ρ ι point hρS hpoint) z a
abbrev base := HNNSubgroup.base
  (AscendingHNN.innerTwist (trans φ D ρ ι) a)
  (AscendingHNN.innerTwist_injective (trans φ D ρ ι) (transInjective φ D ρ ι hφ hρ hι) a)
  (changed φ D S ρ ι point hρS hpoint hφ hρ hι z a)
abbrev endomorphism := HNNSubgroup.baseMap
  (AscendingHNN.innerTwist (trans φ D ρ ι) a)
  (AscendingHNN.innerTwist_injective (trans φ D ρ ι) (transInjective φ D ρ ι hφ hρ hι) a)
  (changed φ D S ρ ι point hρS hpoint hφ hρ hι z a)
  (TorusStabilizer.changed_stable_mem _ _ _ _ z a ha)
abbrev endomorphism_injective := HNNSubgroup.baseMap_injective
  (AscendingHNN.innerTwist (trans φ D ρ ι) a)
  (AscendingHNN.innerTwist_injective (trans φ D ρ ι) (transInjective φ D ρ ι hφ hρ hι) a)
  (changed φ D S ρ ι point hρS hpoint hφ hρ hι z a)
  (TorusStabilizer.changed_stable_mem _ _ _ _ z a ha)

variable (hs : Function.Injective (shift φ S point))
include hs in
lemma base_iff (q : Q R) :
    q ∈ base φ D S ρ ι point hρS hpoint hφ hρ hι z a ↔ ∀ j, q • z j = z j :=
  TorusStabilizer.base_mem_iff _ _ _ _ z a hs q

def baseEquiv : base φ D S ρ ι point hρS hpoint hφ hρ hι z a ≃*
    compressedFixing φ (fun j => S (point (z j))) a where
  toFun q := ⟨q.val, by
    intro j
    change q.val • (a • shift φ S point (z j)) = a • shift φ S point (z j)
    rw [ha j]
    exact (base_iff φ D S ρ ι point hρS hpoint hφ hρ hι z a hs q.val).mp q.property j⟩
  invFun q := ⟨q.val, (base_iff φ D S ρ ι point hρS hpoint hφ hρ hι z a hs q.val).mpr (by
    intro j
    have h := q.property j
    change q.val • (a • shift φ S point (z j)) = a • shift φ S point (z j) at h
    rwa [ha j] at h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable (T : Y → R) (hTρ : ∀ w y, T y*(ρ w).val=T (w⁻¹ • y))

variable (K : Type) [CommRing K] (F : PairDiagrams K ι point)

include hρS ha hs in
lemma conjugated_mem (E : BinaryPrefixOperators.idempotents K)
    (u : base φ D S ρ ι point hρS hpoint hφ hρ hι z a) :
    conjugated φ D ρ a (F.map E u.val) ∈
      base φ D S ρ ι point hρS hpoint hφ hρ hι z a := by
  apply (base_iff φ D S ρ ι point hρS hpoint hφ hρ hι z a hs _).mpr
  intro j
  have hu := (base_iff φ D S ρ ι point hρS hpoint hφ hρ hι z a hs _).mp u.property j
  have hfix := F.fixed E u.val (z j) hu
  have hz' : a⁻¹ • z j = shift φ S point (z j) := by
    calc
      a⁻¹ • z j = a⁻¹ • (a • shift φ S point (z j)) :=
        congrArg (fun x => a⁻¹ • x) (ha j).symm
      _ = shift φ S point (z j) := inv_smul_smul a _
  change (a * transitionUnits φ D (ρ (F.map E u.val)) * a⁻¹) • z j = z j
  change action (a * transitionUnits φ D (ρ (F.map E u.val)) * a⁻¹) (z j) = z j
  rw [map_mul,map_mul]
  change a • (transitionUnits φ D (ρ (F.map E u.val)) • (a⁻¹ • z j)) = z j
  rw [hz']
  change a • action (transitionUnits φ D (ρ (F.map E u.val)))
    (beta φ S (point (z j))) = z j
  rw [transitionUnits_beta φ D S _ _ (point (z j)) (by rw [hρS,hfix])]
  exact ha j

def diagramMap (E : BinaryPrefixOperators.idempotents K) :
    base φ D S ρ ι point hρS hpoint hφ hρ hι z a →*
      base φ D S ρ ι point hρS hpoint hφ hρ hι z a :=
  ((conjugated φ D ρ a).comp ((F.map E).comp
    (base φ D S ρ ι point hρS hpoint hφ hρ hι z a).subtype)).codRestrict _
    (conjugated_mem φ D S ρ ι point hρS hpoint hφ hρ hι z a ha hs K F E)

def splittings : ListChains.IdempotentSplittings
    (base φ D S ρ ι point hρS hpoint hφ hρ hι z a) K
    (endomorphism φ D S ρ ι point hρS hpoint hφ hρ hι z a ha) where
  map := diagramMap φ D S ρ ι point hρS hpoint hφ hρ hι z a ha hs K F
  identity := by
    apply MonoidHom.ext
    intro u
    apply Subtype.ext
    change conjugated φ D ρ a (F.map ⟨1,_⟩ u.val) = _
    rw [F.identity]
    rfl
  commute E P hSum hEP hPE u v := by
    apply Subtype.ext
    exact ((F.commute E P hSum hEP hPE u.val v.val).map
      (conjugated φ D ρ a)).eq
  addition E P hSum hEP hPE u := by
    apply Subtype.ext
    change conjugated φ D ρ a (F.map ⟨_,hSum⟩ u.val) = _
    rw [F.addition E P hSum hEP hPE,map_mul]
    rfl

end StageGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_HomStabilizer
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
namespace SimpleFInftyOvergroups

attribute [instance] SplittingTorusModel.groupU SplittingTorusModel.groupP
  SplittingTorusModel.finitePresentation

end SimpleFInftyOvergroups

namespace StageGeometry
open StageConstruction
variable {R Y W : Type} [Ring R] [Nontrivial R] [Group W] [MulAction W Y] [DecidableEq Y]
variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
variable (e : R) (S T : Y → R)
variable (hTS : ∀ y y', T y*S y'=if y=y' then e else 0) (hSe : ∀ y, S y*e=S y)
variable (ρ : W →* Rˣ) (ι : Q R →* W) (point : X R → Y)
variable (hρS : ∀ w y, (ρ w).val*S y=S (w • y))
variable (hTρ : ∀ w y, T y*(ρ w).val=T (w⁻¹ • y))
variable (hpoint : ∀ q x, ι q • point x=point (q • x))
variable (hφ : Function.Injective φ) (hρ : Function.Injective ρ)
variable (hι : Function.Injective ι) (hpt : Function.Injective point) (he : e≠0)
variable (F₂ : PairDiagrams (ZMod 2) ι point) (F₃ : PairDiagrams (ZMod 3) ι point)

abbrev limitAction : MulAction (LimitGroup φ D ρ ι hφ hρ hι) (LimitPoints φ S point) :=
  MulAction.compHom _ (limitRepresentation φ D S ρ ι point hρS hpoint hφ hρ hι)

end StageGeometry

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_SourceProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace SimpleFInftyOvergroups
namespace SourceModel
open scoped Classical
open FiniteAlgebraicEnvelopes RingAssembly

variable {G : Type} [Group G] {k : ℕ} (s : Fin k → G)
variable (h : ComputablePred (fun w => FiniteAlgebraicEnvelopes.evalWord s w = 1))

def data (hs : Subgroup.closure (Set.range s)=⊤) : SourceRingData G where
  R := B s h
  ringR := bRing s h
  nontrivialR := bNontrivial s h
  algebraR := bAlgebra s h
  φ := φ s h
  φ_injective := φ_injective s h
  binary := binary s h
  e := e s h
  e_idempotent := e_idempotent s h
  e_nonzero := e_nonzero s h
  S y := actionCornerMap s h (SourceActionMonoid.prepend y)
  T y := actionCornerMap s h (SourceActionMonoid.delete y)
  TS y z := by
    by_cases hyz : y=z
    · simpa only [ite_eq_left hyz] using corner_TS (actionCornerMap s h) y z
    · simpa only [ite_eq_right hyz] using corner_TS (actionCornerMap s h) y z
  ρ := actionUnits (actionCornerMap s h)
  ρ_injective := actionUnits_injective (actionCornerMap s h) (actionCornerMap_injective s h)
  ρS := corner_ρS (actionCornerMap s h)
  Tρ := corner_Tρ (actionCornerMap s h)
  A := Generators s h
  finiteA := inferInstance
  π := presentationMap s h
  π_surjective := presentationMap_surjective s h
  rel := differences (Relations s h)
  rel_finite := differences_finite _ (relations_finite s h)
  ker_π := presentationMap_kernel s h
  g := (groupCornerMap s h hs).toHomUnits
  g_injective := fun _ _ hxy => groupCornerMap_injective s h hs (congrArg Units.val hxy)

end SourceModel

universe u

end SimpleFInftyOvergroups
end

end OAI
end


