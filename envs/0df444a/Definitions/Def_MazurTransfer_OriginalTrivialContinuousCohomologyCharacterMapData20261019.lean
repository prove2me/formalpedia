-- Prove2me | Definitions.Def_MazurTransfer_OriginalTrivialContinuousCohomologyCharacterMapData20261019
-- name    : MazurTransfer_OriginalTrivialContinuousCohomologyCharacterMapData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-20T18:29:59.606003+00:00
-- url     : https://prove2.me/theorems/4b20f7b7-655a-4d24-847d-6510427fbfa7
-- title:
--   Original continuous trivial-action cocycle and character maps
-- statement:
--   Retain the original four continuous cocycle-to-character constructor values and the intrinsic quotient descent certificate for the same supplied trivial action. All group, coefficient, topology and action hypotheses remain unchanged. Each complete type, whole constructor value and eight generated structural proof types is independently checked against the original module. Named downstream consumer: bijectivity of the original continuous cohomology character map and genuine characters of the selected arithmetic character kernel.
-- source:
--   MazurTheorem TrivialContinuousH1Characters by Vas and contributors; original constructors and intrinsic quotient descent certificate, with per-file Apache-2.0 attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: original continuous cocycle-to-character constructors for a supplied trivial action, retaining the intrinsic quotient well-definedness certificate required to define the same map on H1. Bijectivity proofs and the resulting equivalence are separate downstream results.
Named downstream consumer: the original trivial-action continuous H1 character theorem and genuine characters of the selected arithmetic character kernel.
-/
import Definitions.Def_MazurTransfer_ContinuousFirstCohomologyPresentationData
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: continuous H1 for a GIVEN trivial multiplicative action
identifies with the ACTUAL continuous group homomorphisms. The existing
continuous cocycle quotient and its coefficient group are retained.
Named downstream consumer: arithmetic characters of the subgroup that
trivializes the selected order-13 reflected character.
-/

noncomputable section
namespace MazurTransfer.TrivialContinuousH1Characters
open ContinuousFirstCohomologyPresentation
variable (G M : Type) [Group G] [CommGroup M] [MulDistribMulAction G M]
  [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M]
variable (htriv : ∀ (g : G) (m : M), g • m = m)
include htriv

def cocycleHom (z : continuousCocycles G M) : G →ₜ* M where
  toFun g := Additive.toMul (z.val g)
  map_one' := by
    have h := groupCohomology.cocycles₁_map_one z.val
    exact congrArg Additive.toMul h
  map_mul' g h := by
    have he := (groupCohomology.mem_cocycles₁_iff _).mp z.val.property g h
    have ht := congrArg Additive.toMul he
    change (Additive.toMul (z.val (g * h)) : M) = g • (Additive.toMul (z.val h) : M) * (Additive.toMul (z.val g) : M) at ht
    rw [htriv, mul_comm] at ht
    exact ht
  continuous_toFun := z.property

def cocycleToHom : continuousCocycles G M →+ Additive (G →ₜ* M) where
  toFun z := Additive.ofMul (cocycleHom G M htriv z)
  map_zero' := by
    apply Additive.toMul.injective
    apply ContinuousMonoidHom.ext
    intro g
    rfl
  map_add' z w := by
    apply Additive.toMul.injective
    apply ContinuousMonoidHom.ext
    intro g
    rfl

theorem forget_kernel_le : (forgetCocycles G M).ker ≤ (cocycleToHom G M htriv).ker := by
  intro z hz
  obtain ⟨m, hm⟩ := groupCohomology.isMulCoboundary₁_of_mem_coboundaries₁
    (fun g : G => (Additive.toMul (z.val g) : M)) ((forgetCocycles_eq_zero_iff G M z).mp hz)
  change Additive.ofMul (cocycleHom G M htriv z) = 0
  apply Additive.toMul.injective
  apply ContinuousMonoidHom.ext
  intro g
  exact (hm g).symm.trans (by rw [htriv]; simp)

def toHom : H1 G M →+ Additive (G →ₜ* M) :=
  QuotientAddGroup.lift (forgetCocycles G M).ker (cocycleToHom G M htriv) (forget_kernel_le G M htriv)







def homCocycle (f : G →ₜ* M) : continuousCocycles G M :=
  ⟨groupCohomology.cocyclesOfIsMulCocycle₁ (f := fun g => f g)
    (fun g h => by change f (g * h) = g • f h * f g; rw [htriv, map_mul, mul_comm]), f.continuous⟩





end MazurTransfer.TrivialContinuousH1Characters
#print axioms MazurTransfer.TrivialContinuousH1Characters.cocycleHom
#print axioms MazurTransfer.TrivialContinuousH1Characters.cocycleToHom
#print axioms MazurTransfer.TrivialContinuousH1Characters.forget_kernel_le
#print axioms MazurTransfer.TrivialContinuousH1Characters.toHom
#print axioms MazurTransfer.TrivialContinuousH1Characters.homCocycle


