-- Prove2me | Definitions.Def_OAIQ116Ta011
-- name    : OAIQ116Ta011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:57:32.87398+00:00
-- url     : https://prove2.me/theorems/fa0d7d9c-9c2a-41f2-ac23-46c30d16016a
-- title:
--   Definitions bundle OAIQ116Ta011 of the split of OpenAI, A counterexample to Tachikawa's second conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Tachikawa.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Tachikawa's second conjecture*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 125 declarations of OpenAI's Lean: 69 definitions, 4 instances and 52 theorems. The definitions and types are `OAI.Tachikawa.Construction.ELeftObj`, `OAI.Tachikawa.Construction.ERightObj`, `OAI.Tachikawa.Construction.XTensorEquiv`, `OAI.Tachikawa.Construction.XTensorObj`, `OAI.Tachikawa.Construction.XTensorUnderlying`, `OAI.Tachikawa.Construction.bSimpleTensor`, `OAI.Tachikawa.Construction.bSimpleTensorResolution`, `OAI.Tachikawa.Construction.bSimpleTensorRestrictionEquiv`, `OAI.Tachikawa.Construction.bSimpleTensorRestrictionIso`, `OAI.Tachikawa.Construction.eLeftRestrictionIso`, `OAI.Tachikawa.Construction.eRightRestrictionIso`, `OAI.Tachikawa.Construction.eRightTensorEquiv`, `OAI.Tachikawa.Construction.eRightUnderlying`, `OAI.Tachikawa.Construction.evaluatedKComparison`, `OAI.Tachikawa.Construction.inclusionOppTensor`, `OAI.Tachikawa.Construction.jjNatIntIso`, `OAI.Tachikawa.Construction.restrictedTwistedUnderlying`, `OAI.Tachikawa.Construction.restrictedXResolution`, `OAI.Tachikawa.Construction.sCanon`, `OAI.Tachikawa.Construction.simpleUnderlying`, `OAI.Tachikawa.Construction.socleBimoduleMap`, `OAI.Tachikawa.Construction.tRightUnderlying`, `OAI.Tachikawa.Enveloping.evalCokerIso`, `OAI.Tachikawa.Enveloping.evalCosyCokerStableEquiv`, `OAI.Tachikawa.Enveloping.evaluatedInducedRegularComparison`, `OAI.Tachikawa.Enveloping.evaluatedInducedRegularIso`, `OAI.Tachikawa.Enveloping.evaluatedRegularComparison`, `OAI.Tachikawa.Enveloping.evaluatedRegularResolution`, `OAI.Tachikawa.Enveloping.inducedLeftComplexIso`, `OAI.Tachikawa.Enveloping.inducedLeftHomotopy`, `OAI.Tachikawa.Enveloping.inducedRegularAugmentation`, `OAI.Tachikawa.Enveloping.inducedRegularCochain`, `OAI.Tachikawa.Enveloping.inducedRightComplexIso`, `OAI.Tachikawa.Enveloping.inducedRightFactorIso`, `OAI.Tachikawa.Enveloping.inducedRightHomotopy`, `OAI.Tachikawa.Enveloping.inductionEvaluation`, `OAI.Tachikawa.Enveloping.leftIndRegularIso`, `OAI.Tachikawa.Enveloping.leftInducedResolution`, `OAI.Tachikawa.Enveloping.leftInducedRightResolution`, `OAI.Tachikawa.Enveloping.regularPreAugmentation` and 29 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory, in whole or in part: `Tachikawa_Bimodule`, `Tachikawa_Coinduction`, `Tachikawa_Coresolution`, `Tachikawa_DerivedDescent`, `Tachikawa_DerivedInduction`, `Tachikawa_HomProfile`, `Tachikawa_Induction`, `Tachikawa_OuterExt`, `Tachikawa_OuterTensor`, `Tachikawa_Perfect`, `Tachikawa_ReverseResolution`, `Tachikawa_RightInduction`, `Tachikawa_Socle`, `Tachikawa_StableLift`.
--
--   **Imports.** It imports the bundles `OAIQ116Ta017`, `OAIQ116Ta007` and `OAIQ116Ta008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ116Ta014` and `OAIQ116Ta015`.
-- source:
--   OpenAI, A counterexample to Tachikawa's second conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ116Ta017
import Definitions.Def_OAIQ116Ta007
import Definitions.Def_OAIQ116Ta008

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coresolution
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa.VectorSplit
open CategoryTheory HomologicalComplex
variable {k : Type*} [Field k] {I : Type*} {c : ComplexShape I}
variable (K : HomologicalComplex (ModuleCat k) c)

abbrev homologyComplex : HomologicalComplex (ModuleCat k) c where
  X i := ModuleCat.of k (H K i)
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

def inclusion : homologyComplex K ⟶ K where
  f i := ModuleCat.ofHom ((inc K i).comp (representatives K i))
  comm' i j _ := by
    rw [show (homologyComplex K).d i j = 0 from rfl, Limits.zero_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change H K i at x
    change K.d i j (representatives K i x) = 0
    exact cycle_d K i j _

def projection : K ⟶ homologyComplex K where
  f i := ModuleCat.ofHom ((quotient K i).comp (retract K i))
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change 0 = quotient K j (retract K j (K.d i j x))
    have hi : c.prev j = i := c.prev_eq' hij
    subst i
    change 0 = quotient K j (retract K j (boundary K j x))
    rw [retract_cycle, quotient_boundary]

lemma inclusion_projection : inclusion K ≫ projection K = 𝟙 (homologyComplex K) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change H K i at x
  change quotient K i (retract K i (representatives K i x)) = x
  rw [retract_cycle, quotient_representatives_apply]

def idHomotopy : Homotopy (𝟙 K) (projection K ≫ inclusion K) where
  hom := hom K
  zero := hom_eq_zero K
  comm i := by
    change 𝟙 (K.X i) = K.d i (c.next i) ≫ hom K (c.next i) i +
      hom K i (c.prev i) ≫ K.d (c.prev i) i + (projection K ≫ inclusion K).f i
    rw [d_hom]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change x = complement K i x + (hom K i (c.prev i) ≫ K.d (c.prev i) i) x +
      inc K i (representatives K i (quotient K i (retract K i x)))
    rw [hom_d]
    change x = (x - inc K i (retract K i x)) +
      (inc K i (retract K i x) - inc K i (representatives K i (quotient K i (retract K i x)))) +
      inc K i (representatives K i (quotient K i (retract K i x)))
    abel

def homologyHomotopyEquiv : HomotopyEquiv K (homologyComplex K) where
  hom := projection K
  inv := inclusion K
  homotopyHomInvId := (idHomotopy K).symm
  homotopyInvHomId := Homotopy.ofEq (inclusion_projection K)

end Tachikawa.VectorSplit



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_OuterTensor
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.objFinite _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section
set_option backward.isDefEq.respectTransparency true



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

@[simp] lemma freeAt_single {m : ℕ} (i j : Fin m) (U : ModuleCat A) (u : U) :
    freeAt (k := k) i U u (freeBasis A j) = if i = j then u else 0 := by
  change ((Pi.single j 1 : Fin m → A) i) • u = _
  by_cases h : i = j
  · subst j; simp
  · simp [h]

variable {U : ModuleCat A} {V : ModuleCat B}

def freeValue {m n : ℕ}
    (f : ((bifunctor k A B).obj (freeObj A m)).obj (freeObj B n) ⟶
      ((bifunctor k A B).obj U).obj V) (i : Fin m) (j : Fin n) : U ⊗[k] V :=
  f.hom (freeTensorBasis (k := k) i j)

def freeLift {m n : ℕ}
    (f : ((bifunctor k A B).obj (freeObj A m)).obj (freeObj B n) ⟶
      ((bifunctor k A B).obj U).obj V) :
    (freeObj A m ⟶ U) ⊗[k] (freeObj B n ⟶ V) :=
  ∑ i, ∑ j, TensorProduct.map (freeAt (k := k) i U) (freeAt (k := k) j V)
    (freeValue f i j)

lemma freeLift_single_component {m n : ℕ} (i i' : Fin m) (j j' : Fin n) (z : U ⊗[k] V) :
    (homMap (TensorProduct.map (freeAt (k := k) i U) (freeAt (k := k) j V) z)).hom
      (freeTensorBasis (k := k) (A := A) (B := B) i' j') =
      if i = i' ∧ j = j' then z else 0 := by
  induction z using OAI.tensorInductionOn with
  | tmul u v =>
    change (freeAt (k := k) i U u (freeBasis A i')) ⊗ₜ[k]
      (freeAt (k := k) j V v (freeBasis B j')) = _
    simp only [freeAt_single]
    split_ifs <;> simp_all
  | add z w hz hw =>
    simp only [map_add, ModuleCat.hom_add]
    change (homMap (TensorProduct.map (freeAt (k := k) i U) (freeAt (k := k) j V) z)).hom
        (freeTensorBasis (k := k) i' j') +
      (homMap (TensorProduct.map (freeAt (k := k) i U) (freeAt (k := k) j V) w)).hom
        (freeTensorBasis (k := k) i' j') = _
    rw [hz, hw]
    split_ifs
    · rfl
    · exact zero_add _

lemma homMap_freeLift_single {m n : ℕ}
    (f : ((bifunctor k A B).obj (freeObj A m)).obj (freeObj B n) ⟶
      ((bifunctor k A B).obj U).obj V) (i : Fin m) (j : Fin n) :
    (homMap (freeLift f)).hom (freeTensorBasis (k := k) (A := A) (B := B) i j) =
      f.hom (freeTensorBasis (k := k) (A := A) (B := B) i j) := by
  classical
  let ev : (((bifunctor k A B).obj (freeObj A m)).obj (freeObj B n) ⟶
      ((bifunctor k A B).obj U).obj V) →+ (U ⊗[k] V) :=
    { toFun := fun g => g.hom (freeTensorBasis (k := k) i j)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (homMap (freeLift f)) = _
  simp only [freeLift, map_sum]
  change (∑ a, ∑ b, (homMap (TensorProduct.map (freeAt (k := k) a U)
    (freeAt (k := k) b V) (freeValue f a b))).hom
    (freeTensorBasis (k := k) i j)) = _
  simp only [freeLift_single_component]
  change (∑ a : Fin m, ∑ b : Fin n,
    (if a = i ∧ b = j then freeValue f a b else 0) : U ⊗[k] V) = freeValue f i j
  have hs (v : Fin m → Fin n → U ⊗[k] V) :
      (∑ a, ∑ b, if a = i ∧ b = j then v a b else 0) = v i j := by
    simp [ite_and, Finset.sum_ite_irrel]
  exact hs (freeValue f)

lemma freeEquiv_single {m n : ℕ} (i : Fin m) (j : Fin n) :
    freeEquiv k A B m n (freeTensorBasis (k := k) (A := A) (B := B) i j) =
      Pi.single i (Pi.single j 1) := by
  ext a b
  change ((Pi.single i 1 : Fin m → A) a) ⊗ₜ[k] ((Pi.single j 1 : Fin n → B) b) = _
  by_cases ha : a = i <;> by_cases hb : b = j <;> subst_vars <;>
    simp_all [Algebra.TensorProduct.one_def]

lemma freeHom_ext {m n : ℕ}
    (f g : ((bifunctor k A B).obj (freeObj A m)).obj (freeObj B n) ⟶
      ((bifunctor k A B).obj U).obj V)
    (h : ∀ i j, f.hom (freeTensorBasis (k := k) (A := A) (B := B) i j) =
      g.hom (freeTensorBasis (k := k) (A := A) (B := B) i j)) : f = g := by
  let e := freeEquiv k A B m n
  have hs (i : Fin m) (j : Fin n) : e.symm (Pi.single i (Pi.single j 1)) =
      freeTensorBasis (k := k) (A := A) (B := B) i j :=
    e.symm_apply_eq.mpr (freeEquiv_single (k := k) i j).symm
  have he : f.hom.comp e.symm.toLinearMap = g.hom.comp e.symm.toLinearMap := by
    apply LinearMap.pi_ext'
    intro i
    apply LinearMap.pi_ext'
    intro j
    apply LinearMap.ext_ring
    change f.hom (e.symm (Pi.single i (Pi.single j 1))) =
      g.hom (e.symm (Pi.single i (Pi.single j 1)))
    rw [hs]
    exact h i j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have hz := LinearMap.congr_fun he (e z)
  change f.hom (e.symm (e z)) = g.hom (e.symm (e z)) at hz
  exact (congrArg f.hom (e.symm_apply_apply z)).symm.trans
    (hz.trans (congrArg g.hom (e.symm_apply_apply z)))

lemma homMap_freeLift {m n : ℕ}
    (f : ((bifunctor k A B).obj (freeObj A m)).obj (freeObj B n) ⟶
      ((bifunctor k A B).obj U).obj V) : homMap (freeLift f) = f :=
  freeHom_ext _ _ (homMap_freeLift_single f)

lemma homMap_free_surjective (m n : ℕ) :
    Function.Surjective (homMap (k := k) (M := freeObj A m) (N := freeObj B n)
      (U := U) (V := V)) := fun f => ⟨freeLift f, homMap_freeLift f⟩

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

lemma homMap_precompose {M M' U : ModuleCat A} {N N' V : ModuleCat B}
    (p : M' ⟶ M) (q : N' ⟶ N) (z : (M ⟶ U) ⊗[k] (N ⟶ V)) :
    homMap (TensorProduct.map (precompose (k := k) p) (precompose (k := k) q) z) =
      morphism p q ≫ homMap z := by
  induction z using OAI.tensorInductionOn with
  | tmul f g =>
    change morphism (p ≫ f) (q ≫ g) = morphism p q ≫ morphism f g
    exact (morphism_comp p f q g).symm
  | add z w hz hw => simp only [map_add, Preadditive.comp_add, hz, hw]

lemma homMap_surjective (M U : ModuleCat A) (N V : ModuleCat B)
    [Module.Finite A M] [Module.Finite B N] [Module.Projective A M] [Module.Projective B N] :
    Function.Surjective (homMap (k := k) (M := M) (N := N) (U := U) (V := V)) := by
  let c := finiteFreeCover (R := A) (M := M)
  let d := finiteFreeCover (R := B) (M := N)
  obtain ⟨i,hi⟩ := Module.projective_lifting_property c.map LinearMap.id c.surjective
  obtain ⟨j,hj⟩ := Module.projective_lifting_property d.map LinearMap.id d.surjective
  intro f
  let p : freeObj A c.rank ⟶ M := ModuleCat.ofHom c.map
  let q : freeObj B d.rank ⟶ N := ModuleCat.ofHom d.map
  let u : M ⟶ freeObj A c.rank := ModuleCat.ofHom i
  let v : N ⟶ freeObj B d.rank := ModuleCat.ofHom j
  obtain ⟨z,hz⟩ := homMap_free_surjective (k := k) c.rank d.rank (morphism p q ≫ f)
  refine ⟨TensorProduct.map (precompose (k := k) u) (precompose (k := k) v) z, ?_⟩
  rw [homMap_precompose, hz, ← Category.assoc, morphism_comp]
  have hu : u ≫ p = 𝟙 M := ModuleCat.hom_ext hi
  have hv : v ≫ q = 𝟙 N := ModuleCat.hom_ext hj
  rw [hu,hv,morphism_id,Category.id_comp]

def homEquiv (M U : ModuleCat A) (N V : ModuleCat B)
    [Module.Finite A M] [Module.Finite B N] [Module.Projective A M] [Module.Projective B N]
    [FiniteDimensional k M] [FiniteDimensional k N] :
    (M ⟶ U) ⊗[k] (N ⟶ V) ≃ₗ[k]
      (((bifunctor k A B).obj M).obj N ⟶ ((bifunctor k A B).obj U).obj V) :=
  LinearEquiv.ofBijective homMap ⟨homMap_injective,homMap_surjective M U N V⟩

end Tachikawa.OuterTensor

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_OuterExt
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.objFinite _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa.OuterTensor
open CategoryTheory HomologicalComplex
open scoped TensorProduct
variable (k A B : Type) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  {K K' : ChainComplex (ModuleCat A) ℕ} {L L' : ChainComplex (ModuleCat B) ℕ}

lemma quasiIso (f : K ⟶ K') (g : L ⟶ L') [QuasiIso f] [QuasiIso g] :
    QuasiIso (mapBifunctorMap f g (bifunctor k A B) (.down ℕ)) := by
  apply (quasiIso_map_iff_of_preservesHomology _ (forgetE k A B)).mp
  rw [← quasiIso_iff_comp_right _ (forgetTotalIso k A B K' L' (.down ℕ)).hom,
    forgetTotalIso_natural]
  have := vectorTensor_quasiIso (((forgetA k A).mapHomologicalComplex (.down ℕ)).map f)
    (((forgetB k B).mapHomologicalComplex (.down ℕ)).map g)
  infer_instance

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory HomologicalComplex
open scoped TensorProduct
variable (k A B : Type) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  {M : ModuleCat A} {N : ModuleCat B}
  (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
  (hP : ∀ n, Module.Finite A (P.complex.X n))
  (hQ : ∀ n, Module.Finite B (Q.complex.X n))

include hP hQ in
lemma total_projective (n : ℕ) :
    Projective ((mapBifunctor P.complex Q.complex (bifunctor k A B) (.down ℕ)).X n) := by
  let (i : ℕ) : Module.Finite A (P.complex.X i) := hP i
  let (i : ℕ) : Module.Finite B (Q.complex.X i) := hQ i
  have (i j : ℕ) : Module.Projective (A ⊗[k] B)
      (Obj k A B (P.complex.X i) (Q.complex.X j)) := projective k A B _ _
  have (i j : ℕ) : Projective
      (((bifunctor k A B).obj (P.complex.X i)).obj (Q.complex.X j)) := by
    change Projective (ModuleCat.of (A ⊗[k] B) (Obj k A B (P.complex.X i) (Q.complex.X j)))
    infer_instance
  change Projective (∐ fun ij : {ij : ℕ × ℕ // ij.1 + ij.2 = n} =>
    ((bifunctor k A B).obj (P.complex.X ij.val.1)).obj (Q.complex.X ij.val.2))
  infer_instance

def resolution : ProjectiveResolution ((bifunctor k A B).obj M |>.obj N) where
  complex := mapBifunctor P.complex Q.complex (bifunctor k A B) (.down ℕ)
  projective := total_projective k A B P Q hP hQ
  π := mapBifunctorMap P.π Q.π (bifunctor k A B) (.down ℕ) ≫
    (bifunctorSingleIso (bifunctor k A B) M N).hom
  quasiIso := by
    have := quasiIso k A B P.π Q.π
    infer_instance

end Tachikawa.OuterTensor



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Socle
attribute [-instance] _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCe _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCf _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleEC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleFC _root_.OAI.Tachikawa.Construction.instProjectiveMulOppositeC _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.objFinite _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

abbrev XTensorObj : ModuleCat (E q) :=
  ((OuterTensor.bifunctor k (T q) (T q)).obj (C.simpleObj q)).obj (C.simpleObj q)

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra TensorProduct
variable {k : Type} [Field k] [CharP k 2] (q : k)

def sCanon : ModuleCat (T q) := C.simpleObj q

omit [CharP k 2] in
def simpleUnderlying : sCanon q ≃ₗ[k] k where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change characterT q (algebraMap k (T q) c) * (show k from x) = c * (show k from x)
    rw [AlgHom.commutes]
    simp

omit [CharP k 2] in
def XTensorUnderlying : OuterTensor.Obj k (T q) (T q) (sCanon q) (sCanon q) ≃ₗ[k] k :=
  (TensorProduct.congr (simpleUnderlying q) (simpleUnderlying q)).trans (TensorProduct.lid k k)

omit [CharP k 2] in
lemma XTensorUnderlying_smul (a : E q)
    (x : OuterTensor.Obj k (T q) (T q) (sCanon q) (sCanon q)) :
    XTensorUnderlying q (a • x) = characterE q a * XTensorUnderlying q x := by
  induction a using OAI.tensorInductionOn with
  | add a b ha hb => simp only [add_smul,map_add,ha,hb,add_mul]
  | tmul a b =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy =>
      erw [smul_add, map_add, hx, hy, map_add, mul_add]
    | tmul x y =>
      change (characterT q a * simpleUnderlying q x) *
        (characterT q b * simpleUnderlying q y) =
        (characterT q a * characterT q b) * (simpleUnderlying q x * simpleUnderlying q y)
      ring

omit [CharP k 2] in

def XTensorEquiv : XTensorObj q ≃ₗ[E q] X q where
  toFun := XTensorUnderlying q
  invFun := (XTensorUnderlying q).symm
  left_inv := (XTensorUnderlying q).left_inv
  right_inv := (XTensorUnderlying q).right_inv
  map_add' := (XTensorUnderlying q).map_add
  map_smul' a x := XTensorUnderlying_smul q a x

end Tachikawa.Construction



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_ReverseResolution
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {k : Type} [Field k]

lemma vectorTensor_quasiIso_int
    {K L M N : ChainComplex (ModuleCat k) ℤ} (f : K ⟶ L) (g : M ⟶ N)
    [QuasiIso f] [QuasiIso g] :
    QuasiIso (mapBifunctorMap f g
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat k)) (.down ℤ)) := by
  let F := CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat k)
  let ef := VectorSplit.homologyHomotopyEquiv K
  let el := VectorSplit.homologyHomotopyEquiv L
  let em := VectorSplit.homologyHomotopyEquiv M
  let en := VectorSplit.homologyHomotopyEquiv N
  let := ef.quasiIso_inv
  let := el.quasiIso_hom
  let := em.quasiIso_inv
  let := en.quasiIso_hom
  let f' := ef.inv ≫ f ≫ el.hom
  let g' := em.inv ≫ g ≫ en.hom
  have : IsIso f' := zeroDifferential_isIso_of_quasiIso f' (fun _ _ => rfl) (fun _ _ => rfl)
  have : IsIso g' := zeroDifferential_isIso_of_quasiIso g' (fun _ _ => rfl) (fun _ _ => rfl)
  let ei := bifunctorHomotopyEquiv F (.down ℤ) ef.symm em.symm
  let ep := bifunctorHomotopyEquiv F (.down ℤ) el en
  let := ei.quasiIso_hom
  let := ep.quasiIso_hom
  have hh : QuasiIso (ei.hom ≫ mapBifunctorMap f g F (.down ℤ) ≫ ep.hom) := by
    change QuasiIso (mapBifunctorMap ef.inv em.inv F (.down ℤ) ≫
      mapBifunctorMap f g F (.down ℤ) ≫ mapBifunctorMap el.hom en.hom F (.down ℤ))
    rw [bifunctorMap_comp, bifunctorMap_comp]
    change QuasiIso (mapBifunctorMap f' g' F (.down ℤ))
    exact (bifunctorHomotopyEquiv F (.down ℤ) (HomotopyEquiv.ofIso (asIso f')) (HomotopyEquiv.ofIso (asIso g'))).quasiIso_hom
  exact (quasiIso_iff_comp_right _ ep.hom).mp ((quasiIso_iff_comp_left ei.hom _).mp hh)

end Tachikawa



namespace Tachikawa.OuterTensor
open CategoryTheory HomologicalComplex
open scoped TensorProduct
variable (k A B : Type) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  {K K' : ChainComplex (ModuleCat A) ℤ} {L L' : ChainComplex (ModuleCat B) ℤ}

lemma quasiIso_int (f : K ⟶ K') (g : L ⟶ L') [QuasiIso f] [QuasiIso g] :
    QuasiIso (mapBifunctorMap f g (bifunctor k A B) (.down ℤ)) := by
  apply (quasiIso_map_iff_of_preservesHomology _ (forgetE k A B)).mp
  rw [← quasiIso_iff_comp_right _ (forgetTotalIso k A B K' L' (.down ℤ)).hom,
    forgetTotalIso_natural]
  have := vectorTensor_quasiIso_int (((forgetA k A).mapHomologicalComplex (.down ℤ)).map f)
    (((forgetB k B).mapHomologicalComplex (.down ℤ)).map g)
  infer_instance

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

lemma total_isZero_above (P : ChainComplex (ModuleCat.{0} A) ℕ)
    (Q : ChainComplex (ModuleCat.{0} B) ℕ) (a b : ℕ)
    (hP : ∀ i, a < i → IsZero (P.X i)) (hQ : ∀ j, b < j → IsZero (Q.X j))
    (n : ℕ) (hn : a+b < n) :
    IsZero ((mapBifunctor P Q (bifunctor k A B) (.down ℕ)).X n) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  have h : IsZero (((bifunctor k A B).obj (P.X i)).obj (Q.X j)) := by
    by_cases hi : a < i
    · exact isZero_obj_left _ _ (hP i hi)
    · exact isZero_obj_right _ _ (hQ j (by dsimp at hij; omega))
  exact h.eq_of_src _ _

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (P : ChainComplex (ModuleCat.{0} A) ℤ) (Q : ChainComplex (ModuleCat.{0} B) ℤ)

lemma total_projective_int (hP : ∀ i, Module.Finite A (P.X i))
    (hQ : ∀ j, Module.Finite B (Q.X j))
    (pP : ∀ i, Module.Projective A (P.X i))
    (pQ : ∀ j, Module.Projective B (Q.X j)) (n : ℤ) :
    Projective ((mapBifunctor P Q (bifunctor k A B) (.down ℤ)).X n) := by
  let (i : ℤ) : Module.Finite A (P.X i) := hP i
  let (j : ℤ) : Module.Finite B (Q.X j) := hQ j
  let (i : ℤ) : Module.Projective A (P.X i) := pP i
  let (j : ℤ) : Module.Projective B (Q.X j) := pQ j
  have (i j : ℤ) : Module.Projective (A ⊗[k] B) (Obj k A B (P.X i) (Q.X j)) :=
    projective k A B _ _
  have (i j : ℤ) : Projective (((bifunctor k A B).obj (P.X i)).obj (Q.X j)) := by
    change Projective (ModuleCat.of (A ⊗[k] B) (Obj k A B (P.X i) (Q.X j)))
    infer_instance
  change Projective (∐ fun ij : {ij : ℤ × ℤ // ij.1+ij.2=n} =>
    ((bifunctor k A B).obj (P.X ij.val.1)).obj (Q.X ij.val.2))
  infer_instance

lemma total_finite_below_int (a b : ℤ)
    (hP : ∀ i, FiniteDimensional k (P.X i)) (hQ : ∀ j, FiniteDimensional k (Q.X j))
    (zP : ∀ i, i < a → IsZero (P.X i)) (zQ : ∀ j, j < b → IsZero (Q.X j))
    (n : ℤ) : Module.Finite (A ⊗[k] B)
      ((mapBifunctor P Q (bifunctor k A B) (.down ℤ)).X n) := by
  let I := {ij : ℤ × ℤ // ij.1+ij.2=n}
  let F := fun ij : I => ((bifunctor k A B).obj (P.X ij.val.1)).obj (Q.X ij.val.2)
  let p : I → Prop := fun ij => a ≤ ij.val.1 ∧ b ≤ ij.val.2
  let : Finite {i // p i} := by
    let f : {i // p i} → Set.Icc a (n-b) := fun i => ⟨i.val.val.1, by
      have h := i.property
      have hi := i.val.property
      dsimp [p] at h
      exact ⟨h.1, by omega⟩⟩
    apply Finite.of_injective f
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z => z.val) h
    · have hh := congrArg (fun z => z.val) h
      have hx := x.val.property
      have hy := y.val.property
      change x.val.val.1 = y.val.val.1 at hh
      omega
  let (i : ℤ) : FiniteDimensional k (P.X i) := hP i
  let (j : ℤ) : FiniteDimensional k (Q.X j) := hQ j
  change Module.Finite (A ⊗[k] B) (∐ F : ModuleCat (A ⊗[k] B))
  apply coproduct_finite_of_support F p
  · intro i hi
    by_cases h : a ≤ i.val.1
    · exact isZero_obj_right _ _ (zQ i.val.2 (by dsimp [p] at hi; omega))
    · exact isZero_obj_left _ _ (zP i.val.1 (by omega))
  · intro i
    exact objFinite _ _

lemma total_finite_above_int (a b : ℤ)
    (hP : ∀ i, FiniteDimensional k (P.X i)) (hQ : ∀ j, FiniteDimensional k (Q.X j))
    (zP : ∀ i, a < i → IsZero (P.X i)) (zQ : ∀ j, b < j → IsZero (Q.X j))
    (n : ℤ) : Module.Finite (A ⊗[k] B)
      ((mapBifunctor P Q (bifunctor k A B) (.down ℤ)).X n) := by
  let I := {ij : ℤ × ℤ // ij.1+ij.2=n}
  let F := fun ij : I => ((bifunctor k A B).obj (P.X ij.val.1)).obj (Q.X ij.val.2)
  let p : I → Prop := fun ij => ij.val.1 ≤ a ∧ ij.val.2 ≤ b
  let : Finite {i // p i} := by
    let f : {i // p i} → Set.Icc (n-b) a := fun i => ⟨i.val.val.1, by
      have h := i.property
      have hi := i.val.property
      dsimp [p] at h
      exact ⟨by omega,h.1⟩⟩
    apply Finite.of_injective f
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z => z.val) h
    · have hh := congrArg (fun z => z.val) h
      have hx := x.val.property
      have hy := y.val.property
      change x.val.val.1 = y.val.val.1 at hh
      omega
  let (i : ℤ) : FiniteDimensional k (P.X i) := hP i
  let (j : ℤ) : FiniteDimensional k (Q.X j) := hQ j
  change Module.Finite (A ⊗[k] B) (∐ F : ModuleCat (A ⊗[k] B))
  apply coproduct_finite_of_support F p
  · intro i hi
    by_cases h : i.val.1 ≤ a
    · exact isZero_obj_right _ _ (zQ i.val.2 (by dsimp [p] at hi; omega))
    · exact isZero_obj_left _ _ (zP i.val.1 (by omega))
  · intro i
    exact objFinite _ _

end Tachikawa.OuterTensor

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Bimodule
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.resFinite _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCe _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCf _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleEC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleFC _root_.OAI.Tachikawa.Construction.instProjectiveMulOppositeC _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.coindEndo_finite _root_.OAI.Tachikawa.Enveloping.coindObj_finite _root_.OAI.Tachikawa.Enveloping.dualRegularLeftInjective _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instAddCommGroupRightIndType _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatAlgRightIndFunctor _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatMulOppositeAlgCoindFunctor _root_.OAI.Tachikawa.Enveloping.instEpiModuleCatAlgCoindπ _root_.OAI.Tachikawa.Enveloping.instFiniteDimensionalCarrierAlgCoindObjOfMulOpposite _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerMulOppositeCarrierRightObj _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerMulOppositeRightIndType _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerRightIndType _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.Enveloping.instModuleMulOppositeRightIndType _root_.OAI.Tachikawa.Enveloping.instModuleRightIndType _root_.OAI.Tachikawa.Enveloping.instModuleRightIndType_1 _root_.OAI.Tachikawa.Enveloping.instMonoFunctorModuleCatAlgCoindUnitNat _root_.OAI.Tachikawa.Enveloping.instMonoModuleCatAlgCoindUnit _root_.OAI.Tachikawa.Enveloping.instSMulCommClassMulOppositeCarrierRightObj _root_.OAI.Tachikawa.Enveloping.instSMulCommClassMulOppositeRightIndType _root_.OAI.Tachikawa.Enveloping.leftFunctor_reflectsIsomorphisms _root_.OAI.Tachikawa.Enveloping.regular_left_projective _root_.OAI.Tachikawa.Enveloping.regular_right_projective _root_.OAI.Tachikawa.Enveloping.rightFunctor_finite _root_.OAI.Tachikawa.Enveloping.rightFunctor_reflectsIsomorphisms _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

omit [CharP k 2] in
lemma reverseObj_finite (j : ℤ) : Module.Finite k (C.reverseObj q j) := by
  let : Module.Finite k (C.Ce q) := Module.Finite.of_injective
    ((C.Ce q).subtype.restrictScalars k) Subtype.val_injective
  let : Module.Finite k (C.Cf q) := Module.Finite.of_injective
    ((C.Cf q).subtype.restrictScalars k) Subtype.val_injective
  let : Module.Finite (C k q) (C.Ce q) := Module.Finite.of_restrictScalars_finite k _ _
  let : Module.Finite (C k q) (C.Cf q) := Module.Finite.of_restrictScalars_finite k _ _
  have hE : Module.Finite (C k q) (ModuleCat.of (C k q) (C.Ce q)) := inferInstance
  have hF : Module.Finite (C k q) (ModuleCat.of (C k q) (C.Cf q)) := inferInstance
  have hf : Module.Finite (C k q) (C.reverseObj q j) := by
    cases j with
    | ofNat n =>
      rcases n with _ | _ | _ | n
      · exact hE
      · exact hE
      · exact hF
      · exact inferInstanceAs (Module.Finite (C k q) PUnit)
    | negSucc n => exact hE
  exact Module.Finite.trans (C k q) (C.reverseObj q j)

omit [CharP k 2] in
lemma reverseObj_projective (j : ℤ) : Module.Projective (C k q) (C.reverseObj q j) := by
  cases j with
  | ofNat n =>
    rcases n with _ | _ | _ | n
    · exact inferInstanceAs (Module.Projective (C k q) (C.Ce q))
    · exact inferInstanceAs (Module.Projective (C k q) (C.Ce q))
    · exact inferInstanceAs (Module.Projective (C k q) (C.Cf q))
    · exact inferInstanceAs (Module.Projective (C k q) PUnit)
  | negSucc n => exact inferInstanceAs (Module.Projective (C k q) (C.Ce q))

lemma reverseJ_finite (hq : q ≠ 0) (j : ℤ) :
    Module.Finite k ((reverseJ q hq).X j) := by
  let := reverseObj_finite q j
  have : Module.Finite k (TrivialInduction.Obj k (C k q) (C.reverseObj q j)) := inferInstance
  let : Module.Finite (C.T q) (TrivialInduction.Obj k (C k q) (C.reverseObj q j)) :=
    Module.Finite.of_restrictScalars_finite k _ _
  have : Module.Finite (C.T q) ((reverseJ q hq).X j) := by
    change Module.Finite (C.T q) (TrivialInduction.Obj k (C k q) (C.reverseObj q j))
    infer_instance
  exact Module.Finite.trans (C.T q) ((reverseJ q hq).X j)

lemma reverseJ_projective (hq : q ≠ 0) (j : ℤ) :
    Module.Projective (C.T q) ((reverseJ q hq).X j) := by
  let := reverseObj_finite q j
  let : Module.Finite (C k q) (C.reverseObj q j) := Module.Finite.of_restrictScalars_finite k _ _
  let := reverseObj_projective q j
  change Module.Projective (C.T q) (TrivialInduction.Obj k (C k q) (C.reverseObj q j))
  infer_instance

lemma reverseJJ_finite (hq : q ≠ 0) (j : ℤ) :
    Module.Finite (E q) ((reverseJJ q hq).X j) :=
  OuterTensor.total_finite_above_int _ _ 2 2 (reverseJ_finite q hq) (reverseJ_finite q hq)
    (reverseJ_above q hq) (reverseJ_above q hq) j

lemma reverseJJ_projective (hq : q ≠ 0) (j : ℤ) :
    Module.Projective (E q) ((reverseJJ q hq).X j) := by
  have h (i : ℤ) : Module.Finite (C.T q) ((reverseJ q hq).X i) := by
    let := reverseJ_finite q hq i
    exact Module.Finite.of_restrictScalars_finite k _ _
  let := OuterTensor.total_projective_int (k := k) _ _ h h (reverseJ_projective q hq) (reverseJ_projective q hq) j
  infer_instance

end Tachikawa.Construction



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
namespace Enveloping
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat.{0} R) (M : ModuleCat.{0} (Alg k S R))

instance evaluation_projective [CategoryTheory.Projective M] :
    CategoryTheory.Projective (evalObj X M) where
  factors {Z Z'} f g _ := by
    obtain ⟨h, hh⟩ := CategoryTheory.Projective.factors (BimoduleTensorHom.curry f)
      (HomBimodule.postMap (k := k) X g)
    refine ⟨BimoduleTensorHom.uncurry h, ?_⟩
    rw [← BimoduleTensorHom.uncurry_postcompose, hh, BimoduleTensorHom.uncurry_curry]

end Enveloping
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat.{0} R)

def evaluationAdjunction : Enveloping.evaluation (k := k) (S := S) X ⊣
    homBimoduleFunctor (k := k) (S := S) X :=
  Adjunction.mkOfHomEquiv
  { homEquiv := fun M Z => (BimoduleTensorHom.equiv (M := M) (X := X) (Z := Z)).toEquiv.symm
    homEquiv_naturality_left_symm := by
      intro M M' Z f g
      exact BimoduleTensorHom.uncurry_precompose f g
    homEquiv_naturality_right := by
      intro M Z Z' f g
      apply (BimoduleTensorHom.equiv (M := M) (X := X) (Z := Z')).injective
      change BimoduleTensorHom.uncurry (BimoduleTensorHom.curry (f ≫ g)) =
        BimoduleTensorHom.uncurry (BimoduleTensorHom.curry f ≫ HomBimodule.postMap X g)
      exact (BimoduleTensorHom.uncurry_curry (f ≫ g)).trans
        ((congrArg (fun h => h ≫ g) (BimoduleTensorHom.uncurry_curry f)).symm.trans
          (BimoduleTensorHom.uncurry_postcompose (BimoduleTensorHom.curry f) g).symm) }

end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (t : SymmetrizingForm (k := k) (R := R))
  (u : SymmetrizingForm (k := k) (R := S))
  (M : FiniteModule k (Alg k R S))

lemma cosyzygy_left_projective [Module.Projective R (Obj M.obj)] :
    Module.Projective R (Obj (M.cosyzygy (envelopingForm t u)).obj) := by
  let : Module.Finite R (Obj M.obj) := Module.Finite.of_restrictScalars_finite k R _
  let : Module.Injective R R := t.injective
  let : Module.Injective R (Obj M.obj) := injective_of_finite_projective
  let τ := envelopingForm t u
  let J := ModuleCat.of (Alg k R S) (Fin (Module.finrank k M) → Alg k R S)
  let : Module.Projective R (Obj J) := freeLeftProjective _
  let i : M.obj ⟶ J := ModuleCat.ofHom (M.embed τ)
  let q : J ⟶ (M.cosyzygy τ).obj := ModuleCat.ofHom (LinearMap.range (M.embed τ)).mkQ
  apply projective_cokernel_of_injective (leftMap i) (leftMap q)
  · exact M.embed_injective τ
  · change Function.Surjective (Submodule.mkQ (LinearMap.range (M.embed τ)))
    exact Submodule.mkQ_surjective _
  · change Function.Exact (M.embed τ) (Submodule.mkQ (LinearMap.range (M.embed τ)))
    intro x
    exact Submodule.Quotient.mk_eq_zero _

lemma cosyzygy_right_projective [Module.Projective Sᵐᵒᵖ (Obj M.obj)] :
    Module.Projective Sᵐᵒᵖ (Obj (M.cosyzygy (envelopingForm t u)).obj) := by
  let : Module.Finite Sᵐᵒᵖ (Obj M.obj) := Module.Finite.of_restrictScalars_finite k Sᵐᵒᵖ _
  let : Module.Injective Sᵐᵒᵖ Sᵐᵒᵖ := u.op.injective
  let : Module.Injective Sᵐᵒᵖ (Obj M.obj) := injective_of_finite_projective
  let τ := envelopingForm t u
  let J := ModuleCat.of (Alg k R S) (Fin (Module.finrank k M) → Alg k R S)
  let : Module.Projective Sᵐᵒᵖ (Obj J) := freeRightProjective _
  let i : M.obj ⟶ J := ModuleCat.ofHom (M.embed τ)
  let q : J ⟶ (M.cosyzygy τ).obj := ModuleCat.ofHom (LinearMap.range (M.embed τ)).mkQ
  apply projective_cokernel_of_injective (rightMap i) (rightMap q)
  · exact M.embed_injective τ
  · change Function.Surjective (Submodule.mkQ (LinearMap.range (M.embed τ)))
    exact Submodule.mkQ_surjective _
  · change Function.Exact (M.embed τ) (Submodule.mkQ (LinearMap.range (M.embed τ)))
    intro x
    exact Submodule.Quotient.mk_eq_zero _

theorem negative_side_projective (n : ℕ)
    [Module.Projective R (Obj M.obj)] [Module.Projective Sᵐᵒᵖ (Obj M.obj)] :
    Module.Projective R (Obj (M.negative (envelopingForm t u) n).obj) ∧
      Module.Projective Sᵐᵒᵖ (Obj (M.negative (envelopingForm t u) n).obj) := by
  induction n with
  | zero => change Module.Projective R (Obj M.obj) ∧ Module.Projective Sᵐᵒᵖ (Obj M.obj)
            exact ⟨inferInstance,inferInstance⟩
  | succ n ih =>
    let := ih.1
    let := ih.2
    exact ⟨cosyzygy_left_projective t u _,cosyzygy_right_projective t u _⟩

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (φ : R →ₐ[k] S)

instance inducedRegularComplex_rightProjective (n : ℕ) :
    Module.Projective Sᵐᵒᵖ (Obj ((inducedRegularComplex φ).X n)) := projective_right _

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (φ : R →ₐ[k] S)

def homBimoduleRestrictionEquiv (X Z : ModuleCat.{0} S) :
    (AlgebraInduction.res (Enveloping.envelopingMap φ)).obj (HomBimodule.obj (k := k) X Z) ≃ₗ[
      Enveloping.Alg k R R]
        HomBimodule.obj (k := k) ((AlgebraInduction.res φ).obj X) ((AlgebraInduction.res φ).obj Z) where
  toFun f := (restrictionUnderlyingEquiv φ Z).symm.toLinearMap.comp
    ((show X →ₗ[k] Z from f).comp (restrictionUnderlyingEquiv φ X).toLinearMap)
  invFun f := (restrictionUnderlyingEquiv φ Z).toLinearMap.comp
    ((show (AlgebraInduction.res φ).obj X →ₗ[k] (AlgebraInduction.res φ).obj Z from f).comp
      (restrictionUnderlyingEquiv φ X).symm.toLinearMap)
  left_inv f := by apply LinearMap.ext; intro x; rfl
  right_inv f := by apply LinearMap.ext; intro x; rfl
  map_add' f g := by apply LinearMap.ext; intro x; rfl
  map_smul' a f := by
    apply LinearMap.ext
    intro x
    induction a using OAI.tensorInductionOn with
    | tmul r s => rfl
    | add a b ha hb =>
      change (show X →ₗ[k] Z from (Enveloping.envelopingMap φ (a+b)) •
        (show HomBimodule.obj (k := k) X Z from f)) x = _
      simp only [map_add]
      erw [add_smul, add_smul]
      exact congrArg₂ (fun u v => u+v) ha hb

def homBimoduleRestrictionIso (X Z : ModuleCat.{0} S) :
    (AlgebraInduction.res (Enveloping.envelopingMap φ)).obj (HomBimodule.obj (k := k) X Z) ≅
      HomBimodule.obj (k := k) ((AlgebraInduction.res φ).obj X) ((AlgebraInduction.res φ).obj Z) :=
  LinearEquiv.toModuleIso (homBimoduleRestrictionEquiv φ X Z)

def homBimoduleRestriction (X : ModuleCat.{0} S) :
    homBimoduleFunctor (k := k) X ⋙ AlgebraInduction.res (Enveloping.envelopingMap φ) ≅
      AlgebraInduction.res φ ⋙ homBimoduleFunctor (k := k) ((AlgebraInduction.res φ).obj X) :=
  NatIso.ofComponents (homBimoduleRestrictionIso φ X) (by
    intro Z Z' f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    apply LinearMap.ext
    intro x
    rfl)

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_RightInduction
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.resFinite _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.coindEndo_finite _root_.OAI.Tachikawa.Enveloping.coindObj_finite _root_.OAI.Tachikawa.Enveloping.dualRegularLeftInjective _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.instAdditiveModuleCatMulOppositeAlgCoindFunctor _root_.OAI.Tachikawa.Enveloping.instEpiModuleCatAlgCoindπ _root_.OAI.Tachikawa.Enveloping.instFiniteDimensionalCarrierAlgCoindObjOfMulOpposite _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.Enveloping.instMonoFunctorModuleCatAlgCoindUnitNat _root_.OAI.Tachikawa.Enveloping.instMonoModuleCatAlgCoindUnit _root_.OAI.Tachikawa.Enveloping.rightFunctor_finite _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff _root_.OAI.Tachikawa.freeEndo_projective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S U : Type} [Field k] [Ring R] [Ring S] [Ring U]
  [Algebra k R] [Algebra k S] [Algebra k U]

instance instAdditiveModuleCatAlgLeftIndFunctor (φ : R →ₐ[k] S) : (leftIndFunctor (U := U) φ).Additive where
  map_add {_X _Y f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (leftIndMap φ (f + g)).hom x = ((leftIndMap φ f) + (leftIndMap φ g)).hom x
    induction x using BalancedTensor.induction_on (k := k) (R := R) (S := S)
      (M := AlgebraInduction.Bimod φ) (N := Obj _X) with
    | h0 => rfl
    | ht s m =>
      exact (BalancedTensor.mk (k := k) (R := R) (S := S)
        (M := AlgebraInduction.Bimod φ) (N := Obj _Y) s).map_add (f m) (g m)
    | ha x y hx hy =>
      exact ((leftIndMap φ (f+g)).hom.map_add x y).trans
        ((congrArg₂ (fun x y => x+y) hx hy).trans ((leftIndMap φ f + leftIndMap φ g).hom.map_add x y).symm)

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S U : Type} [Field k] [Ring R] [Ring S] [Ring U]
  [Algebra k R] [Algebra k S] [Algebra k U]

def rightIndUnderlyingIso (φ : R →ₐ[k] S) (M : ModuleCat (Alg k U R)) :
    (rightFunctor (k := k) (R := U) (S := S)).obj (rightIndObj φ M) ≅
      (AlgebraInduction.functor φ.op).obj ((rightFunctor (k := k) (R := U) (S := R)).obj M) :=
  LinearEquiv.toModuleIso
  { toFun := fun x => x
    invFun := fun x => x
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' s x := by
      change (1:U) • (s • (show RightIndType φ M from x)) = s • (show RightIndType φ M from x)
      rw [one_smul] }

def rightIndUnderlyingComparison (φ : R →ₐ[k] S) :
    rightIndFunctor (U := U) φ ⋙ rightFunctor ≅ rightFunctor ⋙ AlgebraInduction.functor φ.op :=
  NatIso.ofComponents (rightIndUnderlyingIso φ) (by intro M N f; ext x; rfl)




def rightIndComparison (φ : R →ₐ[k] S) :
    AlgebraInduction.functor (rightEnvelopingMap (U := U) φ) ≅ rightIndFunctor φ :=
  NatIso.ofComponents (rightIndComparisonIso φ) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro a m
    change (show Alg k U S from a) • (show rightIndObj φ N from rightIndUnit φ N (f m)) =
      rightIndMap φ f ((show Alg k U S from a) • (show rightIndObj φ M from rightIndUnit φ M m))
    exact ((rightIndMap φ f).hom.map_smul (show Alg k U S from a)
      (show rightIndObj φ M from rightIndUnit φ M m)).symm)

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def rightResolutionOf {M : ModuleCat (Alg k R S)} (P : CategoryTheory.ProjectiveResolution M)
    (hP : ∀ n, Module.Finite (Alg k R S) (P.complex.X n)) :
    CategoryTheory.ProjectiveResolution (rightFunctor.obj M) where
  complex := (rightFunctor.mapHomologicalComplex _).obj P.complex
  projective n := by
    let := hP n
    let : Module.Projective Sᵐᵒᵖ (Obj (P.complex.X n)) := projective_right _
    change Projective (ModuleCat.of Sᵐᵒᵖ (Obj (P.complex.X n)))
    infer_instance
  π := (rightFunctor.mapHomologicalComplex _).map P.π ≫
    (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
  quasiIso := inferInstance

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

omit [FiniteDimensional k S] in
lemma right_induction_regular_quasiIso (φ : R →ₐ[k] S) :
    QuasiIso (((AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)).mapHomologicalComplex _).map
      (regularResolution (k := k) (R := R)).π) := by
  let P := regularResolution (k := k) (R := R)
  let Q := rightResolutionOf P (fun n => inferInstance)
  let : Module.Projective Rᵐᵒᵖ (Obj (regular (k := k) (R := R))) := regular_right_projective
  let : Projective ((rightFunctor (k := k) (R := R) (S := R)).obj
      (regular (k := k) (R := R))) := by
    change Projective (ModuleCat.of Rᵐᵒᵖ (Obj (regular (k := k) (R := R))))
    exact ModuleCat.projective_of_categoryTheory_projective _
  let I := AlgebraInduction.functor φ.op
  let T := rightFunctor (k := k) (R := R) (S := R)
  let T' := rightFunctor (k := k) (R := R) (S := S)
  let J := AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)
  have h : QuasiIso ((I.mapHomologicalComplex _).map Q.π) :=
    Tachikawa.map_resolution_quasiIso I Q
  change QuasiIso ((I.mapHomologicalComplex _).map
    ((T.mapHomologicalComplex _).map P.π ≫
      (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _)) at h
  rw [Functor.map_comp] at h
  let := h
  have hI : QuasiIso ((I.mapHomologicalComplex _).map ((T.mapHomologicalComplex _).map P.π)) :=
    quasiIso_of_comp_right _ ((I.mapHomologicalComplex _).map
      ((HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _))
  have hB : QuasiIso (((rightIndFunctor (U := R) φ ⋙ T').mapHomologicalComplex _).map P.π) :=
    (Tachikawa.quasiIso_map_natIso (rightIndUnderlyingComparison (U := R) φ) P.π).mpr hI
  have hJ : QuasiIso (((J ⋙ T').mapHomologicalComplex _).map P.π) :=
    (Tachikawa.quasiIso_map_natIso (Functor.isoWhiskerRight (rightIndComparison (U := R) φ) T') P.π).mpr hB
  exact (quasiIso_map_iff_of_preservesHomology
    ((J.mapHomologicalComplex _).map P.π) T').mp hJ

def rightInducedResolution (φ : R →ₐ[k] S) :
    ProjectiveResolution ((AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)).obj
      (regular (k := k) (R := R))) where
  complex := ((AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)).mapHomologicalComplex _).obj
    (regularResolution (k := k) (R := R)).complex
  projective n := by
    change Projective ((AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)).obj
      ((regularResolution (k := k) (R := R)).complex.X n))
    exact ModuleCat.projective_of_categoryTheory_projective _
  π := ((AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)).mapHomologicalComplex _).map
    (regularResolution (k := k) (R := R)).π ≫
      (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
  quasiIso := by
    let := right_induction_regular_quasiIso φ
    infer_instance

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (X : ModuleCat.{0} R)

lemma regular_evaluation_quasiIso :
    QuasiIso (((evaluation (k := k) X).mapHomologicalComplex _).map
      (regularResolution (k := k) (R := R)).π) := by
  let P := regularResolution (k := k) (R := R)
  let Q := rightResolutionOf P (fun n => inferInstance)
  let : Module.Projective Rᵐᵒᵖ (Obj (regular (k := k) (R := R))) := regular_right_projective
  let : Projective ((rightFunctor (k := k) (R := R) (S := R)).obj
      (regular (k := k) (R := R))) := by
    change Projective (ModuleCat.of Rᵐᵒᵖ (Obj (regular (k := k) (R := R))))
    exact ModuleCat.projective_of_categoryTheory_projective _
  let I := rightEvaluation (k := k) X
  let T := rightFunctor (k := k) (R := R) (S := R)
  let T' : ModuleCat.{0} R ⥤ ModuleCat.{0} k := ModuleCat.restrictScalars (algebraMap k R)
  let : CategoryTheory.Limits.PreservesFiniteLimits T' :=
    inferInstanceAs (CategoryTheory.Limits.PreservesFiniteLimits
      (AlgebraInduction.res (k := k) (Algebra.ofId k R)))
  let : CategoryTheory.Limits.PreservesFiniteColimits T' :=
    inferInstanceAs (CategoryTheory.Limits.PreservesFiniteColimits
      (AlgebraInduction.res (k := k) (Algebra.ofId k R)))
  let J := evaluation (k := k) (S := R) X
  have h : QuasiIso ((I.mapHomologicalComplex _).map Q.π) :=
    Tachikawa.map_resolution_quasiIso I Q
  change QuasiIso ((I.mapHomologicalComplex _).map
    ((T.mapHomologicalComplex _).map P.π ≫
      (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _)) at h
  rw [Functor.map_comp] at h
  let := h
  have hI : QuasiIso ((I.mapHomologicalComplex _).map ((T.mapHomologicalComplex _).map P.π)) :=
    quasiIso_of_comp_right _ ((I.mapHomologicalComplex _).map
      ((HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _))
  have hJ :=
    (Tachikawa.quasiIso_map_natIso (rightEvaluationComparison (k := k) (S := R) X) P.π).mpr hI
  change QuasiIso ((T'.mapHomologicalComplex _).map ((J.mapHomologicalComplex _).map P.π)) at hJ
  exact (quasiIso_map_iff_of_preservesHomology
    ((J.mapHomologicalComplex _).map P.π) T').mp hJ

def evaluatedRegularResolution : ProjectiveResolution X where
  complex := ((evaluation (k := k) X).mapHomologicalComplex _).obj
    (regularResolution (k := k) (R := R)).complex
  projective n := by
    change Projective (evalObj X ((regularResolution (k := k) (R := R)).complex.X n))
    infer_instance
  π := ((evaluation (k := k) X).mapHomologicalComplex _).map
    (regularResolution (k := k) (R := R)).π ≫
      (HomologicalComplex.singleMapHomologicalComplex
        (evaluation (k := k) (S := R) X) (ComplexShape.down ℕ) 0).hom.app _ ≫
        (ChainComplex.single₀ (ModuleCat R)).map (regularEvalIso (k := k) X).hom
  quasiIso := by
    let := regular_evaluation_quasiIso (k := k) X
    let : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex
        (evaluation (k := k) (S := R) X) (ComplexShape.down ℕ) 0).hom.app
          (regular (k := k) (R := R))) := inferInstance
    have regularQuasiIso : QuasiIso ((ChainComplex.single₀ (ModuleCat R)).map
        (regularEvalIso (k := k) X).hom) := quasiIso_of_isIso _
    let : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex
        (evaluation (k := k) (S := R) X) (ComplexShape.down ℕ) 0).hom.app
          (regular (k := k) (R := R)) ≫ (ChainComplex.single₀ (ModuleCat R)).map
            (regularEvalIso (k := k) X).hom) := quasiIso_comp _ _ (hφ' := regularQuasiIso)
    exact quasiIso_comp _ _

def evaluatedRegularComparison (P : ProjectiveResolution X) :
    HomotopyEquiv (evaluatedRegularResolution (k := k) X).complex P.complex :=
  ProjectiveResolution.homotopyEquiv _ _

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (φ : R →ₐ[k] S) (X : ModuleCat.{0} S)

def inductionEvaluation :
    AlgebraInduction.functor (envelopingMap φ) ⋙ evaluation (k := k) (S := S) X ≅
      evaluation (k := k) (S := R) ((AlgebraInduction.res φ).obj X) ⋙
        AlgebraInduction.functor φ := by
  let a := (AlgebraInduction.adjunction (envelopingMap φ)).comp
    (evaluationAdjunction (k := k) (S := S) X)
  let b := (evaluationAdjunction (k := k) (S := R) ((AlgebraInduction.res φ).obj X)).comp
    (AlgebraInduction.adjunction φ)
  exact Adjunction.leftAdjointUniq (a.ofNatIsoRight (homBimoduleRestriction φ X)) b

variable [FiniteDimensional k R] [FiniteDimensional k S]

def evaluatedInducedRegularIso :
    ((evaluation (k := k) (S := S) X).mapHomologicalComplex _).obj (inducedRegularComplex φ) ≅
      ((AlgebraInduction.functor φ).mapHomologicalComplex _).obj
        (evaluatedRegularResolution (k := k) ((AlgebraInduction.res φ).obj X)).complex :=
  (NatIso.mapHomologicalComplex (inductionEvaluation φ X) (ComplexShape.down ℕ)).app
    (regularResolution (k := k) (R := R)).complex

def evaluatedInducedRegularComparison (P : ProjectiveResolution ((AlgebraInduction.res φ).obj X)) :
    HomotopyEquiv
      (((evaluation (k := k) (S := S) X).mapHomologicalComplex _).obj (inducedRegularComplex φ))
      (((AlgebraInduction.functor φ).mapHomologicalComplex _).obj P.complex) :=
  (HomotopyEquiv.ofIso (evaluatedInducedRegularIso φ X)).trans
    ((AlgebraInduction.functor φ).mapHomotopyEquiv
      (evaluatedRegularComparison (k := k) ((AlgebraInduction.res φ).obj X) P))

end Tachikawa.Enveloping

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coinduction
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.resFinite _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

abbrev ELeftObj : ModuleCat (B q) := ((OuterTensor.bifunctor k (C k q) (C k q)).obj (TLeftObj q)).obj (TLeftObj q)
abbrev ERightObj : ModuleCat ((C k q)ᵐᵒᵖ ⊗[k] (C k q)ᵐᵒᵖ) :=
  ((OuterTensor.bifunctor k (C k q)ᵐᵒᵖ (C k q)ᵐᵒᵖ).obj (TRightObj q)).obj (TRightObj q)

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] (q : k)

def eLeftRestrictionIso : ELeftObj q ≅ (AlgebraInduction.res (inclusionB q)).obj
    (ModuleCat.of (E q) (E q)) := by
  let X := ELeftObj q
  let Z := (AlgebraInduction.res (inclusionB q)).obj (ModuleCat.of (E q) (E q))
  exact LinearEquiv.toModuleIso (X₁ := X) (X₂ := Z) (m₁ := X.isModule) (m₂ := Z.isModule)
    { toFun := eLeftTensorEquiv q
      invFun := (eLeftTensorEquiv q).symm
      left_inv := (eLeftTensorEquiv q).left_inv
      right_inv := (eLeftTensorEquiv q).right_inv
      map_add' := (eLeftTensorEquiv q).map_add
      map_smul' := eLeftTensorEquiv_smul q }

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

abbrev bSimpleTensor : ModuleCat (B q) :=
  ((OuterTensor.bifunctor k (C k q) (C k q)).obj (ModuleCat.of (C k q) (C.Simple q))).obj
    (ModuleCat.of (C k q) (C.Simple q))

def bSimpleTensorResolution (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ProjectiveResolution (bSimpleTensor q) :=
  OuterTensor.resolution k (C k q) (C k q)
    (C.projectiveResolution q hp) (C.projectiveResolution q hp)
    (fun n => cResObj_finite q n) (fun n => cResObj_finite q n)

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra

variable {k : Type} [Field k] (q H : k) (hH : H ≠ 0)

def socleBimoduleMap : S q ⟶ U q H hH :=
  Enveloping.ofBimoduleHom (socleBimoduleLinear q H hH) (by
    intro a f
    change (show k from f ((characterE q a.unop) • (show X q from (1:k)))) • zeta q =
      ((show k from f (show X q from (1:k))) • zeta q) * sigma q H hH a.unop
    have hf := homBase_smul (ModuleCat.of (E q) (X q)) f (characterE q a.unop)
      (show ModuleCat.of (E q) (X q) from (show X q from (1:k)))
    change f ((characterE q (algebraMap k (E q) (characterE q a.unop))) * (1:k)) =
      (characterE q (algebraMap k (E q) (characterE q a.unop))) *
        (show k from f (1:k)) at hf
    simp only [AlgHom.commutes,Algebra.algebraMap_self,RingHom.id_apply] at hf
    refine (congrArg (fun x : ModuleCat.of (E q) (X q) => (show k from x) • zeta q) hf).trans ?_
    change (characterE q a.unop * (show k from f (show X q from (1:k)))) • zeta q = _
    rw [smul_mul_assoc, zeta_right, characterE_sigma, smul_smul, mul_comm])

end Tachikawa.Construction



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Induction
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.resFinite _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff _root_.OAI.Tachikawa.freeEndo_finite _root_.OAI.Tachikawa.freeEndo_projective _root_.OAI.Tachikawa.freeKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Construction
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] (q : k)

lemma rho_left (a : B q) (z : E q) :
    rho q (inclusionB q a * z) = a • rho q z := by
  induction a using OAI.tensorInductionOn with
  | add a b ha hb => simp only [map_add,add_mul,ha,hb,add_smul]
  | tmul a b =>
    induction z using OAI.tensorInductionOn with
    | add x y hx hy => simp only [mul_add,map_add,hx,hy,smul_add]
    | tmul x y =>
      apply TensorProduct.ext'
      intro c d
      change rho q ((inclusionC q a ⊗ₜ[k] inclusionC q b) * (x ⊗ₜ[k] y))
        (c ⊗ₜ[k] d) = rho q (x ⊗ₜ[k] y) ((c ⊗ₜ[k] d) * (a ⊗ₜ[k] b))
      rw [Algebra.TensorProduct.tmul_mul_tmul,Algebra.TensorProduct.tmul_mul_tmul,
        rho_tmul,rho_tmul]
      change (a • x.snd + MulOpposite.op x.fst • (0:DualBimodule k (C k q))) c *
        (b • y.snd + MulOpposite.op y.fst • (0:DualBimodule k (C k q))) d = _
      simp only [smul_zero,add_zero]
      rfl

lemma rho_right (a : B q) (z : E q) :
    rho q (z * inclusionB q a) = MulOpposite.op a • rho q z := by
  induction a using OAI.tensorInductionOn with
  | add a b ha hb => simp only [map_add,mul_add,ha,hb,MulOpposite.op_add,add_smul]
  | tmul a b =>
    induction z using OAI.tensorInductionOn with
    | add x y hx hy => simp only [add_mul,map_add,hx,hy,smul_add]
    | tmul x y =>
      apply TensorProduct.ext'
      intro c d
      change rho q ((x ⊗ₜ[k] y) * (inclusionC q a ⊗ₜ[k] inclusionC q b))
        (c ⊗ₜ[k] d) = rho q (x ⊗ₜ[k] y) ((a ⊗ₜ[k] b) * (c ⊗ₜ[k] d))
      rw [Algebra.TensorProduct.tmul_mul_tmul,Algebra.TensorProduct.tmul_mul_tmul,
        rho_tmul,rho_tmul]
      change (x.fst • (0:DualBimodule k (C k q)) + MulOpposite.op a • x.snd) c *
        (y.fst • (0:DualBimodule k (C k q)) + MulOpposite.op b • y.snd) d = _
      simp only [smul_zero,zero_add]
      rfl

lemma character_inclusion (a : B q) : characterE q (inclusionB q a) = characterB q a := by
  induction a using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y => rfl

end Tachikawa.Construction



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

abbrev rightComplex (P : ChainComplex (ModuleCat (Alg k R S)) ℕ) :=
  ((rightFunctor (k := k) (R := R) (S := S)).mapHomologicalComplex (.down ℕ)).obj P

def rightCokerEquiv (P : ChainComplex (ModuleCat (Alg k R S)) ℕ) (n : ℕ) :
    Obj (ModuleCat.of (Alg k R S) (NatCoker.C P n)) ≃ₗ[Sᵐᵒᵖ] NatCoker.C (rightComplex P) n where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma coker_right_projective_of_homotopy (P : ChainComplex (ModuleCat (Alg k R S)) ℕ)
    (Q : ChainComplex (ModuleCat Sᵐᵒᵖ) ℕ) (n : ℕ) (e : HomotopyEquiv (rightComplex P) Q)
    [Subsingleton (Q.X (n+1))] [Module.Projective Sᵐᵒᵖ (Obj (P.X n))] :
    Module.Projective Sᵐᵒᵖ (Obj (ModuleCat.of (Alg k R S) (NatCoker.C P n))) := by
  let : Module.Projective Sᵐᵒᵖ ((rightComplex P).X n) :=
    inferInstanceAs (Module.Projective Sᵐᵒᵖ (Obj (P.X n)))
  let := NatCoker.projective_of_homotopy (rightComplex P) n e
  exact Module.Projective.of_equiv (rightCokerEquiv P n).symm

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

lemma rightInducedResolution_finite (φ : R →ₐ[k] S) (n : ℕ) :
    Module.Finite (Alg k R S) ((rightInducedResolution φ).complex.X n) := by
  change Module.Finite (Alg k R S)
    ((AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)).obj
      ((regularResolution (k := k) (R := R)).complex.X n))
  let : FiniteDimensional k ((regularResolution (k := k) (R := R)).complex.X n) :=
    Module.Finite.trans (Alg k R R) _
  exact Module.Finite.of_restrictScalars_finite k _ _

def rightInducedLeftResolution (φ : R →ₐ[k] S) :
    ProjectiveResolution ((AlgebraInduction.res φ).obj (ModuleCat.of S S)) :=
  Tachikawa.transportResolution
    (leftResolutionOf (rightInducedResolution φ) (rightInducedResolution_finite φ))
    ((leftFunctor (k := k) (R := R) (S := S)).mapIso
      ((rightIndComparisonIso φ (regular (k := k) (R := R))) ≪≫ rightIndRegularIso φ) ≪≫
      leftRestrictedRegularIso φ)

def inducedLeftComplexIso (φ : R →ₐ[k] S) :
    leftComplex (inducedRegularComplex φ) ≅
      ((AlgebraInduction.functor φ).mapHomologicalComplex _).obj
        (rightInducedLeftResolution φ).complex := by
  let P := (regularResolution (k := k) (R := R)).complex
  let J := AlgebraInduction.functor (rightEnvelopingMap (U := R) φ)
  let L := AlgebraInduction.functor (leftEnvelopingMap (U := S) φ)
  let U := leftFunctor (k := k) (R := S) (S := S)
  let V := leftFunctor (k := k) (R := R) (S := S)
  let I := AlgebraInduction.functor φ
  let a : L ⋙ U ≅ V ⋙ I :=
    Functor.isoWhiskerRight (leftIndComparison (U := S) φ) U ≪≫
      leftIndUnderlyingComparison (U := S) φ
  let b := Functor.isoWhiskerRight (inducedFactorIso φ) U
  exact (NatIso.mapHomologicalComplex b _).symm.app P ≪≫
    (NatIso.mapHomologicalComplex (Functor.isoWhiskerLeft J a) _).app P

def inducedLeftHomotopy (φ : R →ₐ[k] S)
    (Q : ProjectiveResolution ((AlgebraInduction.res φ).obj (ModuleCat.of S S))) :
    HomotopyEquiv (leftComplex (inducedRegularComplex φ))
      (((AlgebraInduction.functor φ).mapHomologicalComplex _).obj Q.complex) :=
  (HomotopyEquiv.ofIso (inducedLeftComplexIso φ)).trans
    ((AlgebraInduction.functor φ).mapHomotopyEquiv
      (ProjectiveResolution.homotopyEquiv (rightInducedLeftResolution φ) Q))

lemma inducedCoker_left_projective (φ : R →ₐ[k] S)
    (Q : ProjectiveResolution ((AlgebraInduction.res φ).obj (ModuleCat.of S S)))
    (n : ℕ) (hn : CategoryTheory.Limits.IsZero (Q.complex.X (n+1))) :
    Module.Projective S (Obj (ModuleCat.of (Alg k S S) (NatCoker.C (inducedRegularComplex φ) n))) := by
  let I := AlgebraInduction.functor φ
  let C := (I.mapHomologicalComplex _).obj Q.complex
  have hC : CategoryTheory.Limits.IsZero (C.X (n+1)) := I.map_isZero hn
  let : Subsingleton (C.X (n+1)) := ModuleCat.isZero_iff_subsingleton.mp hC
  exact coker_left_projective_of_homotopy (inducedRegularComplex φ) C n (inducedLeftHomotopy φ Q)




omit [FiniteDimensional k S] in
lemma left_induction_regular_quasiIso (φ : R →ₐ[k] S) :
    QuasiIso (((AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)).mapHomologicalComplex _).map
      (regularResolution (k := k) (R := R)).π) := by
  let P := regularResolution (k := k) (R := R)
  let Q := leftResolutionOf P (fun n => inferInstance)
  let : Module.Projective R (Obj (regular (k := k) (R := R))) := regular_left_projective
  let : Projective ((leftFunctor (k := k) (R := R) (S := R)).obj
      (regular (k := k) (R := R))) := by
    change Projective (ModuleCat.of R (Obj (regular (k := k) (R := R))))
    exact ModuleCat.projective_of_categoryTheory_projective _
  let I := AlgebraInduction.functor φ
  let T := leftFunctor (k := k) (R := R) (S := R)
  let T' := leftFunctor (k := k) (R := S) (S := R)
  let J := AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)
  have h : QuasiIso ((I.mapHomologicalComplex _).map Q.π) :=
    Tachikawa.map_resolution_quasiIso I Q
  change QuasiIso ((I.mapHomologicalComplex _).map
    ((T.mapHomologicalComplex _).map P.π ≫
      (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _)) at h
  rw [Functor.map_comp] at h
  let := h
  have hI : QuasiIso ((I.mapHomologicalComplex _).map ((T.mapHomologicalComplex _).map P.π)) :=
    quasiIso_of_comp_right _ ((I.mapHomologicalComplex _).map
      ((HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _))
  have hB : QuasiIso (((leftIndFunctor (U := R) φ ⋙ T').mapHomologicalComplex _).map P.π) :=
    (Tachikawa.quasiIso_map_natIso (leftIndUnderlyingComparison (U := R) φ) P.π).mpr hI
  have hJ : QuasiIso (((J ⋙ T').mapHomologicalComplex _).map P.π) :=
    (Tachikawa.quasiIso_map_natIso (Functor.isoWhiskerRight (leftIndComparison (U := R) φ) T') P.π).mpr hB
  exact (quasiIso_map_iff_of_preservesHomology
    ((J.mapHomologicalComplex _).map P.π) T').mp hJ

def leftInducedResolution (φ : R →ₐ[k] S) :
    ProjectiveResolution ((AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)).obj
      (regular (k := k) (R := R))) where
  complex := ((AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)).mapHomologicalComplex _).obj
    (regularResolution (k := k) (R := R)).complex
  projective n := by
    change Projective ((AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)).obj
      ((regularResolution (k := k) (R := R)).complex.X n))
    exact ModuleCat.projective_of_categoryTheory_projective _
  π := ((AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)).mapHomologicalComplex _).map
    (regularResolution (k := k) (R := R)).π ≫
      (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
  quasiIso := by
    let := left_induction_regular_quasiIso φ
    infer_instance

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def leftIndRegularIso (φ : R →ₐ[k] S) :
    leftIndObj φ (regular (k := k) (R := R)) ≅ rightRestrictedRegular φ where
  hom := leftIndRegularHom φ
  inv := leftIndRegularInv φ
  hom_inv_id := by
    apply leftInd_hom_ext φ
    intro s r
    change leftIndRegularInvLinear φ (show S from leftIndRegularHom φ
      (show leftIndObj φ (regular (k := k) (R := R)) from BalancedTensor.mk s r)) =
      BalancedTensor.mk s r
    trans leftIndRegularInvLinear φ ((show S from s) * φ r)
    · exact congrArg (leftIndRegularInvLinear φ) (leftIndRegularHom_mk φ s r)
    rw [leftIndRegularInvLinear_apply]
    trans BalancedTensor.mk (k := k) (R := R) (S := S)
      (M := AlgebraInduction.Bimod φ) (N := Obj (regular (k := k) (R := R)))
      (MulOpposite.op (show R from r) • s) (1:R)
    · rfl
    trans BalancedTensor.mk (k := k) (R := R) (S := S)
      (N := Obj (regular (k := k) (R := R))) s
      ((show R from r) • (show Obj (regular (k := k) (R := R)) from (1:R)))
    · exact BalancedTensor.balance _ _ _
    change BalancedTensor.mk s (show Obj (regular (k := k) (R := R)) from ((show R from r) * (1*1) : R)) =
      BalancedTensor.mk s r
    exact congrArg (fun z : R => BalancedTensor.mk s
      (show Obj (regular (k := k) (R := R)) from z)) (by exact (congrArg (fun z : R => (show R from r)*z) (one_mul (1:R))).trans (mul_one (show R from r)))
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change (show S from leftIndRegularHom φ (leftIndRegularInvLinear φ (show S from s))) =
      (show S from s)
    trans (show S from leftIndRegularHom φ (BalancedTensor.mk
      (show AlgebraInduction.Bimod φ from s) (show Obj (regular (k := k) (R := R)) from (1:R))))
    · exact congrArg (fun x => (show S from leftIndRegularHom φ x)) (leftIndRegularInvLinear_apply φ s)
    exact (leftIndRegularHom_mk φ _ _).trans
      (show (show S from s) * φ (1:R) = (show S from s) by rw [map_one, mul_one])

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

lemma leftInducedResolution_finite (φ : R →ₐ[k] S) (n : ℕ) :
    Module.Finite (Alg k S R) ((leftInducedResolution φ).complex.X n) := by
  change Module.Finite (Alg k S R)
    ((AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)).obj
      ((regularResolution (k := k) (R := R)).complex.X n))
  let : FiniteDimensional k ((regularResolution (k := k) (R := R)).complex.X n) :=
    Module.Finite.trans (Alg k R R) _
  exact Module.Finite.of_restrictScalars_finite k _ _

def leftInducedRightResolution (φ : R →ₐ[k] S) :
    ProjectiveResolution ((AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ)) :=
  Tachikawa.transportResolution
    (rightResolutionOf (leftInducedResolution φ) (leftInducedResolution_finite φ))
    ((rightFunctor (k := k) (R := S) (S := R)).mapIso
      ((leftIndComparisonIso φ (regular (k := k) (R := R))) ≪≫ leftIndRegularIso φ) ≪≫
      rightRestrictedRegularIso φ)

def inducedRightFactorIso (φ : R →ₐ[k] S) :
    AlgebraInduction.functor (leftEnvelopingMap (U := R) φ) ⋙
      AlgebraInduction.functor (rightEnvelopingMap (U := S) φ) ≅
      AlgebraInduction.functor (envelopingMap φ) :=
  AlgebraInduction.compositionIso _ _ ≪≫ eqToIso (by
    congr 1
    ext a <;> rfl)

def inducedRightComplexIso (φ : R →ₐ[k] S) :
    rightComplex (inducedRegularComplex φ) ≅
      ((AlgebraInduction.functor φ.op).mapHomologicalComplex _).obj
        (leftInducedRightResolution φ).complex := by
  let P := (regularResolution (k := k) (R := R)).complex
  let J := AlgebraInduction.functor (leftEnvelopingMap (U := R) φ)
  let L := AlgebraInduction.functor (rightEnvelopingMap (U := S) φ)
  let U := rightFunctor (k := k) (R := S) (S := S)
  let V := rightFunctor (k := k) (R := S) (S := R)
  let I := AlgebraInduction.functor φ.op
  let a : L ⋙ U ≅ V ⋙ I :=
    Functor.isoWhiskerRight (rightIndComparison (U := S) φ) U ≪≫
      rightIndUnderlyingComparison (U := S) φ
  let b := Functor.isoWhiskerRight (inducedRightFactorIso φ) U
  exact (NatIso.mapHomologicalComplex b _).symm.app P ≪≫
    (NatIso.mapHomologicalComplex (Functor.isoWhiskerLeft J a) _).app P

def inducedRightHomotopy (φ : R →ₐ[k] S)
    (Q : ProjectiveResolution ((AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ))) :
    HomotopyEquiv (rightComplex (inducedRegularComplex φ))
      (((AlgebraInduction.functor φ.op).mapHomologicalComplex _).obj Q.complex) :=
  (HomotopyEquiv.ofIso (inducedRightComplexIso φ)).trans
    ((AlgebraInduction.functor φ.op).mapHomotopyEquiv
      (ProjectiveResolution.homotopyEquiv (leftInducedRightResolution φ) Q))

lemma inducedCoker_right_projective (φ : R →ₐ[k] S)
    (Q : ProjectiveResolution ((AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ)))
    (n : ℕ) (hn : CategoryTheory.Limits.IsZero (Q.complex.X (n+1))) :
    Module.Projective Sᵐᵒᵖ (Obj (ModuleCat.of (Alg k S S) (NatCoker.C (inducedRegularComplex φ) n))) := by
  let I := AlgebraInduction.functor φ.op
  let C := (I.mapHomologicalComplex _).obj Q.complex
  have hC : CategoryTheory.Limits.IsZero (C.X (n+1)) := I.map_isZero hn
  let : Subsingleton (C.X (n+1)) := ModuleCat.isZero_iff_subsingleton.mp hC
  exact coker_right_projective_of_homotopy (inducedRegularComplex φ) C n (inducedRightHomotopy φ Q)

end Tachikawa.Enveloping



namespace Tachikawa.Construction
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] (q : k)

def tRightUnderlying : TRightObj q ≃ₗ[k] (T q)ᵐᵒᵖ where
  toFun := MulOpposite.op
  invFun := MulOpposite.unop
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change MulOpposite.op ((algebraMap k (C k q)ᵐᵒᵖ c) •
      (show C k q × DualBimodule k (C k q) from x)) =
      MulOpposite.op (c • (show C k q × DualBimodule k (C k q) from x))
    exact congrArg MulOpposite.op (IsScalarTower.algebraMap_smul (C k q)ᵐᵒᵖ c _)

lemma tRightUnderlying_smul (r : (C k q)ᵐᵒᵖ) (x : TRightObj q) :
    tRightUnderlying q (r • x) = (inclusionC q).op r * tRightUnderlying q x := by
  apply MulOpposite.unop_injective
  apply TrivSqZeroExt.ext
  · rfl
  · change r • (show C k q × DualBimodule k (C k q) from x).2 =
      (show C k q × DualBimodule k (C k q) from x).1 • (0 : DualBimodule k (C k q)) +
        r • (show C k q × DualBimodule k (C k q) from x).2
    rw [smul_zero, zero_add]

def eRightTensorEquiv : OuterTensor.Obj k (C k q)ᵐᵒᵖ (C k q)ᵐᵒᵖ (TRightObj q) (TRightObj q) ≃ₗ[k]
    ((T q)ᵐᵒᵖ ⊗[k] (T q)ᵐᵒᵖ) :=
  TensorProduct.congr (tRightUnderlying q) (tRightUnderlying q)

abbrev inclusionOppTensor : ((C k q)ᵐᵒᵖ ⊗[k] (C k q)ᵐᵒᵖ) →ₐ[k] ((T q)ᵐᵒᵖ ⊗[k] (T q)ᵐᵒᵖ) :=
  Algebra.TensorProduct.map (inclusionC q).op (inclusionC q).op

lemma eRightTensorEquiv_action (r : ((C k q)ᵐᵒᵖ ⊗[k] (C k q)ᵐᵒᵖ)) :
    (eRightTensorEquiv q).toLinearMap.comp
      (OuterTensor.action k (C k q)ᵐᵒᵖ (C k q)ᵐᵒᵖ (TRightObj q) (TRightObj q) r) =
      (LinearMap.mulLeft k (inclusionOppTensor q r)).comp (eRightTensorEquiv q).toLinearMap := by
  induction r using OAI.tensorInductionOn with
  | tmul a b =>
    apply TensorProduct.ext'
    intro x y
    change (tRightUnderlying q (a • x)) ⊗ₜ[k] (tRightUnderlying q (b • y)) =
      ((inclusionC q).op a ⊗ₜ[k] (inclusionC q).op b) *
        ((tRightUnderlying q x) ⊗ₜ[k] (tRightUnderlying q y))
    rw [tRightUnderlying_smul, tRightUnderlying_smul, Algebra.TensorProduct.tmul_mul_tmul]
  | add r s hr hs =>
    apply LinearMap.ext
    intro x
    change eRightTensorEquiv q ((OuterTensor.action k (C k q)ᵐᵒᵖ (C k q)ᵐᵒᵖ (TRightObj q) (TRightObj q) (r+s)) x) =
      inclusionOppTensor q (r+s) * eRightTensorEquiv q x
    rw [map_add, map_add]
    change eRightTensorEquiv q ((OuterTensor.action k (C k q)ᵐᵒᵖ (C k q)ᵐᵒᵖ (TRightObj q) (TRightObj q) r) x +
      (OuterTensor.action k (C k q)ᵐᵒᵖ (C k q)ᵐᵒᵖ (TRightObj q) (TRightObj q) s) x) = _
    apply ((eRightTensorEquiv q).map_add _ _).trans
    apply Eq.trans (congrArg₂ (fun a b : (T q)ᵐᵒᵖ ⊗[k] (T q)ᵐᵒᵖ => a+b) (LinearMap.congr_fun hr x) (LinearMap.congr_fun hs x))
    exact (add_mul (inclusionOppTensor q r) (inclusionOppTensor q s) (eRightTensorEquiv q x)).symm

lemma inclusionOppTensor_natural : (opTensorE q).toAlgHom.comp (inclusionOppTensor q) =
    (inclusionB q).op.comp (opTensorB q).toAlgHom := by
  ext a <;> rfl

def eRightUnderlying : (opTensorRestriction q).obj (ERightObj q) ≃+ (E q)ᵐᵒᵖ :=
  (eRightTensorEquiv q).toAddEquiv.trans (opTensorE q).toAddEquiv

lemma eRightUnderlying_smul (r : (B q)ᵐᵒᵖ) (x : (opTensorRestriction q).obj (ERightObj q)) :
    eRightUnderlying q (r • x) = (inclusionB q).op r * eRightUnderlying q x := by
  change opTensorE q (eRightTensorEquiv q ((opTensorB q).symm r •
      (show OuterTensor.Obj k (C k q)ᵐᵒᵖ (C k q)ᵐᵒᵖ (TRightObj q) (TRightObj q) from x))) = _
  apply Eq.trans (congrArg (opTensorE q)
    (LinearMap.congr_fun (eRightTensorEquiv_action q ((opTensorB q).symm r)) x))
  apply Eq.trans ((opTensorE q).map_mul _ _)
  have h := AlgHom.congr_fun (inclusionOppTensor_natural q) ((opTensorB q).symm r)
  have h' : opTensorE q (inclusionOppTensor q ((opTensorB q).symm r)) = (inclusionB q).op r := by
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] using h
  exact congrArg (fun a : (E q)ᵐᵒᵖ => a * eRightUnderlying q x) h'

def eRightRestrictionIso : (opTensorRestriction q).obj (ERightObj q) ≅
    (AlgebraInduction.res (inclusionB q).op).obj (ModuleCat.of (E q)ᵐᵒᵖ (E q)ᵐᵒᵖ) := by
  let X := (opTensorRestriction q).obj (ERightObj q)
  let Z := (AlgebraInduction.res (inclusionB q).op).obj (ModuleCat.of (E q)ᵐᵒᵖ (E q)ᵐᵒᵖ)
  exact LinearEquiv.toModuleIso (X₁ := X) (X₂ := Z) (m₁ := X.isModule) (m₂ := Z.isModule)
    { toFun := eRightUnderlying q
      invFun := (eRightUnderlying q).symm
      left_inv := (eRightUnderlying q).left_inv
      right_inv := (eRightUnderlying q).right_inv
      map_add' := (eRightUnderlying q).map_add
      map_smul' := eRightUnderlying_smul q }

end Tachikawa.Construction

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_DerivedInduction
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa.Construction
open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct
variable {k : Type} [Field k] [CharP k 2] (q : k)

omit [CharP k 2] in

def bSimpleTensorRestrictionEquiv : bSimpleTensor q ≃ₗ[B q]
    (AlgebraInduction.res (inclusionB q)).obj (ModuleCat.of (E q) (X q)) where
  toFun := bSimpleTensorUnderlying q
  invFun := (bSimpleTensorUnderlying q).symm
  left_inv := (bSimpleTensorUnderlying q).left_inv
  right_inv := (bSimpleTensorUnderlying q).right_inv
  map_add' := (bSimpleTensorUnderlying q).map_add
  map_smul' a x := by
    change bSimpleTensorUnderlying q (a • x) =
      characterE q (inclusionB q a) * bSimpleTensorUnderlying q x
    rw [character_inclusion]
    exact bSimpleTensorUnderlying_smul q a x

omit [CharP k 2] in
def bSimpleTensorRestrictionIso : bSimpleTensor q ≅
    (AlgebraInduction.res (inclusionB q)).obj (ModuleCat.of (E q) (X q)) :=
  LinearEquiv.toModuleIso (bSimpleTensorRestrictionEquiv q)

def restrictedXResolution (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ProjectiveResolution ((AlgebraInduction.res (inclusionB q)).obj (ModuleCat.of (E q) (X q))) :=
  Tachikawa.transportResolution (bSimpleTensorResolution q hp) (bSimpleTensorRestrictionIso q)

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

def evaluatedKComparison (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    HomotopyEquiv
      (((Enveloping.evaluation (k := k) (ModuleCat.of (E q) (X q))).mapHomologicalComplex _).obj
        (Enveloping.inducedRegularComplex (inclusionB q)))
      (((AlgebraInduction.functor (inclusionB q)).mapHomologicalComplex _).obj
        (bSimpleTensorResolution q hp).complex) :=
  Enveloping.evaluatedInducedRegularComparison (inclusionB q)
    (ModuleCat.of (E q) (X q)) (restrictedXResolution q hp)

end Tachikawa.Construction



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B S T : Type} [Field k] [Ring A] [Ring B] [Ring S] [Ring T]
  [Algebra k A] [Algebra k B] [Algebra k S] [Algebra k T]
  (φ : A →ₐ[k] S) (ψ : B →ₐ[k] T)
  (P : ChainComplex (ModuleCat A) ℕ) (Q : ChainComplex (ModuleCat B) ℕ)

abbrev outerDouble := ((bifunctor k A B).mapBifunctorHomologicalComplex
  (.down ℕ) (.down ℕ)).obj P |>.obj Q

abbrev inducedOuterDouble :=
  ((bifunctor k S T).mapBifunctorHomologicalComplex (.down ℕ) (.down ℕ)).obj
    (((AlgebraInduction.functor φ).mapHomologicalComplex _).obj P) |>.obj
    (((AlgebraInduction.functor ψ).mapHomologicalComplex _).obj Q)

def inductionDoubleComparison :
    TotalMap.map₂ (AlgebraInduction.functor (Algebra.TensorProduct.map φ ψ))
      (outerDouble P Q) ⟶ inducedOuterDouble φ ψ P Q :=
  HomologicalComplex₂.homMk (fun ij => inductionComparison φ ψ (P.X ij.1) (Q.X ij.2))
    (by
      intro i i' j _
      have h := (inductionComparison_natural φ ψ (P.X i) (Q.X j)
        (P.d i i') (𝟙 (Q.X j))).symm
      rw [(AlgebraInduction.functor ψ).map_id] at h
      exact h)
    (by
      intro i j j' _
      have h := (inductionComparison_natural φ ψ (P.X i) (Q.X j)
        (𝟙 (P.X i)) (Q.d j j')).symm
      rw [(AlgebraInduction.functor φ).map_id] at h
      exact h)

instance inductionDoubleComparison_isIso : IsIso (inductionDoubleComparison φ ψ P Q) := by
  have (i j : ℕ) : IsIso (((inductionDoubleComparison φ ψ P Q).f i).f j) := by
    change IsIso (inductionComparison φ ψ (P.X i) (Q.X j))
    rw [← inductionIso_hom]
    infer_instance
  have (i : ℕ) : IsIso ((inductionDoubleComparison φ ψ P Q).f i) :=
    HomologicalComplex.Hom.isIso_of_components _
  exact HomologicalComplex.Hom.isIso_of_components _

def inductionTotalIso :
    ((AlgebraInduction.functor (Algebra.TensorProduct.map φ ψ)).mapHomologicalComplex _).obj
      (mapBifunctor P Q (bifunctor k A B) (.down ℕ)) ≅
    mapBifunctor
      (((AlgebraInduction.functor φ).mapHomologicalComplex _).obj P)
      (((AlgebraInduction.functor ψ).mapHomologicalComplex _).obj Q)
      (bifunctor k S T) (.down ℕ) := by
  let F := AlgebraInduction.functor (Algebra.TensorProduct.map φ ψ)
  letI : PreservesColimits F :=
    (AlgebraInduction.adjunction (Algebra.TensorProduct.map φ ψ)).leftAdjoint_preservesColimits
  exact (TotalMap.iso F (outerDouble P Q) (.down ℕ)).symm ≪≫
    HomologicalComplex₂.total.mapIso (asIso (inductionDoubleComparison φ ψ P Q)) (.down ℕ)

end Tachikawa.OuterTensor



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def restrictedRegularMap (φ : R →ₐ[k] S) : regular (k := k) (R := R) ⟶
    (AlgebraInduction.res (envelopingMap φ)).obj (regular (k := k) (R := S)) :=
  homOfLinear
    ((AlgebraInduction.resUnderlyingEquiv (envelopingMap φ) (regular (k := k) (R := S))).symm.toLinearMap.comp
      (regularUnderlyingEquiv.symm.toLinearMap.comp
        (φ.toLinearMap.comp regularUnderlyingEquiv.toLinearMap))) (by
    intro r s x
    change φ (r * ((show R from x) * s.unop)) =
      φ r * (φ (show R from x) * φ s.unop)
    exact (φ.map_mul r ((show R from x) * s.unop)).trans
      (congrArg (fun z : S => φ r * z) (φ.map_mul (show R from x) s.unop)))

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] (φ : R →ₐ[k] S)

abbrev inducedRegularCochain : CochainComplex (ModuleCat.{0} (Alg k S S)) ℤ :=
  (AlgebraInduction.complexInduction (envelopingMap φ) (.up ℤ)).obj
    (regularResolution (k := k) (R := R)).cochainComplex

def regularPreAugmentation : (regularResolution (k := k) (R := R)).cochainComplex ⟶
    (AlgebraInduction.complexRestriction (envelopingMap φ) (.up ℤ)).obj
      ((CochainComplex.singleFunctor _ 0).obj (regular (k := k) (R := S))) :=
  (regularResolution (k := k) (R := R)).π' ≫
    (CochainComplex.singleFunctor _ 0).map (restrictedRegularMap φ) ≫
      (singleMapHomologicalComplex (AlgebraInduction.res (envelopingMap φ)) (.up ℤ) 0).inv.app _

def inducedRegularAugmentation : inducedRegularCochain φ ⟶
    (CochainComplex.singleFunctor _ 0).obj (regular (k := k) (R := S)) :=
  AlgebraInduction.complexExtend (envelopingMap φ) (.up ℤ) (regularPreAugmentation φ)

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {R S : Type} [Ring R] [Ring S]

namespace Enveloping
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] (φ : R →ₐ[k] S)
lemma inducedReflect_exact (n : ℕ) (hn : 0 < n)
    (h : Function.Exact ((inducedRegularComplex φ).d (n+1) n)
      ((inducedRegularComplex φ).d n (n-1))) :
    Function.Exact ((reflectCochain (inducedRegularCochain φ)).d ((n:ℤ)+1) n)
      ((reflectCochain (inducedRegularCochain φ)).d n ((n:ℤ)-1)) :=
  resolution_reflect_exact (regularResolution (k := k) (R := R))
    (AlgebraInduction.functor (envelopingMap φ)) n hn h
end Enveloping
end Tachikawa

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Perfect
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
variable {k : Type} [Field k] [CharP k 2] (q : k)
variable (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

def jjNatIntIso (n : ℕ) : (natJJ q hp).X n ≅ (forwardJJ q hp).X (n:ℤ) where
  hom := jjNatIntX q hp n
  inv := jjIntNatX q hp n
  hom_inv_id := by
    apply total.hom_ext
    intro i j h
    simp only [ι_jjNatIntX_assoc, Category.comp_id]
    erw [ι_jjIntNatX q hp (i:ℤ) (j:ℤ) n]
    rfl
  inv_hom_id := by
    apply total.hom_ext
    intro i j h
    rw [ι_jjIntNatX_assoc, Category.comp_id]
    cases i with
    | ofNat i =>
      cases j with
      | ofNat j => exact ι_jjNatIntX q hp i j n (by dsimp at h; omega)
      | negSucc j =>
        apply (OuterTensor.isZero_obj_right _ _ (forwardJ_below q hp _ (by omega))).eq_of_src
    | negSucc i =>
      apply (OuterTensor.isZero_obj_left _ _ (forwardJ_below q hp _ (by omega))).eq_of_src




lemma forwardJ_d_nat (n : ℕ) : (forwardJ q hp).d ((n:ℤ)+1) (n:ℤ) = C.inducedD q n := by
  change (TrivialInduction.functor (k := k)).map ((C.forwardComplex q hp).d ((n:ℤ)+1) n) = _
  rw [show (C.forwardComplex q hp).d ((n:ℤ)+1) n = C.forwardD q n from ChainComplex.of_d _ _ _]
  rfl

lemma forwardJ_d_bottom : (forwardJ q hp).d 0 (-1) = 0 := by
  change (TrivialInduction.functor (k := k)).map ((C.forwardComplex q hp).d 0 (-1)) = _
  have h : (C.forwardComplex q hp).d 0 (-1) = 0 := by
    change ChainComplex.of.d (C.forwardObj q) (C.forwardD q) 0 (-1) = 0
    simp only [ChainComplex.of.d, dite_eq_left (show (0:ℤ) = -1 + 1 from rfl)]
    rfl
  rw [h, Functor.map_zero]
  try rfl

end Tachikawa.Construction



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat.{0} R)

def evalCokerIso {M N : ModuleCat.{0} (Alg k S R)} (f : M ⟶ N) :
    evalObj (k := k) X (ModuleCat.of _ (N ⧸ LinearMap.range f.hom)) ≅
      ModuleCat.of S (evalObj (k := k) X N ⧸ LinearMap.range (evalMap (k := k) X f).hom) := by
  let : PreservesColimits (evaluation (k := k) (S := S) X) :=
    (evaluationAdjunction (k := k) X).leftAdjoint_preservesColimits
  exact (evaluation (k := k) X).mapIso (ModuleCat.cokernelIsoRangeQuotient f).symm ≪≫
    PreservesCokernel.iso (evaluation (k := k) X) f ≪≫ ModuleCat.cokernelIsoRangeQuotient (evalMap (k := k) X f)

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

abbrev restrictedOuterRegular (φ : R →ₐ[k] S) :=
  ((OuterTensor.bifunctor k R Rᵐᵒᵖ).obj
    ((AlgebraInduction.res φ).obj (ModuleCat.of S S))).obj
      ((AlgebraInduction.res φ.op).obj (ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ))

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_DerivedDescent
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped ModuleCat.Algebra
attribute [instance] IndReplacement.quasiIso

end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
def restrictedTwistedUnderlying {k R S : Type} [Field k] [Ring R] [Ring S]
    [Algebra k R] [Algebra k S] (φ : R →ₐ[k] S) (σ : S ≃ₐ[k] S) :
    (AlgebraInduction.res (Enveloping.envelopingMap φ)).obj
      (Enveloping.twistedRegular σ) ≃ₗ[k] S :=
  (AlgebraInduction.resUnderlyingEquiv (Enveloping.envelopingMap φ)
    (Enveloping.twistedRegular σ)).trans (Enveloping.twistedUnderlying σ)

end Tachikawa.Construction



namespace Tachikawa.Enveloping
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] (φ : R →ₐ[k] S)

def regularUnit : (regularResolution (k := k) (R := R)).cochainComplex ⟶
    ((AlgebraInduction.res (envelopingMap φ)).mapHomologicalComplex (.up ℤ)).obj
      (inducedRegularCochain φ) :=
  AlgebraInduction.complexUnit (envelopingMap φ) (.up ℤ) _

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_StableLift
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat.{0} R) {M P Q : ModuleCat.{0} (Alg k S R)}

lemma evalMap_surjective (g : P ⟶ Q) (hg : Function.Surjective g) :
    Function.Surjective (evalMap X g) :=
  BalancedTensor.mapLeft_surjective (leftMap g) (rightMap g).map_smul hg

lemma evalMap_exact [FiniteDimensional k R] [FiniteDimensional k M]
    [Module.Projective Rᵐᵒᵖ (Obj M)] (t : SymmetrizingForm (k := k) (R := R))
    (f : M ⟶ P) (g : P ⟶ Q) (hi : Function.Injective f)
    (he : Function.Exact f g) (hs : Function.Surjective g) :
    Function.Exact (evalMap X f) (evalMap X g) := by
  let : Module.Injective Rᵐᵒᵖ Rᵐᵒᵖ := t.op.injective
  let : Module.Finite Rᵐᵒᵖ (Obj M) := Module.Finite.of_restrictScalars_finite k Rᵐᵒᵖ (Obj M)
  let : Module.Injective Rᵐᵒᵖ (Obj M) := injective_of_finite_projective
  let H := linearShortExact (rightMap f) (rightMap g) he hi hs
  let : CategoryTheory.Injective (linearShortComplex (rightMap f) (rightMap g) he).X₁ :=
    Module.injective_object_of_injective_module Rᵐᵒᵖ (Obj M)
  let sp := H.splittingOfInjective
  apply BalancedTensor.mapLeft_exact_of_right_splitting (leftMap f) (leftMap g)
    (rightMap f).map_smul (rightMap g).map_smul sp.r.hom sp.s.hom
  · intro p
    exact congrArg (fun z : ModuleCat.of Rᵐᵒᵖ (Obj P) ⟶ ModuleCat.of Rᵐᵒᵖ (Obj P) => z p) sp.id
  · intro m
    exact (he _).mpr ⟨m,rfl⟩
end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_HomProfile
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (t : SymmetrizingForm (k := k) (R := R)) (u : SymmetrizingForm (k := k) (R := S))
  (X : ModuleCat.{0} R) [FiniteDimensional k X]
  (M : FiniteModule k (Alg k S R)) [Module.Projective Rᵐᵒᵖ (Obj M.obj)]
  (P : ChainComplex (ModuleCat.{0} S) ℤ) (hP : ComplexExact P)
  (fin : ∀ j, Module.Finite S (P.X j)) (proj : ∀ j, Module.Projective S (P.X j))

omit [Module.Projective Rᵐᵒᵖ (Obj M.obj)] in
lemma evalFree_finite (Q : ModuleCat.{0} (Alg k S R)) [Module.Finite (Alg k S R) Q] :
    Module.Finite S (evalObj (k := k) X Q) := by
  let : FiniteDimensional k Q := Module.Finite.trans (Alg k S R) Q
  infer_instance

def evalCosyCokerStableEquiv (j : ℤ)
    (e : StableEquiv (k := k) (evalObj (k := k) X M.obj) (ModuleCat.of S (CokerAt P j))) :
    StableEquiv (k := k) (evalObj (k := k) X (M.cosyzygy (envelopingForm u t)).obj)
      (ModuleCat.of S (CokerAt P (j-1))) := by
  let τ := envelopingForm u t
  let J := ModuleCat.of (Alg k S R) (Fin (Module.finrank k M) → Alg k S R)
  let : Module.Finite (Alg k S R) J := inferInstanceAs (Module.Finite (Alg k S R) (Fin (Module.finrank k M) → Alg k S R))
  let : Module.Projective (Alg k S R) J := inferInstanceAs (Module.Projective (Alg k S R) (Fin (Module.finrank k M) → Alg k S R))
  let : Module.Finite S (evalObj (k := k) X J) := evalFree_finite (k := k) X J
  let : Module.Projective S (evalObj (k := k) X J) := by infer_instance
  let i : M.obj ⟶ J := ModuleCat.ofHom (M.embed τ)
  let p : J ⟶ (M.cosyzygy τ).obj := ModuleCat.ofHom (LinearMap.range (M.embed τ)).mkQ
  have hi : Function.Injective i := M.embed_injective τ
  have he : Function.Exact i p := fun _ => Submodule.Quotient.mk_eq_zero _
  have hs : Function.Surjective p := Submodule.mkQ_surjective _
  let : Module.Injective S S := u.injective
  let := fin (j-1)
  let := proj (j-1)
  exact StableEquiv.down (P := evalObj (k := k) X J) (Q := P.X (j-1))
    (evalMap (k := k) X i).hom (evalMap (k := k) X p).hom
    (evalMap_injective X t i hi) (evalMap_exact X t i p hi he hs) (evalMap_surjective X p hs)
    (CokerAt.δ P j (j-1)) (CokerAt.π P (j-1))
    (CokerAt.δ_injective P hP j (j-1) (by omega))
    (CokerAt.δ_π_exact P j (j-1) (by omega)) (CokerAt.π_surjective P (j-1)) e

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k]

namespace OuterTensor
variable {A B : Type} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (P : ChainComplex (ModuleCat.{0} A) ℤ) (Q : ChainComplex (ModuleCat.{0} B) ℤ)
  (U : ModuleCat A) (V : ModuleCat B)

lemma hom_zero_left (M : ModuleCat A) (N : ModuleCat B)
    [Module.Finite A M] [Module.Finite B N] [Module.Projective A M] [Module.Projective B N]
    (hz : ∀ f : M ⟶ U, f = 0)
    (f : ((bifunctor k A B).obj M |>.obj N) ⟶ ((bifunctor k A B).obj U |>.obj V)) : f = 0 := by
  let : Subsingleton (M ⟶ U) := ⟨fun f g => (hz f).trans (hz g).symm⟩
  obtain ⟨x,rfl⟩ := homMap_surjective (k := k) M U N V f
  rw [Subsingleton.elim x 0, map_zero]

lemma hom_zero_right (M : ModuleCat A) (N : ModuleCat B)
    [Module.Finite A M] [Module.Finite B N] [Module.Projective A M] [Module.Projective B N]
    (hz : ∀ f : N ⟶ V, f = 0)
    (f : ((bifunctor k A B).obj M |>.obj N) ⟶ ((bifunctor k A B).obj U |>.obj V)) : f = 0 := by
  let : Subsingleton (N ⟶ V) := ⟨fun f g => (hz f).trans (hz g).symm⟩
  obtain ⟨x,rfl⟩ := homMap_surjective (k := k) M U N V f
  rw [Subsingleton.elim x 0, map_zero]

lemma total_hom_zero (a b n : ℤ) (hn : n ≠ a+b)
    (fP : ∀ i, Module.Finite A (P.X i)) (fQ : ∀ j, Module.Finite B (Q.X j))
    (pP : ∀ i, Module.Projective A (P.X i)) (pQ : ∀ j, Module.Projective B (Q.X j))
    (zP : ∀ i, i ≠ a → ∀ f : P.X i ⟶ U, f = 0)
    (zQ : ∀ j, j ≠ b → ∀ f : Q.X j ⟶ V, f = 0)
    (f : (mapBifunctor P Q (bifunctor k A B) (.down ℤ)).X n ⟶
      ((bifunctor k A B).obj U).obj V) : f = 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  let := fP i
  let := fQ j
  let := pP i
  let := pQ j
  rw [comp_zero]
  by_cases hi : i = a
  · exact hom_zero_right U V (P.X i) (Q.X j) (zQ j (by dsimp at hij; omega)) _
  · exact hom_zero_left U V (P.X i) (Q.X j) (zP i hi) _

def totalHomSupported (a b : ℤ)
    (fP : ∀ i, Module.Finite A (P.X i)) (fQ : ∀ j, Module.Finite B (Q.X j))
    (pP : ∀ i, Module.Projective A (P.X i)) (pQ : ∀ j, Module.Projective B (Q.X j))
    (zP : ∀ i, i ≠ a → ∀ f : P.X i ⟶ U, f = 0)
    (zQ : ∀ j, j ≠ b → ∀ f : Q.X j ⟶ V, f = 0) :
    ((mapBifunctor P Q (bifunctor k A B) (.down ℤ)).X (a+b) ⟶
      ((bifunctor k A B).obj U).obj V) ≃ₗ[k]
      (((bifunctor k A B).obj (P.X a)).obj (Q.X b) ⟶
      ((bifunctor k A B).obj U).obj V) := by
  let I := {ij : ℤ × ℤ // ij.1+ij.2=a+b}
  let F := fun ij : I => ((bifunctor k A B).obj (P.X ij.val.1)).obj (Q.X ij.val.2)
  let W := ((bifunctor k A B).obj U).obj V
  change (∐ F ⟶ W) ≃ₗ[k] _
  refine (coproductHomEquiv F W).trans (piSupportedEquiv _ (⟨(a,b),rfl⟩ : I) ?_)
  intro ij hij
  let := fP ij.val.1
  let := fQ ij.val.2
  let := pP ij.val.1
  let := pQ ij.val.2
  have hz (f : F ij ⟶ W) : f = 0 := by
    by_cases h : ij.val.1 = a
    · apply hom_zero_right U V (P.X ij.val.1) (Q.X ij.val.2) _ f
      apply zQ
      intro h'
      apply hij
      exact Subtype.ext (Prod.ext h h')
    · exact hom_zero_left U V (P.X ij.val.1) (Q.X ij.val.2) (zP _ h) f
  exact ⟨fun f g => (hz f).trans (hz g).symm⟩

end OuterTensor
end Tachikawa



end

end OAI
end


