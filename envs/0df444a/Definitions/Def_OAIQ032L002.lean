-- Prove2me | Definitions.Def_OAIQ032L002
-- name    : OAIQ032L002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:42:23.679989+00:00
-- url     : https://prove2.me/theorems/cf1dba7b-92c5-42e7-beb7-0139eca2b0bb
-- title:
--   Definitions bundle OAIQ032L002 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 83 declarations of OpenAI's Lean: 40 definitions, 5 inductive types or structures, 3 instances and 35 theorems. The definitions and types are `OAI.Lech.BinaryCover.Data`, `OAI.Lech.CarrierOperators.Agree`, `OAI.Lech.CarrierOperators.Carrier`, `OAI.Lech.CarrierOperators.Op`, `OAI.Lech.CarrierOperators.Op.add`, `OAI.Lech.CarrierOperators.Op.comp`, `OAI.Lech.CarrierOperators.Op.id`, `OAI.Lech.CarrierOperators.Op.sub`, `OAI.Lech.CarrierOperators.Sections`, `OAI.Lech.CarrierOperators.lift`, `OAI.Lech.CarrierOperators.toFixed`, `OAI.Lech.CartierQuotient.quotient`, `OAI.Lech.CartierQuotient.reduction`, `OAI.Lech.CartierQuotient.shortComplex`, `OAI.Lech.CartierQuotient.step`, `OAI.Lech.CechNormalization.extendEquivalence`, `OAI.Lech.CechNormalization.sortedCarrier`, `OAI.Lech.CechNormalization.tensorHomotopy`, `OAI.Lech.CharP.parameterIdeal`, `OAI.Lech.CoefficientField.frobeniusFactor`, `OAI.Lech.CoefficientField.localSection`, `OAI.Lech.CoefficientField.sectionMap`, `OAI.Lech.CoefficientField.stage`, `OAI.Lech.CoefficientReduction.grade`, `OAI.Lech.CoefficientReduction.graded`, `OAI.Lech.FiniteComplex.bottomProjection`, `OAI.Lech.FiniteComplex.bottomShortComplex`, `OAI.Lech.FiniteComplex.bottomShortComplexMap`, `OAI.Lech.FiniteComplex.bottomSplitting`, `OAI.Lech.FiniteComplex.dropBottom`, `OAI.Lech.FiniteComplex.dropBottomMap`, `OAI.Lech.FiniteComplex.dropBottomXIso`, `OAI.Lech.FiniteModuleCech.Diagram`, `OAI.Lech.FiniteModuleCech.cochains`, `OAI.Lech.FiniteModuleCech.toFixed`, `OAI.Lech.RootGluing.rootShift`, `OAI.Lech.SourceGraded.sourceGrade`, `OAI.Lech.TensorIdeal.idealQuotientMap`, `OAI.Lech.TensorIdeal.quotientFunctor`, `OAI.Lech.TensorTotal.Right.degreeMap` and 5 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_CarrierOperators`, `Multiplicity_CartierQuotientDevissage`, `Multiplicity_CechCarrierOperators`, `Multiplicity_CoefficientFieldLocalSection`, `Multiplicity_FibreSquare`, `Multiplicity_FiniteModuleCech`, `Multiplicity_IdealQuotientFunctor`, `Multiplicity_LechHomogeneousEval`, `Multiplicity_LechTorsionOf`, `Multiplicity_PowerSeriesFinDimension`, `Multiplicity_PrimitiveChartFaithfullyFlat`, `Multiplicity_ProductSourceCoverFaceSlice`, `Multiplicity_ProjectiveReduction`, `Multiplicity_TensorCechHomotopy`, `Multiplicity_TensorTotalHomologyProperty`, `Multiplicity_TowerRestrictedLength`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L011`, `OAIQ032L012`, `OAIQ032L013`, `OAIQ032L014`, `OAIQ032L015`, `OAIQ032L016` and `OAIQ032L017`; the statements `OAI.Lech.CharP.normalized_perfection_module_finite` and `OAI.Lech.CharP.perfection_complex_value`; the proofs of `OAI.Lech.CharP.perfection_complex_value` and `OAI.Lech.dutta_algClosed`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ032_LECH.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechTorsionOf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory

attribute [local instance] Classical.propDecidable


namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ} (z : Fin h → R)
  (hz : Ideal.span (Set.range z) = I)
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev sourceGrade (h n : ℕ) : Submodule R (MvPolynomial (Fin h) (R ⧸ I)) :=
  (homogeneousSubmodule (Fin h) (R ⧸ I) n).restrictScalars R
end Lech.SourceGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverFaceSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.FiniteComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type*} [Category C] [Abelian C]
variable (F : CochainComplex C ℤ) (n : ℤ)
  (hn : ∀ i, i < n → IsZero (F.X i))

noncomputable def bottomProjection : F ⟶ (single C (.up ℤ) n).obj (F.X n) :=
  mkHomToSingle (𝟙 _) (by
    intro i hi
    have hi' : i+1=n := hi
    exact (hn i (by omega)).eq_of_src _ _)

instance bottomProjection_epi : Epi (bottomProjection F n hn) := by
  apply epi_of_epi_f
  intro i
  by_cases hi : i=n
  · subst i
    dsimp [bottomProjection]
    rw [mkHomToSingle_f,Category.id_comp]
    infer_instance
  · exact (isZero_single_obj_X _ _ _ _ hi).epi _

noncomputable def dropBottom : CochainComplex C ℤ := kernel (bottomProjection F n hn)

noncomputable def bottomShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (kernel.ι _) (bottomProjection F n hn) (kernel.condition _)

lemma bottomShortExact : (bottomShortComplex F n hn).ShortExact where
  exact := ShortComplex.exact_kernel _
  mono_f := inferInstanceAs (Mono (kernel.ι (bottomProjection F n hn)))
  epi_g := bottomProjection_epi F n hn

lemma bottomShortExact_eval (i : ℤ) :
    ((bottomShortComplex F n hn).map (eval C (.up ℤ) i)).ShortExact :=
  (bottomShortExact F n hn).map_of_exact _

lemma bottomProjection_f_isIso : IsIso ((bottomProjection F n hn).f n) := by
  dsimp [bottomProjection]
  rw [mkHomToSingle_f,Category.id_comp]
  infer_instance

lemma dropBottom_X_bottom : IsZero ((dropBottom F n hn).X n) := by
  apply (bottomShortExact_eval F n hn n).isIso_g_iff.mp
  exact bottomProjection_f_isIso F n hn

lemma dropBottom_ι_isIso (i : ℤ) (hi : i ≠ n) :
    IsIso ((kernel.ι (bottomProjection F n hn)).f i) := by
  apply (bottomShortExact_eval F n hn i).isIso_f_iff.mpr
  exact isZero_single_obj_X (.up ℤ) n (F.X n) i hi

noncomputable def dropBottomXIso (i : ℤ) (hi : i ≠ n) :
    (dropBottom F n hn).X i ≅ F.X i := by
  exact @asIso _ _ _ _ ((kernel.ι (bottomProjection F n hn)).f i)
    (dropBottom_ι_isIso F n hn i hi)

noncomputable def bottomSplitting (i : ℤ) :
    ((bottomShortComplex F n hn).map (eval C (.up ℤ) i)).Splitting := by
  let S := (bottomShortComplex F n hn).map (eval C (.up ℤ) i)
  have hS : S.ShortExact := bottomShortExact_eval F n hn i
  by_cases hi : i=n
  · subst i
    haveI : IsIso S.g := bottomProjection_f_isIso F n hn
    exact ShortComplex.Splitting.ofExactOfSection S hS.exact (inv S.g)
      (by simp) hS.mono_f
  · haveI : IsIso S.f := dropBottom_ι_isIso F n hn i hi
    exact ShortComplex.Splitting.ofExactOfRetraction S hS.exact (inv S.f)
      (by simp) hS.epi_g

lemma dropBottom_boundedBelow : ∀ i, i < n+1 → IsZero ((dropBottom F n hn).X i) := by
  intro i hi
  by_cases hin : i=n
  · subst i
    exact dropBottom_X_bottom F n hn
  · exact (hn i (by omega)).of_iso (dropBottomXIso F n hn i hin)

variable {G : CochainComplex C ℤ} (hg : ∀ i, i < n → IsZero (G.X i))
  (f : F ⟶ G)

@[reassoc] lemma bottomProjection_naturality :
    bottomProjection F n hn ≫ (single C (.up ℤ) n).map (f.f n) =
      f ≫ bottomProjection G n hg := by
  apply Hom.ext
  funext i
  by_cases hi : i=n
  · subst i
    simp [bottomProjection,single_map_f_self]
  · exact (isZero_single_obj_X (.up ℤ) n (G.X n) i hi).eq_of_tgt _ _

noncomputable def dropBottomMap : dropBottom F n hn ⟶ dropBottom G n hg :=
  kernel.map _ _ f ((single C (.up ℤ) n).map (f.f n))
    (bottomProjection_naturality F n hn hg f)

@[reassoc (attr := simp)] lemma dropBottomMap_ι :
    dropBottomMap F n hn hg f ≫ kernel.ι (bottomProjection G n hg) =
      kernel.ι (bottomProjection F n hn) ≫ f := by
  exact kernel.lift_ι _ _ _

noncomputable def bottomShortComplexMap :
    bottomShortComplex F n hn ⟶ bottomShortComplex G n hg where
  τ₁ := dropBottomMap F n hn hg f
  τ₂ := f
  τ₃ := (single C (.up ℤ) n).map (f.f n)
  comm₁₂ := dropBottomMap_ι F n hn hg f
  comm₂₃ := (bottomProjection_naturality F n hn hg f).symm
end Lech.FiniteComplex

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteModuleCech
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex Set
universe u
variable (R : Type u) [CommRing R] (ι : Type) [Fintype ι] [LinearOrder ι]

 

structure Diagram where
  obj : Finset ι → ModuleCat.{u} R
  res : ∀ {s t : Finset ι}, s ⊆ t → (obj s ⟶ obj t)
  res_self : ∀ s, res (Finset.Subset.refl s) = 𝟙 (obj s)
  res_comp : ∀ {s t v : Finset ι} (hst : s ⊆ t) (htv : t ⊆ v),
    res hst ≫ res htv = res (hst.trans htv)

variable {R ι}
variable (D : Diagram R ι)
abbrev cochains (n : ℕ) := ∀ s : powersetCard ι n, D.obj s.val



def toFixed (S : Finset ι) (n : ℕ) (f : cochains D n) : powersetCard ι n → D.obj S :=
  fun t => if ht : t.val ⊆ S then (D.res ht).hom (f t) else 0

end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CarrierOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.CarrierOperators
open CategoryTheory
universe u
variable {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι]

structure Carrier (ι : Type) where
  Index : Type
  support : Index → Finset ι

variable (A B C : Carrier ι)

def Agree (M : Type u) (S : Finset ι) (f g : A.Index → M) : Prop :=
  ∀ a,A.support a⊆S → f a=g a

structure Op where
  app : ∀ M : ModuleCat.{u} R, (A.Index → M) →ₗ[R] (B.Index → M)
  natural : ∀ {M N : ModuleCat.{u} R} (l : M →ₗ[R] N) (f : A.Index → M),
    app N (l ∘ f)=l ∘ app M f
  locality : ∀ (M : ModuleCat.{u} R) (S : Finset ι) (f g : A.Index → M),
    Agree A M S f g → Agree B M S (app M f) (app M g)

variable {A B C}

def Op.id (A : Carrier ι) : Op (R:=R) A A where
  app _ := LinearMap.id
  natural _ _ := rfl
  locality _ _ _ _ h := h

def Op.comp (Q : Op (R:=R) B C) (P : Op (R:=R) A B) : Op (R:=R) A C where
  app M := (Q.app M).comp (P.app M)
  natural l f := by change Q.app _ (P.app _ (l ∘ f))=_; rw [P.natural,Q.natural]; rfl
  locality M S f g h := Q.locality M S _ _ (P.locality M S f g h)

def Op.add (P Q : Op (R:=R) A B) : Op (R:=R) A B where
  app M := P.app M+Q.app M
  natural l f := by
    ext b
    change P.app _ (l ∘ f) b+Q.app _ (l ∘ f) b=l (P.app _ f b+Q.app _ f b)
    rw [P.natural,Q.natural,map_add]
    rfl
  locality M S f g h b hb := by
    change P.app M f b+Q.app M f b=P.app M g b+Q.app M g b
    rw [P.locality M S f g h b hb,Q.locality M S f g h b hb]

def Op.sub (P Q : Op (R:=R) A B) : Op (R:=R) A B where
  app M := P.app M-Q.app M
  natural l f := by
    ext b
    change P.app _ (l ∘ f) b-Q.app _ (l ∘ f) b=l (P.app _ f b-Q.app _ f b)
    rw [P.natural,Q.natural,map_sub]
    rfl
  locality M S f g h b hb := by
    change P.app M f b-Q.app M f b=P.app M g b-Q.app M g b
    rw [P.locality M S f g h b hb,Q.locality M S f g h b hb]

variable (D : FiniteModuleCech.Diagram R ι)
abbrev Sections (A : Carrier ι) := ∀ a : A.Index,D.obj (A.support a)

def toFixed (A : Carrier ι) (S : Finset ι) : Sections D A →ₗ[R] (A.Index → D.obj S) where
  toFun f a := if ha : A.support a⊆S then (D.res ha).hom (f a) else 0
  map_add' f g := by
    funext a
    split_ifs with h <;> simp [h]
  map_smul' r f := by
    funext a
    split_ifs with h <;> simp [h]

lemma toFixed_self (A : Carrier ι) (f : Sections D A) (a : A.Index) :
    toFixed D A (A.support a) f a=f a := by
  change (if ha : A.support a⊆A.support a then (D.res ha).hom (f a) else 0)=f a
  rw [dite_eq_left (Finset.Subset.refl _),D.res_self]
  rfl

lemma toFixed_restrict (A : Carrier ι) {S T : Finset ι} (hST : S⊆T) (f : Sections D A) :
    Agree A (D.obj T) S (toFixed D A T f) ((D.res hST).hom ∘ toFixed D A S f) := by
  intro a ha
  change (if ht : A.support a⊆T then _ else _) =
    (D.res hST).hom (if hs : A.support a⊆S then _ else _)
  rw [dite_eq_left (ha.trans hST),dite_eq_left ha]
  exact congrArg (fun g : D.obj (A.support a) ⟶ D.obj T => g.hom (f a)) (D.res_comp ha hST).symm

 
def lift (P : Op (R:=R) A B) : Sections D A →ₗ[R] Sections D B :=
  LinearMap.pi (fun b => (LinearMap.proj b).comp
    ((P.app (D.obj (B.support b))).comp (toFixed D A (B.support b))))

lemma toFixed_lift (P : Op (R:=R) A B) (S : Finset ι) (f : Sections D A) :
    Agree B (D.obj S) S (toFixed D B S (lift D P f)) (P.app (D.obj S) (toFixed D A S f)) := by
  intro b hb
  change (if hb : B.support b⊆S then _ else _) = _
  rw [dite_eq_left hb]
  change (D.res hb).hom (P.app (D.obj (B.support b)) (toFixed D A (B.support b) f) b)=_
  have he := P.locality (D.obj S) (B.support b) _ _ (toFixed_restrict D A hb f) b (Finset.Subset.refl _)
  rw [P.natural] at he
  exact he.symm

lemma lift_comp (Q : Op (R:=R) B C) (P : Op (R:=R) A B) :
    lift D (Q.comp P)=(lift D Q).comp (lift D P) := by
  apply LinearMap.ext
  intro f
  funext c
  exact (Q.locality (D.obj (C.support c)) (C.support c) _ _ (toFixed_lift D P _ f)
    c (Finset.Subset.refl _)).symm

lemma lift_id (A : Carrier ι) : lift D (Op.id A)=LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext a
  exact toFixed_self D A f a

lemma lift_add (P Q : Op (R:=R) A B) : lift D (P.add Q)=lift D P+lift D Q := rfl
lemma lift_sub (P Q : Op (R:=R) A B) : lift D (P.sub Q)=lift D P-lift D Q := rfl

lemma lift_congr {P Q : Op (R:=R) A B} (h : ∀ M,P.app M=Q.app M) : lift D P=lift D Q := by
  apply LinearMap.ext
  intro f
  funext b
  change P.app (D.obj (B.support b)) (toFixed D A (B.support b) f) b=_
  rw [h]
  rfl
end Lech.CarrierOperators

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FibreSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory
open scoped TensorProduct
universe u
section Quotient
variable {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (I : Ideal R)

def idealQuotientMap (f : M →ₗ[R] N) :
    (M ⧸ (I • (⊤ : Submodule R M))) →ₗ[R] (N ⧸ (I • (⊤ : Submodule R N))) :=
  Submodule.mapQ _ _ f (by
    rw [←Submodule.map_le_iff_le_comap,Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)

end Quotient

end Lech.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealQuotientFunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory MonoidalCategory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

def quotientFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (M ⧸ (I • (⊤ : Submodule R M)))
  map f := ModuleCat.ofHom (idealQuotientMap I f.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

instance quotientFunctor_additive : (quotientFunctor I).Additive where
  map_add {X Y} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

end Lech.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CartierQuotientDevissage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.CartierQuotient
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{u} R) c} (f : K ⟶ L)
  (hr : ∀ q,(f.f q).hom.range=I • (⊤ : Submodule R (L.X q)))

abbrev quotient (J : Ideal R) (K : HomologicalComplex (ModuleCat.{u} R) c) :=
  ((TensorIdeal.quotientFunctor J).mapHomologicalComplex c).obj K

include hr in
lemma map_power (N : ℕ) (q : ι) :
    (I^N • (⊤ : Submodule R (K.X q))).map (f.f q).hom=
      I^(N+1) • (⊤ : Submodule R (L.X q)) := by
  rw [Submodule.map_smul'',Submodule.map_top,hr,pow_succ,Submodule.mul_smul]

def step (N : ℕ) : quotient (I^N) K ⟶ quotient (I^(N+1)) L where
  f q := ModuleCat.ofHom ((I^N • (⊤ : Submodule R (K.X q))).mapQ
    (I^(N+1) • (⊤ : Submodule R (L.X q))) (f.f q).hom
      (Submodule.map_le_iff_le_comap.mp (map_power I f hr N q).le))
  comm' p q hpq := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => exact congrArg (fun g : K.X p ⟶ L.X q => Submodule.Quotient.mk (g.hom x)) (f.comm p q)

 
def reduction (N : ℕ) : quotient (I^(N+1)) L ⟶ quotient I L where
  f q := ModuleCat.ofHom ((I^(N+1) • (⊤ : Submodule R (L.X q))).mapQ
    (I • (⊤ : Submodule R (L.X q))) LinearMap.id (by
      simpa only [Submodule.comap_id] using
        (Submodule.smul_mono_left (show I^(N+1)≤I from by simpa only [pow_one] using (Ideal.pow_le_pow_right (I:=I) (show 1≤N+1 by omega))))))
  comm' p q hpq := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

lemma step_reduction (N : ℕ) : step I f hr N ≫ reduction (L:=L) I N=0 := by
  apply Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      rw [←hr q]
      exact LinearMap.mem_range_self _ _

def shortComplex (N : ℕ) : ShortComplex (HomologicalComplex (ModuleCat.{u} R) c) :=
  ShortComplex.mk (step I f hr N) (reduction I N) (step_reduction I f hr N)

end Lech.CartierQuotient

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechCarrierOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.CechNormalization
open Set CarrierOperators
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]

abbrev sortedCarrier (p : ℕ) : Carrier ι := ⟨powersetCard ι p,Subtype.val⟩

end Lech.CechNormalization

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechHomogeneousEval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.UniversalSplitting
open Polynomial
universe u

structure Data (R : Type u) [CommRing R] (n : ℕ) (f : R[X]) where
  S : Type u
  [ring : CommRing S]
  [algebra : Algebra R S]
  basis : Module.Basis (Fin n.factorial) R S
  roots : Fin n → S
  factorization : f.map (algebraMap R S) = ∏ i, (Polynomial.X - C (roots i))
  universal : ∀ (T : Type u) [CommRing T] [Algebra R T] (xs : Fin n → T),
    f.map (algebraMap R T) = ∏ i, (Polynomial.X - C (xs i)) →
    ∃! φ : S →ₐ[R] T, ∀ i, φ (roots i)=xs i
attribute [instance] Data.ring Data.algebra


theorem exists_data (n : ℕ) : ∀ (R : Type u) [CommRing R] [Nontrivial R]
    (f : R[X]), f.Monic → f.natDegree=n → Nonempty (Data R n f) := by
  induction n with
  | zero =>
    intro R _ _ f hf hn
    have hf1 : f=1 := hf.natDegree_eq_zero.mp hn
    exact ⟨{
      S := R
      basis := Module.Basis.singleton (Fin 1) R
      roots := Fin.elim0
      factorization := by simp [hf1]
      universal := by
        intro T _ _ xs _
        refine ⟨Algebra.ofId R T, fun i => Fin.elim0 i, ?_⟩
        intro φ _
        ext }⟩
  | succ n ih =>
    intro R _ _ f hf hn
    let B := AdjoinRoot f
    let b : Module.Basis (Fin (n+1)) R B :=
      (AdjoinRoot.powerBasisAux' hf).reindex (finCongr hn)
    let : Nontrivial B := b.repr.symm.injective.nontrivial
    let g : B[X] := f.map (algebraMap R B) /ₘ (Polynomial.X-C (AdjoinRoot.root f))
    have hfac : f.map (algebraMap R B) = (Polynomial.X-C (AdjoinRoot.root f))*g := by
      apply Eq.symm
      exact (mul_divByMonic_eq_iff_isRoot).mpr (AdjoinRoot.isRoot_root f)
    have hg : g.Monic := (monic_X_sub_C _).of_mul_monic_left (hfac ▸ hf.map _)
    have hdeg : g.natDegree=n := by
      rw [show g = _ from rfl, natDegree_divByMonic _ (monic_X_sub_C _),
        hf.natDegree_map, natDegree_X_sub_C, hn]
      omega
    obtain ⟨d⟩ := ih B g hg hdeg
    let : Algebra R d.S := ((algebraMap B d.S).comp (algebraMap R B)).toAlgebra
    let : IsScalarTower R B d.S := IsScalarTower.of_algebraMap_eq fun r => rfl
    let bb : Module.Basis (Fin (n+1) × Fin n.factorial) R d.S := b.smulTower d.basis
    let c : Module.Basis (Fin (n+1).factorial) R d.S :=
      bb.reindex (finProdFinEquiv.trans (finCongr (Nat.factorial_succ n).symm))
    let rs : Fin (n+1) → d.S := Fin.cons
      (algebraMap B d.S (AdjoinRoot.root f)) d.roots
    refine ⟨{
      S := d.S
      basis := c
      roots := rs
      factorization := ?_
      universal := ?_ }⟩
    · have hmap := congrArg (Polynomial.map (algebraMap B d.S)) hfac
      rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
        Polynomial.map_C, d.factorization] at hmap
      simpa [rs, Fin.prod_univ_succ, Polynomial.map_map,
        IsScalarTower.algebraMap_eq R B d.S] using hmap

    · intro T _ _ xs hxs
      have hx0 : f.eval₂ (algebraMap R T) (xs 0)=0 := by
        rw [← Polynomial.eval_map, hxs, Fin.prod_univ_succ]
        simp
      let β : B →ₐ[R] T := AdjoinRoot.liftAlgHom f (Algebra.ofId R T) (xs 0) hx0
      have hβ : β (AdjoinRoot.root f)=xs 0 := AdjoinRoot.liftAlgHom_root _ _ _ _
      let : Algebra B T := β.toRingHom.toAlgebra
      let : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq fun r => (β.commutes r).symm
      have hgxs : g.map (algebraMap B T)=∏ i : Fin n, (Polynomial.X-C (xs i.succ)) := by
        apply (monic_X_sub_C (xs 0)).isRegular.left
        have hmap := congrArg (Polynomial.map β.toRingHom) hfac
        rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
          Polynomial.map_C, show β.toRingHom (AdjoinRoot.root f)=xs 0 from hβ] at hmap
        have heq : (f.map (algebraMap R B)).map β.toRingHom =
            f.map (algebraMap R T) := by
          rw [Polynomial.map_map]
          congr 1
          exact β.comp_algebraMap
        rw [heq, hxs, Fin.prod_univ_succ] at hmap
        exact hmap.symm
      obtain ⟨φ, hφ, huniq⟩ := d.universal T (fun i => xs i.succ) hgxs
      refine ⟨φ.restrictScalars R, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · change φ (algebraMap B d.S (AdjoinRoot.root f))=xs 0
          rw [φ.commutes]
          exact hβ
        · exact hφ j
      · intro ψ hψ
        have hc : ψ.toRingHom.comp (algebraMap B d.S)=β.toRingHom := by
          apply AdjoinRoot.ringHom_ext
          · ext r
            change ψ ((algebraMap B d.S) ((algebraMap R B) r))=β ((algebraMap R B) r)
            rw [← IsScalarTower.algebraMap_apply R B d.S, ψ.commutes, β.commutes]
          · change ψ (algebraMap B d.S (AdjoinRoot.root f))=β (AdjoinRoot.root f)
            rw [hβ]
            exact hψ 0
        let ψB : d.S →ₐ[B] T := {
          toRingHom := ψ.toRingHom
          commutes' := fun b => DFunLike.congr_fun hc b }
        have hψB : ψB=φ := huniq ψB (fun i => hψ i.succ)
        ext x
        exact DFunLike.congr_fun hψB x


end Lech.UniversalSplitting

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PrimitiveChartFaithfullyFlat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.BinaryChange
open Polynomial
universe u
variable {B : Type u} [CommRing B]

lemma linear_degree (t : B) : (C t*Polynomial.X+1).natDegree≤1 := by
  apply natDegree_add_le_of_degree_le
  · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  · simp

lemma term_degree (t : B) (c : B) {k n : ℕ} (hk : k≤n) :
    (C c*(C t*Polynomial.X+1)^k*Polynomial.X^(n-k)).natDegree≤n := by
  apply natDegree_mul_le.trans
  have hpow : ((C t*Polynomial.X+1)^k).natDegree≤k := by
    exact natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left k (linear_degree t))
  have hleft := (natDegree_C_mul_le c _).trans hpow
  have hright : (Polynomial.X^(n-k) : B[X]).natDegree≤n-k := by
    exact natDegree_X_pow_le (n-k)
  omega

lemma term_coeff (t c : B) {k n : ℕ} (hk : k≤n) :
    (C c*(C t*Polynomial.X+1)^k*Polynomial.X^(n-k)).coeff n=c*t^k := by
  have hpow : ((C t*Polynomial.X+1)^k).natDegree≤k :=
    natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left k (linear_degree t))
  have hp := coeff_mul_add_eq_of_natDegree_le hpow (natDegree_X_pow_le (R := B) (n-k))
  rw [Nat.add_sub_of_le hk] at hp
  rw [mul_assoc,coeff_C_mul,hp]
  have he := coeff_pow_of_natDegree_le (m := k) (linear_degree t)
  simp only [mul_one] at he
  rw [he]
  simp [coeff_one]

end Lech.BinaryChange


namespace Lech.BinaryCover
open Polynomial
universe u

lemma ordered_splitting_of_top (R : Type u) [CommRing R] (n : ℕ) (g : R[X])
    (hn : g.natDegree≤n) (ht : g.coeff n=1) :
    Nonempty (UniversalSplitting.Data R n g) := by
  cases subsingleton_or_nontrivial R with
  | inr h =>
    apply UniversalSplitting.exists_data n R g
    · exact monic_of_natDegree_le_of_coeff_eq_one n hn ht
    · apply le_antisymm hn
      apply le_natDegree_of_ne_zero
      rw [ht]
      exact one_ne_zero
  | inl h =>
    refine ⟨{
      S := R
      basis := Module.Basis.ofRepr (LinearEquiv.ofSubsingleton R (Fin n.factorial →₀ R))
      roots := fun _ => 0
      factorization := Subsingleton.elim _ _
      universal := ?_ }⟩
    intro T _ _ xs _
    have : Subsingleton T := Module.subsingleton R T
    refine ⟨Algebra.ofId R T,fun _ => Subsingleton.elim _ _,?_⟩
    intro φ _
    exact Subsingleton.elim _ _



structure Data (A : Type u) [CommRing A] (n : ℕ) (f : A[X]) where
  S : Type u
  [ring : CommRing S]
  [algebra : Algebra A S]
  [chartAlgebra : Algebra (Localization.Away f) S]
  [tower : IsScalarTower A (Localization.Away f) S]
  basis : Module.Basis (Fin n.factorial) (Localization.Away f) S
  faithfullyFlat : Module.FaithfullyFlat A S
  unit : Sˣ
  p : Fin n → S
  q : Fin n → S
  factorization : MvPolynomial.map (algebraMap A S) (f.homogenize n)=
    MvPolynomial.C (unit : S)*∏ i,
      (MvPolynomial.C (p i)*MvPolynomial.X 0+MvPolynomial.C (q i)*MvPolynomial.X 1)
  unimodular : ∀ i, Ideal.span ({p i,q i} : Set S)=⊤
attribute [instance] Data.ring Data.algebra Data.chartAlgebra Data.tower

end Lech.BinaryCover


namespace Lech.RootGluing
open Polynomial
universe u
variable {B : Type u} [CommRing B]

def rootShift (a x : B) : B := x*Ring.inverse (1+a*x)

end Lech.RootGluing
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorTotalHomologyProperty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject


namespace Lech.TensorTotal.Right
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]

 
def functor (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  (curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj K

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
  {F G H : CochainComplex (ModuleCat.{u} R) ℤ}

 

def degreeMap (a : ∀ j, F.X j ⟶ G.X j) (i : ℤ) :
    ((functor K).obj F).X i ⟶ ((functor K).obj G).X i :=
  mapBifunctorDesc (fun p q hpq =>
    ((curriedTensor (ModuleCat.{u} R)).obj (K.X p)).map (a q) ≫
      ιMapBifunctor K G (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq)

@[reassoc (attr := simp)] lemma ι_degreeMap (a : ∀ j, F.X j ⟶ G.X j)
    (p q i : ℤ) (hpq : p+q=i) :
    ιMapBifunctor K F (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq ≫ degreeMap K a i =
      ((curriedTensor (ModuleCat.{u} R)).obj (K.X p)).map (a q) ≫
        ιMapBifunctor K G (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq := by
  apply ι_mapBifunctorDesc

lemma degreeMap_id (i : ℤ) : degreeMap K (fun j => 𝟙 (F.X j)) i = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  change _ = ιMapBifunctor K F (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq ≫
    𝟙 ((mapBifunctor K F (curriedTensor (ModuleCat.{u} R)) (.up ℤ)).X i)
  simp

lemma degreeMap_comp (a : ∀ j, F.X j ⟶ G.X j) (b : ∀ j, G.X j ⟶ H.X j) (i : ℤ) :
    degreeMap K (fun j => a j ≫ b j) i=degreeMap K a i ≫ degreeMap K b i := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  refine (ι_degreeMap K (fun j => a j ≫ b j) p q i hpq).trans ?_
  simp only [Functor.map_comp]
  exact (Category.assoc _ _ _).trans
    ((congrArg (((curriedTensor (ModuleCat.{u} R)).obj (K.X p)).map (a q) ≫ ·)
      (ι_degreeMap K b p q i hpq).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ degreeMap K b i) (ι_degreeMap K a p q i hpq).symm).trans
            (Category.assoc _ _ _))))

lemma degreeMap_add (a b : ∀ j, F.X j ⟶ G.X j) (i : ℤ) :
    degreeMap K (fun j => a j+b j) i=degreeMap K a i+degreeMap K b i := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  refine (ι_degreeMap K (fun j => a j + b j) p q i hpq).trans ?_
  simp only [Functor.map_add]
  exact (Preadditive.add_comp _ _ _ _ _ _).trans
    ((congrArg₂ (· + ·) (ι_degreeMap K a p q i hpq).symm
      (ι_degreeMap K b p q i hpq).symm).trans (Preadditive.comp_add _ _ _ _ _ _).symm)

lemma map_f (f : F ⟶ G) (i : ℤ) :
    ((functor K).map f).f i=degreeMap K f.f i := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  simp only [functor]
  refine (ι_mapBifunctorMap (𝟙 K) f (curriedTensor (ModuleCat.{u} R)) (.up ℤ)
    p q i hpq).trans ?_
  exact (congrArg (fun t => t ≫
    ((curriedTensor (ModuleCat.{u} R)).obj (K.X p)).map (f.f q) ≫
      ιMapBifunctor K G (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq)
        (congrArg (fun t => t.app (F.X q)) ((curriedTensor (ModuleCat.{u} R)).map_id (K.X p)))).trans
    ((Category.id_comp _).trans (ι_degreeMap K f.f p q i hpq).symm)

instance instAdditiveCochainComplexModuleCatIntFunctor : (functor K).Additive where
  map_add {F G} f g := by
    apply HomologicalComplex.Hom.ext
    funext i
    change ((functor K).map (f+g)).f i=((functor K).map f).f i+((functor K).map g).f i
    simp only [map_f]
    exact degreeMap_add K f.f g.f i

 

def splitting (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (s : ∀ j, (S.map (eval (ModuleCat.{u} R) (.up ℤ) j)).Splitting) (i : ℤ) :
    ((S.map (functor K)).map (eval (ModuleCat.{u} R) (.up ℤ) i)).Splitting where
  r := degreeMap K (fun j => (s j).r) i
  s := degreeMap K (fun j => (s j).s) i
  f_r := by
    change ((functor K).map S.f).f i ≫ degreeMap K (fun j => (s j).r) i = 𝟙 (((functor K).obj S.X₁).X i)
    erw [map_f,←degreeMap_comp]
    erw [show (fun j => S.f.f j ≫ (s j).r)=(fun j => 𝟙 (S.X₁.X j)) from
      funext (fun j => (s j).f_r),degreeMap_id]
  s_g := by
    change degreeMap K (fun j => (s j).s) i ≫ ((functor K).map S.g).f i = 𝟙 (((functor K).obj S.X₃).X i)
    erw [map_f,←degreeMap_comp]
    erw [show (fun j => (s j).s ≫ S.g.f j)=(fun j => 𝟙 (S.X₃.X j)) from
      funext (fun j => (s j).s_g),degreeMap_id]
  id := by
    change degreeMap K (fun j => (s j).r) i ≫ ((functor K).map S.f).f i + ((functor K).map S.g).f i ≫ degreeMap K (fun j => (s j).s) i = 𝟙 (((functor K).obj S.X₂).X i)
    erw [map_f,map_f,←degreeMap_comp,←degreeMap_comp,←degreeMap_add]
    erw [show (fun j => (show S.X₂.X j ⟶ S.X₁.X j from (s j).r) ≫ S.f.f j + S.g.f j ≫ (show S.X₃.X j ⟶ S.X₂.X j from (s j).s))=
      (fun j => 𝟙 (S.X₂.X j)) from funext (fun j => (s j).id),degreeMap_id]

end Lech.TensorTotal.Right


namespace Lech.TensorTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R]
  (F K : CochainComplex (ModuleCat.{u} R) ℤ)
  (hK : ∀ j, j < 0 → IsZero (K.X j))

noncomputable def bottomSequence : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  (FiniteComplex.bottomShortComplex K 0 hK).map (Right.functor F)

lemma bottomSequence_shortExact : (bottomSequence F K hK).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro i
  exact (Right.splitting F _ (FiniteComplex.bottomSplitting K 0 hK) i).shortExact

noncomputable def bottomComparison (i : ℤ) :
    ((Right.functor F).obj ((single (ModuleCat.{u} R) (.up ℤ) 0).obj (K.X 0))).homology i ⟶
      ((Right.functor F).obj (FiniteComplex.dropBottom K 0 hK)).homology (i+1) :=
  (bottomSequence_shortExact F K hK).δ i (i+1) rfl

@[reassoc]
lemma bottomComparison_naturality (L : CochainComplex (ModuleCat.{u} R) ℤ)
    (hL : ∀ j, j < 0 → IsZero (L.X j)) (f : K ⟶ L) (i : ℤ) :
    bottomComparison F K hK i ≫ homologyMap ((Right.functor F).map
      (FiniteComplex.dropBottomMap K 0 hK hL f)) (i+1) =
    homologyMap ((Right.functor F).map ((single (ModuleCat.{u} R) (.up ℤ) 0).map (f.f 0))) i ≫
      bottomComparison F L hL i := by
  exact HomologySequence.δ_naturality
    ((Right.functor F).mapShortComplex.map (FiniteComplex.bottomShortComplexMap K 0 hK hL f))
    (bottomSequence_shortExact F K hK) (bottomSequence_shortExact F L hL) i (i+1) rfl
end Lech.TensorTotal


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PowerSeriesFinDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open CategoryTheory


namespace Lech.CoefficientField
variable (R : Type*) [CommRing R] (I : Ideal R) (p : ℕ) [Fact p.Prime] [CharP R p]
  [CharP (R ⧸ I) p] [PerfectRing (R ⧸ I) p]

 
def frobeniusFactor (n : ℕ) : R ⧸ I →+* R ⧸ I^(p^n) :=
  Ideal.Quotient.lift I ((Ideal.Quotient.mk (I^(p^n))).comp (iterateFrobenius R p n)) (by
    intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change x^(p^n) ∈ I^(p^n)
    exact Ideal.pow_mem_pow hx (p^n))


def stage (n : ℕ) : R ⧸ I →+* R ⧸ I^(p^n) :=
  (frobeniusFactor R I p n).comp (iterateFrobeniusEquiv (R ⧸ I) p n).symm.toRingHom

lemma stage_pow_mk (n : ℕ) (x : R) :
    stage R I p n ((Ideal.Quotient.mk I x)^(p^n)) =
      Ideal.Quotient.mk (I^(p^n)) (x^(p^n)) := by
  change frobeniusFactor R I p n
    ((iterateFrobeniusEquiv (R ⧸ I) p n).symm
      ((iterateFrobeniusEquiv (R ⧸ I) p n) (Ideal.Quotient.mk I x))) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

lemma power_strictMono : StrictMono (fun n : ℕ => p^n) :=
  pow_right_strictMono₀ (Nat.Prime.one_lt (Fact.out : p.Prime))

lemma stage_compatible (n : ℕ) :
    (Ideal.Quotient.factorPow I ((power_strictMono p).monotone (Nat.le_succ n))).comp
      (stage R I p (n+1)) = stage R I p n := by
  apply RingHom.ext
  intro x
  obtain ⟨y,hy⟩ := (iterateFrobeniusEquiv (R ⧸ I) p (n+1)).surjective x
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← hy]
  change Ideal.Quotient.factorPow I ((power_strictMono p).monotone (Nat.le_succ n))
    (stage R I p (n+1) ((Ideal.Quotient.mk I a)^(p^(n+1)))) =
      stage R I p n ((Ideal.Quotient.mk I a)^(p^(n+1)))
  rw [stage_pow_mk]
  have he : (Ideal.Quotient.mk I a)^(p^(n+1)) =
      (Ideal.Quotient.mk I (a^p))^(p^n) := by
    rw [map_pow,← pow_mul,pow_succ']
  rw [he,stage_pow_mk]
  simp only [← pow_mul,pow_succ']
  rfl

variable [IsAdicComplete I R]

 

def sectionMap : R ⧸ I →+* R :=
  IsAdicComplete.StrictMono.liftRingHom I (power_strictMono p) (stage R I p)
    (fun {n} => stage_compatible R I p n)

end Lech.CoefficientField
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CoefficientFieldLocalSection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open CategoryTheory
namespace Lech.CoefficientField
variable (R : Type*) [CommRing R] [IsDomain R] [IsLocalRing R]
  (p : ℕ) [Fact p.Prime] [CharP R p]
  [PerfectRing (IsLocalRing.ResidueField R) p]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

 

def localSection : IsLocalRing.ResidueField R →+* R := by
  let : CharP (R ⧸ IsLocalRing.maximalIdeal R) p :=
    CharP.of_ringHom_of_ne_zero (Ideal.Quotient.mk _) p (Nat.Prime.ne_zero Fact.out)
  let : PerfectRing (R ⧸ IsLocalRing.maximalIdeal R) p :=
    inferInstanceAs (PerfectRing (IsLocalRing.ResidueField R) p)
  exact sectionMap R (IsLocalRing.maximalIdeal R) p

end Lech.CoefficientField


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProjectiveReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.CoefficientReduction
open MvPolynomial HomogeneousLocalization
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) (h : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra 

abbrev grade := homogeneousSubmodule (Fin h) R

def graded : grade (R:=R) h →+*ᵍ SourceGraded.sourceGrade I h where
  toRingHom := MvPolynomial.map (Ideal.Quotient.mk I)
  map_mem {i} {x} hx := by
    intro e he
    exact hx (fun heq => he (by simp only [coeff_map,heq,map_zero]))

end Lech.CoefficientReduction

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorCechHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.CechNormalization
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]

def extendEquivalence {K L : CochainComplex (ModuleCat.{u} R) ℕ} (e : HomotopyEquiv K L) :
    HomotopyEquiv (K.extend ComplexShape.embeddingUpNat) (L.extend ComplexShape.embeddingUpNat) where
  hom := extendMap e.hom ComplexShape.embeddingUpNat
  inv := extendMap e.inv ComplexShape.embeddingUpNat
  homotopyHomInvId := by
    simpa only [extendMap_comp,extendMap_id] using e.homotopyHomInvId.extend ComplexShape.embeddingUpNat
  homotopyInvHomId := by
    simpa only [extendMap_comp,extendMap_id] using e.homotopyInvHomId.extend ComplexShape.embeddingUpNat

variable (F : CochainComplex (ModuleCat.{u} R) ℤ)
def tensorHomotopy {K L : CochainComplex (ModuleCat.{u} R) ℤ} {f g : K ⟶ L} (h : Homotopy f g) :
    Homotopy ((TensorTotal.Right.functor F).map f) ((TensorTotal.Right.functor F).map g) :=
  mapBifunctorMapHomotopy₂ (𝟙 F) h (curriedTensor (ModuleCat.{u} R)) (.up ℤ)

end Lech.CechNormalization

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TowerRestrictedLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open CategoryTheory
attribute [local instance] Classical.propDecidable


namespace Lech.CharP
open IsLocalRing Filter
open scoped ENNReal Topology nonZeroDivisors
universe u
variable (D : Type u) [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  (p : ℕ) [Fact p.Prime] [CharP D p] [PerfectRing (ResidueField D) p]

 
def parameterIdeal {h : ℕ} (z : Fin h → D) (a : ℕ) : Ideal D :=
  Ideal.span (Set.range fun j => z j^a)



end Lech.CharP


end
end

end OAI
end


