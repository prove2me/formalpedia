-- Prove2me | Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian_Lib
-- name    : ProEtale_Mathlib_RingTheory_Henselian_Lib
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:40:46.571556+00:00
-- url     : https://prove2.me/theorems/ed53dcfc-4fb5-4326-9503-665bf9357835
-- title:
--   Strictly henselian rings, a standard étale presentation, and the henselization as a left Kan extension
-- statement:
--   This file continues the published file of the same name on henselian rings.
--
--   Principal results and constructions:
--   1. A strictly henselian local ring has a separably closed residue field. A local ring $R$ is strictly henselian if and only if it is henselian and its residue field is separably closed. Henselianity and strict henselianity transfer along ring isomorphisms.
--   2. For $f \in R[X]$, the algebra $R[x_0,x_1]/(f(x_0),\ f'(x_0)x_1 - 1)$ is given a submersive presentation, so it is standard smooth of relative dimension $0$. This uses the partial derivatives of polynomials in one variable placed in $n$ variables: $\partial_i(f(x_j)) = 0$ for $i \ne j$ and $\partial_i(f(x_i)) = f'(x_i)$. The Jacobian entries are computed as auxiliary lemmas.
--   3. Categorical preliminaries: the forgetful functor from the category of étale ring maps under $R$ to commutative $R$-algebras; categories $\mathrm{Under}(X)$ have colimits when the ambient category does; comma categories $(S \downarrow T)$ are essentially small under smallness hypotheses. As a result, the category of étale $R$-algebras is essentially small and the inclusion admits pointwise left Kan extensions along itself.
--   4. **Henselization functor.** The endofunctor of commutative $R$-algebras is the left Kan extension of the inclusion $\iota$ of étale $R$-algebras along itself. For an $R$-algebra $S$, the **henselization** $\mathrm{Hens}_R(S)$ is its value at $S$. Concretely, it is the colimit of the étale $R$-algebras $E$ equipped with an $R$-algebra map $E \to S$:
--   $$\mathrm{Hens}_R(S) = \operatorname{colim}_{(E,\,E\to S)} E.$$
--
--   A section comment sketches why the henselization of a pair $(A, I)$ is henselian (Stacks 0A02). That statement is not proved in this file.
--
--   **Formalization Note** The public declarations are `isStrictlyHenselianLocalRing_iff_henselianLocalRing_and_isSepClosed`, `HenselianLocalRing.of_ringEquiv`, `IsStrictlyHenselianLocalRing.of_ringEquiv`, `pderiv_toMvPolynomial_eq_zero_of_ne`, `pderiv_toMvPolynomial_eq_toMvPolynomial_pderiv`, `CommRingCat.Under.inclusion`, `CategoryTheory.CommRingCat.Etale`, `henselizationFunctor` and `Henselization` (with its `CommRing` and `Algebra R` instances). The standard étale algebra and its presentation are `private`. An instance named `foo` provides essential smallness of costructured-arrow categories. $R$ and $S$ live in the same universe `u`. Mathlib's `HenselianLocalRing` and `IsStrictlyHenselianLocalRing` are used as in Mathlib.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014); cited in the code: Stacks Project, Tag 0A02. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/RingTheory/Henselian.lean (declarations needed by the transplanted proofs, unused ones removed). Continues the published definition file Def_ProEtale_Mathlib_RingTheory_Henselian of the same module.

import Mathlib
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.TensorProduct.Quotient
import Definitions.Def_ProEtale_FiniteFields_Etale_AlgebraicHenselization
import Definitions.Def_ProEtale_FiniteFields_Etale_IndEtale
import Definitions.Def_ProEtale_FiniteFields_Etale_IndEtaleStructural
import Definitions.Def_ProEtale_Mathlib_FieldTheory_IsSepClosed
import Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
-- Rename `HenselianRing` to `IsHenselianRing`, ``HenselianLocalRing` to `IsHenselianLocalRing`.


instance inst_MathlibRingTheoryHenselian_L11 (R : Type*) [CommRing R] [IsStrictlyHenselianLocalRing R] :
    IsSepClosed (IsLocalRing.ResidueField R) :=
  IsStrictlyHenselianLocalRing.isSepClosed_residueField

/-- A local ring is strictly Henselian if and only if it is Henselian and its residue
field is separably closed. -/
theorem isStrictlyHenselianLocalRing_iff_henselianLocalRing_and_isSepClosed
    (R : Type*) [CommRing R] [IsLocalRing R] :
    IsStrictlyHenselianLocalRing R ↔
      HenselianLocalRing R ∧ IsSepClosed (IsLocalRing.ResidueField R) :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩,
    fun h ↦ have := h.1; ⟨h.2⟩⟩

/-- `HenselianLocalRing` transfers along a ring isomorphism. -/
theorem HenselianLocalRing.of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [HenselianLocalRing R] (e : R ≃+* S) : HenselianLocalRing S := by
  have : IsLocalRing S := e.isLocalRing
  refine HenselianLocalRing.mk fun f hf a₀ hmem hunit => ?_
  let f' : Polynomial R := f.map e.symm.toRingHom
  have heval : f'.eval (e.symm a₀) = e.symm (f.eval a₀) :=
    Polynomial.eval_map_apply (p := f) e.symm.toRingHom a₀
  have hderiv : f'.derivative.eval (e.symm a₀) = e.symm (f.derivative.eval a₀) := by
    rw [Polynomial.derivative_map (f := e.symm.toRingHom)]
    exact Polynomial.eval_map_apply (p := f.derivative) e.symm.toRingHom a₀
  have hmem' : f'.eval (e.symm a₀) ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal] at hmem
    rw [heval, IsLocalRing.mem_maximalIdeal]
    intro hu
    exact hmem (by simpa using hu.map e)
  have hunit' : IsUnit (f'.derivative.eval (e.symm a₀)) :=
    hderiv ▸ hunit.map e.symm.toRingHom
  obtain ⟨a, ha_root, ha_diff⟩ :=
    HenselianLocalRing.is_henselian f' (hf.map _) (e.symm a₀) hmem' hunit'
  refine ⟨e a, ?_, ?_⟩
  · have hf_eq : f'.map e.toRingHom = f := by
      simp [f', Polynomial.map_map]
    have key : f.eval (e a) = e (f'.eval a) := by
      rw [← hf_eq]; exact Polynomial.eval_map_apply (p := f') e.toRingHom a
    rw [Polynomial.IsRoot.def, key, Polynomial.IsRoot.def.mp ha_root, map_zero]
  · rw [IsLocalRing.mem_maximalIdeal] at ha_diff ⊢
    intro hu
    apply ha_diff
    have : a - e.symm a₀ = e.symm (e a - a₀) := by simp
    rw [this]
    exact hu.map e.symm.toRingHom


/-- `IsStrictlyHenselianLocalRing` transfers along a ring isomorphism. -/
theorem IsStrictlyHenselianLocalRing.of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsStrictlyHenselianLocalRing R] (e : R ≃+* S) : IsStrictlyHenselianLocalRing S :=
  have : HenselianLocalRing S := .of_ringEquiv e
  ⟨IsSepClosed.of_ringEquiv (IsLocalRing.ResidueField.mapEquiv e)⟩

universe u v

noncomputable section
open Polynomial
open MvPolynomial Ideal Quotient Algebra

variable {R : Type u} [CommRing R] (f : R[X])

-- f(X), f'(X)Y - 1
private def idealJ (f : R[X]) : Ideal (MvPolynomial (Fin 2) R) :=
  (span (Set.range
    ![toMvPolynomial (0 : Fin 2) f, (toMvPolynomial (0 : Fin 2) f.derivative) * X 1 - 1]))

private def S : Type u := MvPolynomial (Fin 2) R ⧸ (idealJ f)

private instance inst_MathlibRingTheoryHenselian_L126 : CommRing (S f) := by
  unfold S
  infer_instance

private instance inst_MathlibRingTheoryHenselian_L130 : Algebra R (S f) := by
  unfold S
  infer_instance

private def presentationS : Presentation R (S f) (Fin 2) (Fin 2) := by
  let s : (S f) → (MvPolynomial (Fin 2) R) :=
    Function.surjInv (f := (Ideal.Quotient.mk (idealJ f))) Quotient.mk_surjective
  have hs (x : S f) : Ideal.Quotient.mk _ (s x) = x := by
    rw [Function.surjInv_eq (f := (Ideal.Quotient.mk (idealJ f)))]
  apply Presentation.naive s hs

private def preSubmersivePresentationS : PreSubmersivePresentation R (S f) (Fin 2) (Fin 2) := {
  toPresentation := presentationS f
  map := id
  map_inj _ _ h := h
}

@[simp]
theorem pderiv_toMvPolynomial_eq_zero_of_ne (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    (pderiv i) ((toMvPolynomial j) f) = 0 := by
  induction f using Polynomial.induction_on with
  | C a => simp
  | add p q _ _ => simp_all
  | monomial n a _ => simp [Pi.single_eq_of_ne h.symm]

@[simp]
theorem pderiv_toMvPolynomial_eq_toMvPolynomial_pderiv (n : ℕ) (i : Fin n) :
    (pderiv i) ((toMvPolynomial i) f) = (toMvPolynomial i) f.derivative := by
  induction f using Polynomial.induction_on with
  | C a => simp
  | add p q _ _ => simp_all
  | monomial n a _ => simp

lemma preSubmersivePresentationS_jacobiMatrix_00 :
    (preSubmersivePresentationS f).jacobiMatrix 0 0 =
    (mk (idealJ f) (toMvPolynomial (0 : Fin 2) f.derivative)) := by
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  simp [preSubmersivePresentationS, presentationS]

lemma preSubmersivePresentationS_jacobiMatrix_11 :
    (preSubmersivePresentationS f).jacobiMatrix 1 1 =
    (mk (idealJ f) (toMvPolynomial (0 : Fin 2) f.derivative)) := by
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  simp [preSubmersivePresentationS, presentationS]

lemma preSubmersivePresentationS_jacobiMatrix_01 :
    (preSubmersivePresentationS f).jacobiMatrix 1 0 = 0 := by
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  simp [preSubmersivePresentationS, presentationS]

private def submersivePresentationS (f : R[X]) : SubmersivePresentation R (S f) (Fin 2) (Fin 2) := {
  toPreSubmersivePresentation := preSubmersivePresentationS f
  jacobian_isUnit := by
    let f' := (mk (idealJ f) (toMvPolynomial (0 : Fin 2) f.derivative))
    have unit_f' : IsUnit f' := by
      apply IsUnit.of_mul_eq_one (mk (idealJ f) (X 1))
      rw [← map_mul, ← map_one (Ideal.Quotient.mk _), mk_eq_mk_iff_sub_mem]
      apply Ideal.subset_span
      simp
    have : (preSubmersivePresentationS f).jacobian = f' * f' := by
      rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
      rw [Matrix.det_fin_two]
      have (x : (MvPolynomial (Fin 2) R)) :
          (algebraMap (preSubmersivePresentationS f).Ring (S f)) x = mk (idealJ f) x := by rfl
      rw [this]
      simp only [Fin.isValue, map_sub, map_mul]
      rw [preSubmersivePresentationS_jacobiMatrix_00]
      rw [preSubmersivePresentationS_jacobiMatrix_11]
      rw [preSubmersivePresentationS_jacobiMatrix_01]
      simp [f']
    rw [this]
    simp [unit_f']
}

private instance inst_MathlibRingTheoryHenselian_L204 : IsStandardSmoothOfRelativeDimension 0 R (S f) := by
  unfold S
  constructor
  use (Fin 2), (Fin 2), inferInstance, inferInstance, (submersivePresentationS f)
  simp [Presentation.dimension]


-- Success

/-! ### The henselization of a pair is henselian (Stacks 0A02)

Let `H` be the algebraic henselization of `A → A ⧸ I`: the filtered colimit of the étale
`A`-algebras with an `A`-algebra map to `A ⧸ I`. Its counit `H → A ⧸ I` is surjective with kernel
`I H`, and `A`-algebra maps from an ind-étale `A`-algebra `D` to `H` correspond to ring maps
`D → A ⧸ I` (`FiniteFields.Etale.algebraicHenselization_existsUnique_lift`). We deduce that
`(H, I H)` is a henselian pair through `henselian_if_exists_section`:

* `I H` lies in the Jacobson radical: if `c(x) = 0` then `u = x y + 1` maps to `1`, so the counit
  extends to `H[1/u]`; the lift `H[1/u] → H` composed with `H → H[1/u]` is the identity by
  uniqueness, hence `u` is a unit;
* an `H`-algebra map `S → H ⧸ I H` from an étale `H`-algebra gives a ring map `S → A ⧸ I`, whose
  lift `S → H` is `H`-linear by uniqueness. -/


open CategoryTheory CommAlgCat Limits

universe u₁ v₁ u₂ v₂ w

variable (Q : MorphismProperty CommRingCat) (R : CommRingCat.{u})

noncomputable
def CommRingCat.Under.inclusion :
    MorphismProperty.Under Q ⊤ R ⥤ CommAlgCat R :=
  MorphismProperty.Under.forget _ _ _ ⋙ (commAlgCatEquivUnder R).inverse

abbrev CategoryTheory.CommRingCat.Etale : MorphismProperty CommRingCat :=
  RingHom.toMorphismProperty RingHom.Etale

instance inst_MathlibRingTheoryHenselian_L429 {C : Type*} [Category C] [HasColimits C] (X : C) : HasColimits (Under X) := by
  constructor
  intro J _
  constructor
  intro K
  constructor
  constructor
  refine ⟨?_, ?_⟩
  · exact WithInitial.coconeEquiv.inverse.obj (colimit.cocone _)
  · apply WithInitial.isColimitEquiv.toFun
    apply IsColimit.ofIsoColimit _ (WithInitial.coconeEquiv.counitIso.app _).symm
    exact colimit.isColimit (WithInitial.liftFromUnder.obj K)

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (S : C ⥤ D) (T : D)

instance foo [EssentiallySmall.{w} C] [∀ (X : C), Small.{w} (S.obj X ⟶ T)] :
    EssentiallySmall.{w} (CostructuredArrow S T) := by
  obtain ⟨C', _, ⟨e⟩⟩ := EssentiallySmall.equiv_smallCategory (C := C)
  let eq : CostructuredArrow (e.inverse ⋙ S) T ⥤ CostructuredArrow S T :=
    Comma.map (F₂ := 𝟭 _) (Functor.rightUnitor _).inv (𝟙 _)
  have : eq.IsEquivalence := Comma.isEquivalenceMap _ _
  let f (x : CostructuredArrow (e.inverse ⋙ S) T) : Σ (X : C'), (S.obj (e.inverse.obj X) ⟶ T) :=
    ⟨x.1, x.3⟩
  have : Function.Injective f := by
    intro ⟨x, ⟨⟨⟩⟩, x3⟩ ⟨y, ⟨⟨⟩⟩, y3⟩ h
    obtain rfl : x = y := congr($(h).1)
    congr
    exact congr($(h).2)
  have : Small.{w} (CostructuredArrow (e.inverse ⋙ S) T) := small_of_injective this
  have : LocallySmall.{w} (CostructuredArrow (e.inverse ⋙ S) T) := by
    constructor
    intro X Y
    exact small_of_injective ((CostructuredArrow.proj _ _).map_injective)
  have := essentiallySmall_of_small_of_locallySmall (CostructuredArrow (e.inverse ⋙ S) T)
  apply essentiallySmall_of_fully_faithful.{w} (eq.asEquivalence.inverse)

instance inst_MathlibRingTheoryHenselian_L466 : EssentiallySmall.{u, u, u + 1} (CommRingCat.Etale.Under ⊤ R) := by
  apply essentiallySmall_of_le
  intro X Y f hf
  exact .of_finitePresentation hf.2

instance inst_MathlibRingTheoryHenselian_L471 (R : Type u) [CommRing R] :
    (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R)).HasPointwiseLeftKanExtension
    (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R)) := by
  dsimp [Functor.HasPointwiseLeftKanExtension]
  rintro _
  dsimp [Functor.HasPointwiseLeftKanExtensionAt]
  apply (config := {allowSynthFailures := true}) Limits.HasColimitsOfShape.has_colimit
  apply hasColimitsOfShape_of_essentiallySmall

def henselizationFunctor (R : Type u) [CommRing R] :
    (CommAlgCat R) ⥤ CommAlgCat R :=
  (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R)).leftKanExtension
    (CommRingCat.Under.inclusion CommRingCat.Etale (CommRingCat.of R))

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

def Henselization : Type u := (henselizationFunctor R).obj (of R S)

instance inst_MathlibRingTheoryHenselian_L489 : CommRing (Henselization R S) := by
  unfold Henselization
  infer_instance

instance inst_MathlibRingTheoryHenselian_L493 : Algebra R (Henselization R S) := by
  unfold Henselization
  infer_instance


