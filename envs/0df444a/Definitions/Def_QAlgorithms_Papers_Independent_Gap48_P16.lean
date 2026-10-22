-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16
-- name    : QAlgorithms_Papers_Independent_Gap48_P16
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T21:50:53.851982+00:00
-- url     : https://prove2.me/theorems/849c8db8-80b1-483f-ae52-b9b33294b6f1
-- title:
--   Definitions for Duality and Rational Modules in Hopf Algebras over Commutative Rings
-- statement:
--   The objects the formalized statements of *Duality and Rational Modules in Hopf Algebras over Commutative Rings* (arXiv:math/0011207) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `pairingAlpha`: The map alpha_M of section 2.1, PDF p.3.
--   - `evaluationEmbedding`: The embedding in ALL functions used on PDF p.5.
--   - `IsRationalSystem`: Definition 2.2, PDF p.4: injectivity for every module in the ambient universe.
--   - `IsTensorInjective`: X-purity of a specified map, with tensor factors in the order of PDF p.3.
--   - `IsPureMap`: A pure inclusion of modules, PDF p.3; the inclusion itself is injective.
--   - `IsMockProjective`: Definition 2.6, PDF p.5. Reconstruction functions need not be linear.
--   - `tensorPairing`: The induced tensor pairing in Proposition 2.5, PDF pp.4-5.
--   - `IsRationalPairing`: Definition 2.8, PDF p.5, using the two explicit identities (2).
--   - `IsRationalParameters`: Rational parameters for a module element, Definition 2.9, PDF p.6.
--   - `LeftQuotient`: The R-module quotient by a LEFT ideal, section 4, PDF p.12.
--   - `IsCofiniteLeft`: Cofiniteness always refers to finite generation over R, PDF p.12.
--   - `PropertyLeft`: Property P-left, Definition 4.1, PDF p.12.
--   - `PropertyRight`: Property P-right, Remark 4.4, PDF p.13, expressed through the opposite algebra.
--   - `PropertyTwoSided`: The two-sided property P, Remark 4.4, PDF p.13.
--   - `finiteDual`: Finite dual as the sum of dual cofinite left quotients; PDF pp.7,13, equation (4). Over a noetherian base the generators already form a submodule, so the span adds no forms.
--   - `finiteDualPairing`: The canonical evaluation pairing for the finite dual, PDF p.7.
--   - `CofiniteLeftIdeal`: The cofinite left ideals indexing the completion of Remark 4.5, PDF p.13.
--   - `leftQuotientTransition`: Quotient transition along an inclusion of left ideals; no quotient algebra is used.
--   - `cofiniteCompletion`: The cofinite completion as compatible families of module quotient classes, PDF p.13.
--   - `cofiniteDualElement`: The canonical finite-dual element defined by a functional on a cofinite quotient.
--   - `convolutionPairing`: The evaluation pairing with the convolution-dual carrier, Corollary 2.16, PDF p.9.
--   - `IsCanonicalFiniteDualCoalgebra`: The canonical finite-dual comultiplication and counit, PDF pp.7-9. These are specifications on the coalgebra constructed in the conclusion, not assumptions.
--   - `tensorSubmoduleSum`: The sum of the two tensor-inclusion images, Lemma 4.8, PDF p.14.
--   - `IsFiniteProjectiveRightExtension`: Finiteness and projectivity of the RIGHT module restricted along the given map, p.13.
--   - `finiteDualTensorMap`: The canonical finite-dual tensor map into the ordinary dual, PDF pp.14-15.
--   - `IsReversiblePolynomial`: Reversible polynomial, Definition 4.11, PDF p.15. Degree zero is permitted.
--   - `IsReversibleIdeal`: Reversible ideal, Definition 4.11, PDF p.15.
-- source:
--   Duality and Rational Modules in Hopf Algebras over Commutative Rings, arXiv:math/0011207v1, https://arxiv.org/abs/math/0011207v1

import Mathlib

/-!
Paper-local statements for Abuhlail, Gomez-Torrecillas and Lobillo,
*Duality and Rational Modules in Hopf Algebras over Commutative Rings*,
arXiv:math/0011207v1. All page references are PDF pages.

The universe is arbitrary; none of the module carriers below is assumed finite.
The finite dual is the sum of the duals of cofinite left quotients, as in
(4), p.7, and Remark 4.5, p.13. Over the noetherian base used below this is
exactly the set of forms annihilating a cofinite left ideal.
-/

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section Pairings

variable {R A P Q B M : Type u} [CommRing R]
variable [AddCommGroup A] [Module R A] [AddCommGroup P] [Module R P]
variable [AddCommGroup Q] [Module R Q] [AddCommGroup B] [Module R B]
variable [AddCommGroup M] [Module R M]

/-- The map alpha_M of section 2.1, PDF p.3. -/
def pairingAlpha (b : P →ₗ[R] A →ₗ[R] R) (M : Type u)
    [AddCommGroup M] [Module R M] : M ⊗[R] P →ₗ[R] A →ₗ[R] M :=
  (dualTensorHom R A M).comp
    ((TensorProduct.map b (LinearMap.id : M →ₗ[R] M)).comp
      (TensorProduct.comm R M P).toLinearMap)

/-- The embedding in ALL functions used on PDF p.5. -/
def evaluationEmbedding (b : P →ₗ[R] A →ₗ[R] R) : P →ₗ[R] (A → R) :=
  (LinearMap.ltoFun R A R R).comp b

/-- Definition 2.2, PDF p.4: injectivity for every module in the ambient universe. -/
def IsRationalSystem (b : P →ₗ[R] A →ₗ[R] R) : Prop :=
  ∀ (X : Type u) [AddCommGroup X] [Module R X], Function.Injective (pairingAlpha b X)

/-- X-purity of a specified map, with tensor factors in the order of PDF p.3. -/
def IsTensorInjective {N L : Type u} [AddCommGroup N] [Module R N]
    [AddCommGroup L] [Module R L] (i : N →ₗ[R] L) (X : Type u)
    [AddCommGroup X] [Module R X] : Prop :=
  Function.Injective (TensorProduct.map i (LinearMap.id : X →ₗ[R] X))

/-- A pure inclusion of modules, PDF p.3; the inclusion itself is injective. -/
def IsPureMap {N L : Type u} [AddCommGroup N] [Module R N]
    [AddCommGroup L] [Module R L] (i : N →ₗ[R] L) : Prop :=
  Function.Injective i ∧
    ∀ (X : Type u) [AddCommGroup X] [Module R X], IsTensorInjective i X

/-- Definition 2.6, PDF p.5. Reconstruction functions need not be linear. -/
def IsMockProjective (b : P →ₗ[R] A →ₗ[R] R) : Prop :=
  Function.Injective (pairingAlpha b R) ∧
    ∀ (n : ℕ) (p : Fin n → P), ∃ (m : ℕ) (a : Fin m → A)
      (g : Fin m → A → R), ∀ i x, b (p i) x = ∑ l, b (p i) (a l) * g l x

/-- The induced tensor pairing in Proposition 2.5, PDF pp.4-5. -/
def tensorPairing (b : P →ₗ[R] A →ₗ[R] R) (c : Q →ₗ[R] B →ₗ[R] R) :
    P ⊗[R] Q →ₗ[R] A ⊗[R] B →ₗ[R] R :=
  (TensorProduct.dualDistrib R A B).comp (TensorProduct.map b c)

/-- Sanity: alpha has the stated scalar order on an elementary tensor. -/
example (b : P →ₗ[R] A →ₗ[R] R) (m : M) (p : P) (a : A) :
    pairingAlpha b M (m ⊗ₜ[R] p) a = b p a • m := by
  rfl

/-- Sanity: tensor pairing multiplies the two scalar evaluations. -/
example (b : P →ₗ[R] A →ₗ[R] R) (c : Q →ₗ[R] B →ₗ[R] R)
    (p : P) (q : Q) (a : A) (d : B) :
    tensorPairing b c (p ⊗ₜ[R] q) (a ⊗ₜ[R] d) = b p a * c q d := by
  rfl

end Pairings

section RationalParameters

variable {R C A M : Type u} [CommRing R]
variable [AddCommGroup C] [Module R C] [Coalgebra R C]
variable [Ring A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- Definition 2.8, PDF p.5, using the two explicit identities (2). -/
def IsRationalPairing (b : C →ₗ[R] A →ₗ[R] R) : Prop :=
  IsRationalSystem b ∧
    (∀ c a d, b c (a * d) = tensorPairing b b (Coalgebra.comul c) (a ⊗ₜ[R] d)) ∧
    ∀ c, b c 1 = Coalgebra.counit c

/-- Rational parameters for a module element, Definition 2.9, PDF p.6. -/
def IsRationalParameters (b : C →ₗ[R] A →ₗ[R] R) (m : M)
    {n : ℕ} (ms : Fin n → M) (cs : Fin n → C) : Prop :=
  ∀ a : A, a • m = ∑ i, b (cs i) a • ms i

/-- Sanity: the zero element has the empty family of rational parameters. -/
example (b : C →ₗ[R] A →ₗ[R] R) :
    IsRationalParameters b (0 : M) (n := 0) Fin.elim0 Fin.elim0 := by
  intro a
  simp

end RationalParameters

section Cofinite

variable (R A : Type u) [CommRing R] [Ring A] [Algebra R A]

/-- The R-module quotient by a LEFT ideal, section 4, PDF p.12. -/
abbrev LeftQuotient (I : Submodule A A) := A ⧸ I.restrictScalars R

/-- Cofiniteness always refers to finite generation over R, PDF p.12. -/
def IsCofiniteLeft (I : Submodule A A) : Prop := Module.Finite R (LeftQuotient R A I)

/-- Property P-left, Definition 4.1, PDF p.12. -/
def PropertyLeft : Prop :=
  ∀ I : Submodule A A, IsCofiniteLeft R A I →
    ∃ J : Submodule A A, J ≤ I ∧ Module.Finite R (LeftQuotient R A J) ∧
      Module.Projective R (LeftQuotient R A J)

/-- Property P-right, Remark 4.4, PDF p.13, expressed through the opposite algebra. -/
def PropertyRight : Prop := PropertyLeft R Aᵐᵒᵖ

/-- The two-sided property P, Remark 4.4, PDF p.13. -/
def PropertyTwoSided : Prop :=
  ∀ I : Ideal A, I.IsTwoSided → IsCofiniteLeft R A I →
    ∃ J : Ideal A, J.IsTwoSided ∧ J ≤ I ∧ Module.Finite R (LeftQuotient R A J) ∧
      Module.Projective R (LeftQuotient R A J)

/-- Finite dual as the sum of dual cofinite left quotients; PDF pp.7,13, equation (4).
Over a noetherian base the generators already form a submodule, so the span adds no forms. -/
def finiteDual : Submodule R (Module.Dual R A) :=
  Submodule.span R {f | ∃ I : Submodule A A, IsCofiniteLeft R A I ∧ ∀ a ∈ I, f a = 0}

/-- The canonical evaluation pairing for the finite dual, PDF p.7. -/
def finiteDualPairing : finiteDual R A →ₗ[R] A →ₗ[R] R := (finiteDual R A).subtype

/-- Sanity: every form from a cofinite quotient is in the finite dual. -/
example (f : Module.Dual R A) (I : Submodule A A)
    (hI : IsCofiniteLeft R A I) (hf : ∀ a ∈ I, f a = 0) : f ∈ finiteDual R A :=
  Submodule.subset_span ⟨I, hI, hf⟩

/-- Sanity: finite-dual evaluation is evaluation of the underlying linear form. -/
example (f : finiteDual R A) (a : A) : finiteDualPairing R A f a = f.val a := rfl

/-- The cofinite left ideals indexing the completion of Remark 4.5, PDF p.13. -/
abbrev CofiniteLeftIdeal := {I : Submodule A A // IsCofiniteLeft R A I}

/-- Quotient transition along an inclusion of left ideals; no quotient algebra is used. -/
def leftQuotientTransition (I J : Submodule A A) (h : I ≤ J) :
    LeftQuotient R A I →ₗ[R] LeftQuotient R A J :=
  (I.restrictScalars R).mapQ (J.restrictScalars R) LinearMap.id (by
    intro a ha
    exact h ha)

/-- The cofinite completion as compatible families of module quotient classes, PDF p.13. -/
def cofiniteCompletion : Submodule R (∀ I : CofiniteLeftIdeal R A, LeftQuotient R A I.val) where
  carrier := {x | ∀ (I J : CofiniteLeftIdeal R A) (h : I.val ≤ J.val),
    leftQuotientTransition R A I.val J.val h (x I) = x J}
  zero_mem' := by intro I J h; exact map_zero _
  add_mem' := by
    intro x y hx hy I J h
    change leftQuotientTransition R A I.val J.val h (x I + y I) = x J + y J
    rw [map_add, hx I J h, hy I J h]
  smul_mem' := by
    intro r x hx I J h
    change leftQuotientTransition R A I.val J.val h (r • x I) = r • x J
    rw [map_smul, hx I J h]

/-- The canonical finite-dual element defined by a functional on a cofinite quotient. -/
def cofiniteDualElement (I : CofiniteLeftIdeal R A)
    (f : Module.Dual R (LeftQuotient R A I.val)) : finiteDual R A :=
  ⟨f.comp (I.val.restrictScalars R).mkQ, Submodule.subset_span
    ⟨I.val, I.property, by
      intro a ha
      change f ((I.val.restrictScalars R).mkQ a) = 0
      have hz : (I.val.restrictScalars R).mkQ a = 0 :=
        (Submodule.Quotient.mk_eq_zero (I.val.restrictScalars R)).mpr ha
      rw [hz, map_zero]⟩⟩

/-- Sanity: quotient transition sends a representative to the same representative. -/
example (I J : Submodule A A) (h : I ≤ J) (a : A) :
    leftQuotientTransition R A I J h ((I.restrictScalars R).mkQ a) =
      (J.restrictScalars R).mkQ a := rfl

/-- Sanity: evaluation of a lifted quotient dual is quotient evaluation. -/
example (I : CofiniteLeftIdeal R A) (f : Module.Dual R (LeftQuotient R A I.val)) (a : A) :
    (cofiniteDualElement R A I f).val a = f ((I.val.restrictScalars R).mkQ a) := rfl

variable {R A}

end Cofinite

section ConvolutionPairing

variable {R C A : Type u} [CommRing R] [AddCommGroup C] [Module R C]
variable [Ring A] [Algebra R A]

/-- The evaluation pairing with the convolution-dual carrier, Corollary 2.16, PDF p.9. -/
def convolutionPairing : C →ₗ[R] WithConv (Module.Dual R C) →ₗ[R] R :=
  (WithConv.linearEquiv R (Module.Dual R C)).toLinearMap.flip

/-- The canonical finite-dual comultiplication and counit, PDF pp.7-9.
These are specifications on the coalgebra constructed in the conclusion, not assumptions. -/
def IsCanonicalFiniteDualCoalgebra (c : Coalgebra R (finiteDual R A)) : Prop :=
  letI : Coalgebra R (finiteDual R A) := c
  (∀ (f : finiteDual R A) (a b : A),
    tensorPairing (finiteDualPairing R A) (finiteDualPairing R A)
      (Coalgebra.comul f) (a ⊗ₜ[R] b) = f.val (a * b)) ∧
  ∀ f : finiteDual R A, Coalgebra.counit f = f.val 1

/-- Sanity: the convolution evaluation pairing evaluates the actual functional. -/
example (c : C) (l : WithConv (Module.Dual R C)) :
    convolutionPairing c l = l.ofConv c := rfl

end ConvolutionPairing

section TensorQuotients

variable {R M N : Type u} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The sum of the two tensor-inclusion images, Lemma 4.8, PDF p.14. -/
def tensorSubmoduleSum (I : Submodule R M) (J : Submodule R N) : Submodule R (M ⊗[R] N) :=
  LinearMap.range (TensorProduct.map I.subtype (LinearMap.id : N →ₗ[R] N)) ⊔
    LinearMap.range (TensorProduct.map (LinearMap.id : M →ₗ[R] M) J.subtype)

end TensorQuotients

section AlgebraOperations

variable {R A B : Type u} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/-- Finiteness and projectivity of the RIGHT module restricted along the given map, p.13. -/
def IsFiniteProjectiveRightExtension (f : A →ₐ[R] B) : Prop :=
  letI : Module Aᵐᵒᵖ Bᵐᵒᵖ := Module.compHom Bᵐᵒᵖ f.op.toRingHom
  Module.Finite Aᵐᵒᵖ Bᵐᵒᵖ ∧ Module.Projective Aᵐᵒᵖ Bᵐᵒᵖ

/-- Sanity: the induced right action is multiplication on the right by the actual inclusion. -/
example (f : A →ₐ[R] B) (a : A) (b : B) :
    letI : Module Aᵐᵒᵖ Bᵐᵒᵖ := Module.compHom Bᵐᵒᵖ f.op.toRingHom
    MulOpposite.unop (MulOpposite.op a • MulOpposite.op b) = b * f a := rfl

/-- The canonical finite-dual tensor map into the ordinary dual, PDF pp.14-15. -/
def finiteDualTensorMap : finiteDual R A ⊗[R] finiteDual R B →ₗ[R]
    Module.Dual R (A ⊗[R] B) :=
  (TensorProduct.dualDistrib R A B).comp
    (TensorProduct.map (finiteDual R A).subtype (finiteDual R B).subtype)

/-- Sanity: the canonical tensor map evaluates as the product of evaluations. -/
example (f : finiteDual R A) (g : finiteDual R B) (a : A) (b : B) :
    finiteDualTensorMap (f ⊗ₜ[R] g) (a ⊗ₜ[R] b) = f.val a * g.val b := rfl

end AlgebraOperations

section Laurent

variable {R : Type u} [CommRing R]

/-- Reversible polynomial, Definition 4.11, PDF p.15. Degree zero is permitted. -/
def IsReversiblePolynomial (q : Polynomial R) : Prop := q.Monic ∧ IsUnit (q.coeff 0)

/-- Reversible ideal, Definition 4.11, PDF p.15. -/
def IsReversibleIdeal (I : Ideal (LaurentPolynomial R)) : Prop :=
  ∃ q : Polynomial R, IsReversiblePolynomial q ∧ q.toLaurent ∈ I

/-- Sanity: the unit polynomial is reversible, including over the zero ring. -/
example : IsReversiblePolynomial (1 : Polynomial R) := by
  constructor
  · exact Polynomial.monic_one
  · simpa using (isUnit_one : IsUnit (1 : R))

end Laurent

end QAlgorithms.Papers.Independent.Gap48.P16


