-- Prove2me | Definitions.Def_ProEtale_Algebra_StalkAlgebraic
-- name    : ProEtale_Algebra_StalkAlgebraic
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:56:19.818746+00:00
-- url     : https://prove2.me/theorems/6f92d759-7e2c-4a47-88d8-33ad41340c2c
-- title:
--   A prime lying over a maximal ideal with algebraic residue field extension is maximal
-- statement:
--   Principal results:
--
--   1. Let $k \to R \to K$ be a tower, with $k$ and $K$ fields, $R$ a commutative semiring, $R \to K$ injective and $K$ algebraic over $k$. Then $R$ is a field.
--   2. Let $A \to B$ be a homomorphism of commutative rings, $\mathfrak m \subset A$ a maximal ideal and $\mathfrak q \subset B$ a prime lying over $\mathfrak m$. Assume the residue field $\kappa(\mathfrak q)$ is algebraic over $\kappa(\mathfrak m)$. Then
--   $$\mathfrak q \text{ is a maximal ideal of } B.$$
--   This is Stacks 00GA.
--
--   The second statement shows that, for maps whose residue field extensions are algebraic (for example maps identifying local rings, or ind-étale maps), closed points map to and come from closed points. It is used to control closed points of spectra in the w-local theory.
--
--   **Formalization Note** The declarations are `IsField.of_isScalarTower_of_isAlgebraic`, with hypotheses `[IsScalarTower k R K] [FaithfulSMul R K] [Algebra.IsAlgebraic k K]`, and `Ideal.IsMaximal.of_isAlgebraic`. The latter takes as instance arguments `[q.LiesOver m]`, an algebra structure `Localization.AtPrime m → Localization.AtPrime q` with `[Localization.AtPrime.IsLiesOverAlgebra m q]`, and `[Algebra.IsAlgebraic m.ResidueField q.ResidueField]`. This residue-field algebra structure is the one induced by that local map.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014); cited in the code: Stacks Project, Tag 00GA. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/StalkAlgebraic.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.Topology.JacobsonSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-- `IsScalarTower` version of `Subalgebra.isField_of_algebraic`. -/
lemma IsField.of_isScalarTower_of_isAlgebraic (k R K : Type*) [Field k] [Field K]
    [CommSemiring R] [Algebra k R] [Algebra R K] [Algebra k K] [IsScalarTower k R K]
    [FaithfulSMul R K] [Algebra.IsAlgebraic k K] : IsField R :=
  AlgEquiv.ofInjective (IsScalarTower.toAlgHom k R K)
    (FaithfulSMul.algebraMap_injective R K) |>.isField <| Subalgebra.isField_of_algebraic _

/-- If `q` lies over a maximal ideal `m` and the residue field extension is algebraic, `q`
is maximal. -/
@[stacks 00GA]
lemma Ideal.IsMaximal.of_isAlgebraic {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (m : Ideal A) [m.IsMaximal] (q : Ideal B) [Ideal.IsPrime q]
    [q.LiesOver m]
    [Algebra (Localization.AtPrime m) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra m q]
    [Algebra.IsAlgebraic m.ResidueField q.ResidueField] : q.IsMaximal := by
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  letI := Ideal.Quotient.field m
  let lf : m.ResidueField →+* B ⧸ q :=
    IsLocalization.lift (M := nonZeroDivisors _ ) (g := algebraMap (A ⧸ m) (B ⧸ q))
      fun y ↦ (isUnit_of_mem_nonZeroDivisors y.2).map _
  algebraize [lf]
  have h : IsScalarTower m.ResidueField (B ⧸ q) q.ResidueField := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext (nonZeroDivisors (A ⧸ m))
    rw [← RingHom.cancel_right Ideal.Quotient.mk_surjective]
    ext
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.algebraMap_toAlgebra lf, lf,
      IsLocalization.lift_eq]
    rw [Ideal.algebraMap_quotient_residueField_mk, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply _ B]
    rfl
  have h : FaithfulSMul (B ⧸ q) q.ResidueField := by
    rw [faithfulSMul_iff_algebraMap_injective]
    apply IsFractionRing.injective
  exact .of_isScalarTower_of_isAlgebraic m.ResidueField (B ⧸ q) q.ResidueField


