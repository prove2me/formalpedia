-- Prove2me | Definitions.Def_CurveSymmetry_08_Differentials
-- name    : CurveSymmetry_08_Differentials
-- status  : Definition
-- author  : @carlok
-- created : 2026-10-07T12:19:21.025973+00:00
-- url     : https://prove2.me/theorems/221a6230-6021-4034-be6f-6dc16bad8fc3
-- title:
--   Kähler differentials of the double cover $w^2=h(t)$: the generator $dt$, local rings at points, transport
-- statement:
--   For a commutative ring $A$ over a ring $R$, let $\Omega_{A/R}$ be the module of Kähler differentials, with universal derivation $d:A\to\Omega_{A/R}$. Let $h\in\mathbb C[t]$ be such that $W^2-h$ is irreducible over $\mathbb C(t)$, let $L_h=\mathbb C(t)[W]/(W^2-h)$, a field, and $R_h=\mathbb C[t][W]/(W^2-h)$ its affine coordinate ring, and let $t\in L_h$ be the image of the variable.
--
--   The file defines one-element bases of the differentials of $\mathbb C[t]$, of $\mathbb C(t)$ and of $L_h$ over $\mathbb C$, each given by $dt$:
--   $$\Omega_{\mathbb C[t]/\mathbb C}=\mathbb C[t]\,dt,\qquad \Omega_{\mathbb C(t)/\mathbb C}=\mathbb C(t)\,dt,\qquad \Omega_{L_h/\mathbb C}=L_h\,dt.$$
--   It also defines:
--
--   1. The transport of bases: if $S\to T$ is a formally étale homomorphism of $R$-algebras and $\Omega_{S/R}$ has a one-element basis, the corresponding one-element basis of $\Omega_{T/R}$, obtained through the isomorphism $T\otimes_S\Omega_{S/R}\cong\Omega_{T/R}$.
--   2. The local ring of the double cover at a point: for $h$ squarefree and $(c,d)\in\mathbb C^2$ with $d^2=h(c)$, the localization $\mathcal O_{c,d}\subseteq L_h$ of $R_h$ at the kernel of the evaluation $t\mapsto c$, $W\mapsto d$.
--   3. The transport of differentials along an isomorphism of $R$-algebras $e:A\to B$: the additive map $\Omega_{A/R}\to\Omega_{B/R}$ with $a\,db\mapsto e(a)\,d(e(b))$.
--
--   The genus clause of Lemma 4 is computed in $\Omega_{L_h/\mathbb C}$ for $h=h_{m,\alpha}$, where every differential is a multiple $f\,dt$ and the holomorphic ones are those regular at every place. The local rings $\mathcal O_{c,d}$ are where regularity at the point places is tested, and the transport moves differentials through the chart at infinity and between isomorphic function fields, as used for Remark 5.
--
--   **Formalization Note**: Differentials are Mathlib's `KaehlerDifferential`, bases are indexed by a one-element type, and the hypotheses on $h$ are `Fact` instances. Besides definitions, the file keeps with proofs the facts they rely on: $\Omega_{L_h/\mathbb C}$ has dimension one over $L_h$; each $\mathcal O_{c,d}$ is a discrete valuation ring in which every element is congruent to a constant modulo the maximal ideal; it has a uniformizer $u$, and $du$ generates both $\Omega_{\mathcal O_{c,d}/\mathbb C}$ and $\Omega_{L_h/\mathbb C}$; and the differentials of two uniformizers differ by a unit of $\mathcal O_{c,d}$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), definitions of the formalization, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean modules QuadraticDifferentials, LocalDifferentials, PlaceDifferentials in https://github.com/carlok/curve-symmetry-lean/tree/d99bc17a1c397956c05d7417de50f9beed56580f/lean (C. Perassi)

-- Definitions, part 08 of 12, generated from curve-symmetry-lean by skeleton
-- subtraction: the source modules below, in dependency order, each in its own
-- section; only definitions, instances and the theorems they need are kept.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

-- lean/QuadraticDifferentials.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial TensorProduct

section BaseChange

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T] [Algebra.FormallyEtale S T] {ι : Type*} [Unique ι]

/-- A basis of `Ω[S⁄R]` transported along a formally étale `S → T`. -/
noncomputable def kaehlerBasisOfEtale (b : Module.Basis ι S Ω[S⁄R]) : Module.Basis ι T Ω[T⁄R] :=
  (b.baseChange T).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T)

end BaseChange

/-- `Ω[ℂ[t]⁄ℂ]` is free of rank one on `dt`. -/
noncomputable def polynomialKaehlerBasis : Module.Basis Unit ℂ[X] Ω[ℂ[X]⁄ℂ] :=
  (Module.Basis.singleton Unit ℂ[X]).map (KaehlerDifferential.polynomialEquiv ℂ).symm

/-- `ℂ(t)` is a localization of `ℂ[t]`, hence formally étale over it. -/
instance ratFunc_formallyEtale : Algebra.FormallyEtale ℂ[X] (RatFunc ℂ) :=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors ℂ[X])

/-- `Ω[ℂ(t)⁄ℂ]` is free of rank one on `dt`. -/
noncomputable def ratFuncKaehlerBasis : Module.Basis Unit (RatFunc ℂ) Ω[RatFunc ℂ⁄ℂ] :=
  kaehlerBasisOfEtale ℂ ℂ[X] (RatFunc ℂ) polynomialKaehlerBasis

section Quad

variable (h : ℂ[X]) [Fact (Irreducible (quadRat h))]

/-- The coordinate `t` of the base line, inside the quadratic extension. -/
noncomputable def quadT : QuadField h := algebraMap ℂ[X] (QuadField h) X

/-- Characteristic zero makes the quadratic extension separable, hence formally étale. -/
instance quadField_formallyEtale : Algebra.FormallyEtale (RatFunc ℂ) (QuadField h) :=
  Algebra.FormallyEtale.of_isSeparable _ _

/-- **G09a-1**: `Ω[K⁄ℂ]` is free of rank one on `dt`. -/
noncomputable def quadKaehlerBasis : Module.Basis Unit (QuadField h) Ω[QuadField h⁄ℂ] :=
  kaehlerBasisOfEtale ℂ (RatFunc ℂ) (QuadField h) ratFuncKaehlerBasis

theorem quad_kaehler_finrank : Module.finrank (QuadField h) Ω[QuadField h⁄ℂ] = 1 := by
  rw [Module.finrank_eq_card_basis (quadKaehlerBasis h), Fintype.card_unit]

/-- A differential that spans is nonzero, because the space is one-dimensional. -/
theorem quad_D_ne_zero_of_span {x : QuadField h}
    (hspan : Submodule.span (QuadField h) {KaehlerDifferential.D ℂ (QuadField h) x} = ⊤) :
    KaehlerDifferential.D ℂ (QuadField h) x ≠ 0 := by
  intro hzero
  rw [hzero, Submodule.span_singleton_eq_bot.mpr rfl] at hspan
  have : Subsingleton Ω[QuadField h⁄ℂ] := by
    constructor
    intro y z
    have hy : y ∈ (⊥ : Submodule (QuadField h) Ω[QuadField h⁄ℂ]) := by rw [hspan]; trivial
    have hz : z ∈ (⊥ : Submodule (QuadField h) Ω[QuadField h⁄ℂ]) := by rw [hspan]; trivial
    rw [Submodule.mem_bot] at hy hz
    rw [hy, hz]
  have hfin := quad_kaehler_finrank h
  rw [Module.finrank_eq_zero_of_subsingleton] at hfin
  exact zero_ne_one hfin

end Quad

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

end CurveSymmetry

end

-- lean/LocalDifferentials.lean
section

namespace CurveSymmetry

set_option autoImplicit false

section

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsLocalRing A]
  [Module.Finite A Ω[A⁄R]]

/-- With a residue field generated by `R` and a principal maximal ideal `(u)`,
the differentials `Ω[A⁄R]` are generated by `du`. -/
theorem localKaehler_span_eq_top {u : A}
    (hres : ∀ x : A, ∃ r : R, x - algebraMap R A r ∈ IsLocalRing.maximalIdeal A)
    (hu : IsLocalRing.maximalIdeal A = Ideal.span {u}) :
    Submodule.span A {KaehlerDifferential.D R A u} = ⊤ := by
  have humem : u ∈ IsLocalRing.maximalIdeal A := by
    rw [hu]; exact Ideal.mem_span_singleton_self u
  refine eq_top_iff.mpr (Submodule.le_of_le_smul_of_le_jacobson_bot
    (Module.finite_def.mp inferInstance) (IsLocalRing.maximalIdeal_le_jacobson ⊥) ?_)
  have hspan : (⊤ : Submodule A Ω[A⁄R]) =
      Submodule.span A (Set.range (KaehlerDifferential.D R A)) :=
    (KaehlerDifferential.span_range_derivation R A).symm
  conv_lhs => rw [hspan]
  rw [Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  obtain ⟨r, hr⟩ := hres x
  rw [hu, Ideal.mem_span_singleton] at hr
  obtain ⟨a, ha⟩ := hr
  have hx : x = algebraMap R A r + u * a := by
    have := sub_eq_iff_eq_add.mp ha
    rw [this]; ring
  refine Submodule.mem_sup.mpr ⟨a • KaehlerDifferential.D R A u,
    Submodule.mem_span_singleton.mpr ⟨a, rfl⟩,
    u • KaehlerDifferential.D R A a,
    Submodule.smul_mem_smul humem Submodule.mem_top, ?_⟩
  rw [hx, map_add, Derivation.map_algebraMap, zero_add,
    (KaehlerDifferential.D R A).leibniz u a, add_comm]

/-- Every differential is a multiple of `du`. -/
theorem localKaehler_exists_smul {u : A}
    (hres : ∀ x : A, ∃ r : R, x - algebraMap R A r ∈ IsLocalRing.maximalIdeal A)
    (hu : IsLocalRing.maximalIdeal A = Ideal.span {u}) :
    ∀ ω : Ω[A⁄R], ∃ c : A, ω = c • KaehlerDifferential.D R A u := by
  intro ω
  have hmem : ω ∈ Submodule.span A {KaehlerDifferential.D R A u} := by
    rw [localKaehler_span_eq_top hres hu]; trivial
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨c, hc.symm⟩

end

section Localization

variable {R S A : Type*} [Field R] [CommRing S] [Algebra R S] [CommRing A] [Algebra S A]
  [Algebra R A] [IsScalarTower R S A] [IsLocalRing A] (P : Ideal S) [P.IsPrime]
  [IsLocalization.AtPrime A P]

/-- A residue field generated by the base survives localization: if every element of `S`
differs from a constant by an element of `P`, the same holds in `A = S_P` for its maximal
ideal. Constants are inverted here, so the base is required to be a field. -/
theorem localization_residue (hres : ∀ s : S, ∃ r : R, s - algebraMap R S r ∈ P) (x : A) :
    ∃ r : R, x - algebraMap R A r ∈ IsLocalRing.maximalIdeal A := by
  obtain ⟨s, t, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl x
  obtain ⟨rs, hs⟩ := hres s
  obtain ⟨rt, ht⟩ := hres (t : S)
  have htne : rt ≠ 0 := by
    rintro rfl
    refine t.2 ?_
    simpa using ht
  refine ⟨rs * rt⁻¹, ?_⟩
  have key : IsLocalization.mk' A s t - algebraMap R A (rs * rt⁻¹) =
      IsLocalization.mk' A (s - algebraMap R S (rs * rt⁻¹) * t) t := by
    rw [IsLocalization.eq_mk'_iff_mul_eq, sub_mul, IsLocalization.mk'_spec, map_sub, map_mul,
      IsScalarTower.algebraMap_apply R S A]
    simp [map_mul, mul_assoc]
    rw [IsScalarTower.algebraMap_apply R S A rt⁻¹]
  rw [key]
  refine (IsLocalization.AtPrime.mk'_mem_maximal_iff A P _ t).mpr ?_
  have hzero : algebraMap R S rs - algebraMap R S (rs * rt⁻¹) * algebraMap R S rt = 0 := by
    rw [← map_mul, ← map_sub]
    have : rs - rs * rt⁻¹ * rt = 0 := by
      rw [mul_assoc, inv_mul_cancel₀ htne, mul_one, sub_self]
    rw [this, map_zero]
  have hsplit : s - algebraMap R S (rs * rt⁻¹) * (t : S) =
      (s - algebraMap R S rs) - algebraMap R S (rs * rt⁻¹) * ((t : S) - algebraMap R S rt) +
        (algebraMap R S rs - algebraMap R S (rs * rt⁻¹) * algebraMap R S rt) := by ring
  rw [hsplit, hzero, add_zero]
  exact P.sub_mem hs (Ideal.mul_mem_left _ _ ht)

end Localization

section BaseChangeSpan

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T] [Algebra.FormallyEtale S T]

/-- A single generator of `Ω[S⁄R]` stays a generator after a formally étale base change. -/
theorem kaehler_span_map_eq_top {v : Ω[S⁄R]} (hv : Submodule.span S {v} = ⊤) :
    Submodule.span T {KaehlerDifferential.map R R S T v} = ⊤ := by
  rw [eq_top_iff]
  rintro ω -
  obtain ⟨x, rfl⟩ := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).surjective ω
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | tmul a m =>
    have hm : m ∈ Submodule.span S {v} := by rw [hv]; trivial
    obtain ⟨cc, rfl⟩ := Submodule.mem_span_singleton.mp hm
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul, map_smul,
      ← IsScalarTower.algebraMap_smul T cc (KaehlerDifferential.map R R S T v), smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

end BaseChangeSpan

section Transport

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Differentials transported along an isomorphism of `R`-algebras. -/
noncomputable def kaehlerTransport (e : A ≃ₐ[R] B) : Ω[A⁄R] →+ Ω[B⁄R] :=
  letI : Algebra A B := e.toRingEquiv.toRingHom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (e.commutes r).symm
  (KaehlerDifferential.map R R A B).toAddMonoidHom

@[simp] lemma kaehlerTransport_D (e : A ≃ₐ[R] B) (a : A) :
    kaehlerTransport e (KaehlerDifferential.D R A a) = KaehlerDifferential.D R B (e a) := by
  let : Algebra A B := e.toRingEquiv.toRingHom.toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (e.commutes r).symm
  exact KaehlerDifferential.map_D R R A B a

lemma kaehlerTransport_smul (e : A ≃ₐ[R] B) (a : A) (ω : Ω[A⁄R]) :
    kaehlerTransport e (a • ω) = e a • kaehlerTransport e ω := by
  let : Algebra A B := e.toRingEquiv.toRingHom.toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (e.commutes r).symm
  show KaehlerDifferential.map R R A B (a • ω) = _
  rw [map_smul, ← IsScalarTower.algebraMap_smul B a]
  rfl

/-- The transport is linear over the common base. -/
lemma kaehlerTransport_smul_base (e : A ≃ₐ[R] B) (r : R) (ω : Ω[A⁄R]) :
    kaehlerTransport e (r • ω) = r • kaehlerTransport e ω := by
  rw [← algebraMap_smul A r ω, kaehlerTransport_smul, AlgEquiv.commutes, algebraMap_smul]

end Transport

end CurveSymmetry

end

-- lean/PlaceDifferentials.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial

section

variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]

instance quadRing_scalarTower_complex : IsScalarTower ℂ (QuadRing h) (QuadField h) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply ℂ ℂ[X] (QuadField h),
      IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h) (QuadField h),
      IsScalarTower.algebraMap_apply ℂ ℂ[X] (QuadRing h)]

variable (c d : ℂ) (hd : d ^ 2 = h.eval c)

/-- The local ring of the double cover at the point place `(c, d)`. -/
noncomputable abbrev quadLocalRing : Subalgebra (QuadRing h) (QuadField h) :=
  primeLocalization (QuadField h) (RingHom.ker (quadEval h c d hd))

noncomputable instance quadLocalRing_essFiniteType_quadRing :
    Algebra.EssFiniteType (QuadRing h) (quadLocalRing h c d hd) :=
  Algebra.EssFiniteType.of_isLocalization (S := (quadLocalRing h c d hd))
    (RingHom.ker (quadEval h c d hd)).primeCompl

noncomputable instance quadLocalRing_essFiniteType :
    Algebra.EssFiniteType ℂ (quadLocalRing h c d hd) :=
  Algebra.EssFiniteType.comp ℂ (QuadRing h) (quadLocalRing h c d hd)

instance quadLocalRing_dvr : IsDiscreteValuationRing (quadLocalRing h c d hd) :=
  primeLocalization_dvr _ (quadEval_ker_ne_bot h c d hd)

omit [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))] in
/-- Constants of `ℂ` represent every residue of the coordinate ring at the point. -/
theorem quadRing_residue (s : QuadRing h) :
    ∃ r : ℂ, s - algebraMap ℂ (QuadRing h) r ∈ RingHom.ker (quadEval h c d hd) := by
  refine ⟨quadEval h c d hd s, ?_⟩
  have hconst : quadEval h c d hd (algebraMap ℂ (QuadRing h) (quadEval h c d hd s)) =
      quadEval h c d hd s := by
    rw [IsScalarTower.algebraMap_apply ℂ ℂ[X] (QuadRing h), ← Polynomial.C_eq_algebraMap,
      show (algebraMap ℂ[X] (QuadRing h)) = AdjoinRoot.of (quadPoly h) from rfl,
      quadEval_of, eval_C]
  rw [RingHom.mem_ker, map_sub, hconst, sub_self]

/-- The residue field of the local ring at a point place is generated by the constants. -/
theorem quadLocal_residue (x : quadLocalRing h c d hd) :
    ∃ r : ℂ, x - algebraMap ℂ (quadLocalRing h c d hd) r ∈
      IsLocalRing.maximalIdeal (quadLocalRing h c d hd) :=
  localization_residue (RingHom.ker (quadEval h c d hd)) (quadRing_residue h c d hd) x

/-- **G09a-2b**: at a point place, the differentials of the local ring are generated by
`du` for any generator `u` of the maximal ideal. -/
theorem quadLocal_kaehler_span_eq_top {u : quadLocalRing h c d hd}
    (hu : IsLocalRing.maximalIdeal (quadLocalRing h c d hd) = Ideal.span {u}) :
    Submodule.span (quadLocalRing h c d hd)
      {KaehlerDifferential.D ℂ (quadLocalRing h c d hd) u} = ⊤ :=
  localKaehler_span_eq_top (quadLocal_residue h c d hd) hu

/-- A uniformizer exists at every point place, and its differential generates. -/
theorem quadLocal_exists_uniformizer :
    ∃ u : quadLocalRing h c d hd,
      IsLocalRing.maximalIdeal (quadLocalRing h c d hd) = Ideal.span {u} ∧
        Submodule.span (quadLocalRing h c d hd)
          {KaehlerDifferential.D ℂ (quadLocalRing h c d hd) u} = ⊤ := by
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.exists_irreducible (quadLocalRing h c d hd)
  have hspan := (IsDiscreteValuationRing.irreducible_iff_uniformizer u).mp hu
  exact ⟨u, hspan, quadLocal_kaehler_span_eq_top h c d hd hspan⟩

/-- Pushing a differential of the local ring into the function field. -/
lemma quadLocal_map_D (x : quadLocalRing h c d hd) :
    KaehlerDifferential.map ℂ ℂ (quadLocalRing h c d hd) (QuadField h)
        (KaehlerDifferential.D ℂ (quadLocalRing h c d hd) x) =
      KaehlerDifferential.D ℂ (QuadField h) (x : QuadField h) :=
  KaehlerDifferential.map_D ℂ ℂ (quadLocalRing h c d hd) (QuadField h) x

instance quadLocalRing_formallyEtale :
    Algebra.FormallyEtale (quadLocalRing h c d hd) (QuadField h) :=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (quadLocalRing h c d hd))

/-- The differential of a uniformizer spans the differentials of the function field. -/
theorem quadLocal_D_uniformizer_spans {u : quadLocalRing h c d hd}
    (hu : IsLocalRing.maximalIdeal (quadLocalRing h c d hd) = Ideal.span {u}) :
    Submodule.span (QuadField h)
      {KaehlerDifferential.D ℂ (QuadField h) (u : QuadField h)} = ⊤ := by
  have hmap := kaehler_span_map_eq_top ℂ (quadLocalRing h c d hd) (QuadField h)
    (quadLocal_kaehler_span_eq_top h c d hd hu)
  rwa [quadLocal_map_D] at hmap

/-- The differential of a uniformizer is not zero. -/
theorem quadLocal_D_uniformizer_ne_zero {u : quadLocalRing h c d hd}
    (hu : IsLocalRing.maximalIdeal (quadLocalRing h c d hd) = Ideal.span {u}) :
    KaehlerDifferential.D ℂ (QuadField h) (u : QuadField h) ≠ 0 :=
  quad_D_ne_zero_of_span h (quadLocal_D_uniformizer_spans h c d hd hu)

/-- Every differential of the function field is a multiple of `du`. -/
theorem quadLocal_exists_coeff {u : quadLocalRing h c d hd}
    (hu : IsLocalRing.maximalIdeal (quadLocalRing h c d hd) = Ideal.span {u})
    (ω : Ω[QuadField h⁄ℂ]) :
    ∃ f : QuadField h, ω = f • KaehlerDifferential.D ℂ (QuadField h) (u : QuadField h) := by
  have hmem : ω ∈ Submodule.span (QuadField h)
      {KaehlerDifferential.D ℂ (QuadField h) (u : QuadField h)} := by
    rw [quadLocal_D_uniformizer_spans h c d hd hu]; trivial
  obtain ⟨f, hf⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨f, hf.symm⟩

/-- Two uniformizers at the same place have differentials that differ by a unit of the
local ring. This is what makes an order of a differential at the place independent of the
uniformizer used to read it off. -/
theorem quadLocal_D_uniformizer_unit {u u' : quadLocalRing h c d hd}
    (hu : IsLocalRing.maximalIdeal (quadLocalRing h c d hd) = Ideal.span {u})
    (hu' : IsLocalRing.maximalIdeal (quadLocalRing h c d hd) = Ideal.span {u'}) :
    ∃ e : QuadField h, e ∈ quadLocalRing h c d hd ∧ e⁻¹ ∈ quadLocalRing h c d hd ∧
      KaehlerDifferential.D ℂ (QuadField h) (u' : QuadField h) =
        e • KaehlerDifferential.D ℂ (QuadField h) (u : QuadField h) := by
  obtain ⟨a, ha⟩ := localKaehler_exists_smul (quadLocal_residue h c d hd) hu
    (KaehlerDifferential.D ℂ (quadLocalRing h c d hd) u')
  obtain ⟨b, hb⟩ := localKaehler_exists_smul (quadLocal_residue h c d hd) hu'
    (KaehlerDifferential.D ℂ (quadLocalRing h c d hd) u)
  have hpush : ∀ (x y : quadLocalRing h c d hd) (z : quadLocalRing h c d hd),
      KaehlerDifferential.D ℂ (quadLocalRing h c d hd) x =
          z • KaehlerDifferential.D ℂ (quadLocalRing h c d hd) y →
        KaehlerDifferential.D ℂ (QuadField h) (x : QuadField h) =
          (z : QuadField h) • KaehlerDifferential.D ℂ (QuadField h) (y : QuadField h) := by
    intro x y z hxyz
    have := congrArg (KaehlerDifferential.map ℂ ℂ (quadLocalRing h c d hd) (QuadField h)) hxyz
    rw [quadLocal_map_D, map_smul, quadLocal_map_D,
      ← IsScalarTower.algebraMap_smul (QuadField h) z] at this
    exact this
  have ha' := hpush u' u a ha
  have hb' := hpush u u' b hb
  have hdu := quadLocal_D_uniformizer_ne_zero h c d hd hu
  have hone : (b : QuadField h) * (a : QuadField h) = 1 := by
    have hcomb : KaehlerDifferential.D ℂ (QuadField h) (u : QuadField h) =
        ((b : QuadField h) * (a : QuadField h)) •
          KaehlerDifferential.D ℂ (QuadField h) (u : QuadField h) := by
      conv_lhs => rw [hb', ha']
      rw [smul_smul]
    have hsub : (((b : QuadField h) * (a : QuadField h)) - 1) •
        KaehlerDifferential.D ℂ (QuadField h) (u : QuadField h) = 0 := by
      rw [sub_smul, one_smul, ← hcomb, sub_self]
    rcases smul_eq_zero.mp hsub with hzero | hzero
    · exact sub_eq_zero.mp hzero
    · exact absurd hzero hdu
  refine ⟨(a : QuadField h), a.2, ?_, ha'⟩
  have : (a : QuadField h)⁻¹ = (b : QuadField h) := inv_eq_of_mul_eq_one_left hone
  rw [this]
  exact b.2

/-- The coefficient read off from two uniformizers differs by a unit of the local ring. -/
theorem quadLocal_coeff_unit {u u' : quadLocalRing h c d hd}
    (hu : IsLocalRing.maximalIdeal (quadLocalRing h c d hd) = Ideal.span {u})
    (hu' : IsLocalRing.maximalIdeal (quadLocalRing h c d hd) = Ideal.span {u'})
    {ω : Ω[QuadField h⁄ℂ]} {f f' : QuadField h}
    (hf : ω = f • KaehlerDifferential.D ℂ (QuadField h) (u : QuadField h))
    (hf' : ω = f' • KaehlerDifferential.D ℂ (QuadField h) (u' : QuadField h)) :
    ∃ e : QuadField h, e ∈ quadLocalRing h c d hd ∧ e⁻¹ ∈ quadLocalRing h c d hd ∧
      f = e * f' := by
  obtain ⟨e, he, he', hD⟩ := quadLocal_D_uniformizer_unit h c d hd hu hu'
  refine ⟨e, he, he', ?_⟩
  have hdu := quadLocal_D_uniformizer_ne_zero h c d hd hu
  have hω : ω = (e * f') • KaehlerDifferential.D ℂ (QuadField h) (u : QuadField h) := by
    rw [hf', hD, smul_smul, mul_comm f' e]
  have : (f - e * f') • KaehlerDifferential.D ℂ (QuadField h) (u : QuadField h) = 0 := by
    rw [sub_smul, ← hf, ← hω, sub_self]
  rcases smul_eq_zero.mp this with hzero | hzero
  · exact sub_eq_zero.mp hzero
  · exact absurd hzero hdu

end

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

end CurveSymmetry

end


