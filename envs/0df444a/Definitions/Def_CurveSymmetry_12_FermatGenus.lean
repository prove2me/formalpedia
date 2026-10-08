-- Prove2me | Definitions.Def_CurveSymmetry_12_FermatGenus
-- name    : CurveSymmetry_12_FermatGenus
-- status  : Definition
-- author  : @carlok
-- created : 2026-10-07T12:28:14.581719+00:00
-- url     : https://prove2.me/theorems/f6f7eede-b88e-4052-b6c3-727af9d233e5
-- title:
--   Places of Kummer covers, the quartic $X^4+Y^4=2$ at infinity, and the automorphism $y\mapsto iy$
-- statement:
--   Let $n\ge1$ and let $f\in\mathbb C[x]$ be squarefree of positive degree, with $R_{n,f}=\mathbb C[x][Y]/(Y^n-f)$, $K_{n,f}=\mathbb C(x)[Y]/(Y^n-f)$, and $\mathrm{ev}_{a,b}:R_{n,f}\to\mathbb C$ the evaluation at a point $(a,b)$ with $b^n=f(a)$. Let $K_4=K_{4,\,2-x^4}$ be the function field of $y^4=2-x^4$, the Kummer form of the curve $X^4+Y^4=2$, and $K_4'=K_{4,\,2s^4-1}$ that of $r^4=2s^4-1$, with coordinates $s,r$.
--
--   The central construction is the chart at infinity of the quartic, the isomorphism of $\mathbb C$-algebras
--   $$K_4\longrightarrow K_4',\qquad x\longmapsto\frac1s,\qquad y\longmapsto\frac rs,$$
--   which is well defined because $(r/s)^4=(2s^4-1)/s^4=2-(1/s)^4$. The file defines it together with:
--
--   1. The local ring $\mathcal O_{a,b}\subseteq K_{n,f}$ of the Kummer cover at $(a,b)$, the localization of $R_{n,f}$ at $\ker\mathrm{ev}_{a,b}$, and the place of $K_{n,f}$ at $(a,b)$, the same ring viewed as a valuation subring.
--   2. The polynomial $2s^4-1$ and the coordinates $s,r$ of $K_4'$.
--   3. A fourth root $\zeta$ of $-1$, chosen once and for all, the local ring of $K_4'$ at $(0,\zeta)$, and the place of $K_4$ over $x=\infty$ obtained as the preimage of the place of $K_4'$ at $(0,\zeta)$ under the chart isomorphism.
--   4. The element $i\in K_4$ and the automorphism $\sigma$ of $K_4$ that fixes $\mathbb C(x)$ and sends $y$ to $iy$.
--   5. The complex subspace of the $F\in K_4$ for which $F\,dx$ is holomorphic, that is, regular at every place, and the elements $p(x)\,y^j/y^3$ for $p\in\mathbb C[x]$ and $j\in\mathbb N$.
--
--   These are the ingredients of the genus-three computation for $X^4+Y^4=2$ in Remark 5: the places at the points $(a,b)$ and the place over $x=\infty$ are where regularity of differentials is tested, while $\sigma$, the space of coefficients $F$ and the pieces $p(x)\,y^j/y^3$ organize the holomorphic differentials $F\,dx$.
--
--   **Formalization Note**: $\zeta$ is chosen by algebraic closedness, so only one of the places over $x=\infty$ (they lie at the points $(0,\zeta)$ with $\zeta^4=-1$) is named. Instances record that, for $n\ne0$ and $f$ squarefree of positive degree, $R_{n,f}$ is a Dedekind domain with fraction field $K_{n,f}$ and each $\mathcal O_{a,b}$ is a discrete valuation ring; the file also proves that $2-x^4$ and $2s^4-1$ are squarefree of degree four.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), definitions of the formalization, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean modules KummerPlaces, FermatInfinity, FermatSplit, PaperRemarks in https://github.com/carlok/curve-symmetry-lean/tree/d99bc17a1c397956c05d7417de50f9beed56580f/lean (C. Perassi)

-- Definitions, part 12 of 12, generated from curve-symmetry-lean by skeleton
-- subtraction: the source modules below, in dependency order, each in its own
-- section; only definitions, instances and the theorems they need are kept.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Definitions.Def_CurveSymmetry_10_KummerField
import Definitions.Def_CurveSymmetry_11_KummerLocal
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
import Mathlib.LinearAlgebra.Dimension.Finrank
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
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

-- lean/KummerPlaces.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial

variable {n : ℕ} [NeZero n] {f : ℂ[X]} [Fact (Squarefree f)] [Fact (0 < f.natDegree)]

instance kummerRing_isDedekindDomain' : IsDedekindDomain (KummerRing n f) :=
  kummerRing_isDedekindDomain

instance kummerRing_isFractionRing' : IsFractionRing (KummerRing n f) (KummerField n f) :=
  kummerRing_isFractionRing n f (NeZero.ne n)

instance kummerRing_scalarTower_poly : IsScalarTower ℂ[X] (KummerRing n f) (KummerField n f) :=
  IsScalarTower.of_algebraMap_eq fun p => by
    rw [kummerRing_algebraMap_apply, AlgHom.commutes]

instance kummerField_charZero : CharZero (KummerField n f) :=
  charZero_of_injective_algebraMap (algebraMap ℂ (KummerField n f)).injective

section Local

variable (a b : ℂ) (hb : b ^ n = f.eval a)

/-- The local ring of the Kummer cover at the point `(a, b)`, inside the function field. -/
noncomputable abbrev kummerLocalRing : Subalgebra (KummerRing n f) (KummerField n f) :=
  primeLocalization (KummerField n f) (RingHom.ker (kummerEval n f a b hb))

/-- The place of the Kummer field at the point `(a, b)`. -/
noncomputable def kummerPlace : ValuationSubring (KummerField n f) :=
  primeValuationSubring (KummerField n f) (RingHom.ker (kummerEval n f a b hb))
    (kummerEval_ker_ne_bot a b hb)

instance kummerLocalRing_dvr : IsDiscreteValuationRing (kummerLocalRing a b hb) :=
  primeLocalization_dvr _ (kummerEval_ker_ne_bot a b hb)

noncomputable instance kummerLocalRing_essFiniteType_ring :
    Algebra.EssFiniteType (KummerRing n f) (kummerLocalRing a b hb) :=
  Algebra.EssFiniteType.of_isLocalization (S := kummerLocalRing a b hb)
    (RingHom.ker (kummerEval n f a b hb)).primeCompl

noncomputable instance kummerLocalRing_essFiniteType :
    Algebra.EssFiniteType ℂ (kummerLocalRing a b hb) :=
  Algebra.EssFiniteType.comp ℂ (KummerRing n f) (kummerLocalRing a b hb)

end Local

end CurveSymmetry

end

-- lean/FermatInfinity.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial

/-- `2s⁴ − 1`: the quartic's equation in the chart at infinity is `r⁴ = 2s⁴ − 1`. -/
noncomputable def fermatDual : ℂ[X] := C 2 * X ^ 4 - 1

lemma fermatQuartic_squarefree : Squarefree fermatQuartic := by
  have hsep : (X ^ 4 - C (2 : ℂ)).Separable :=
    separable_X_pow_sub_C _ (by norm_num) (by norm_num)
  have hassoc : Associated (X ^ 4 - C (2 : ℂ)) fermatQuartic :=
    ⟨-1, by simp only [Units.val_neg, Units.val_one, fermatQuartic]; ring⟩
  exact hassoc.squarefree_iff.mp hsep.squarefree

lemma fermatDual_squarefree : Squarefree fermatDual := by
  have hsep : (X ^ 4 - C (1 / 2 : ℂ)).Separable :=
    separable_X_pow_sub_C _ (by norm_num) (by norm_num)
  have h2 : IsUnit (C (2 : ℂ)) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr two_ne_zero)
  have hassoc : Associated (X ^ 4 - C (1 / 2 : ℂ)) fermatDual := by
    refine ⟨h2.unit, ?_⟩
    rw [IsUnit.unit_spec, fermatDual, sub_mul, ← C_mul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, C_1]
    ring
  exact hassoc.squarefree_iff.mp hsep.squarefree

lemma fermatQuartic_natDegree : fermatQuartic.natDegree = 4 := by
  unfold fermatQuartic
  compute_degree!

lemma fermatDual_natDegree : fermatDual.natDegree = 4 := by
  unfold fermatDual
  compute_degree!

instance fermatQuartic_squarefree_fact : Fact (Squarefree fermatQuartic) :=
  ⟨fermatQuartic_squarefree⟩

instance fermatQuartic_natDegree_fact : Fact (0 < fermatQuartic.natDegree) :=
  ⟨by rw [fermatQuartic_natDegree]; norm_num⟩

instance fermatDual_squarefree_fact : Fact (Squarefree fermatDual) :=
  ⟨fermatDual_squarefree⟩

instance fermatDual_natDegree_fact : Fact (0 < fermatDual.natDegree) :=
  ⟨by rw [fermatDual_natDegree]; norm_num⟩

local notation "K₄" => KummerField 4 fermatQuartic

local notation "K₄'" => KummerField 4 fermatDual

/-- The chart coordinate `s` of `K'`. -/
noncomputable abbrev dualS : K₄' := kummerX 4 fermatDual

/-- The chart coordinate `r` of `K'`. -/
noncomputable abbrev dualR : K₄' := AdjoinRoot.root (kummerRat 4 fermatDual)

lemma dualS_eq : dualS = algebraMap (RatFunc ℂ) K₄' RatFunc.X := kummerX_eq 4 fermatDual

lemma dualS_ne_zero : dualS ≠ 0 := by
  rw [dualS_eq]
  exact (map_ne_zero_iff _ (algebraMap (RatFunc ℂ) K₄').injective).mpr RatFunc.X_ne_zero

lemma dualR_pow : dualR ^ 4 = 2 * dualS ^ 4 - 1 := by
  rw [dualR, kummerRoot_pow]
  show algebraMap ℂ[X] K₄' (C 2 * X ^ 4 - 1) = _
  rw [map_sub, map_mul, map_pow, map_one, C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply ℂ ℂ[X] K₄', map_ofNat]
  rfl

/-- `f(1/s) = 2 − 1/s⁴` in `ℂ(s)`. -/
lemma fermatQuartic_ratInv :
    ratInv (algebraMap ℂ[X] (RatFunc ℂ) fermatQuartic) =
      2 - ((RatFunc.X : RatFunc ℂ)⁻¹) ^ 4 := by
  rw [ratInv_algebraMap]
  show aeval (RatFunc.X : RatFunc ℂ)⁻¹ (C 2 - X ^ 4) = _
  rw [map_sub, aeval_C, map_pow, aeval_X, map_ofNat]

/-- The chart map `x ↦ 1/s`, `y ↦ r/s`. -/
noncomputable def fermatInfinityMap : K₄ →+* K₄' :=
  AdjoinRoot.lift ((algebraMap (RatFunc ℂ) K₄').comp ratInv.toRingHom)
    (dualR * dualS⁻¹) (by
      have hs := dualS_ne_zero
      show eval₂ _ _ (X ^ 4 - C (algebraMap ℂ[X] (RatFunc ℂ) fermatQuartic)) = 0
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, RingHom.comp_apply,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, fermatQuartic_ratInv, map_sub, map_pow,
        map_inv₀, ← dualS_eq, map_ofNat, mul_pow, dualR_pow]
      field_simp
      ring)

lemma fermatInfinityMap_of (q : RatFunc ℂ) :
    fermatInfinityMap (algebraMap (RatFunc ℂ) K₄ q) = algebraMap (RatFunc ℂ) K₄' (ratInv q) :=
  AdjoinRoot.lift_of _

lemma fermatInfinityMap_root :
    fermatInfinityMap (AdjoinRoot.root (kummerRat 4 fermatQuartic)) = dualR * dualS⁻¹ :=
  AdjoinRoot.lift_root _

lemma fermatInfinityMap_surjective : Function.Surjective fermatInfinityMap := by
  let φ := fermatInfinityMap
  have hadd {a b : K₄'} (ha : a ∈ Set.range φ) (hb : b ∈ Set.range φ) : a + b ∈ Set.range φ := by
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x + y, map_add φ x y⟩
  have hmul {a b : K₄'} (ha : a ∈ Set.range φ) (hb : b ∈ Set.range φ) : a * b ∈ Set.range φ := by
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x * y, map_mul φ x y⟩
  have hof (q : RatFunc ℂ) : algebraMap (RatFunc ℂ) K₄' q ∈ Set.range φ := by
    obtain ⟨p, rfl⟩ := ratInv_surjective q
    exact ⟨algebraMap (RatFunc ℂ) K₄ p, fermatInfinityMap_of p⟩
  have hroot : dualR ∈ Set.range φ := by
    have he : dualR = φ (AdjoinRoot.root (kummerRat 4 fermatQuartic)) * dualS := by
      rw [fermatInfinityMap_root, mul_assoc, inv_mul_cancel₀ dualS_ne_zero, mul_one]
    rw [he, dualS_eq]
    exact hmul ⟨_, rfl⟩ (hof _)
  intro z
  induction z using AdjoinRoot.induction_on with
  | ih p =>
    induction p using Polynomial.induction_on with
    | C a =>
        rw [AdjoinRoot.mk_C]
        exact hof a
    | add p q hp hq =>
        rw [map_add]
        exact hadd hp hq
    | monomial k a hk =>
        rw [pow_succ, ← mul_assoc, map_mul, AdjoinRoot.mk_X]
        exact hmul hk hroot

lemma fermatInfinityMap_bijective : Function.Bijective fermatInfinityMap :=
  ⟨fermatInfinityMap.injective, fermatInfinityMap_surjective⟩

/-- **R01e-1**: the chart isomorphism `x ↦ 1/s`, `y ↦ r/s`, as `ℂ`-algebras. -/
noncomputable def fermatInfinityAlgEquiv : K₄ ≃ₐ[ℂ] K₄' :=
  AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofBijective fermatInfinityMap fermatInfinityMap_bijective)
    fun z => by
      rw [RingEquiv.ofBijective_apply, IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) K₄,
        fermatInfinityMap_of, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

@[simp] lemma fermatInfinityAlgEquiv_apply (z : K₄) :
    fermatInfinityAlgEquiv z = fermatInfinityMap z :=
  rfl

/-- A fourth root of `−1`: the four places over `s = 0` are the points `(0, ζ)`, `ζ⁴ = −1`. -/
noncomputable def fermatZeta : ℂ :=
  (IsAlgClosed.exists_pow_nat_eq (-1 : ℂ) (by norm_num : 0 < 4)).choose

lemma fermatZeta_pow : fermatZeta ^ 4 = fermatDual.eval 0 := by
  rw [fermatZeta, (IsAlgClosed.exists_pow_nat_eq (-1 : ℂ) (by norm_num : 0 < 4)).choose_spec]
  simp [fermatDual]

/-- The local ring of `K'` at `(0, ζ)`. -/
noncomputable abbrev dualLocalRing : Subalgebra (KummerRing 4 fermatDual) K₄' :=
  kummerLocalRing 0 fermatZeta fermatZeta_pow

/-- **R01e-1**: a place of the quartic's function field over `x = ∞`. -/
noncomputable def fermatInfinityPlace : ValuationSubring K₄ :=
  (kummerPlace (n := 4) (f := fermatDual) 0 fermatZeta fermatZeta_pow).comap
    (fermatInfinityAlgEquiv : K₄ →+* K₄')

end CurveSymmetry

end

-- lean/FermatSplit.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial

section Reduction

end Reduction

section Quartic

local notation "K₄" => KummerField 4 fermatQuartic

/-- `i` in the quartic's function field. -/
noncomputable abbrev quarticI : K₄ := algebraMap ℂ K₄ Complex.I

lemma quarticI_sq : quarticI ^ 2 = -1 := by
  rw [quarticI, ← map_pow, Complex.I_sq, map_neg, map_one]

lemma quarticI_pow_four : quarticI ^ 4 = 1 := by
  linear_combination (quarticI ^ 2 - 1) * quarticI_sq

/-- `y ↦ i·y` over `ℂ(x)`: well defined because `(i·y)⁴ = y⁴ = f(x)`. -/
noncomputable def quarticRotHom : K₄ →ₐ[RatFunc ℂ] K₄ :=
  AdjoinRoot.liftAlgHom (kummerRat 4 fermatQuartic) (Algebra.ofId (RatFunc ℂ) K₄)
    (quarticI * quarticY) (by
      show eval₂ _ _ (X ^ 4 - C (algebraMap ℂ[X] (RatFunc ℂ) fermatQuartic)) = 0
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, mul_pow, quarticI_pow_four, one_mul, quarticY,
        kummerRoot_pow, AlgHom.coe_toRingHom, Algebra.ofId_apply,
        ← IsScalarTower.algebraMap_apply, sub_self])

/-- **R01e-2**: the automorphism `σ : y ↦ i·y` of the quartic's function field, fixing
`ℂ(x)`. -/
noncomputable def quarticRot : K₄ ≃ₐ[ℂ] K₄ :=
  (AlgEquiv.ofBijective quarticRotHom (AlgHom.bijective quarticRotHom)).restrictScalars ℂ

/-- The coefficients `F` with `F·dx` holomorphic, a `ℂ`-subspace of the function field. -/
noncomputable def quarticHoloCoeffs : Submodule ℂ K₄ :=
  (holomorphicSpace K₄).comap
    ((LinearMap.toSpanSingleton K₄ _ (KaehlerDifferential.D ℂ K₄ quarticX)).restrictScalars ℂ)

/-- The piece `p(x)·yʲ/y³`. -/
noncomputable def quarticTerm (p : ℂ[X]) (j : ℕ) : K₄ :=
  algebraMap ℂ[X] K₄ p * quarticY ^ j * quarticY⁻¹ ^ 3

end Quartic

end CurveSymmetry

end

-- lean/PaperRemarks.lean
section

namespace CurveSymmetry

set_option autoImplicit false

/-- `m = 2` in the family's instances. -/
local instance fact_zero_lt_two : Fact (0 < 2) :=
  ⟨by norm_num⟩

end CurveSymmetry

end


