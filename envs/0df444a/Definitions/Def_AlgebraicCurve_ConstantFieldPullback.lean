-- Prove2me | Definitions.Def_AlgebraicCurve_ConstantFieldPullback
-- name    : AlgebraicCurve_ConstantFieldPullback
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/ec760831-5bdb-561d-ad18-040181cce032
-- title:
--   Constant-field extension: places, divisor pullback, Picard base change
-- statement:
--   Throughout, a `Place K F` is a valuation subring of $F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring (hence a discrete valuation ring); `ord` is the associated normalised integer valuation, `deg` is the residue-field degree over $K$, and `Divisor K F` is the free abelian group on places, with `degree` the sum of coefficients weighted by `deg`.
--
--   For a tower $K \to K' \to F'$, `Place.forgetConstants` sends a place of $F'$ over $K'$ to the place of $F'$ over $K$ with the same valuation subring; it is injective and leaves `ord` unchanged. When $K'/K$ is integral, `Place.algebraMap_mem_of_isIntegral` shows the image of $K'$ lies in every such valuation subring (a valuation ring is integrally closed), so `Place.extendConstants` goes back, and `Place.constantFieldEquiv` is the resulting bijection $\mathrm{Place}(K,F') \simeq \mathrm{Place}(K',F')$; it preserves valuation subrings, hence `ord`, but not degrees.
--
--   In the commuting square $K \to K'$, $K \to F$, $K' \to F'$, $F \to F'$ with $F'/F$ integral, `Place.restrictConstants` sends $w$ of $F'$ over $K'$ to the place of $F$ over $K$ cut out by the contraction of its valuation subring along $F \to F'$; then $w(\mathrm{alg}_{F,F'} f) = e(w)\,(w|_F)(f)$, where $e(w)$ is the ramification index of `forgetConstants w` over $F$ (the least positive value of $w$ on nonzero elements of $F$). Assuming `HasPrincipalDivisors K' F'`, the fibres are finite (`fiberConstants`), and `Divisor.pullbackConstants` is the additive map determined by $v \mapsto \sum_{w \mapsto v} e(w)\,w$; equivalently $(\pi^*D)(w) = e(w)\,D(w|_F)$. It carries the divisor of $f \in F^\times$ to that of its image, hence principal divisors to principal divisors, and so induces `Pic.baseChange` $: \mathrm{Pic}(F/K) \to \mathrm{Pic}(F'/K')$. Finally `ConstantFieldDegreeFormula` is a one-field class asserting $\deg_{K'}(\pi^*D) = \deg_K D$ for all $D$, a hypothesis rather than a theorem; under it, degree-zero divisors pull back to degree-zero divisors.
--
--   **Relation to Mathlib.** The notions `Place`, `Divisor`, `Pic` and the ramification index used here are the project's own, built on Mathlib's valuation subrings and discrete valuation rings rather than on Mathlib's Dedekind-domain height-one spectrum formalism; this module is the constant-field-changing counterpart of the fixed-constant-field push/pull maps defined alongside it.
--
--   **Where it is used.** This supplies the divisor- and Picard-group-level comparison between a curve over a base field and the same curve after enlarging the constant field, for instance passing from the degree-zero Picard group of a modular curve over a number field to its Jacobian over a larger or algebraically closed field of constants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_ConstantFieldPullback.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

section Forget

variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']

namespace Place

def forgetConstants (w : Place K' F') : Place K F' where
  toValuationSubring := w.toValuationSubring
  algebraMap_mem' a := by
    rw [IsScalarTower.algebraMap_apply K K' F']
    exact w.algebraMap_mem' (algebraMap K K' a)
  ne_top' := w.ne_top'
  isPrincipalIdealRing' := w.isPrincipalIdealRing'

@[simp]
theorem forgetConstants_toValuationSubring (w : Place K' F') :
    (forgetConstants (K := K) w).toValuationSubring = w.toValuationSubring :=
  rfl

theorem forgetConstants_injective :
    Function.Injective (forgetConstants (K := K) (K' := K') (F' := F')) := by
  intro v w h
  exact Place.ext (congrArg (fun p : Place K F' => p.toValuationSubring) h)

@[simp]
theorem ord_forgetConstants (w : Place K' F') (f : F') :
    (forgetConstants (K := K) w).ord f = w.ord f :=
  rfl

end Place

end Forget

section Extend

variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']

namespace Place

variable (K') in

theorem algebraMap_mem_of_isIntegral [Algebra.IsIntegral K K'] (v : Place K F') (a : K') :
    algebraMap K' F' a ∈ v.toValuationSubring := by

  have hint : IsIntegral K (algebraMap K' F' a) :=
    (Algebra.IsIntegral.isIntegral (R := K) a).map (IsScalarTower.toAlgHom K K' F')

  have hint' : IsIntegral v.toValuationSubring (algebraMap K' F' a) := hint.tower_top

  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
  rw [← hy]
  exact y.2

variable (K') in

def extendConstants [Algebra.IsIntegral K K'] (v : Place K F') : Place K' F' where
  toValuationSubring := v.toValuationSubring
  algebraMap_mem' := v.algebraMap_mem_of_isIntegral K'
  ne_top' := v.ne_top'
  isPrincipalIdealRing' := v.isPrincipalIdealRing'

@[simp]
theorem extendConstants_toValuationSubring [Algebra.IsIntegral K K'] (v : Place K F') :
    (extendConstants K' v).toValuationSubring = v.toValuationSubring :=
  rfl

variable (K K') in

def constantFieldEquiv [Algebra.IsIntegral K K'] : Place K F' ≃ Place K' F' where
  toFun := extendConstants K'
  invFun := forgetConstants
  left_inv _ := Place.ext rfl
  right_inv _ := Place.ext rfl

@[simp]
theorem constantFieldEquiv_apply_toValuationSubring [Algebra.IsIntegral K K']
    (v : Place K F') :
    (constantFieldEquiv K K' v).toValuationSubring = v.toValuationSubring :=
  rfl

@[simp]
theorem constantFieldEquiv_symm_apply [Algebra.IsIntegral K K'] (w : Place K' F') :
    (constantFieldEquiv K K' (F' := F')).symm w = forgetConstants w :=
  rfl

end Place

end Extend

section Pullback

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
  [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F']

namespace Place

variable (F) in

def restrictConstants (w : Place K' F') : Place K F :=
  (forgetConstants (K := K) w).restrict F

@[simp]
theorem restrictConstants_toValuationSubring (w : Place K' F') :
    (restrictConstants F (K := K) w).toValuationSubring
      = w.toValuationSubring.comap (algebraMap F F') :=
  rfl

theorem ord_restrictConstants (w : Place K' F') (f : F) :
    w.ord (algebraMap F F' f)
      = ramificationIndex (F := F) (forgetConstants (K := K) w)
          * (restrictConstants F (K := K) w).ord f :=
  (forgetConstants (K := K) w).ord_restrict f

variable (K') in

theorem restrictConstants_fiber_finite [HasPrincipalDivisors K' F'] (v : Place K F) :
    {w : Place K' F' | restrictConstants F (K := K) w = v}.Finite := by
  obtain ⟨f, hf0, hford⟩ : ∃ f : F, f ≠ 0 ∧ 0 < v.ord f := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    refine ⟨(π : F), ?_, ?_⟩
    · simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
    · rw [v.ord_coe_irreducible hπ]
      exact one_pos
  have hf0' : algebraMap F F' f ≠ 0 := fun h =>
    hf0 ((map_eq_zero_iff _ (algebraMap F F').injective).mp h)
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K') (algebraMap F F' f) hf0'
  apply Set.Finite.subset D.support.finite_toSet
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, hD w]
  have := (forgetConstants (K := K) w).ord_algebraMap_ne_zero_of_restrict_eq
    (v := v) (f := f) (by omega) hw
  exact this

variable (K' F') in

def fiberConstants [HasPrincipalDivisors K' F'] (v : Place K F) : Finset (Place K' F') :=
  (restrictConstants_fiber_finite K' v).toFinset

@[simp]
theorem mem_fiberConstants [HasPrincipalDivisors K' F'] {v : Place K F} {w : Place K' F'} :
    w ∈ fiberConstants K' F' v ↔ restrictConstants F (K := K) w = v := by
  simp only [fiberConstants, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

end Place

namespace Divisor

variable [HasPrincipalDivisors K' F']

variable (K' F') in

def pullbackConstantsSingleHom (v : Place K F) : ℤ →+ Divisor K' F' where
  toFun n := ∑ w ∈ Place.fiberConstants K' F' v,
    Finsupp.single w (n * (Place.forgetConstants (K := K) w).ramificationIndex F)
  map_zero' := by simp
  map_add' m n := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => by rw [add_mul, Finsupp.single_add]

variable (K' F') in

def pullbackConstants : Divisor K F →+ Divisor K' F' :=
  Finsupp.liftAddHom (pullbackConstantsSingleHom K' F')

theorem pullbackConstants_single (v : Place K F) (n : ℤ) :
    pullbackConstants K' F' (Finsupp.single v n)
      = ∑ w ∈ Place.fiberConstants K' F' v,
          Finsupp.single w (n * (Place.forgetConstants (K := K) w).ramificationIndex F) :=
  Finsupp.liftAddHom_apply_single _ _ _

theorem pullbackConstants_single_apply_of_restrict_eq {v : Place K F} {w : Place K' F'}
    (hw : Place.restrictConstants F (K := K) w = v) (n : ℤ) :
    pullbackConstants K' F' (Finsupp.single v n) w
      = n * (Place.forgetConstants (K := K) w).ramificationIndex F := by
  rw [pullbackConstants_single, Finset.sum_apply']
  refine (Finset.sum_eq_single_of_mem w (Place.mem_fiberConstants.mpr hw) ?_).trans
    (by rw [Finsupp.single_eq_same])
  intro b _ hb
  exact Finsupp.single_eq_of_ne hb.symm

theorem pullbackConstants_single_apply_of_restrict_ne {v : Place K F} {w : Place K' F'}
    (hw : Place.restrictConstants F (K := K) w ≠ v) (n : ℤ) :
    pullbackConstants K' F' (Finsupp.single v n) w = 0 := by
  rw [pullbackConstants_single, Finset.sum_apply']
  refine Finset.sum_eq_zero fun b hb => ?_
  refine Finsupp.single_eq_of_ne fun h => hw ?_
  exact h ▸ Place.mem_fiberConstants.mp hb

theorem pullbackConstants_apply (D : Divisor K F) (w : Place K' F') :
    pullbackConstants K' F' D w
      = (Place.forgetConstants (K := K) w).ramificationIndex F
          * D (Place.restrictConstants F (K := K) w) := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
    rw [map_add, Finsupp.add_apply, ih, Finsupp.add_apply, mul_add]
    congr 1
    rcases eq_or_ne (Place.restrictConstants F (K := K) w) v with hw | hw
    · rw [pullbackConstants_single_apply_of_restrict_eq hw, hw, Finsupp.single_eq_same,
        mul_comm]
    · rw [pullbackConstants_single_apply_of_restrict_ne hw, Finsupp.single_eq_of_ne hw,
        mul_zero]

theorem pullbackConstants_apply_eq_ord {f : F} {D : Divisor K F}
    (hD : ∀ v : Place K F, D v = v.ord f) (w : Place K' F') :
    pullbackConstants K' F' D w = w.ord (algebraMap F F' f) := by
  rw [pullbackConstants_apply, hD, Place.ord_restrictConstants (K := K) w f]

theorem isPrincipal_pullbackConstants {D : Divisor K F} (hD : D.IsPrincipal) :
    (pullbackConstants K' F' D).IsPrincipal := by
  obtain ⟨f, hf, hDf⟩ := hD
  exact ⟨algebraMap F F' f,
    fun h => hf ((map_eq_zero_iff _ (algebraMap F F').injective).mp h),
    fun w => pullbackConstants_apply_eq_ord hDf w⟩

theorem pullbackConstants_mem_principal {D : Divisor K F}
    (hD : D ∈ principal (K := K) (F := F)) :
    pullbackConstants K' F' D ∈ principal (K := K') (F := F') :=
  isPrincipal_pullbackConstants hD

end Divisor

end Pullback

section ClassGroup

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
  [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [HasPrincipalDivisors K' F']

variable (K K' F F') in

def Pic.baseChange : Pic K F →+ Pic K' F' :=
  QuotientAddGroup.map _ _ (Divisor.pullbackConstants K' F')
    fun _ hD => Divisor.pullbackConstants_mem_principal hD

@[simp]
theorem Pic.baseChange_mk (D : Divisor K F) :
    Pic.baseChange K K' F F' (QuotientAddGroup.mk D)
      = QuotientAddGroup.mk (Divisor.pullbackConstants K' F' D) :=
  rfl

variable (K K' F F') in

class ConstantFieldDegreeFormula : Prop where
  degree_pullbackConstants : ∀ D : Divisor K F,
    Divisor.degree (Divisor.pullbackConstants K' F' D) = Divisor.degree D

theorem Divisor.pullbackConstants_mem_degZero [ConstantFieldDegreeFormula K K' F F']
    {D : Divisor K F} (hD : D ∈ Divisor.degZero (K := K) (F := F)) :
    Divisor.pullbackConstants K' F' D ∈ Divisor.degZero (K := K') (F := F') := by
  rw [Divisor.mem_degZero] at hD ⊢
  rw [ConstantFieldDegreeFormula.degree_pullbackConstants (K := K) (F := F) D, hD]

end ClassGroup

end AlgebraicCurve


