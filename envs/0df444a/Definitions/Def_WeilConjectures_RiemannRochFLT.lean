-- Prove2me | Definitions.Def_WeilConjectures_RiemannRochFLT
-- name    : WeilConjectures_RiemannRochFLT
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T13:37:18.86031+00:00
-- url     : https://prove2.me/theorems/e317db52-cea1-45fd-99ef-cca2f0de9715
-- title:
--   Bridge between RiemannRoch places and divisors and the FLT algebraic-curve places
-- statement:
--   Let $k$ be a field and $K$ a field extension of $k$. Two formalizations of the places of $K/k$ are available on the platform:
--
--   * the **RiemannRoch places**: valuation subrings $\mathcal O\subsetneq K$ containing $k$ whose value group is order-isomorphic to $\mathbb Z$ (file `RiemannRoch_Places`);
--   * the **FLT places** (`AlgebraicCurve.Place`): valuation subrings $\mathcal O\subsetneq K$ containing $k$ that are principal ideal domains, each with its adic valuation.
--
--   This file identifies them and transports the divisor groups:
--
--   1. the adic valuation of an FLT place is a rank-one discrete valuation whose valuation ring is the given ring, and the valuation ring of a RiemannRoch place is a principal ideal ring;
--   2. maps $\varphi$ from RiemannRoch places to FLT places and back, keeping the same valuation ring, and the resulting bijection
--   $$\varphi:\ \{\text{RiemannRoch places of }K/k\}\ \xrightarrow{\ \sim\ }\ \{\text{FLT places of }K/k\},\qquad \mathcal O_{\varphi(P)}=\mathcal O_P;$$
--   3. the induced isomorphism of divisor groups $\operatorname{Div}(K)\cong\operatorname{Div}_{\mathrm{FLT}}(K)$, $\sum n_PP\mapsto\sum n_P\,\varphi(P)$;
--   4. in the setting $k[X]\subset k(X)\subset K$ with $K/k(X)$ finite separable: the element $x_K$ (image of $X$), the $k$-isomorphism $k(X)\cong k(x_K)\subseteq K$, and the facts that $K$ is finite-dimensional and separable over the intermediate field $k(x_K)$, which are the hypotheses of the FLT characterization of the genus.
--
--   The file also contains the lemma that the FLT adic valuation ring coincides with the place, needed for the definitions above.
--
--   The bridge lets the Riemann–Roch theorem of `RiemannRoch` (degrees, spaces $\mathcal L(D)$, genus) be transported to the algebraic-curve definitions of the FLT project, for instance to identify the FLT genus with the genus defined here and to show that the function field of an elliptic Weierstrass curve has FLT genus one. In the chain of definition files it imports `RiemannRoch_WeierstrassGenus` (and `Def_AlgebraicCurve_AdelicIndex` from the FLT project); it is the last file of the chain.
--
--   **Formalization Note** The RiemannRoch side is `FunctionField.Place k K` and `FunctionField.Divisor k K`; the FLT side is `AlgebraicCurve.Place k K` and `AlgebraicCurve.Divisor k K`, imported from `Def_AlgebraicCurve_AdelicIndex`. The bijection is `WeilConjectures.Bridge.placeEquiv` and the divisor isomorphism is `WeilConjectures.Bridge.divEquiv` (`Finsupp.domCongr`). Item 4 assumes `Algebra k[X] K`, `Algebra k⟮X⟯ K`, `IsScalarTower k[X] k⟮X⟯ K`, Mathlib's `FunctionField k K` (i.e. $K$ is finite-dimensional over $k(X)$) and `Algebra.IsSeparable k⟮X⟯ K`, plus `Algebra k K` and `IsScalarTower k k[X] K`; the subfield $k(x_K)$ is Mathlib's `IntermediateField.adjoin`, written `k⟮xK k K⟯`. The file also declares, without content, the variable contexts (full constant field; perfect base field and elliptic Weierstrass curve) used by the bridge theorems.
-- source:
--   H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Section 1.1 (valuation rings of a function field are discrete valuation rings and principal ideal domains, cf. Theorem 1.1.6); the identification between the two formalizations is an auxiliary construction. Lean: bridge written for this port, file `Bridge/RiemannRochFLT.lean`

import Mathlib
import Definitions.Def_RiemannRoch_WeierstrassGenus
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option linter.style.haveILetI false

section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
open scoped WithZero
open MonoidWithZeroHom
noncomputable section
namespace WeilConjectures.Bridge
section Valuations
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
namespace FLTPlace
variable (v : AlgebraicCurve.Place k K)
instance adicValuation_isRankOneDiscrete : v.adicValuation.IsRankOneDiscrete := by
  unfold AlgebraicCurve.Place.adicValuation
  infer_instance
theorem adicValuation_valuationSubring :
    v.adicValuation.valuationSubring = v.toValuationSubring := by
  ext x
  rw [Valuation.mem_valuationSubring_iff]
  refine ⟨fun hx => ?_, v.adicValuation_le_one_of_mem⟩
  by_contra hxV
  have hx0 : x ≠ 0 := fun h => hxV (h ▸ v.toValuationSubring.zero_mem)
  have hinv : x⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem x).resolve_left hxV
  have hnu : ¬IsUnit (⟨x⁻¹, hinv⟩ : v.toValuationSubring) := by
    intro hu
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hu
    have h2 : x⁻¹ * (b : K) = 1 := by simpa using congrArg Subtype.val hb
    have hbx : x = (b : K) := (inv_mul_eq_one₀ hx0).mp h2
    exact hxV (hbx ▸ b.2)
  have hlt : v.adicValuation x⁻¹ < 1 := by
    have h1 : v.adicValuation x⁻¹ ≤ 1 := v.adicValuation_le_one_of_mem hinv
    refine lt_of_le_of_ne h1 fun h => hnu ?_
    exact (v.adicValuation_coe_eq_one_iff ⟨x⁻¹, hinv⟩).mp h
  have hgt : 1 < v.adicValuation x := by
    rw [map_inv₀] at hlt
    exact (inv_lt_one₀ (zero_lt_iff.mpr (v.adicValuation_ne_zero hx0))).mp hlt
  exact absurd hx (not_le.mpr hgt)
end FLTPlace
end Valuations
section Places
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
instance rrPlace_isPrincipalIdealRing (w : FunctionField.Place k K) :
    IsPrincipalIdealRing w.toValuationSubring := by
  have h := Valuation.valuationSubring_isPrincipalIdealRing w.valuation
  rwa [FunctionField.Place.valuationSubring_valuation] at h
def toFLTPlace (w : FunctionField.Place k K) : AlgebraicCurve.Place k K where
  toValuationSubring := w.toValuationSubring
  algebraMap_mem' := w.triv_on_k
  ne_top' := w.ne_top
  isPrincipalIdealRing' := rrPlace_isPrincipalIdealRing k K w
def ofFLTPlace (v : AlgebraicCurve.Place k K) : FunctionField.Place k K where
  toValuationSubring := v.toValuationSubring
  ne_top := v.ne_top'
  triv_on_k := v.algebraMap_mem'
  isDiscrete := by
    let q := v.adicValuation
    let h := Valuation.isEquiv_valuation_valuationSubring q
    have e : ValueGroup₀ (.ofClass q.valuationSubring.valuation) ≃*o ℤᵐ⁰ :=
      h.orderMonoidIso.symm.trans (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt q)
    rw [FLTPlace.adicValuation_valuationSubring v] at e
    exact ⟨e⟩
def placeEquiv : FunctionField.Place k K ≃ AlgebraicCurve.Place k K where
  toFun := toFLTPlace k K
  invFun := ofFLTPlace k K
  left_inv _ := FunctionField.Place.ext rfl
  right_inv _ := AlgebraicCurve.Place.ext rfl
@[simp]
theorem placeEquiv_toValuationSubring (w : FunctionField.Place k K) :
    (placeEquiv k K w).toValuationSubring = w.toValuationSubring := rfl
variable {k K}
end Places
section Divisors
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
def divEquiv : FunctionField.Divisor k K ≃+ AlgebraicCurve.Divisor k K :=
  Finsupp.domCongr (placeEquiv k K)
variable {k K}
end Divisors
section Hypotheses
open scoped Polynomial RatFunc IntermediateField
variable (k K : Type*) [Field k] [Field K] [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]
local instance instIsScalarTowerRatFunc : IsScalarTower k k⟮X⟯ K :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k k[X] K, IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K,
      ← IsScalarTower.algebraMap_apply k k[X] k⟮X⟯]
abbrev xK : K := FunctionField.Chart.XK k K
theorem transcendental_xK : Transcendental k (xK k K) := FunctionField.Chart.transcendental_XK k K
abbrev ratFuncEquivAdjoin : k⟮X⟯ ≃ₐ[k] k⟮xK k K⟯ :=
  RatFunc.algEquivOfTranscendental (xK k K) (transcendental_xK k K)
theorem algebraMap_ratFuncEquivAdjoin :
    (algebraMap k⟮xK k K⟯ K).comp ((ratFuncEquivAdjoin k K : k⟮X⟯ ≃+* k⟮xK k K⟯) : k⟮X⟯ →+* _) =
      ((RingEquiv.refl K : K ≃+* K) : K →+* K).comp (algebraMap k⟮X⟯ K) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors k[X])
  apply Polynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.refl_apply, RingHom.coe_coe]
    rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply k k[X] k⟮X⟯,
      ← IsScalarTower.algebraMap_apply k k⟮X⟯ K]
    change algebraMap k⟮xK k K⟯ K (ratFuncEquivAdjoin k K (algebraMap k k⟮X⟯ c)) = _
    rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply k k⟮xK k K⟯ K]
  · simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.refl_apply, RingHom.coe_coe]
    change ((ratFuncEquivAdjoin k K RatFunc.X : k⟮xK k K⟯) : K) = algebraMap k⟮X⟯ K RatFunc.X
    rw [RatFunc.algEquivOfTranscendental_X]
    rfl
instance finiteDimensional_adjoin_xK : FiniteDimensional k⟮xK k K⟯ K :=
  Module.Finite.of_equiv_equiv _ _ (algebraMap_ratFuncEquivAdjoin k K)
instance isSeparable_adjoin_xK : Algebra.IsSeparable k⟮xK k K⟯ K :=
  Algebra.IsSeparable.of_equiv_equiv _ _ (algebraMap_ratFuncEquivAdjoin k K)
end Hypotheses
section Genus
open scoped Polynomial RatFunc
variable (k K : Type*) [Field k] [Field K] [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [FunctionField.IsFullConstantField k K]
end Genus
section Weierstrass
open scoped Polynomial RatFunc
variable {k : Type*} [Field k] [PerfectField k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
  (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
  [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
  [Algebra k K] [IsScalarTower k k[X] K] [FunctionField.IsFullConstantField k K]
end Weierstrass
end WeilConjectures.Bridge
end
end


