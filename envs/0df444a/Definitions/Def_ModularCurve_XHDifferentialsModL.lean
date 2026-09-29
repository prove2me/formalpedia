-- Prove2me | Definitions.Def_ModularCurve_XHDifferentialsModL
-- name    : ModularCurve_XHDifferentialsModL
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/748f41ba-1ea2-5dce-b04a-be8f7df1fa39
-- title:
--   Mod-ℓ differentials on XH​: supersingular poles, Hecke and Frobenius operators
-- statement:
--   For a field $K$, a subgroup $\Gamma\le\mathrm{SL}_2(\mathbb Z)$ and a natural number $p$, a place $v$ of the $q$-expansion function field `qExpFunctionFieldC K Γ` satisfies `IsSSPlaceQExp` when some element $x$ of that field whose underlying Laurent series is the $q$-expansion `jqModC K` takes at $v$ a value $a\in K$ lying in `ssJSet p K`, i.e. such that every elliptic Weierstrass curve over $K$ with $j$-invariant $a$ has no nonzero point killed by $p$. The set of such places is `ssPlacesQExp`, and `ssPolarDifferentials` is the $K$-submodule of $\Omega^1$ of differentials regular away from these places and with at most a simple pole at each of them (`polarDifferentials`); regular differentials are contained in it. On Laurent series, `qDecimate K p` is the $K$-linear map with $k$-th coefficient the $(pk)$-th coefficient of the argument; it is a left inverse of `qExpand K p`. A $K$-endomorphism $C$ of $\Omega^1$ satisfies `IsFrobPushDiff` when $\Theta(C\omega)=\mathrm{qDecimate}_p(\Theta\omega)$ for all $\omega$, where $\Theta=$ `diffQExp`; `frobPushDiffModL` is a choice of such $C$ when one exists and $0$ otherwise, and any two such agree once $\Theta$ is injective.
--
--   For level $N$ with character group $H'$ and $\ell\ge1$, `heckeAlphaModLH` is the inclusion of $q$-expansion fields for $\Gamma_{H'}(N)\supseteq\Gamma_{H'}(N)\cap\Gamma_0(N\ell)$, and `heckeBetaModLH` is the $q\mapsto q^{\ell}$ substitution `qExpand K ℓ` viewed as an algebra map when `HeckeBetaModLHDefined` holds (i.e. `qExpand K ℓ` maps the upper field into the lower), and `heckeAlphaModLH` otherwise; `heckeDiffModLH` is the associated correspondence on differentials, trace along $\beta$ of pullback along $\alpha$. `diamondActionModL` is a choice of monoid homomorphism $\Gamma_0(N)\to\mathrm{Aut}_K$ satisfying `IsDiamondPullbackModL` (compatibility with slashing integral $q$-expansions), or the trivial one; `diamondDiffModLH d` is pullback along the automorphism attached to a lift of $d^{-1}$. With $p\mid M$, `infSubgroup` is the image of $H$ in $(\mathbb Z/(M/p))^\times$, and `genDiffModL` assigns to each Hecke generator [`CohCarrier.Gen M S`](../def/CohCarrier_Inst.html#L13) an operator on $\Omega^1$ at level $M/p$: $T_\ell$ and $U_q$ ($q\ne p$) give `heckeDiffModLH`, $U_p$ gives `frobPushDiffModL`, diamonds give `diamondDiffModLH`. For $K$ of characteristic $p$, `ssNodePairsQExp` consists of pairs $(\mathrm{Frob}(v),v)$ with $v$ supersingular, and `twoCompRegularDifferentials` is the glued polar module for that set, matching residues with opposite signs; `pairUpModL C`$(\omega)=(C\omega_1,-\omega_1)$ and `pairDiagModL T`$=T\times T$ give, via `genPairDiffModL`, the two-component operators, $U_p$ acting through `pairUpModL`.
--
--   On the forms side, [`CuspForm.IntTwoCuspForms M H p`](../def/ModularCurve_XHDifferentialsModL.html#L374) is `TwoCuspForms M H 2 p (⊥ : Subring ℂ)` modulo the ideal $(p)$ of $\mathbb Z\subset\mathbb C$; it is killed by $p$, hence a $\mathbb Z/p$-module, with reduction map `intTwoCuspReduce` from the weight-two integral Hecke lattice and operators `intTwoCuspGenMod` induced by the Hecke generators. Finally `IsInfReductionMap` is the predicate on a $K$-linear map $\rho\colon K\otimes_{\mathbb Z/p}\mathrm{IntTwoCuspForms}\to\Omega^1$ at level $M/p$ asserting that for every weight-two cusp form $f$ in the integral set with integral $q$-expansion $p_f$, the differential $q$-expansion of $\rho(1\otimes\bar f)$ equals the mod-$p$ reduction `intSeriesC K pf` of $p_f$.
--
--   **Relation to Mathlib.** Mathlib has none of these notions: the $q$-expansion function field, its places and polar differentials, the decimation operator on Laurent series and the Hecke/diamond/Frobenius operators on differentials are the project's own constructions, built on Mathlib's `HahnSeries`/`LaurentSeries`, `KaehlerDifferential`, congruence subgroups and cusp forms.
--
--   **Where it is used.** These are the objects used for the mod-$\ell$ geometry of modular curves in the level-lowering step: differentials with at most simple poles at the supersingular points and the two-component (glued) version model the dualising sheaf of the Deligne–Rapoport model of $X_H(M)$ at $p$ with its two irreducible components crossing at supersingular points, while `IsInfReductionMap` records the comparison between mod-$p$ weight-two cusp forms and such differentials, compatibly with the Hecke action in which $U_p$ acts through Frobenius push-forward.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_XHDifferentialsModL.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDiamondModL
import Definitions.Def_ModularCurve_QExpFrobeniusModL
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_AlgebraicCurve_PolarDifferentials
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_CuspForm_TwoCuspLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open HahnSeries KaehlerDifferential AlgebraicCurve IntermediateField CongruenceSubgroup

open scoped MatrixGroups

namespace ModularCurve

section Supersingular

variable (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ)) (p : ℕ)

def IsSSPlaceQExp (v : Place K (qExpFunctionFieldC K Γ)) : Prop :=
  ∃ (x : qExpFunctionFieldC K Γ) (a : K), (x : LaurentSeries K) = jqModC K ∧ v.HasValue x a ∧
    a ∈ @ssJSet p K _ (Classical.decEq K)

def ssPlacesQExp : Set (Place K (qExpFunctionFieldC K Γ)) :=
  {v | IsSSPlaceQExp K Γ p v}

variable {K Γ p} in
theorem mem_ssPlacesQExp_iff (v : Place K (qExpFunctionFieldC K Γ)) :
    v ∈ ssPlacesQExp K Γ p ↔ IsSSPlaceQExp K Γ p v :=
  Iff.rfl

def ssPolarDifferentials : Submodule K Ω[qExpFunctionFieldC K Γ⁄K] :=
  polarDifferentials K (qExpFunctionFieldC K Γ) (ssPlacesQExp K Γ p)

variable {K Γ p} in
theorem mem_ssPolarDifferentials_iff (ω : Ω[qExpFunctionFieldC K Γ⁄K]) :
    ω ∈ ssPolarDifferentials K Γ p ↔
      ∀ v : Place K (qExpFunctionFieldC K Γ),
        (v ∉ ssPlacesQExp K Γ p → v.IsRegularAt ω) ∧ (v ∈ ssPlacesQExp K Γ p → v.HasSimplePoleAt ω) :=
  Iff.rfl

theorem regularDifferentials_le_ssPolarDifferentials :
    regularDifferentials K (qExpFunctionFieldC K Γ) ≤ ssPolarDifferentials K Γ p :=
  regularDifferentials_le_polarDifferentials _

end Supersingular

section Decimate

variable (K : Type*) [Field K] (p : ℕ) [NeZero p]

variable {K p} in
private theorem bddBelow_support_decimate (x : LaurentSeries K) :
    BddBelow (Function.support fun k : ℤ => x.coeff ((p : ℤ) * k)) := by
  by_cases hne : x.support.Nonempty
  · refine ⟨min (x.isWF_support.min hne) 0, fun k hk => ?_⟩
    have hk' : (p : ℤ) * k ∈ x.support := hk
    have hmin := x.isWF_support.min_le hne hk'
    have hp : (1 : ℤ) ≤ p := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
    rcases le_or_gt 0 k with h0 | h0
    · exact (min_le_right _ _).trans h0
    · have : (p : ℤ) * k ≤ k := by nlinarith
      exact (min_le_left _ _).trans (hmin.trans this)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    refine ⟨0, fun k hk => ?_⟩
    exfalso
    have : (p : ℤ) * k ∈ x.support := hk
    rw [hne] at this
    exact this

def qDecimate : LaurentSeries K →ₗ[K] LaurentSeries K where
  toFun x := HahnSeries.ofSuppBddBelow (fun k : ℤ => x.coeff ((p : ℤ) * k)) (bddBelow_support_decimate x)
  map_add' x y := by
    ext k
    simp only [HahnSeries.coeff_ofSuppBddBelow, HahnSeries.coeff_add]
  map_smul' c x := by
    ext k
    simp only [HahnSeries.coeff_ofSuppBddBelow, HahnSeries.coeff_smul, RingHom.id_apply]

@[simp]
theorem coeff_qDecimate (x : LaurentSeries K) (k : ℤ) : (qDecimate K p x).coeff k = x.coeff ((p : ℤ) * k) := by
  simp only [qDecimate, LinearMap.coe_mk, AddHom.coe_mk, HahnSeries.coeff_ofSuppBddBelow]

theorem qDecimate_qExpand (x : LaurentSeries K) : qDecimate K p (qExpand K p x) = x := by
  ext k
  rw [coeff_qDecimate, qExpand_coeff_mul]

end Decimate

section FrobPush

variable (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ)) (p : ℕ) [NeZero p]

def IsFrobPushDiff (C : Ω[qExpFunctionFieldC K Γ⁄K] →ₗ[K] Ω[qExpFunctionFieldC K Γ⁄K]) : Prop :=
  ∀ ω : Ω[qExpFunctionFieldC K Γ⁄K],
    diffQExp (qExpFunctionFieldC K Γ) (C ω) = qDecimate K p (diffQExp (qExpFunctionFieldC K Γ) ω)

open Classical in

def frobPushDiffModL : Ω[qExpFunctionFieldC K Γ⁄K] →ₗ[K] Ω[qExpFunctionFieldC K Γ⁄K] :=
  if h : ∃ C : Ω[qExpFunctionFieldC K Γ⁄K] →ₗ[K] Ω[qExpFunctionFieldC K Γ⁄K], IsFrobPushDiff K Γ p C
  then h.choose else 0

variable {K Γ p}

theorem isFrobPushDiff_frobPushDiffModL
    (h : ∃ C : Ω[qExpFunctionFieldC K Γ⁄K] →ₗ[K] Ω[qExpFunctionFieldC K Γ⁄K], IsFrobPushDiff K Γ p C) :
    IsFrobPushDiff K Γ p (frobPushDiffModL K Γ p) := by
  rw [frobPushDiffModL, dif_pos h]
  exact h.choose_spec

theorem frobPushDiffModL_of_not
    (h : ¬ ∃ C : Ω[qExpFunctionFieldC K Γ⁄K] →ₗ[K] Ω[qExpFunctionFieldC K Γ⁄K], IsFrobPushDiff K Γ p C) :
    frobPushDiffModL K Γ p = 0 := by
  rw [frobPushDiffModL, dif_neg h]

theorem IsFrobPushDiff.eq_of_injective {C C' : Ω[qExpFunctionFieldC K Γ⁄K] →ₗ[K] Ω[qExpFunctionFieldC K Γ⁄K]}
    (hC : IsFrobPushDiff K Γ p C) (hC' : IsFrobPushDiff K Γ p C')
    (hinj : Function.Injective (diffQExp (qExpFunctionFieldC K Γ))) : C = C' := by
  refine LinearMap.ext fun ω => hinj ?_
  rw [hC ω, hC' ω]

end FrobPush

section HeckeDiff

variable (K : Type*) [Field K] (N : ℕ) (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [NeZero ℓ]

def heckeAlphaModLH :
    qExpFunctionFieldC K (CohCarrier.GammaH N H') →ₐ[K]
      qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ)) :=
  IntermediateField.inclusion (qExpFunctionFieldC_mono K inf_le_left)

omit [NeZero ℓ] in
@[simp]
theorem coe_heckeAlphaModLH (x : qExpFunctionFieldC K (CohCarrier.GammaH N H')) :
    (heckeAlphaModLH K N H' ℓ x : LaurentSeries K) = (x : LaurentSeries K) :=
  IntermediateField.coe_inclusion _ x

def HeckeBetaModLHDefined : Prop :=
  ∀ y ∈ qExpFunctionFieldC K (CohCarrier.GammaH N H'),
    qExpand K ℓ y ∈ qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ))

def heckeBetaModLHOf (h : HeckeBetaModLHDefined K N H' ℓ) :
    qExpFunctionFieldC K (CohCarrier.GammaH N H') →ₐ[K]
      qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ)) where
  toFun x := ⟨qExpand K ℓ (x : LaurentSeries K), h x x.2⟩
  map_one' := Subtype.ext (map_one (qExpand K ℓ))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand K ℓ) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand K ℓ))
  map_add' _ _ := Subtype.ext (map_add (qExpand K ℓ) _ _)
  commutes' a := Subtype.ext <| by
    show qExpand K ℓ (algebraMap K (LaurentSeries K) a) = algebraMap K (LaurentSeries K) a
    rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

@[simp]
theorem coe_heckeBetaModLHOf (h : HeckeBetaModLHDefined K N H' ℓ)
    (x : qExpFunctionFieldC K (CohCarrier.GammaH N H')) :
    (heckeBetaModLHOf K N H' ℓ h x : LaurentSeries K) = qExpand K ℓ (x : LaurentSeries K) :=
  rfl

open Classical in

def heckeBetaModLH :
    qExpFunctionFieldC K (CohCarrier.GammaH N H') →ₐ[K]
      qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ)) :=
  if h : HeckeBetaModLHDefined K N H' ℓ then heckeBetaModLHOf K N H' ℓ h else heckeAlphaModLH K N H' ℓ

theorem heckeBetaModLH_eq (h : HeckeBetaModLHDefined K N H' ℓ) :
    heckeBetaModLH K N H' ℓ = heckeBetaModLHOf K N H' ℓ h := by
  rw [heckeBetaModLH, dif_pos h]

theorem heckeBetaModLH_of_not (h : ¬ HeckeBetaModLHDefined K N H' ℓ) :
    heckeBetaModLH K N H' ℓ = heckeAlphaModLH K N H' ℓ := by
  rw [heckeBetaModLH, dif_neg h]

theorem coe_heckeBetaModLH (h : HeckeBetaModLHDefined K N H' ℓ)
    (x : qExpFunctionFieldC K (CohCarrier.GammaH N H')) :
    (heckeBetaModLH K N H' ℓ x : LaurentSeries K) = qExpand K ℓ (x : LaurentSeries K) := by
  rw [heckeBetaModLH_eq K N H' ℓ h, coe_heckeBetaModLHOf]

def heckeDiffModLH :
    Ω[qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K] →ₗ[K] Ω[qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K] :=
  Differential.correspondence (heckeBetaModLH K N H' ℓ) (heckeAlphaModLH K N H' ℓ)

theorem heckeDiffModLH_apply (ω : Ω[qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) :
    heckeDiffModLH K N H' ℓ ω =
      Differential.traceAlong (heckeBetaModLH K N H' ℓ)
        (Differential.pullbackAlong (heckeAlphaModLH K N H' ℓ) ω) :=
  rfl

end HeckeDiff

section DiamondDiff

variable (K : Type*) [Field K] (N : ℕ) (H' : Subgroup (ZMod N)ˣ)

open Classical in

def diamondActionModL :
    Gamma0 N →*
      (qExpFunctionFieldC K (CohCarrier.GammaH N H') ≃ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH N H')) :=
  if h : ∃ ρ : Gamma0 N →*
      (qExpFunctionFieldC K (CohCarrier.GammaH N H') ≃ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH N H')),
      IsDiamondPullbackModL K N H' ρ
  then h.choose else 1

variable {K N H'}

theorem isDiamondPullbackModL_diamondActionModL
    (h : ∃ ρ : Gamma0 N →*
      (qExpFunctionFieldC K (CohCarrier.GammaH N H') ≃ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH N H')),
      IsDiamondPullbackModL K N H' ρ) :
    IsDiamondPullbackModL K N H' (diamondActionModL K N H') := by
  rw [diamondActionModL, dif_pos h]
  exact h.choose_spec

theorem diamondActionModL_of_not
    (h : ¬ ∃ ρ : Gamma0 N →*
      (qExpFunctionFieldC K (CohCarrier.GammaH N H') ≃ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH N H')),
      IsDiamondPullbackModL K N H' ρ) :
    diamondActionModL K N H' = 1 := by
  rw [diamondActionModL, dif_neg h]

variable (K N H')
variable [NeZero N]

def diamondDiffModLH (d : (ZMod N)ˣ) :
    Ω[qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K] →ₗ[K] Ω[qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K] :=
  Differential.pullbackAlong (diamondActionModL K N H' (CuspForm.gammaLift N d⁻¹)).toAlgHom

theorem diamondDiffModLH_apply (d : (ZMod N)ˣ) (ω : Ω[qExpFunctionFieldC K (CohCarrier.GammaH N H')⁄K]) :
    diamondDiffModLH K N H' d ω =
      Differential.pullbackAlong (diamondActionModL K N H' (CuspForm.gammaLift N d⁻¹)).toAlgHom ω :=
  rfl

end DiamondDiff

section GenFamily

variable (K : Type*) [Field K] (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)

def infSubgroup : Subgroup (ZMod (M / p))ˣ :=
  H.map (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM))

omit [Fact p.Prime] [NeZero M] in
theorem mem_infSubgroup_iff (u : (ZMod (M / p))ˣ) :
    u ∈ infSubgroup p M H hpM ↔ ∃ d ∈ H, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d = u :=
  Subgroup.mem_map

omit [Fact p.Prime] [NeZero M] in
theorem unitsMap_mem_infSubgroup {d : (ZMod M)ˣ} (hd : d ∈ H) :
    ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ infSubgroup p M H hpM :=
  Subgroup.mem_map_of_mem _ hd

include hpM in

theorem neZero_div : NeZero (M / p) :=
  ⟨(Nat.div_ne_zero_iff_of_dvd hpM).mpr ⟨NeZero.ne M, (Fact.out : p.Prime).ne_zero⟩⟩

variable (S : Set ℕ)

def genDiffModL : CohCarrier.Gen M S →
    (Ω[qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))⁄K] →ₗ[K]
      Ω[qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))⁄K])
  | .T ℓ hℓ _ _ => haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeDiffModLH K (M / p) (infSubgroup p M H hpM) ℓ
  | .U q hq _ =>
      if q = p then
        haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        frobPushDiffModL K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p
      else haveI : NeZero q := ⟨hq.ne_zero⟩; heckeDiffModLH K (M / p) (infSubgroup p M H hpM) q
  | .dia d =>
      haveI : NeZero (M / p) := neZero_div p M hpM
      diamondDiffModLH K (M / p) (infSubgroup p M H hpM) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)

theorem genDiffModL_T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) :
    genDiffModL K p M H hpM S (.T ℓ hℓ hℓS hℓM) =
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeDiffModLH K (M / p) (infSubgroup p M H hpM) ℓ) :=
  rfl

theorem genDiffModL_U_self (hp : p.Prime) (hpM' : p ∣ M) :
    genDiffModL K p M H hpM S (.U p hp hpM') =
      (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩;
        frobPushDiffModL K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p) := by
  simp only [genDiffModL, if_true]

theorem genDiffModL_U_of_ne (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hqp : q ≠ p) :
    genDiffModL K p M H hpM S (.U q hq hqM) =
      (haveI : NeZero q := ⟨hq.ne_zero⟩; heckeDiffModLH K (M / p) (infSubgroup p M H hpM) q) := by
  simp only [genDiffModL, if_neg hqp]

theorem genDiffModL_dia (d : (ZMod M)ˣ) :
    genDiffModL K p M H hpM S (.dia d) =
      (haveI : NeZero (M / p) := neZero_div p M hpM;
        diamondDiffModLH K (M / p) (infSubgroup p M H hpM) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)) :=
  rfl

end GenFamily

section TwoComponent

variable (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ)) (p : ℕ) [Fact p.Prime] [CharP K p]

def ssNodePairsQExp : Set (Place K (qExpFunctionFieldC K Γ) × Place K (qExpFunctionFieldC K Γ)) :=
  {s | s.2 ∈ ssPlacesQExp K Γ p ∧ s.1 = qExpFrobeniusPlaceModL K Γ p s.2}

variable {K Γ p} in
theorem mem_ssNodePairsQExp_iff (s : Place K (qExpFunctionFieldC K Γ) × Place K (qExpFunctionFieldC K Γ)) :
    s ∈ ssNodePairsQExp K Γ p ↔ s.2 ∈ ssPlacesQExp K Γ p ∧ s.1 = qExpFrobeniusPlaceModL K Γ p s.2 :=
  Iff.rfl

variable {K Γ p} in
theorem frob_mk_mem_ssNodePairsQExp {y : Place K (qExpFunctionFieldC K Γ)} (hy : y ∈ ssPlacesQExp K Γ p) :
    (qExpFrobeniusPlaceModL K Γ p y, y) ∈ ssNodePairsQExp K Γ p :=
  ⟨hy, rfl⟩

def twoCompRegularDifferentials :
    Submodule K (Ω[qExpFunctionFieldC K Γ⁄K] × Ω[qExpFunctionFieldC K Γ⁄K]) :=
  gluedPolarDifferentials K (qExpFunctionFieldC K Γ) (ssNodePairsQExp K Γ p)

end TwoComponent

section PairOperators

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

def pairUpModL (C : V →ₗ[K] V) : (V × V) →ₗ[K] (V × V) :=
  LinearMap.prod (C ∘ₗ LinearMap.fst K V V) (-LinearMap.fst K V V)

@[simp]
theorem pairUpModL_apply (C : V →ₗ[K] V) (ω : V × V) : pairUpModL C ω = (C ω.1, -ω.1) :=
  rfl

def pairDiagModL (T : V →ₗ[K] V) : (V × V) →ₗ[K] (V × V) :=
  LinearMap.prodMap T T

@[simp]
theorem pairDiagModL_apply (T : V →ₗ[K] V) (ω : V × V) : pairDiagModL T ω = (T ω.1, T ω.2) :=
  rfl

end PairOperators

section GenPair

variable (K : Type*) [Field K] (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (S : Set ℕ)

def genPairDiffModL (g : CohCarrier.Gen M S) :
    (Ω[qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))⁄K] ×
        Ω[qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))⁄K]) →ₗ[K]
      (Ω[qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))⁄K] ×
        Ω[qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))⁄K]) :=
  match g with
  | .U q _ _ => if q = p then pairUpModL (genDiffModL K p M H hpM S g) else pairDiagModL (genDiffModL K p M H hpM S g)
  | _ => pairDiagModL (genDiffModL K p M H hpM S g)

end GenPair

end ModularCurve

namespace CuspForm

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (p : ℕ)

abbrev intIdeal : Ideal (⊥ : Subring ℂ) :=
  Ideal.span {(p : (⊥ : Subring ℂ))}

theorem natCast_mem_intIdeal : (p : (⊥ : Subring ℂ)) ∈ intIdeal p :=
  Ideal.subset_span rfl

def IntTwoCuspForms : Type :=
  TwoCuspForms M H 2 p (⊥ : Subring ℂ) (intIdeal p)

instance instAddCommGroupIntTwoCuspForms : AddCommGroup (IntTwoCuspForms M H p) :=
  inferInstanceAs (AddCommGroup (TwoCuspForms M H 2 p (⊥ : Subring ℂ) (intIdeal p)))

def IntTwoCuspForms.equivTwoCuspForms :
    IntTwoCuspForms M H p ≃+ TwoCuspForms M H 2 p (⊥ : Subring ℂ) (intIdeal p) :=
  AddEquiv.refl _

theorem IntTwoCuspForms.nsmul_eq_zero (x : IntTwoCuspForms M H p) : p • x = 0 := by
  change p • (x : TwoCuspForms M H 2 p (⊥ : Subring ℂ) (intIdeal p)) = 0
  obtain ⟨y, rfl⟩ := twoCuspReduce_surjective M H 2 p (⊥ : Subring ℂ) (intIdeal p) x
  have h : p • twoCuspReduce (intIdeal p) y = twoCuspReduce (intIdeal p) (p • y) :=
    (map_nsmul (twoCuspReduce (M := M) (H := H) (k := 2) (p := p) (A := (⊥ : Subring ℂ)) (intIdeal p)) p y).symm
  refine h.trans ((twoCuspReduce_eq_zero_iff (M := M) (H := H) (k := 2) (p := p) (A := (⊥ : Subring ℂ))
    (intIdeal p) (p • y)).mpr ?_)
  rw [← Nat.cast_smul_eq_nsmul (⊥ : Subring ℂ)]
  exact Submodule.smul_mem_smul (natCast_mem_intIdeal p) Submodule.mem_top

variable [Fact p.Prime]

instance instModuleZModIntTwoCuspForms : Module (ZMod p) (IntTwoCuspForms M H p) :=
  AddCommGroup.zmodModule (IntTwoCuspForms.nsmul_eq_zero M H p)

omit [Fact p.Prime] in

def intTwoCuspReduce : twoCuspLattice M H 2 p (⊥ : Subring ℂ) →+ IntTwoCuspForms M H p :=
  (twoCuspReduce (M := M) (H := H) (k := 2) (p := p) (A := (⊥ : Subring ℂ)) (intIdeal p)).toAddMonoidHom

omit [Fact p.Prime] in
theorem intTwoCuspReduce_apply (x : twoCuspLattice M H 2 p (⊥ : Subring ℂ)) :
    intTwoCuspReduce M H p x = (twoCuspReduce (intIdeal p) x : TwoCuspForms M H 2 p (⊥ : Subring ℂ) (intIdeal p)) :=
  rfl

omit [Fact p.Prime] in
theorem intTwoCuspReduce_surjective : Function.Surjective (intTwoCuspReduce M H p) :=
  twoCuspReduce_surjective M H 2 p (⊥ : Subring ℂ) (intIdeal p)

omit [Fact p.Prime] in

def intTwoCuspGenModAdd (S : Set ℕ) (g : CohCarrier.Gen M S) : IntTwoCuspForms M H p →+ IntTwoCuspForms M H p :=
  (twoCuspGenMod (M := M) (H := H) (k := 2) (p := p) (A := (⊥ : Subring ℂ)) (intIdeal p) S g).toAddMonoidHom

def intTwoCuspGenMod (S : Set ℕ) (g : CohCarrier.Gen M S) :
    IntTwoCuspForms M H p →ₗ[ZMod p] IntTwoCuspForms M H p :=
  (intTwoCuspGenModAdd M H p S g).toZModLinearMap p

theorem intTwoCuspGenMod_apply (S : Set ℕ) (g : CohCarrier.Gen M S) (x : IntTwoCuspForms M H p) :
    intTwoCuspGenMod M H p S g x =
      (twoCuspGenMod (intIdeal p) S g (x : TwoCuspForms M H 2 p (⊥ : Subring ℂ) (intIdeal p)) :
        TwoCuspForms M H 2 p (⊥ : Subring ℂ) (intIdeal p)) :=
  rfl

theorem intTwoCuspGenMod_reduce (S : Set ℕ) (g : CohCarrier.Gen M S)
    (x : twoCuspLattice M H 2 p (⊥ : Subring ℂ)) :
    intTwoCuspGenMod M H p S g (intTwoCuspReduce M H p x) =
      intTwoCuspReduce M H p (twoCuspEnd ⟨heckeGenH S 2 g, heckeGenH_mem_heckeRingH S 2 g⟩ x) :=
  rfl

end CuspForm

namespace ModularCurve

open scoped TensorProduct

variable (K : Type*) [Field K] (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  [Algebra (ZMod p) K]

def IsInfReductionMap
    (ρ : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K]
      Ω[qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))⁄K]) : Prop :=
  ∀ (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (pf : PowerSeries ℤ), IsIntegralQExp f pf →
      diffQExp (qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))
          (ρ ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
            ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩)) =
        intSeriesC K pf

variable {K p M H hpM} in
theorem IsInfReductionMap.diffQExp_apply
    {ρ : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K]
      Ω[qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))⁄K]}
    (hρ : IsInfReductionMap K p M H hpM ρ) {f : CuspForm (CohCarrier.GammaH M H) 2}
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) {pf : PowerSeries ℤ}
    (hpf : IsIntegralQExp f pf) :
    diffQExp (qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))
        (ρ ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
          ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩)) =
      intSeriesC K pf :=
  hρ f hf pf hpf

end ModularCurve

end


