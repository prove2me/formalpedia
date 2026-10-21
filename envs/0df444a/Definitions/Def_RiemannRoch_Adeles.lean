-- Prove2me | Definitions.Def_RiemannRoch_Adeles
-- name    : RiemannRoch_Adeles
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T11:44:23.671544+00:00
-- url     : https://prove2.me/theorems/3fc6c58b-91a4-4488-bcb7-89cb3c4d4047
-- title:
--   Adele space $\mathcal A_K$ of a function field, its filtration $\mathcal A_K(D)$, and chart places versus places
-- statement:
--   Throughout, $k$ is a field and $K$ is a field together with compatible embeddings $k[X]\subset k(X)\subset K$ such that $K/k(X)$ is a finite separable extension; $K$ is thus an algebraic function field in one variable over $k$, presented together with the transcendental element $x=X\in K$. Write $\mathcal O_\infty=\{f\in k(X):\deg f\le0\}$ for the valuation ring at infinity of $k(X)$ (with $\deg f=\deg(\text{numerator})-\deg(\text{denominator})$) and $\mathfrak m_\infty$ for its maximal ideal, $\mathcal O_K$ for the integral closure of $k[X]$ in $K$ and $\mathcal O_{K,\infty}$ for the integral closure of $\mathcal O_\infty$ in $K$. The *chart places* are the elements of $\mathbb P^{\mathrm{ch}}_K=\operatorname{Spec}^1(\mathcal O_K)\sqcup\operatorname{Spec}^1(\mathcal O_{K,\infty})$ (finite and infinite places), $v_P$ is the normalized $P$-adic valuation, $\deg P=\dim_k(\mathcal O/P)$ for the relevant Dedekind domain $\mathcal O$, and a chart divisor is a finitely supported $D:\mathbb P^{\mathrm{ch}}_K\to\mathbb Z$ with $\deg D=\sum_P D(P)\deg P$. Intrinsic places are valuation subrings $\mathcal O_P\subsetneq K$ containing $k$ with value group $\cong\mathbb Z$ (file `RiemannRoch_Places`), and $\mathcal L(D)$ is the Riemann–Roch space.
--
--   This file introduces Stichtenoth's adeles of $K$ on chart places (with components in $K$ itself, not in completions), and the bijection between chart places and intrinsic places.
--
--   1. **Adeles.** An adele is a family $\alpha=(\alpha_P)_{P\in\mathbb P^{\mathrm{ch}}_K}$ of elements of $K$ with $v_P(\alpha_P)\ge0$ for all but finitely many $P$. Adeles form a $k$-vector space $\mathcal A_K$, which is a $K$-module through $(x\alpha)_P=x\alpha_P$; multiplication by $x$ is also given as a $k$-linear map.
--   2. **Filtration and diagonal.** For a chart divisor $D$,
--   $$\mathcal A_K(D)=\{\alpha\in\mathcal A_K:\ v_P(\alpha_P)\ge -D(P)\ \text{for all }P\},$$
--   and the diagonal embedding $K\to\mathcal A_K$, $f\mapsto(f)_P$, has image the principal adeles $\widetilde K$.
--   3. **Ranks.** For divisors $D,D'$ the dimension $\dim_k\mathcal A_K(D')/\mathcal A_K(D)$ and, for $D\le D'$, the *sandwich rank* $\dim_k(\mathcal A_K(D')+\widetilde K)/(\mathcal A_K(D)+\widetilde K)$; also the operation replacing one component of an adele.
--   4. **Chart places versus intrinsic places.** Each chart place $P$ gives the intrinsic place with valuation ring $\{f: v_P(f)\ge0\}$ and the same normalized valuation. Conversely, for an intrinsic place, its restriction to $k(X)$ is a nontrivial valuation trivial on $k$, equivalent either to the valuation at infinity or to the valuation of exactly one prime of $k[X]$; the centre of the valuation ring in $\mathcal O_K$, resp. $\mathcal O_{K,\infty}$, is then a nonzero prime whose localization is the given valuation ring. This yields a bijection
--   $$\mathbb P^{\mathrm{ch}}_K\ \xrightarrow{\ \sim\ }\ \{\text{places of }K/k\}$$
--   compatible with the normalized valuations.
--
--   The file also contains the structural lemmas needed for these definitions: every $f\in K$ is integral at almost all chart places; $\mathcal A_K(D)\cap\widetilde K$ is the diagonal image of $\mathcal L(D)$; $\mathcal A_K(D)$ is monotone in $D$ and $\mathcal A_K(D_1\vee D_2)=\mathcal A_K(D_1)+\mathcal A_K(D_2)$; $v_P(X)\ge0$ at finite and $v_P(X)<0$ at infinite chart places; and injectivity and surjectivity of the chart map.
--
--   Adeles are the framework of the adelic proof of Riemann–Roch: the genus and the index of speciality are read off from the quotients $\mathcal A_K/(\mathcal A_K(D)+\widetilde K)$, and Weil differentials are linear forms on $\mathcal A_K$. In the chain of definition files it imports `RiemannRoch_RRSpace` and is imported by `RiemannRoch_IntrinsicAdeles`.
--
--   **Formalization Note** The function field is not constructed from $k$: $K$ is an arbitrary field carrying the instances `Algebra k[X] K`, `Algebra k⟮X⟯ K`, `IsScalarTower k[X] k⟮X⟯ K`, Mathlib's `FunctionField k K` (i.e. $K$ is finite-dimensional over $k(X)$) and `Algebra.IsSeparable k⟮X⟯ K`; when constants are needed, also `Algebra k K` with `IsScalarTower k k[X] K`. The adele space `FunctionField.Chart.AdeleSpace k K` is a `Submodule k (PlaceA k K → K)` cut out by a `Filter.cofinite` condition; the ranks are `finrankAdeleFiltDiff` and `sandwichRank` (an integer). The bijection `FunctionField.chartToPlace : PlaceA k K ≃ Place k K` is `Place.ofChart` with inverse chosen by `Classical.choose` from the surjectivity statement; the classification of the restriction to $k(X)$ is stated as an exclusive or (`Xor`) and relies on Mathlib's description of the places of $k(X)$. Valuations take values in $\mathbb Z_{m0}=\{0\}\cup\{\exp(n):n\in\mathbb Z\}$, written multiplicatively, so that the Lean valuation of $f\ne0$ at $P$ is $\exp(-v_P(f))$; the inequality $\exp(-v_P(f))\le\exp(D(P))$ is the additive condition $v_P(f)\ge -D(P)$.
-- source:
--   H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Section 1.5 (adele space $\mathcal A_F$, the subspaces $\mathcal A_F(A)$ and principal adeles, cf. Definition 1.5.1); places of $k(x)$: Section 1.2 (cf. Theorem 1.2.2). Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/AdeleSpace/Basic.lean, https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/PlaceEquiv.lean

import Mathlib
import Definitions.Def_RiemannRoch_RRSpace

/-
Contains code from riemann-roch-function-fields
(https://github.com/vaca22/riemann-roch-function-fields, commit dbca5bee),
Copyright (c) 2026 Guanghao Li, released under the Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
Modified: ported to Lean v4.33.1 / Mathlib 0df444a (module headers converted, some proofs
adapted to this Mathlib, a few names qualified, `picTorsor` omitted; statements unchanged), then
split into prove2.me definitions and theorems, with comments removed.
-/

set_option linter.style.haveILetI false

section
section
open scoped nonZeroDivisors Polynomial RatFunc WithZero
open Filter
noncomputable section
namespace FunctionField.Chart
variable (k K : Type*) [Field k] [Field K]
variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]
local instance instDecidableEqRatFuncAdele : DecidableEq k⟮X⟯ := Classical.decEq _
local instance instDecidableEqPlaceAAdele : DecidableEq (PlaceA k K) := Classical.decEq _
def adeleSubmodule : Submodule k (PlaceA k K → K) where
  carrier := {α | ∀ᶠ v in cofinite, α v ∈ placeValuationSubring k K v}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    change ∀ᶠ v in cofinite, a v ∈ placeValuationSubring k K v at ha
    change ∀ᶠ v in cofinite, b v ∈ placeValuationSubring k K v at hb
    change ∀ᶠ v in cofinite, (a + b) v ∈ placeValuationSubring k K v
    exact (ha.and hb).mono fun _ h => add_mem h.1 h.2
  smul_mem' c a ha := by
    change ∀ᶠ v in cofinite, a v ∈ placeValuationSubring k K v at ha
    change ∀ᶠ v in cofinite, (c • a) v ∈ placeValuationSubring k K v
    filter_upwards [ha] with v hv
    rw [Pi.smul_apply, Algebra.smul_def]
    exact mul_mem (by
      change placeValuation k K v (algebraMap k K c) ≤ 1
      exact placeValuation_algebraMap_le_one k K v c) hv
omit [Algebra k K] [IsScalarTower k k[X] K] in
theorem eventually_mem_placeValuationSubring (f : K) :
    ∀ᶠ v : PlaceA k K in cofinite, f ∈ placeValuationSubring k K v := by
  rw [Filter.eventually_cofinite]
  refine ((IsDedekindDomain.HeightOneSpectrum.Support.finite
      (R := ringOfIntegers k K) f).image Sum.inl).union
        ((IsDedekindDomain.HeightOneSpectrum.Support.finite
          (R := infiniteIntegers k K) f).image Sum.inr) |>.subset ?_
  intro v hv
  rcases v with v | v
  · left
    refine ⟨v, ?_, rfl⟩
    simpa [IsDedekindDomain.HeightOneSpectrum.Support, placeValuationSubring,
      placeValuation, not_le] using hv
  · right
    refine ⟨v, ?_, rfl⟩
    simpa [IsDedekindDomain.HeightOneSpectrum.Support, placeValuationSubring,
      placeValuation, not_le] using hv
abbrev AdeleSpace := adeleSubmodule k K
def smulAdele (x : K) (a : AdeleSpace k K) : AdeleSpace k K := ⟨fun v => x * a.val v, by
  have hx := eventually_mem_placeValuationSubring k K x
  have ha := a.property
  change ∀ᶠ v : PlaceA k K in cofinite, a.val v ∈ placeValuationSubring k K v at ha
  change ∀ᶠ v : PlaceA k K in cofinite, x * a.val v ∈ placeValuationSubring k K v
  exact (hx.and ha).mono fun _ h => mul_mem h.1 h.2⟩
instance : SMul K (AdeleSpace k K) := ⟨smulAdele k K⟩
instance : Module K (AdeleSpace k K) :=
  Module.ofMinimalAxioms
    (fun _ _ _ => Subtype.ext <| funext fun _ => mul_add _ _ _)
    (fun _ _ _ => Subtype.ext <| funext fun _ => add_mul _ _ _)
    (fun _ _ _ => Subtype.ext <| funext fun _ => mul_assoc _ _ _)
    (fun _ => Subtype.ext <| funext fun _ => one_mul _)
def mulAdeleLinear (x : K) : AdeleSpace k K →ₗ[k] AdeleSpace k K where
  toFun a := x • a
  map_add' _ _ := smul_add x _ _
  map_smul' c a := by
    ext v
    change x * (c • a.val v) = c • (x * a.val v)
    simp only [Algebra.smul_def]
    ring
def memAdeleFilt (D : DivisorA k K) (α : AdeleSpace k K) : Prop :=
  ∀ v, placeValuation k K v (α.val v) ≤ WithZero.exp (D v)
def adeleFilt (D : DivisorA k K) : Submodule k (AdeleSpace k K) where
  carrier := {a | memAdeleFilt k K D a}
  zero_mem' := fun v => by simp
  add_mem' {a b} ha hb := by
    change memAdeleFilt k K D a at ha
    change memAdeleFilt k K D b at hb
    change memAdeleFilt k K D (a + b)
    exact fun v => (Valuation.map_add _ (a.val v) (b.val v)).trans (max_le (ha v) (hb v))
  smul_mem' c a ha := by
    change memAdeleFilt k K D a at ha
    change memAdeleFilt k K D (c • a)
    intro v
    change placeValuation k K v (c • a.val v) ≤ _
    rw [Algebra.smul_def, map_mul]
    exact (mul_le_mul' (placeValuation_algebraMap_le_one k K v c) (ha v)).trans_eq
      (one_mul _)
def diagonal : K →ₗ[k] AdeleSpace k K where
  toFun f := ⟨fun _ => f, by
    simpa [adeleSubmodule] using
      eventually_mem_placeValuationSubring k K f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def diagonalSubmodule : Submodule k (AdeleSpace k K) := LinearMap.range (diagonal k K)
theorem adeleFilt_inf_diagonal (D : DivisorA k K) :
    adeleFilt k K D ⊓ diagonalSubmodule k K =
      Submodule.map (diagonal k K : K →ₗ[k] AdeleSpace k K) (RRspace k K D) := by
  ext a
  constructor
  · rintro ⟨ha, f, rfl⟩
    refine ⟨f, ?_, rfl⟩
    simpa [adeleFilt, memAdeleFilt, RRspace, memRRspace, diagonal] using ha
  · rintro ⟨f, hf, rfl⟩
    refine ⟨?_, ⟨f, rfl⟩⟩
    simpa [adeleFilt, memAdeleFilt, RRspace, memRRspace, diagonal] using hf
theorem adeleFilt_mono {D D' : DivisorA k K} (h : D ≤ D') :
    adeleFilt k K D ≤ adeleFilt k K D' := by
  intro a ha v
  exact (ha v).trans (WithZero.exp_le_exp.mpr (h v))
@[nolint unusedArguments]
def adeleFiltWithin {D D' : DivisorA k K} (_h : D ≤ D') :
    Submodule k (adeleFilt k K D') :=
  Submodule.comap (adeleFilt k K D').subtype (adeleFilt k K D)
noncomputable def finrankAdeleFiltDiff (D D' : DivisorA k K) : ℕ := by
  letI : AddCommGroup (adeleFilt k K D') := Submodule.addCommGroup _
  letI : Module k (adeleFilt k K D') := Submodule.module _
  exact Module.finrank k <|
    (adeleFilt k K D') ⧸
      Submodule.comap (adeleFilt k K D').subtype (adeleFilt k K D)
@[nolint unusedArguments]
noncomputable def sandwichRank (D D' : DivisorA k K) (_h : D ≤ D') : ℤ :=
  by
  letI : AddCommGroup (adeleFilt k K D' + diagonalSubmodule k K) :=
    Submodule.addCommGroup _
  letI : Module k (adeleFilt k K D' + diagonalSubmodule k K) := Submodule.module _
  exact Int.ofNat (Module.finrank k <|
    (adeleFilt k K D' + diagonalSubmodule k K) ⧸
      Submodule.comap (adeleFilt k K D' + diagonalSubmodule k K).subtype
        (adeleFilt k K D + diagonalSubmodule k K))
def adeleUpdate (α : AdeleSpace k K) (v : PlaceA k K) (a : K) : AdeleSpace k K :=
  ⟨Function.update α.val v a, by
    change ∀ᶠ w : PlaceA k K in cofinite,
      Function.update α.val v a w ∈ placeValuationSubring k K w
    filter_upwards [α.property, Filter.eventually_cofinite_ne v] with w hw hwv
    simpa [Function.update_of_ne hwv] using hw⟩
theorem adeleFilt_sup_eq_add {D₁ D₂ : DivisorA k K} :
    adeleFilt k K (D₁ ⊔ D₂) = adeleFilt k K D₁ + adeleFilt k K D₂ := by
  classical
  rw [Submodule.add_eq_sup]
  apply le_antisymm
  · intro a ha
    have haevent := a.property
    change ∀ᶠ v : PlaceA k K in cofinite,
      a.val v ∈ placeValuationSubring k K v at haevent
    let a₁ : AdeleSpace k K := ⟨fun v => if D₂ v ≤ D₁ v then a.val v else 0, by
      simpa [adeleSubmodule] using haevent.mono fun v hv => by
        by_cases h : D₂ v ≤ D₁ v
        · rw [if_pos h]
          exact hv
        · rw [if_neg h]
          exact zero_mem _⟩
    let a₂ : AdeleSpace k K := ⟨fun v => if D₂ v ≤ D₁ v then 0 else a.val v, by
      simpa [adeleSubmodule] using haevent.mono fun v hv => by
        by_cases h : D₂ v ≤ D₁ v
        · rw [if_pos h]
          exact zero_mem _
        · rw [if_neg h]
          exact hv⟩
    have ha₁ : a₁ ∈ adeleFilt k K D₁ := by
      change memAdeleFilt k K D₁ a₁
      intro v
      by_cases h : D₂ v ≤ D₁ v
      · change placeValuation k K v (if D₂ v ≤ D₁ v then a.val v else 0) ≤ _
        rw [if_pos h]
        simpa [Finsupp.sup_apply, sup_eq_left.mpr h] using ha v
      · simp [a₁, h]
    have ha₂ : a₂ ∈ adeleFilt k K D₂ := by
      change memAdeleFilt k K D₂ a₂
      intro v
      by_cases h : D₂ v ≤ D₁ v
      · simp [a₂, h]
      · have hv : D₁ v ≤ D₂ v := le_of_not_ge h
        change placeValuation k K v (if D₂ v ≤ D₁ v then 0 else a.val v) ≤ _
        rw [if_neg h]
        simpa [Finsupp.sup_apply, sup_eq_right.mpr hv] using ha v
    refine Submodule.mem_sup.mpr ⟨a₁, ha₁, a₂, ha₂, ?_⟩
    ext v
    by_cases h : D₂ v ≤ D₁ v <;> simp [a₁, a₂, h]
  · apply sup_le
    · intro a ha
      change memAdeleFilt k K (D₁ ⊔ D₂) a
      intro v
      exact (ha v).trans (WithZero.exp_le_exp.mpr le_sup_left)
    · intro a ha
      change memAdeleFilt k K (D₁ ⊔ D₂) a
      intro v
      exact (ha v).trans (WithZero.exp_le_exp.mpr le_sup_right)
end FunctionField.Chart
end
end
end

section
section
open scoped nonZeroDivisors Polynomial RatFunc WithZero
noncomputable section
namespace FunctionField
open MonoidWithZeroHom
open Chart
variable (k K : Type*) [Field k] [Field K]
  [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]
local instance instDecidableEqRatFuncPlaceEquiv : DecidableEq k⟮X⟯ := Classical.decEq _
noncomputable def Place.ofChart (w : PlaceA k K) : Place k K := by
  let q := placeValuation k K w
  let V := q.valuationSubring
  have hqdisc : q.IsRankOneDiscrete := by
    rcases w with w | w <;> dsimp [q, placeValuation] <;> infer_instance
  have hqnontrivial : q.IsNontrivial := by
    rcases w with w | w <;> dsimp [q, placeValuation] <;> infer_instance
  refine
    { toValuationSubring := V
      ne_top := by
        change q.valuationSubring ≠ ⊤
        intro htop
        exact (Valuation.valuationSubring_eq_top_iff q).mp htop hqnontrivial
      triv_on_k := fun c => by
        rw [Valuation.mem_valuationSubring_iff]
        exact placeValuation_algebraMap_le_one k K w c
      isDiscrete := ?_ }
  letI : q.IsRankOneDiscrete := hqdisc
  let h := Valuation.isEquiv_valuation_valuationSubring q
  exact ⟨h.orderMonoidIso.symm.trans
    (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt q)⟩
@[simp]
theorem Place.ofChart_toValuationSubring (w : PlaceA k K) :
    (Place.ofChart k K w).toValuationSubring =
      (placeValuation k K w).valuationSubring := rfl
theorem Place.ofChart_valuation_eq (w : PlaceA k K) :
    (Place.ofChart k K w).valuation = placeValuation k K w := by
  let q := placeValuation k K w
  let V := q.valuationSubring
  have hqdisc : q.IsRankOneDiscrete := by
    rcases w with w | w <;> dsimp [q, placeValuation] <;> infer_instance
  letI : q.IsRankOneDiscrete := hqdisc
  let h := Valuation.isEquiv_valuation_valuationSubring q
  let e : ValueGroup₀ (.ofClass V.valuation) ≃*o ℤᵐ⁰ :=
    h.orderMonoidIso.symm.trans
      (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt q)
  have hnorm : (Place.ofChart k K w).normalization = e :=
    orderMonoidIso_withZeroMulInt_unique _ _
  ext x
  change (Place.ofChart k K w).normalization
      (V.valuation.restrict x) = q x
  rw [hnorm]
  change (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt q)
      (h.orderMonoidIso.symm (V.valuation.restrict x)) = q x
  rw [show h.orderMonoidIso.symm (V.valuation.restrict x) = q.restrict x by
    change h.orderMonoidIso.symm
      (q.valuationSubring.valuation.restrict x) = q.restrict x
    exact h.orderMonoidIso.symm_apply_eq.mpr (h.orderMonoidIso_spec x).symm]
  exact Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
      (by
        rcases w with w | w
        · exact w.valuation_surjective K
        · exact w.valuation_surjective K) x
omit [Algebra k K] [IsScalarTower k k[X] K] in
theorem Place.finite_X_le_one
    (w : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    w.valuation K (algebraMap k⟮X⟯ K RatFunc.X) ≤ 1 := by
  let r : ringOfIntegers k K := algebraMap k[X] (ringOfIntegers k K) Polynomial.X
  have hr := w.valuation_le_one (K := K) r
  have hr_eq : (r : K) = algebraMap k⟮X⟯ K RatFunc.X := by
    calc
      (r : K) = algebraMap (ringOfIntegers k K) K r := rfl
      _ = algebraMap k[X] K Polynomial.X := by
        simpa only [r] using
          (IsScalarTower.algebraMap_apply k[X] (ringOfIntegers k K) K Polynomial.X).symm
      _ = algebraMap k⟮X⟯ K RatFunc.X := by
        rw [IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K, RatFunc.algebraMap_X]
  rw [← hr_eq]
  exact hr
namespace Place
variable {R L : Type*} [CommRing R] [IsDedekindDomain R] [Field L]
  [Algebra R L] [IsFractionRing R L]
noncomputable def centerIdeal (V : ValuationSubring L)
    (hR : ∀ r : R, algebraMap R L r ∈ V) : Ideal R :=
  (IsLocalRing.maximalIdeal V).comap
    ((algebraMap R L).codRestrict V hR)
instance centerIdeal_isPrime (V : ValuationSubring L)
    (hR : ∀ r : R, algebraMap R L r ∈ V) : (centerIdeal V hR).IsPrime :=
  (IsLocalRing.maximalIdeal V).comap_isPrime _
noncomputable def center (V : ValuationSubring L)
    (hR : ∀ r : R, algebraMap R L r ∈ V) (hne : centerIdeal V hR ≠ ⊥) :
    IsDedekindDomain.HeightOneSpectrum R where
  asIdeal := centerIdeal V hR
  isPrime := inferInstance
  ne_bot := hne
theorem valuationSubringAtPrime_center (V : ValuationSubring L) (hV : V ≠ ⊤)
    (hR : ∀ r : R, algebraMap R L r ∈ V) (hne : centerIdeal V hR ≠ ⊥) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L (center V hR hne) = V := by
  let w := center V hR hne
  let A := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L w
  have hle : A ≤ V := by
    rintro x hx
    have hvx : w.valuation L x ≤ 1 := by
      rw [← Valuation.mem_valuationSubring_iff,
        ← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact hx
    obtain ⟨a, s, hxs⟩ := w.exists_primeCompl_mul_eq_of_integer x hvx
    have hs_not_center : (s : R) ∉ centerIdeal V hR := by
      change (s : R) ∉ w.asIdeal
      exact s.property
    have hs_inv_mem : (algebraMap R L s)⁻¹ ∈ V := by
      have hs_not_max :
          ((⟨algebraMap R L s, hR s⟩ : V) ∉ IsLocalRing.maximalIdeal V) := by
        exact hs_not_center
      have hs_unit : IsUnit (⟨algebraMap R L s, hR s⟩ : V) := by
        simpa [IsLocalRing.mem_maximalIdeal] using hs_not_max
      obtain ⟨u, hu⟩ := hs_unit
      have hinv_mem : (algebraMap R L s)⁻¹ ∈ V := by
        have huval : ((u : V) : L) = algebraMap R L s := by
          exact congrArg Subtype.val hu
        have huinv : (((u⁻¹ : Vˣ) : V) : L) = (algebraMap R L s)⁻¹ := by
          have hmV : ((u⁻¹ : Vˣ) : V) * (u : V) = 1 := by simp
          have hmL := congrArg (fun z : V => (z : L)) hmV
          change (((u⁻¹ : Vˣ) : V) : L) * ((u : V) : L) = 1 at hmL
          rw [huval] at hmL
          exact eq_inv_of_mul_eq_one_left hmL
        rw [← huinv]
        exact (u⁻¹ : Vˣ).val.property
      exact hinv_mem
    have hs_ne : algebraMap R L s ≠ 0 := by
      have hsR : (s : R) ≠ 0 := by
        intro hs0
        exact s.property (hs0 ▸ w.asIdeal.zero_mem)
      intro hs0
      apply hsR
      apply FaithfulSMul.algebraMap_injective R L
      simpa using hs0
    have hx_eq : x = algebraMap R L a * (algebraMap R L s)⁻¹ := by
      apply (eq_mul_inv_iff_mul_eq₀ hs_ne).2
      exact hxs
    rw [hx_eq]
    exact V.mul_mem _ _ (hR a) hs_inv_mem
  exact ValuationSubring.eq_of_le_of_ne_top A hle hV
end Place
namespace Place
local instance instTowerConstantsRatFunc : IsScalarTower k k⟮X⟯ K :=
  IsScalarTower.of_algebraMap_eq fun c => by
    exact (IsScalarTower.algebraMap_apply k k[X] K c).trans
      (IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K (algebraMap k k[X] c))
noncomputable def restrict (v : Place k K) : Valuation k⟮X⟯ ℤᵐ⁰ :=
  v.valuation.comap (algebraMap k⟮X⟯ K)
instance restrict_isTrivialOn (v : Place k K) : (restrict k K v).IsTrivialOn k where
  eq_one c hc := by
    change v.valuation
      (algebraMap k⟮X⟯ K (algebraMap k k⟮X⟯ c)) = 1
    rw [← IsScalarTower.algebraMap_apply k k⟮X⟯ K]
    exact Valuation.IsTrivialOn.eq_one c hc
omit [Algebra k[X] K] [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K]
    [FunctionField k K] in
theorem restrict_isNontrivial (v : Place k K) :
    (restrict k K v).IsNontrivial := by
  let q := restrict k K v
  by_contra hq
  letI : v.valuation.IsTrivialOn k⟮X⟯ :=
    { eq_one := fun a ha => by
        change q a = 1
        by_contra hne
        apply hq
        refine ⟨a, ?_, hne⟩
        simp [restrict, ha] }
  obtain ⟨y, hy0, hy1⟩ :=
    (inferInstance : v.valuation.IsNontrivial).exists_val_nontrivial
  have hy : y ≠ 0 := v.valuation.ne_zero_iff.mp hy0
  exact (Valuation.transcendental_of_ne_one k⟮X⟯ y hy hy1)
    (Algebra.IsAlgebraic.isAlgebraic y)
omit [FunctionField k K] in
theorem restrict_classification (v : Place k K) :
    Xor ((restrict k K v).IsEquiv (RatFunc.inftyValuation k))
      (∃! u : IsDedekindDomain.HeightOneSpectrum k[X],
        (restrict k K v).IsEquiv (u.valuation k⟮X⟯)) := by
  let q := restrict k K v
  letI : q.IsNontrivial := restrict_isNontrivial k K v
  letI : q.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' q
  exact RatFunc.valuation_isEquiv_infty_or_adic (v := q)
omit [IsScalarTower k k[X] K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
theorem finiteRing_le (v : Place k K)
    (u : IsDedekindDomain.HeightOneSpectrum k[X])
    (h : (restrict k K v).IsEquiv (u.valuation k⟮X⟯)) :
    ∀ r : ringOfIntegers k K, algebraMap (ringOfIntegers k K) K r ∈
      v.toValuationSubring := by
  have hpoly : ∀ p : k[X], algebraMap k[X] K p ∈ v.toValuationSubring := by
    intro p
    rw [← v.valuationSubring_valuation, Valuation.mem_valuationSubring_iff]
    rw [IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K]
    exact h.le_one_iff_le_one.mpr (u.valuation_le_one p)
  letI : IsIntegrallyClosedIn v.toValuationSubring.toSubring K :=
    Subring.isIntegrallyClosedIn_iff.mpr fun {_x} hx =>
      LocalSubring.mem_of_isMax_of_isIntegral
        v.toValuationSubring.isMax_toLocalSubring hx
  have hle : (ringOfIntegers k K).toSubring ≤ v.toValuationSubring.toSubring :=
    (Subring.integralClosure_le_iff).mpr hpoly
  exact fun r => hle r.property
omit [IsScalarTower k k[X] K] in
theorem finiteCenter_ne (v : Place k K)
    (u : IsDedekindDomain.HeightOneSpectrum k[X])
    (h : (restrict k K v).IsEquiv (u.valuation k⟮X⟯)) :
    centerIdeal v.toValuationSubring (finiteRing_le k K v u h) ≠ ⊥ := by
  obtain ⟨a, ha_mem, ha_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot u.ne_bot
  let r : ringOfIntegers k K := algebraMap k[X] (ringOfIntegers k K) a
  have hr_ne : r ≠ 0 := by
    intro hr
    apply ha_ne
    apply FaithfulSMul.algebraMap_injective k[X] (ringOfIntegers k K)
    simpa [r] using hr
  intro hbot
  have hr_center : r ∈
      centerIdeal v.toValuationSubring (finiteRing_le k K v u h) := by
    change (⟨algebraMap (ringOfIntegers k K) K r,
      finiteRing_le k K v u h r⟩ : v.toValuationSubring) ∈
        IsLocalRing.maximalIdeal v.toValuationSubring
    rw [v.toValuationSubring.valuation_lt_one_iff]
    have hnorm : v.valuation (algebraMap (ringOfIntegers k K) K r) < 1 := by
      rw [show algebraMap (ringOfIntegers k K) K r = algebraMap k[X] K a by
        simpa only [r] using
          (IsScalarTower.algebraMap_apply k[X] (ringOfIntegers k K) K a).symm,
        IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K]
      exact h.lt_one_iff_lt_one.mpr
        ((u.valuation_lt_one_iff_mem a).mpr ha_mem)
    simpa only [map_one] using
      v.valuation_isEquiv_canonical.lt_one_iff_lt_one.mp hnorm
  rw [hbot] at hr_center
  exact hr_ne (Ideal.mem_bot.mp hr_center)
omit [Algebra k[X] K] [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K]
    [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
theorem infiniteRing_le (v : Place k K)
    (h : (restrict k K v).IsEquiv (RatFunc.inftyValuation k)) :
    ∀ r : infiniteIntegers k K, algebraMap (infiniteIntegers k K) K r ∈
      v.toValuationSubring := by
  have hbase : ∀ a : inftyValuationSubring k,
      algebraMap (inftyValuationSubring k) K a ∈ v.toValuationSubring := by
    intro a
    rw [← v.valuationSubring_valuation, Valuation.mem_valuationSubring_iff]
    rw [IsScalarTower.algebraMap_apply (inftyValuationSubring k) k⟮X⟯ K]
    exact h.le_one_iff_le_one.mpr a.property
  letI : IsIntegrallyClosedIn v.toValuationSubring.toSubring K :=
    Subring.isIntegrallyClosedIn_iff.mpr fun {_x} hx =>
      LocalSubring.mem_of_isMax_of_isIntegral
        v.toValuationSubring.isMax_toLocalSubring hx
  have hle : (infiniteIntegers k K).toSubring ≤ v.toValuationSubring.toSubring :=
    (Subring.integralClosure_le_iff).mpr hbase
  exact fun r => hle r.property
omit [Algebra k[X] K] [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] in
theorem infiniteCenter_ne (v : Place k K)
    (h : (restrict k K v).IsEquiv (RatFunc.inftyValuation k)) :
    centerIdeal v.toValuationSubring (infiniteRing_le k K v h) ≠ ⊥ := by
  let A := inftyValuationSubring k
  let u := IsDiscreteValuationRing.maximalIdeal A
  obtain ⟨a, ha_mem, ha_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot u.ne_bot
  let r : infiniteIntegers k K := algebraMap A (infiniteIntegers k K) a
  have hr_ne : r ≠ 0 := by
    intro hr
    apply ha_ne
    apply FaithfulSMul.algebraMap_injective A (infiniteIntegers k K)
    simpa [r] using hr
  intro hbot
  have hr_center : r ∈
      centerIdeal v.toValuationSubring (infiniteRing_le k K v h) := by
    change (⟨algebraMap (infiniteIntegers k K) K r,
      infiniteRing_le k K v h r⟩ : v.toValuationSubring) ∈
        IsLocalRing.maximalIdeal v.toValuationSubring
    rw [v.toValuationSubring.valuation_lt_one_iff]
    have hnorm : v.valuation (algebraMap (infiniteIntegers k K) K r) < 1 := by
      rw [show algebraMap (infiniteIntegers k K) K r = algebraMap A K a by
        simpa only [r] using
          (IsScalarTower.algebraMap_apply A (infiniteIntegers k K) K a).symm,
        IsScalarTower.algebraMap_apply A k⟮X⟯ K]
      exact h.lt_one_iff_lt_one.mpr
        ((Valuation.mem_maximalIdeal_iff (v := RatFunc.inftyValuation k)).mp ha_mem)
    simpa only [map_one] using
      v.valuation_isEquiv_canonical.lt_one_iff_lt_one.mp hnorm
  rw [hbot] at hr_center
  exact hr_ne (Ideal.mem_bot.mp hr_center)
omit [Algebra k K] [Algebra k[X] K] [IsScalarTower k k[X] K]
    [IsScalarTower k[X] k⟮X⟯ K] in
theorem infinite_X_gt_one
    (w : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    1 < w.valuation K (algebraMap k⟮X⟯ K RatFunc.X) := by
  let A := inftyValuationSubring k
  let u := IsDiscreteValuationRing.maximalIdeal A
  have hund : w.asIdeal.under A = u.asIdeal := by
    exact IsLocalRing.eq_maximalIdeal inferInstance
  letI : w.asIdeal.LiesOver u.asIdeal := ⟨hund.symm⟩
  have hbase : (u.valuation k⟮X⟯).IsEquiv (RatFunc.inftyValuation k) := by
    rw [Valuation.isEquiv_iff_valuationSubring]
    apply ValuationSubring.toSubring_injective
    have hmap : Subring.map (algebraMap A k⟮X⟯) ⊤ = A.toSubring := by
      ext x
      constructor
      · rintro ⟨a, _, rfl⟩
        exact a.property
      · intro hx
        exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
    exact (IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring
      (A := A) (K := k⟮X⟯)).symm.trans hmap
  have hbaseX : 1 < u.valuation k⟮X⟯ RatFunc.X :=
    hbase.one_lt_iff_one_lt.mpr (by simp [← WithZero.exp_zero])
  have he : u.asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal u.ne_bot
  have hpow : 1 < (u.valuation k⟮X⟯ RatFunc.X) ^
      u.asIdeal.ramificationIdx' w.asIdeal := by
    exact one_lt_pow₀ hbaseX he
  rw [u.valuation_liesOver K w RatFunc.X] at hpow
  exact hpow
theorem ofChart_injective : Function.Injective (Place.ofChart k K) := by
  intro w₁ w₂ hw
  have hsub := congrArg Place.toValuationSubring hw
  simp only [Place.ofChart_toValuationSubring] at hsub
  rcases w₁ with w₁ | w₁ <;> rcases w₂ with w₂ | w₂
  · congr 1
    exact IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
      ((Valuation.isEquiv_iff_valuationSubring _ _).mpr hsub)
  · have hequiv : (w₁.valuation K).IsEquiv (w₂.valuation K) :=
      (Valuation.isEquiv_iff_valuationSubring _ _).mpr hsub
    have hle := hequiv.le_one_iff_le_one.mp (finite_X_le_one k K w₁)
    exact (not_le_of_gt (infinite_X_gt_one k K w₂) hle).elim
  · have hequiv : (w₂.valuation K).IsEquiv (w₁.valuation K) :=
      (Valuation.isEquiv_iff_valuationSubring _ _).mpr hsub.symm
    have hle := hequiv.le_one_iff_le_one.mp (finite_X_le_one k K w₂)
    exact (not_le_of_gt (infinite_X_gt_one k K w₁) hle).elim
  · congr 1
    exact IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation
      ((Valuation.isEquiv_iff_valuationSubring _ _).mpr hsub)
theorem exists_chart (v : Place k K) :
    ∃ w : PlaceA k K, Place.ofChart k K w = v := by
  rcases restrict_classification k K v with h | h
  · let w := center v.toValuationSubring
      (infiniteRing_le k K v h.1) (infiniteCenter_ne k K v h.1)
    refine ⟨Sum.inr w, Place.ext ?_⟩
    rw [Place.ofChart_toValuationSubring]
    change (w.valuation K).valuationSubring = _
    rw [← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact valuationSubringAtPrime_center v.toValuationSubring v.ne_top
      (infiniteRing_le k K v h.1) (infiniteCenter_ne k K v h.1)
  · let u := h.1.choose
    have hu := h.1.choose_spec.1
    let w := center v.toValuationSubring
      (finiteRing_le k K v u hu) (finiteCenter_ne k K v u hu)
    refine ⟨Sum.inl w, Place.ext ?_⟩
    rw [Place.ofChart_toValuationSubring]
    change (w.valuation K).valuationSubring = _
    rw [← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact valuationSubringAtPrime_center v.toValuationSubring v.ne_top
      (finiteRing_le k K v u hu) (finiteCenter_ne k K v u hu)
noncomputable def toChart (v : Place k K) : PlaceA k K :=
  Classical.choose (exists_chart k K v)
theorem ofChart_toChart (v : Place k K) :
    Place.ofChart k K (toChart k K v) = v :=
  Classical.choose_spec (exists_chart k K v)
noncomputable def chartToPlaceCore : PlaceA k K ≃ Place k K where
  toFun := Place.ofChart k K
  invFun := toChart k K
  left_inv w := ofChart_injective k K (ofChart_toChart k K (Place.ofChart k K w))
  right_inv := ofChart_toChart k K
end Place
noncomputable abbrev chartToPlace : PlaceA k K ≃ Place k K :=
  Place.chartToPlaceCore k K
@[simp]
theorem chartToPlace_apply (w : PlaceA k K) :
    chartToPlace k K w = Place.ofChart k K w := rfl
theorem placeValuation_eq (w : PlaceA k K) :
    (chartToPlace k K w).valuation = placeValuation k K w :=
  Place.ofChart_valuation_eq k K w
end FunctionField
end
end
end


