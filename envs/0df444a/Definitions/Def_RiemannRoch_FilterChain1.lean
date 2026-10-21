-- Prove2me | Definitions.Def_RiemannRoch_FilterChain1
-- name    : RiemannRoch_FilterChain1
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T12:36:08.370074+00:00
-- url     : https://prove2.me/theorems/8784cad6-fa41-49ce-8bef-bf2d1aff24d0
-- title:
--   Local residue maps on adeles at finite chart places: $\dim\mathcal A_K(D+P)/\mathcal A_K(D)=\deg P$
-- statement:
--   Throughout, $k$ is a field and $K$ is a field together with compatible embeddings $k[X]\subset k(X)\subset K$ such that $K/k(X)$ is a finite separable extension; $K$ is thus an algebraic function field in one variable over $k$, presented together with the transcendental element $x=X\in K$. Write $\mathcal O_\infty=\{f\in k(X):\deg f\le0\}$ for the valuation ring at infinity of $k(X)$ (with $\deg f=\deg(\text{numerator})-\deg(\text{denominator})$) and $\mathfrak m_\infty$ for its maximal ideal, $\mathcal O_K$ for the integral closure of $k[X]$ in $K$ and $\mathcal O_{K,\infty}$ for the integral closure of $\mathcal O_\infty$ in $K$. The *chart places* are the elements of $\mathbb P^{\mathrm{ch}}_K=\operatorname{Spec}^1(\mathcal O_K)\sqcup\operatorname{Spec}^1(\mathcal O_{K,\infty})$ (finite and infinite places), $v_P$ is the normalized $P$-adic valuation, $\deg P=\dim_k(\mathcal O/P)$ for the relevant Dedekind domain $\mathcal O$, and a chart divisor is a finitely supported $D:\mathbb P^{\mathrm{ch}}_K\to\mathbb Z$ with $\deg D=\sum_P D(P)\deg P$. Let $\mathcal A_K$ be the chart adele space of $K$, $\mathcal A_K(D)=\{\alpha: v_P(\alpha_P)\ge -D(P)\ \forall P\}$ its filtration and $\widetilde K$ the principal adeles (file `RiemannRoch_Adeles`).
--
--   This file is the **first of four consecutive parts** of the source module `RiemannRoch/AdeleSpace/FilterChain.lean`, which was cut into quarters for publication (the other parts are `RiemannRoch_FilterChain2`, `RiemannRoch_FilterChain3`, `RiemannRoch_FilterChain4`). It introduces the zero adele and, for a finite chart place $P\in\operatorname{Spec}^1(\mathcal O_K)$ with chosen uniformizer $\pi_P$ and residue field $k_P$, the **one-step local residue map**
--   $$\rho_{D,P}:\ \mathcal A_K(D+P)\longrightarrow k_P,\qquad \alpha\longmapsto\overline{\pi_P^{\,D(P)+1}\,\alpha_P},$$
--   which is $k$-linear, together with the auxiliary map lifting $\pi_P^{D(P)+1}\alpha_P$ to the valuation ring at $P$; the same auxiliary lift is also defined for infinite chart places (the infinite residue map itself is in the next quarter).
--
--   It also contains the structural lemmas for finite $P$: $\ker\rho_{D,P}=\mathcal A_K(D)$ and $\rho_{D,P}$ is surjective, hence
--   $$\dim_k\mathcal A_K(D+P)/\mathcal A_K(D)=\deg P .$$
--
--   These one-step computations are the induction steps for the dimension formula $\dim\mathcal A_K(D')/\mathcal A_K(D)=\deg D'-\deg D$, a key input of the adelic description of the index of speciality. In the chain of definition files it imports `RiemannRoch_GenusCharts` and is imported by `RiemannRoch_FilterChain2`.
--
--   **Formalization Note** The function field is not constructed from $k$: $K$ is an arbitrary field carrying the instances `Algebra k[X] K`, `Algebra k⟮X⟯ K`, `IsScalarTower k[X] k⟮X⟯ K`, Mathlib's `FunctionField k K` (i.e. $K$ is finite-dimensional over $k(X)$) and `Algebra.IsSeparable k⟮X⟯ K`; when constants are needed, also `Algebra k K` with `IsScalarTower k k[X] K`. These files do not assume the full constant field. The filtration pieces are the submodules `adeleFilt k K D` of `AdeleSpace k K`, and $\dim_k\mathcal A_K(D')/\mathcal A_K(D)$ is `finrankAdeleFiltDiff k K D D'`. The maps are `finiteAdeleLocalResidueToSubring` and `finiteAdeleLocalResidueMap` (and `infiniteAdeleLocalResidueToSubring`) in `FunctionField.Chart`, landing in Mathlib's `valuationSubringAtPrime` and `Ideal.ResidueField`; they are defined on the submodule `adeleFilt k K (D + Finsupp.single P 1)`. The uniformizer is chosen with `Classical.choose`. The file also declares local instances (classical decidable equality on $k(X)$ and on chart places, module structures on the filtration pieces) reused by the next quarters.
-- source:
--   H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Section 1.5 (the dimension of $\mathcal A_F(B)/\mathcal A_F(A)$ for $A\le B$, cf. Lemma 1.5.2); the local residue maps are auxiliary constructions of the formalization. Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/AdeleSpace/FilterChain.lean

import Mathlib
import Definitions.Def_RiemannRoch_GenusCharts

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
open IsDedekindDomain Cardinal
set_option maxHeartbeats 4000000
noncomputable section
namespace FunctionField.Chart
variable (k K : Type*) [Field k] [Field K]
variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]
local instance instDecidableEqRatFuncAdeleFilter : DecidableEq k⟮X⟯ := Classical.decEq _
local instance instDecidableEqPlaceAAdeleFilter : DecidableEq (PlaceA k K) := Classical.decEq _
local instance adeleFiltAddCommGroup (D' : DivisorA k K) : AddCommGroup (adeleFilt k K D') :=
  Submodule.addCommGroup _
local instance adeleFiltModule (D' : DivisorA k K) : Module k (adeleFilt k K D') :=
  Submodule.module _
def zeroAdele : AdeleSpace k K := ⟨0, by simp⟩
noncomputable def finiteAdeleLocalResidueToSubring (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K))
    (a : adeleFilt k K (D + Finsupp.single (Sum.inl v) 1)) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v := by
  let π : K := Classical.choose (v.valuation_exists_uniformizer K)
  let n : ℤ := D (Sum.inl v) + 1
  refine ⟨π ^ n * (a.val : AdeleSpace k K).val (Sum.inl v), ?_⟩
  have hmem : v.valuation K (π ^ n * (a.val : AdeleSpace k K).val (Sum.inl v)) ≤ 1 := by
    have hπpow : v.valuation K (π ^ n) = WithZero.exp (-1) ^ n := by
      rw [map_zpow₀, Classical.choose_spec (v.valuation_exists_uniformizer K)]
    rw [map_mul, hπpow]
    have hf : v.valuation K ((a.val : AdeleSpace k K).val (Sum.inl v)) ≤ WithZero.exp n := by
      have := a.property (Sum.inl v)
      simpa [memAdeleFilt, placeValuation, n, Finsupp.add_apply, Finsupp.single_apply,
        add_comm] using this
    calc
      WithZero.exp (-1) ^ n * v.valuation K ((a.val : AdeleSpace k K).val (Sum.inl v))
          ≤ WithZero.exp (-1) ^ n * WithZero.exp n := mul_le_mul_right hf _
      _ = 1 := by
        rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
        convert WithZero.exp_zero
        simp
  rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    Valuation.mem_valuationSubring_iff]
  exact hmem
noncomputable def finiteAdeleLocalResidueMap (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    adeleFilt k K (D + Finsupp.single (Sum.inl v) 1) →ₗ[k] v.asIdeal.ResidueField :=
  let A := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v
  letI : Algebra k A :=
    ((algebraMap (ringOfIntegers k K) A).comp
      (algebraMap k (ringOfIntegers k K))).toAlgebra
  letI : IsScalarTower k (ringOfIntegers k K) A :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  {
    toFun := fun a =>
      IsDedekindDomain.HeightOneSpectrum.residueHom (K := K) v
        (finiteAdeleLocalResidueToSubring k K D v a)
    map_add' := fun a b => by
      rw [← map_add]
      congr 1
      simp [finiteAdeleLocalResidueToSubring, mul_add]
    map_smul' := fun c a => by
      let π : K := Classical.choose (v.valuation_exists_uniformizer K)
      let n : ℤ := D (Sum.inl v) + 1
      have hz :
          finiteAdeleLocalResidueToSubring k K D v (c • a) =
            algebraMap k A c * finiteAdeleLocalResidueToSubring k K D v a := by
        apply Subtype.ext
        simp only [finiteAdeleLocalResidueToSubring, Submodule.coe_smul_of_tower, Algebra.smul_def,
          Pi.smul_apply]
        let α : PlaceA k K → K := (a.val : AdeleSpace k K).val
        change π ^ n * (algebraMap k K c * α (Sum.inl v)) =
          (↑(algebraMap k A c) : K) * (π ^ n * α (Sum.inl v))
        have hcA : (↑(algebraMap k A c) : K) = algebraMap k K c := by
          calc
            (↑(algebraMap k A c) : K) =
                ↑(algebraMap (ringOfIntegers k K) A
                  (algebraMap k (ringOfIntegers k K) c)) := by
              rw [IsScalarTower.algebraMap_apply k (ringOfIntegers k K) A]
            _ = algebraMap (ringOfIntegers k K) K
                (algebraMap k (ringOfIntegers k K) c) := rfl
            _ = algebraMap k K c :=
              (IsScalarTower.algebraMap_apply k (ringOfIntegers k K) K c).symm
        rw [hcA]
        ring
      rw [hz, map_mul, Algebra.smul_def]
      congr 1
      rw [IsScalarTower.algebraMap_apply k (ringOfIntegers k K) A]
      rw [IsDedekindDomain.HeightOneSpectrum.residueHom, IsLocalization.lift_eq]
      exact (IsScalarTower.algebraMap_apply k (ringOfIntegers k K)
        v.asIdeal.ResidueField c).symm }
theorem finiteAdeleLocalResidueMap_ker (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    (finiteAdeleLocalResidueMap k K D v).ker =
      Submodule.comap (adeleFilt k K (D + Finsupp.single (Sum.inl v) 1)).subtype
        (adeleFilt k K D) := by
  ext a
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype,
    finiteAdeleLocalResidueMap, finiteAdeleLocalResidueToSubring]
  change IsDedekindDomain.HeightOneSpectrum.residueHom (K := K) v
      ⟨(Classical.choose (v.valuation_exists_uniformizer K)) ^
          (D (Sum.inl v) + 1) * ((a.val : AdeleSpace k K).val (Sum.inl v)), _⟩ = 0 ↔
    ∀ w, placeValuation k K w ((a.val : AdeleSpace k K).val w) ≤ WithZero.exp (D w)
  rw [IsDedekindDomain.HeightOneSpectrum.residueHom_eq_zero_iff]
  have hπ := Classical.choose_spec (v.valuation_exists_uniformizer K)
  rw [map_mul, map_zpow₀, hπ]
  rw [← WithZero.exp_zsmul]
  have hnsmul : (D (Sum.inl v) + 1) • (-1 : ℤ) = -(D (Sum.inl v) + 1) := by simp
  rw [hnsmul]
  have hlocal : WithZero.exp (-(D (Sum.inl v) + 1)) *
      v.valuation K ((a.val : AdeleSpace k K).val (Sum.inl v)) < 1 ↔
      v.valuation K ((a.val : AdeleSpace k K).val (Sum.inl v)) ≤
        WithZero.exp (D (Sum.inl v)) := by
    simpa using exp_neg_mul_lt_one_iff_le
      (v.valuation K ((a.val : AdeleSpace k K).val (Sum.inl v))) (D (Sum.inl v) + 1)
  rw [hlocal]
  constructor
  · intro hv w
    by_cases hw : w = Sum.inl v
    · subst hw
      exact hv
    · simpa [placeValuation, hw] using a.property w
  · intro hf
    simpa [placeValuation] using hf (Sum.inl v)
theorem finiteAdeleLocalResidueMap_surjective (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    Function.Surjective (finiteAdeleLocalResidueMap k K D v) := by
  let π : K := Classical.choose (v.valuation_exists_uniformizer K)
  let n : ℤ := D (Sum.inl v) + 1
  intro y
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective y
  let z : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v :=
    IsDedekindDomain.HeightOneSpectrum.localizationAlgEquiv (K := K) v x
  have hz : IsDedekindDomain.HeightOneSpectrum.residueHom (K := K) v z = y := by
    rwa [IsDedekindDomain.HeightOneSpectrum.residueHom_apply_localizationAlgEquiv]
  let xK : K := π ^ (-n) * (z : K)
  let a₀ : AdeleSpace k K := adeleUpdate k K (zeroAdele k K) (Sum.inl v) xK
  have ha₀ : a₀ ∈ adeleFilt k K (D + Finsupp.single (Sum.inl v) 1) := by
    intro w
    by_cases hw : w = Sum.inl v
    · subst hw
      simp only [placeValuation, Finsupp.add_apply, Finsupp.single_apply]
      have hπpow : v.valuation K (π ^ (-n)) = WithZero.exp (-1) ^ (-n) := by
        rw [map_zpow₀, Classical.choose_spec (v.valuation_exists_uniformizer K)]
      have hzle : v.valuation K (z : K) ≤ 1 := by
        simpa [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
          Valuation.mem_valuationSubring_iff] using z.property
      have hval :
          (v.valuation K) (a₀.val (Sum.inl v)) ≤ WithZero.exp (D (Sum.inl v) + 1) := by
        have hmul' : (v.valuation K) (a₀.val (Sum.inl v)) =
            (v.valuation K) (π ^ (-n)) * (v.valuation K) (z : K) := by
          show (v.valuation K)
              (Function.update (0 : PlaceA k K → K) (Sum.inl v) xK (Sum.inl v)) = _
          simp only [Function.update_self, xK]
          exact Valuation.map_mul (v.valuation K) _ _
        have hbound :
            (v.valuation K) (π ^ (-n)) * (v.valuation K) (z : K) ≤ WithZero.exp n := by
          have hπpow : v.valuation K (π ^ (-n)) = WithZero.exp (-1) ^ (-n) := by
            rw [map_zpow₀, Classical.choose_spec (v.valuation_exists_uniformizer K)]
          rw [hπpow]
          have hzle0 : (v.valuation K) (z : K) ≤ WithZero.exp (0 : ℤ) := by
            simpa [WithZero.exp_zero] using hzle
          calc
            WithZero.exp (-1) ^ (-n) * (v.valuation K) (z : K)
                ≤ WithZero.exp (-1) ^ (-n) * WithZero.exp 0 := mul_le_mul_right hzle0 _
            _ = WithZero.exp n := by
              rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
              simp
        simpa [n] using (le_of_eq hmul').trans hbound
      exact hval
    · simp only [placeValuation, zeroAdele, adeleUpdate, a₀,
        Function.update_of_ne hw, Pi.zero_apply, Valuation.map_zero,
        Finsupp.add_apply, Finsupp.single_apply]
      exact zero_le
  refine ⟨⟨a₀, ha₀⟩, ?_⟩
  have hmul : (finiteAdeleLocalResidueToSubring k K D v ⟨a₀, ha₀⟩ : K) = (z : K) := by
    dsimp [finiteAdeleLocalResidueToSubring, a₀, adeleUpdate, xK, zeroAdele, n, π]
    simp only [Function.update_self]
    have hπne : π ≠ 0 := by
      intro h0
      have huniform := Classical.choose_spec (v.valuation_exists_uniformizer K)
      have hπdef : v.valuation K π = WithZero.exp (-1) := by dsimp [π]; exact huniform
      rw [h0, Valuation.map_zero] at hπdef
      exact absurd hπdef.symm WithZero.exp_ne_zero
    have h1 : π ^ (D (Sum.inl v) + 1) * π ^ (-(D (Sum.inl v) + 1)) = (1 : K) := by
      rw [← zpow_add₀ hπne, add_neg_cancel, zpow_zero]
    calc
      π ^ (D (Sum.inl v) + 1) * (π ^ (-(D (Sum.inl v) + 1)) * (z : K))
          = (π ^ (D (Sum.inl v) + 1) * π ^ (-(D (Sum.inl v) + 1))) * (z : K) := by ring
      _ = (z : K) := by rw [h1, one_mul]
  simp only [finiteAdeleLocalResidueMap, finiteAdeleLocalResidueToSubring]
  exact congr_arg (IsDedekindDomain.HeightOneSpectrum.residueHom (K := K) v)
    (Subtype.ext_iff.mpr hmul) ▸ hz
theorem finrankAdeleFiltDiff_single_finite (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    finrankAdeleFiltDiff k K D (D + Finsupp.single (Sum.inl v) 1) =
      placeDegree k K (Sum.inl v) := by
  let f := finiteAdeleLocalResidueMap k K D v
  let e : (ringOfIntegers k K ⧸ v.asIdeal) ≃ₗ[k] v.asIdeal.ResidueField :=
    LinearEquiv.ofBijective
      ((Algebra.linearMap (ringOfIntegers k K ⧸ v.asIdeal)
        v.asIdeal.ResidueField).restrictScalars k)
      (Ideal.bijective_algebraMap_quotient_residueField v.asIdeal)
  letI : FiniteDimensional k v.asIdeal.ResidueField := e.finiteDimensional
  have hker := finiteAdeleLocalResidueMap_ker k K D v
  have hsurj := finiteAdeleLocalResidueMap_surjective k K D v
  rw [finrankAdeleFiltDiff, ← hker, f.quotKerEquivRange.finrank_eq]
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top]
  calc
    Module.finrank k v.asIdeal.ResidueField = Module.finrank k (ringOfIntegers k K ⧸ v.asIdeal) :=
      e.finrank_eq.symm
    _ = placeDegree k K (Sum.inl v) := rfl
noncomputable def infiniteAdeleLocalResidueToSubring (D : DivisorA k K)
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K))
    (a : adeleFilt k K (D + Finsupp.single (Sum.inr v) 1)) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K v := by
  let π : K := Classical.choose (v.valuation_exists_uniformizer K)
  let n : ℤ := D (Sum.inr v) + 1
  refine ⟨π ^ n * (a.val : AdeleSpace k K).val (Sum.inr v), ?_⟩
  have hmem : v.valuation K (π ^ n * (a.val : AdeleSpace k K).val (Sum.inr v)) ≤ 1 := by
    have hπpow : v.valuation K (π ^ n) = WithZero.exp (-1) ^ n := by
      rw [map_zpow₀, Classical.choose_spec (v.valuation_exists_uniformizer K)]
    rw [map_mul, hπpow]
    have hf : v.valuation K ((a.val : AdeleSpace k K).val (Sum.inr v)) ≤ WithZero.exp n := by
      have := a.property (Sum.inr v)
      simpa [memAdeleFilt, placeValuation, n, Finsupp.add_apply, Finsupp.single_apply,
        add_comm] using this
    calc
      WithZero.exp (-1) ^ n * v.valuation K ((a.val : AdeleSpace k K).val (Sum.inr v))
          ≤ WithZero.exp (-1) ^ n * WithZero.exp n := mul_le_mul_right hf _
      _ = 1 := by
        rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
        convert WithZero.exp_zero
        simp
  rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    Valuation.mem_valuationSubring_iff]
  exact hmem
end FunctionField.Chart
end
end
end


