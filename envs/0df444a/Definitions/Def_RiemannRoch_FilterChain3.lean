-- Prove2me | Definitions.Def_RiemannRoch_FilterChain3
-- name    : RiemannRoch_FilterChain3
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T12:56:22.178662+00:00
-- url     : https://prove2.me/theorems/b1abfceb-575b-4009-bdb3-250131f26ac1
-- title:
--   Exact dimension of adele quotients: $\dim\mathcal A_K(D')/\mathcal A_K(D)=\deg D'-\deg D$
-- statement:
--   Throughout, $k$ is a field and $K$ is a field together with compatible embeddings $k[X]\subset k(X)\subset K$ such that $K/k(X)$ is a finite separable extension; $K$ is thus an algebraic function field in one variable over $k$, presented together with the transcendental element $x=X\in K$. Write $\mathcal O_\infty=\{f\in k(X):\deg f\le0\}$ for the valuation ring at infinity of $k(X)$ (with $\deg f=\deg(\text{numerator})-\deg(\text{denominator})$) and $\mathfrak m_\infty$ for its maximal ideal, $\mathcal O_K$ for the integral closure of $k[X]$ in $K$ and $\mathcal O_{K,\infty}$ for the integral closure of $\mathcal O_\infty$ in $K$. The *chart places* are the elements of $\mathbb P^{\mathrm{ch}}_K=\operatorname{Spec}^1(\mathcal O_K)\sqcup\operatorname{Spec}^1(\mathcal O_{K,\infty})$ (finite and infinite places), $v_P$ is the normalized $P$-adic valuation, $\deg P=\dim_k(\mathcal O/P)$ for the relevant Dedekind domain $\mathcal O$, and a chart divisor is a finitely supported $D:\mathbb P^{\mathrm{ch}}_K\to\mathbb Z$ with $\deg D=\sum_P D(P)\deg P$. Let $\mathcal A_K$ be the chart adele space of $K$, $\mathcal A_K(D)=\{\alpha: v_P(\alpha_P)\ge -D(P)\ \forall P\}$ its filtration and $\widetilde K$ the principal adeles (file `RiemannRoch_Adeles`).
--
--   This file is the **third of four consecutive parts** of the source module `RiemannRoch/AdeleSpace/FilterChain.lean`, which was cut into quarters for publication (the other parts are `RiemannRoch_FilterChain1`, `RiemannRoch_FilterChain2`, `RiemannRoch_FilterChain4`). It introduces **no new definition**; it contains the lemmas that turn the one-step computations of the previous quarters into the exact dimension formula:
--
--   1. finiteness: $\mathcal A_K(N)/\mathcal A_K(D)$ is finite-dimensional over $k$ for $N=D$, for $N=D+nP$ ($n\in\mathbb N$), for $N=D+E$ with $E\ge0$, and for $D\le M\le N$ whenever both steps are;
--   2. additivity: for $D\le M\le N$, $\dim\mathcal A_K(N)/\mathcal A_K(D)=\dim\mathcal A_K(M)/\mathcal A_K(D)+\dim\mathcal A_K(N)/\mathcal A_K(M)$, and adding a place $P$ to $M$ adds $\deg P$;
--   3. for an effective divisor $E$, $\dim_k\mathcal A_K(D+E)/\mathcal A_K(D)=\deg E$, hence for $D\le D'$
--   $$\dim_k\frac{\mathcal A_K(D')}{\mathcal A_K(D)}=\deg(D'-D)=\deg D'-\deg D;$$
--   4. a linear-algebra lemma computing the dimension of the image of a submodule in a quotient, used in the next quarter.
--
--   This formula is one of the two dimension counts of the adelic proof of Riemann–Roch (the other, for the sandwich quotients, is in the next quarter). In the chain of definition files it imports `RiemannRoch_FilterChain2` and is imported by `RiemannRoch_FilterChain4`.
--
--   **Formalization Note** The function field is not constructed from $k$: $K$ is an arbitrary field carrying the instances `Algebra k[X] K`, `Algebra k⟮X⟯ K`, `IsScalarTower k[X] k⟮X⟯ K`, Mathlib's `FunctionField k K` (i.e. $K$ is finite-dimensional over $k(X)$) and `Algebra.IsSeparable k⟮X⟯ K`; when constants are needed, also `Algebra k K` with `IsScalarTower k k[X] K`. These files do not assume the full constant field. The filtration pieces are the submodules `adeleFilt k K D` of `AdeleSpace k K`, and $\dim_k\mathcal A_K(D')/\mathcal A_K(D)$ is `finrankAdeleFiltDiff k K D D'`. The degree in item 3 is converted with `Int.toNat` (it is nonnegative since $D\le D'$).
-- source:
--   H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Section 1.5 (cf. Lemma 1.5.2: $\dim\mathcal A_F(B)/\mathcal A_F(A)=\deg B-\deg A$ for $A\le B$). Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/AdeleSpace/FilterChain.lean

import Mathlib
import Definitions.Def_RiemannRoch_FilterChain2

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
attribute [local instance] FunctionField.Chart.instDecidableEqRatFuncAdeleFilter
attribute [local instance] FunctionField.Chart.instDecidableEqPlaceAAdeleFilter
attribute [local instance] FunctionField.Chart.adeleFiltAddCommGroup
attribute [local instance] FunctionField.Chart.adeleFiltModule
theorem finiteAdeleFiltDiff_quotient_self (D : DivisorA k K) :
    Module.Finite k ((adeleFilt k K D) ⧸
      Submodule.comap (adeleFilt k K D).subtype (adeleFilt k K D)) := by
  rw [show Submodule.comap (adeleFilt k K D).subtype (adeleFilt k K D) = ⊤ from
    Submodule.comap_subtype_self (adeleFilt k K D)]
  exact inferInstanceAs
    (Module.Finite k ((adeleFilt k K D) ⧸ (⊤ : Submodule k (adeleFilt k K D))))
theorem finiteAdeleFiltDiff_quotient_mono_add {D M N : DivisorA k K}
    (hDM : D ≤ M) (hMN : M ≤ N)
    [Module.Finite k ((adeleFilt k K N) ⧸
      Submodule.comap (adeleFilt k K N).subtype (adeleFilt k K M))]
    [Module.Finite k ((adeleFilt k K M) ⧸
      Submodule.comap (adeleFilt k K M).subtype (adeleFilt k K D))] :
    Module.Finite k ((adeleFilt k K N) ⧸
      Submodule.comap (adeleFilt k K N).subtype (adeleFilt k K D)) := by
  let p := adeleFilt k K N
  let q := Submodule.comap p.subtype (adeleFilt k K D)
  let r := Submodule.comap p.subtype (adeleFilt k K M)
  let pM := adeleFilt k K M
  let qM := Submodule.comap pM.subtype (adeleFilt k K D)
  have hqr : q ≤ r := Submodule.comap_mono (adeleFilt_mono k K hDM)
  let eR := Submodule.comapSubtypeEquivOfLe (adeleFilt_mono k K hMN)
  let qInR : Submodule k ↥r := Submodule.comap r.subtype q
  have hqmap : qM.map (eR.symm : pM →ₗ[k] r) = qInR := by
    rw [Submodule.map_equiv_eq_comap_symm eR.symm qM]
    rfl
  have eMq : (pM ⧸ qM) ≃ₗ[k] (r ⧸ qInR) := Submodule.Quotient.equiv qM qInR eR.symm hqmap
  haveI : Module.Finite k (r ⧸ qInR) := Module.Finite.equiv eMq
  have hker : (q.mkQ.comp (r.subtype : r →ₗ[k] p)).ker = qInR := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : (q.mkQ.comp (r.subtype : r →ₗ[k] p)).range = r.map q.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have eQuot : (r ⧸ qInR) ≃ₗ[k] r.map q.mkQ := by
    rw [← hker, ← hrange]
    exact LinearMap.quotKerEquivRange (q.mkQ.comp (r.subtype : r →ₗ[k] p))
  haveI : Module.Finite k (r.map q.mkQ) := Module.Finite.equiv eQuot
  have eThird := Submodule.quotientQuotientEquivQuotient q r hqr
  haveI : Module.Finite k (p ⧸ r) := by dsimp only [p, r]; infer_instance
  haveI : Module.Finite k ((p ⧸ q) ⧸ Submodule.map q.mkQ r) := Module.Finite.equiv eThird.symm
  exact Module.Finite.of_submodule_quotient (Submodule.map q.mkQ r)
theorem finiteAdeleFiltDiff_quotient_single_nat (D : DivisorA k K) (v : PlaceA k K) (n : ℕ) :
    Module.Finite k ((adeleFilt k K (D + Finsupp.single v (n : ℤ))) ⧸
      Submodule.comap (adeleFilt k K (D + Finsupp.single v (n : ℤ))).subtype
        (adeleFilt k K D)) := by
  induction n with
  | zero =>
      have heq : D + Finsupp.single v ((0 : ℕ) : ℤ) = D := by simp
      rw [heq]
      exact finiteAdeleFiltDiff_quotient_self k K D
  | succ n ih =>
      have heq : D + Finsupp.single v ((n + 1 : ℕ) : ℤ) =
          D + Finsupp.single v (n : ℤ) + Finsupp.single v 1 := by
        ext w
        simp only [Finsupp.add_apply, Finsupp.single_apply]
        split <;> omega
      have hDM : D ≤ D + Finsupp.single v (n : ℤ) := by
        intro w
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (by
          simp only [Finsupp.single_apply]
          split <;> omega)
      have hMN : D + Finsupp.single v (n : ℤ) ≤
          D + Finsupp.single v (n : ℤ) + Finsupp.single v 1 := by
        intro w
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (by
          simp only [Finsupp.single_apply]
          split <;> omega)
      letI := ih
      haveI := finiteAdeleFiltDiff_quotient_single k K (D + Finsupp.single v (n : ℤ)) v
      rw [heq]
      exact finiteAdeleFiltDiff_quotient_mono_add k K hDM hMN
theorem finiteAdeleFiltDiff_quotient_add_effective (D E : DivisorA k K)
    (hE : IsEffective k K E) :
    Module.Finite k ((adeleFilt k K (D + E)) ⧸
      Submodule.comap (adeleFilt k K (D + E)).subtype (adeleFilt k K D)) := by
  classical
  induction E using Finsupp.induction generalizing D with
  | zero =>
      rw [add_zero]
      exact finiteAdeleFiltDiff_quotient_self k K D
  | single_add a b f ha hb ih =>
      have hfa : f a = 0 := Finsupp.notMem_support_iff.mp ha
      have hff : IsEffective k K f := by
        intro w
        by_cases hw : w = a
        · subst w
          rw [hfa]
        · simpa [Finsupp.single_apply, hw] using hE w
      have hb0 : 0 ≤ b := by
        simpa [Finsupp.single_apply, hfa] using hE a
      letI := ih D hff
      haveI := finiteAdeleFiltDiff_quotient_single_nat k K (D + f) a b.toNat
      have hbcast : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb0
      have heq : D + (Finsupp.single a b + f) =
          (D + f) + Finsupp.single a (b.toNat : ℤ) := by
        rw [hbcast]
        abel
      have hDM : D ≤ D + f := by
        intro w
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (hff w)
      have hMN : D + f ≤ (D + f) + Finsupp.single a (b.toNat : ℤ) := by
        intro w
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (by
          simp only [Finsupp.single_apply]
          split <;> omega)
      rw [heq]
      exact finiteAdeleFiltDiff_quotient_mono_add k K hDM hMN
theorem finiteAdeleFiltDiff_quotient_add_eq {M N : DivisorA k K}
    (hN : N = M + (N - M)) (hE : IsEffective k K (N - M)) :
    Module.Finite k ((adeleFilt k K N) ⧸
      Submodule.comap (adeleFilt k K N).subtype (adeleFilt k K M)) :=
  hN ▸ finiteAdeleFiltDiff_quotient_add_effective k K M (N - M) hE
theorem finrankAdeleFiltDiff_mono_add {D M N : DivisorA k K}
    (hDM : D ≤ M) (hMN : M ≤ N) :
    finrankAdeleFiltDiff k K D N =
      finrankAdeleFiltDiff k K D M + finrankAdeleFiltDiff k K M N := by
  let p := adeleFilt k K N
  let q := Submodule.comap p.subtype (adeleFilt k K D)
  let r := Submodule.comap p.subtype (adeleFilt k K M)
  have hqr : q ≤ r := Submodule.comap_mono (adeleFilt_mono k K hDM)
  have hDN : D ≤ N := hDM.trans hMN
  have hE := (le_iff_sub_effective k K).mp hDN
  have hEN := (le_iff_sub_effective k K).mp hMN
  have hND : D + (N - D) = N := by ext w; simp [sub_eq_add_neg]
  have hNM : M + (N - M) = N := by ext w; simp [sub_eq_add_neg]
  haveI : Module.Finite k (p ⧸ q) :=
    finiteAdeleFiltDiff_quotient_add_eq k K (M := D) hND.symm hE
  haveI : Module.Finite k (p ⧸ r) :=
    finiteAdeleFiltDiff_quotient_add_eq k K (M := M) hNM.symm hEN
  dsimp only [finrankAdeleFiltDiff]
  have e := Submodule.quotientQuotientEquivQuotient q r hqr
  have hadd := Submodule.finrank_quotient_add_finrank (r.map q.mkQ)
  have hrmap : Module.finrank k (r.map q.mkQ) = finrankAdeleFiltDiff k K D M := by
    let pM := adeleFilt k K M
    let qM := Submodule.comap pM.subtype (adeleFilt k K D)
    let qInR : Submodule k ↥r := Submodule.comap r.subtype q
    let eR := Submodule.comapSubtypeEquivOfLe (adeleFilt_mono k K hMN)
    have hqmap : qM.map (eR.symm : pM →ₗ[k] r) = qInR := by
      rw [Submodule.map_equiv_eq_comap_symm eR.symm qM]
      rfl
    have eM : (pM ⧸ qM) ≃ₗ[k] (r ⧸ qInR) := Submodule.Quotient.equiv qM qInR eR.symm hqmap
    have hker : (q.mkQ.comp (r.subtype : r →ₗ[k] p)).ker = qInR := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    have hrange : (q.mkQ.comp (r.subtype : r →ₗ[k] p)).range = r.map q.mkQ := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have eQuot : (r ⧸ qInR) ≃ₗ[k] r.map q.mkQ := by
      rw [← hker, ← hrange]
      exact LinearMap.quotKerEquivRange (q.mkQ.comp (r.subtype : r →ₗ[k] p))
    dsimp [finrankAdeleFiltDiff]
    rw [← eQuot.finrank_eq, eM.finrank_eq]
  calc
    Module.finrank k (↥p ⧸ q)
        = Module.finrank k ((↥p ⧸ q) ⧸ Submodule.map q.mkQ r) +
            Module.finrank k ↥(Submodule.map q.mkQ r) := hadd.symm
    _ = Module.finrank k (↥p ⧸ r) + finrankAdeleFiltDiff k K D M := by
      rw [e.finrank_eq, hrmap]
    _ = finrankAdeleFiltDiff k K D M + finrankAdeleFiltDiff k K M N := by
      dsimp only [finrankAdeleFiltDiff]
      rw [add_comm]
theorem finrankAdeleFiltDiff_add_one {D M : DivisorA k K} (v : PlaceA k K) (hDM : D ≤ M) :
    finrankAdeleFiltDiff k K D (M + Finsupp.single v 1) =
      finrankAdeleFiltDiff k K D M + placeDegree k K v := by
  have hMN : M ≤ M + Finsupp.single v 1 := by
    intro w
    simp only [Finsupp.add_apply]
    exact le_add_of_nonneg_right (by
      simp only [Finsupp.single_apply]
      split <;> omega)
  rw [finrankAdeleFiltDiff_mono_add k K hDM hMN, finrankAdeleFiltDiff_single_one]
theorem finrankAdeleFiltDiff_add_effective (D E : DivisorA k K)
    (hE : IsEffective k K E) :
    finrankAdeleFiltDiff k K D (D + E) = (deg k K E).toNat := by
  classical
  induction E using Finsupp.induction generalizing D with
  | zero =>
      rw [add_zero, finrankAdeleFiltDiff, deg_zero]
      have hp : Submodule.comap (adeleFilt k K D).subtype (adeleFilt k K D) = ⊤ := by
        ext a
        simp
      rw [hp]
      exact Module.finrank_eq_zero_of_subsingleton k _
  | single_add a b f ha hb ih =>
      have hfa : f a = 0 := Finsupp.notMem_support_iff.mp ha
      have hff : IsEffective k K f := by
        intro w
        by_cases hw : w = a
        · subst w
          rw [hfa]
        · have hwE := hE w
          simpa [Finsupp.single_apply, hw] using hwE
      have hb0 : 0 ≤ b := by
        have haE := hE a
        simpa [Finsupp.single_apply, hfa] using haE
      let M := D + f
      let N := M + Finsupp.single a (b.toNat : ℤ)
      have hDM : D ≤ M := by
        intro w
        dsimp only [M]
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (hff w)
      have hMN : M ≤ N := by
        intro w
        dsimp only [N]
        simp only [Finsupp.add_apply]
        exact le_add_of_nonneg_right (by
          simp only [Finsupp.single_apply]
          split <;> omega)
      have hfirst := ih D hff
      have hsecond : finrankAdeleFiltDiff k K M N = b.toNat * placeDegree k K a := by
        have hbcast : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb0
        have heq : N = M + Finsupp.single a (b.toNat : ℤ) := rfl
        rw [heq]
        induction b.toNat with
        | zero =>
            simp only [Nat.cast_zero, Finsupp.single_zero, add_zero, zero_mul]
            rw [finrankAdeleFiltDiff]
            have hp : Submodule.comap (adeleFilt k K M).subtype (adeleFilt k K M) = ⊤ := by
              ext a
              simp
            rw [hp]
            exact Module.finrank_eq_zero_of_subsingleton k _
        | succ n ihN =>
            let P := M + Finsupp.single a (n : ℤ)
            have hMP : M ≤ P := by
              intro w
              dsimp only [P]
              simp only [Finsupp.add_apply]
              exact le_add_of_nonneg_right (by
                simp only [Finsupp.single_apply]
                split <;> omega)
            have heqP : M + Finsupp.single a ((n + 1 : ℕ) : ℤ) = P + Finsupp.single a 1 := by
              dsimp [P]
              ext w
              simp only [Finsupp.add_apply, Finsupp.single_apply]
              split <;> omega
            have hadd := finrankAdeleFiltDiff_add_one k K (M := P) a hMP
            have hcast : M + Finsupp.single a (Int.ofNat (n + 1)) =
                M + Finsupp.single a ((n + 1 : ℕ) : ℤ) := by simp [Int.ofNat_eq_natCast]
            calc
              finrankAdeleFiltDiff k K M (M + Finsupp.single a ↑(n + 1))
                  = finrankAdeleFiltDiff k K M (M + Finsupp.single a (Int.ofNat (n + 1))) := by
                simp [Int.ofNat_eq_natCast]
              _ = finrankAdeleFiltDiff k K M (M + Finsupp.single a ((n + 1 : ℕ) : ℤ)) := by
                rw [hcast]
              _ = finrankAdeleFiltDiff k K M (P + Finsupp.single a 1) := by rw [heqP]
              _ = finrankAdeleFiltDiff k K M P + placeDegree k K a := hadd
              _ = n * placeDegree k K a + placeDegree k K a := by
                rw [← ihN]
              _ = (n + 1) * placeDegree k K a := by ring
      have hdegf : 0 ≤ deg k K f := deg_nonneg k K hff
      have hdegE : deg k K (Finsupp.single a b + f) =
          b * (placeDegree k K a : ℤ) + deg k K f := by
        rw [deg_add]
        simp [deg]
      have hdegE0 : 0 ≤ deg k K (Finsupp.single a b + f) := deg_nonneg k K hE
      have hdegNat : (deg k K (Finsupp.single a b + f)).toNat =
          b.toNat * placeDegree k K a + (deg k K f).toNat := by
        have hfcast : ((deg k K f).toNat : ℤ) = deg k K f := Int.toNat_of_nonneg hdegf
        have hEcast : ((deg k K (Finsupp.single a b + f)).toNat : ℤ) =
            deg k K (Finsupp.single a b + f) := Int.toNat_of_nonneg hdegE0
        apply Int.ofNat_injective
        change ((deg k K (Finsupp.single a b + f)).toNat : ℤ) =
          ((b.toNat * placeDegree k K a + (deg k K f).toNat : ℕ) : ℤ)
        rw [hEcast, Nat.cast_add, Nat.cast_mul, Int.toNat_of_nonneg hb0, hfcast]
        exact hdegE
      have htotal : finrankAdeleFiltDiff k K D N =
          (deg k K (Finsupp.single a b + f)).toNat := by
        have hadd := finrankAdeleFiltDiff_mono_add k K hDM hMN
        rw [hadd, hfirst, hsecond, hdegNat, Nat.add_comm]
      have heq : D + (Finsupp.single a b + f) = N := by
        dsimp only [N, M]
        rw [Int.toNat_of_nonneg hb0]
        abel
      rw [heq]
      exact htotal
theorem finrank_adeleFilt_quotient {D D' : DivisorA k K} (h : D ≤ D') :
    finrankAdeleFiltDiff k K D D' = (deg k K (D' - D)).toNat := by
  have hE : IsEffective k K (D' - D) := (le_iff_sub_effective k K).mp h
  have hrank := finrankAdeleFiltDiff_add_effective k K D (D' - D) hE
  have heq : D + (D' - D) = D' := by abel
  rw [heq] at hrank
  exact hrank
theorem finrank_map_comap_mkQ_eq_quotient {D' : DivisorA k K}
    {s t : Submodule k (AdeleSpace k K)} (_hs : s ≤ adeleFilt k K D')
    (ht : t ≤ adeleFilt k K D') (_hst : s ≤ t) :
    Module.finrank k (Submodule.map (Submodule.comap (adeleFilt k K D').subtype s).mkQ
      (Submodule.comap (adeleFilt k K D').subtype t)) =
      Module.finrank k
        (↥(Submodule.comap (adeleFilt k K D').subtype t) ⧸
          Submodule.comap (Submodule.comap (adeleFilt k K D').subtype t).subtype
            (Submodule.comap (adeleFilt k K D').subtype s)) := by
  classical
  let p := adeleFilt k K D'
  let qp := Submodule.comap p.subtype s
  let qt := Submodule.comap p.subtype t
  let st := Submodule.comap t.subtype s
  let qpInQt := Submodule.comap qt.subtype qp
  letI : AddCommGroup ↥t := Submodule.addCommGroup _
  letI : Module k ↥t := Submodule.module _
  letI : AddCommGroup ↥qt := Submodule.addCommGroup _
  letI : Module k ↥qt := Submodule.module _
  let eT := Submodule.comapSubtypeEquivOfLe ht
  have hmap : st.map (eT.symm : ↥t →ₗ[k] ↥qt) = qpInQt := by
    ext x
    simp [Submodule.mem_comap, st, qpInQt, qp, qt, eT]
  have hker : (qp.mkQ.comp (qt.subtype : qt →ₗ[k] p)).ker = qpInQt := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : (qp.mkQ.comp (qt.subtype : qt →ₗ[k] p)).range = Submodule.map qp.mkQ qt := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have eQuot : (↥qt ⧸ qpInQt) ≃ₗ[k] Submodule.map qp.mkQ qt := by
    rw [← hker, ← hrange]
    exact LinearMap.quotKerEquivRange (qp.mkQ.comp (qt.subtype : qt →ₗ[k] p))
  have eTS : ((↥t) ⧸ st) ≃ₗ[k] ((↥qt) ⧸ qpInQt) :=
    Submodule.Quotient.equiv st qpInQt eT.symm hmap
  rw [← eQuot.finrank_eq, ← eTS.finrank_eq]
end FunctionField.Chart
end
end
end


