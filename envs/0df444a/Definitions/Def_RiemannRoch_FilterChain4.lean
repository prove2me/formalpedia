-- Prove2me | Definitions.Def_RiemannRoch_FilterChain4
-- name    : RiemannRoch_FilterChain4
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T12:59:43.779972+00:00
-- url     : https://prove2.me/theorems/6ff7ad27-03e1-44bb-9894-f573893c604c
-- title:
--   Sandwich formula and the index of speciality: $\dim\mathcal A_K/(\mathcal A_K(D)+K)=i(D)$
-- statement:
--   Throughout, $k$ is a field and $K$ is a field together with compatible embeddings $k[X]\subset k(X)\subset K$ such that $K/k(X)$ is a finite separable extension; $K$ is thus an algebraic function field in one variable over $k$, presented together with the transcendental element $x=X\in K$. Write $\mathcal O_\infty=\{f\in k(X):\deg f\le0\}$ for the valuation ring at infinity of $k(X)$ (with $\deg f=\deg(\text{numerator})-\deg(\text{denominator})$) and $\mathfrak m_\infty$ for its maximal ideal, $\mathcal O_K$ for the integral closure of $k[X]$ in $K$ and $\mathcal O_{K,\infty}$ for the integral closure of $\mathcal O_\infty$ in $K$. The *chart places* are the elements of $\mathbb P^{\mathrm{ch}}_K=\operatorname{Spec}^1(\mathcal O_K)\sqcup\operatorname{Spec}^1(\mathcal O_{K,\infty})$ (finite and infinite places), $v_P$ is the normalized $P$-adic valuation, $\deg P=\dim_k(\mathcal O/P)$ for the relevant Dedekind domain $\mathcal O$, and a chart divisor is a finitely supported $D:\mathbb P^{\mathrm{ch}}_K\to\mathbb Z$ with $\deg D=\sum_P D(P)\deg P$. Let $\mathcal A_K$ be the chart adele space of $K$, $\mathcal A_K(D)=\{\alpha: v_P(\alpha_P)\ge -D(P)\ \forall P\}$ its filtration and $\widetilde K$ the principal adeles (file `RiemannRoch_Adeles`). Let $\ell(D)=\dim_k\mathcal L(D)$, and let $g$, $\delta(D)=\deg D+1-\ell(D)$ and $i(D)=\ell(D)-\deg D-1+g$ be the genus, the defect and the index of speciality (file `RiemannRoch_GenusCharts`).
--
--   This file is the **fourth of four consecutive parts** of the source module `RiemannRoch/AdeleSpace/FilterChain.lean`, which was cut into quarters for publication (the other parts are `RiemannRoch_FilterChain1`, `RiemannRoch_FilterChain2`, `RiemannRoch_FilterChain3`). It is followed by the module `RiemannRoch/Genus/AdeleQuotient.lean`. It introduces:
--
--   1. the top submodule of $\mathcal A_K$;
--   2. for an adele $\alpha$, the finite set of places where $\alpha_P$ is not integral, and the divisor $D_\alpha$ with $D_\alpha(P)=-v_P(\alpha_P)$ at these places and $0$ elsewhere, so that $\alpha\in\mathcal A_K(D_\alpha)$.
--
--   It also contains the remaining dimension formulas of the adelic method: for $D\le D'$,
--   $$\dim_k\frac{\mathcal A_K(D')+\widetilde K}{\mathcal A_K(D)+\widetilde K}=\big(\deg D'-\ell(D')\big)-\big(\deg D-\ell(D)\big),$$
--   the identity $\mathcal A_K(D')\cap(\mathcal A_K(D)+\widetilde K)=\mathcal L(D')+\mathcal A_K(D)$ (with $\mathcal L(D')$ embedded diagonally), and $\mathcal A_K(D')+\widetilde K=\mathcal A_K(D)+\widetilde K$ when this sandwich rank is zero. When $k$ is the full constant field: every adele lies in some $\mathcal A_K(D)$; if $\delta(D)=g$ then $\delta(D')=g$ for every $D'\ge D$ and $\mathcal A_K=\mathcal A_K(D)+\widetilde K$; and finally, for every divisor $D$,
--   $$\dim_k\mathcal A_K\big/\big(\mathcal A_K(D)+\widetilde K\big)=i(D).$$
--
--   This identification of the index of speciality with an adelic quotient is what allows $i(D)$ to be computed by Weil differentials, leading to the Riemann–Roch theorem. In the chain of definition files it imports `RiemannRoch_FilterChain3` and is imported by `RiemannRoch_WeilDifferentials`.
--
--   **Formalization Note** The function field is not constructed from $k$: $K$ is an arbitrary field carrying the instances `Algebra k[X] K`, `Algebra k⟮X⟯ K`, `IsScalarTower k[X] k⟮X⟯ K`, Mathlib's `FunctionField k K` (i.e. $K$ is finite-dimensional over $k(X)$) and `Algebra.IsSeparable k⟮X⟯ K`; when constants are needed, also `Algebra k K` with `IsScalarTower k k[X] K`. The second part (module `AdeleQuotient`) assumes `[IsFullConstantField k K]`. All divisors here are chart divisors (`DivisorA k K`); the dimensions are `Module.finrank k` of quotients of submodules of `AdeleSpace k K`, the displayed sandwich rank is `sandwichRank` of `RiemannRoch_Adeles`, and $D_\alpha$ is `divisorOfAdele` (defined with `WithZero.log` of the valuation, i.e. $-v_P(\alpha_P)$, where it exceeds $1$).
-- source:
--   H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Section 1.5: dimension of $(\mathcal A_F(B)+F)/(\mathcal A_F(A)+F)$ (cf. Lemma 1.5.3) and Theorem 1.5.4 ($i(A)=\dim_K\mathcal A_F/(\mathcal A_F(A)+F)$). Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/AdeleSpace/FilterChain.lean, https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/Genus/AdeleQuotient.lean

import Mathlib
import Definitions.Def_RiemannRoch_FilterChain3

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
theorem sandwich {D D' : DivisorA k K} (h : D ≤ D') :
    sandwichRank k K D D' h = deg k K D' - ell k K D' - (deg k K D - ell k K D) := by
  let p := adeleFilt k K D'
  let s := adeleFilt k K D
  let r := diagonalSubmodule k K
  let l := Submodule.map (diagonal k K) (RRspace k K D')
  let t := l ⊔ s
  have hs_le_p : s ≤ p := adeleFilt_mono k K h
  have hst : s ≤ t := le_sup_right
  have htp : t ≤ p := by
    rintro x hx
    rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
    rcases hy with ⟨f, hf, rfl⟩
    exact Submodule.add_mem p
      (by simpa [adeleFilt, memAdeleFilt, memRRspace, RRspace, diagonal, p] using hf) (hs_le_p hz)
  have hmod : p ⊓ (s + r) = s + p ⊓ r := by
    apply le_antisymm
    · rintro x ⟨hxp, hxsr⟩
      rcases Submodule.mem_sup.mp hxsr with ⟨a, has, y, hy, rfl⟩
      obtain ⟨f, rfl⟩ := LinearMap.mem_range.mp hy
      refine Submodule.mem_sup.mpr ⟨a, has, (diagonal k K f), ?_, rfl⟩
      exact Submodule.mem_inf.mpr
        ⟨(by simpa [sub_add_cancel] using Submodule.sub_mem p hxp (hs_le_p has)), hy⟩
    · rintro x hx
      rcases Submodule.mem_sup.mp hx with ⟨a, has, y, hy, rfl⟩
      rcases Submodule.mem_inf.mp hy with ⟨hyp, hyr⟩
      refine ⟨Submodule.add_mem p (hs_le_p has) hyp,
        Submodule.add_mem (s + r) (Submodule.mem_sup_left has) (Submodule.mem_sup_right hyr)⟩
  have hinter : p ⊓ (s + r) = t := by
    have hpr : p ⊓ r = l := adeleFilt_inf_diagonal k K D'
    calc p ⊓ (s + r) = s + (p ⊓ r) := hmod
      _ = s + l := by rw [hpr]
      _ = t := by simp [t, Submodule.add_eq_sup, sup_comm]
  letI : AddCommGroup ↥p := Submodule.addCommGroup _
  letI : Module k ↥p := Submodule.module _
  letI : AddCommGroup ↥(p + r) := Submodule.addCommGroup _
  letI : Module k ↥(p + r) := Submodule.module _
  let qp := Submodule.comap p.subtype s
  let qt := Submodule.comap p.subtype t
  have hqp : qp ≤ qt := Submodule.comap_mono hst
  have hpsum : p ⊔ (s + r) = p + r := by
    rw [← Submodule.add_eq_sup]
    apply le_antisymm
    · refine sup_le le_sup_left (add_le_add hs_le_p le_rfl)
    · intro x hx
      rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, rfl⟩
      have hb' : b ∈ s + r := Submodule.mem_sup_right hb
      exact Submodule.add_mem _ (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hb')
  haveI : AddCommGroup ↥(p ⊔ (s + r)) := Submodule.addCommGroup _
  haveI : Module k ↥(p ⊔ (s + r)) := Submodule.module _
  have e1 := LinearMap.quotientInfEquivSupQuotient p (s + r)
  have hsand :
      Module.finrank k (↥(p + r) ⧸ Submodule.comap (p + r).subtype (s + r)) =
        Module.finrank k (↥p ⧸ qt) := by
    have hinfl :
        Submodule.comap p.subtype p ⊓ Submodule.comap p.subtype (s + r) = qt := by
      rw [← Submodule.comap_inf, hinter]
    have hfin := e1.symm.finrank_eq
    rw [← hpsum.symm, hinfl] at hfin
    exact hfin
  have hE : IsEffective k K (D' - D) := (le_iff_sub_effective k K).mp h
  have e2 := Submodule.quotientQuotientEquivQuotient qp qt hqp
  have hdiv : D + (D' - D) = D' := by ext w; simp [sub_eq_add_neg]
  haveI : Module.Finite k (↥p ⧸ qp) :=
    finiteAdeleFiltDiff_quotient_add_eq k K (M := D) hdiv.symm hE
  have hsecond : Module.finrank k (Submodule.map qp.mkQ qt) = finrankRRspaceDiff k K D D' := by
    have hld : l ⊓ s = Submodule.map (diagonal k K) (RRspace k K D) := by
      refine Submodule.ext fun a => ⟨?_, ?_⟩
      · rintro ⟨hxl, hxs⟩
        rcases hxl with ⟨f, hf, rfl⟩
        refine ⟨f, fun v => ?_, rfl⟩
        have hxv := hxs v
        simpa [memRRspace, memAdeleFilt, placeValuation, diagonal, adeleFilt, s] using hxv
      · rintro ⟨f, hf, rfl⟩
        refine ⟨⟨f, RRspace_mono k K h hf, rfl⟩, fun v => ?_⟩
        simpa [memRRspace, memAdeleFilt, placeValuation, diagonal, adeleFilt, s] using hf v
    have hfin_map := finrank_map_comap_mkQ_eq_quotient k K hs_le_p htp hst
    let st := Submodule.comap t.subtype s
    let qpInQt := Submodule.comap qt.subtype qp
    letI : AddCommGroup ↥t := Submodule.addCommGroup _
    letI : Module k ↥t := Submodule.module _
    let eT := Submodule.comapSubtypeEquivOfLe htp
    have hmap : st.map (eT.symm : ↥t →ₗ[k] ↥qt) = qpInQt := by
      ext x
      simp [Submodule.mem_comap, st, qpInQt, qp, qt, eT]
    have eTS : ((↥t) ⧸ st) ≃ₗ[k] ((↥qt) ⧸ qpInQt) :=
      Submodule.Quotient.equiv st qpInQt eT.symm hmap
    have e3 := LinearMap.quotientInfEquivSupQuotient l s
    letI : AddCommGroup ↥(l ⊔ s) := Submodule.addCommGroup _
    letI : Module k ↥(l ⊔ s) := Submodule.module _
    letI : AddCommGroup ↥l := Submodule.addCommGroup _
    letI : Module k ↥l := Submodule.module _
    dsimp [finrankRRspaceDiff]
    calc
      Module.finrank k (Submodule.map qp.mkQ qt)
          = Module.finrank k (↥qt ⧸ Submodule.comap qt.subtype qp) := hfin_map
      _ = Module.finrank k (↥t ⧸ st) := eTS.finrank_eq.symm
      _ = Module.finrank k (↥(l ⊔ s) ⧸ Submodule.comap (l ⊔ s).subtype s) := rfl
      _ = Module.finrank k
          (↥l ⧸ (Submodule.comap l.subtype l ⊓ Submodule.comap l.subtype s)) :=
        e3.symm.finrank_eq
      _ = Module.finrank k
          ((RRspace k K D') ⧸ Submodule.comap (RRspace k K D').subtype (RRspace k K D)) := by
        let pR := RRspace k K D'
        let qR := Submodule.comap pR.subtype (RRspace k K D)
        let qInL : Submodule k ↥l :=
          Submodule.comap l.subtype (Submodule.map (diagonal k K) (RRspace k K D))
        let f' := (diagonal k K).comp pR.subtype
        have hf' : ∀ g, f' g ∈ l := fun g => Submodule.mem_map.mpr ⟨g, g.property, rfl⟩
        let f : pR →ₗ[k] l := f'.codRestrict l hf'
        have hf_ker : f.ker = ⊥ := by
          rw [eq_bot_iff]
          intro g hg
          apply Subtype.ext
          let w : PlaceA k K := Classical.choice (nonempty_placeA k K)
          have hfg := LinearMap.mem_ker.mp hg
          have hzero : (f g : AdeleSpace k K) = 0 := congrArg Subtype.val hfg
          have hz : ((f g : AdeleSpace k K).val : PlaceA k K → K) w = 0 := by
            rw [hzero]
            simp
          simpa [f, f', diagonal, LinearMap.comp_apply, Submodule.coe_subtype] using hz
        have hf_inj : Function.Injective f := by
          intro g₁ g₂ hfg
          have hmem : g₁ - g₂ ∈ f.ker := by
            rw [LinearMap.mem_ker, map_sub, hfg, sub_self]
          rw [hf_ker] at hmem
          exact sub_eq_zero.mp hmem
        have hf_surj : Function.Surjective f := by
          rintro ⟨a, g, hg, rfl⟩
          exact ⟨⟨g, hg⟩, rfl⟩
        let eL : pR ≃ₗ[k] l := LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
        have hmap : qR.map f = qInL := by
          ext x
          simp only [Submodule.mem_map, Submodule.mem_comap, qR, qInL, l]
          constructor
          · rintro ⟨g, hg, heq⟩
            refine ⟨g.val, ?_, ?_⟩
            · simpa [mem_RRspace_iff] using hg
            · rw [← heq]
              rfl
          · rintro ⟨y, hy, hxy⟩
            refine ⟨⟨y, RRspace_mono k K h hy⟩, ?_, ?_⟩
            · simpa [mem_RRspace_iff] using hy
            · apply Subtype.ext
              exact hxy
        have eQuot : (pR ⧸ qR) ≃ₗ[k] (l ⧸ qInL) := Submodule.Quotient.equiv qR qInL eL hmap
        rw [← Submodule.comap_inf, hld, eQuot.finrank_eq]
  have hsplit :
      Module.finrank k (↥p ⧸ qt) =
        finrankAdeleFiltDiff k K D D' - finrankRRspaceDiff k K D D' := by
    unfold finrankAdeleFiltDiff
    have hfin := finrank_adeleFilt_quotient k K h
    have hle' : finrankRRspaceDiff k K D D' ≤ finrankAdeleFiltDiff k K D D' := by
      rw [hfin]
      exact finrank_RRspace_quotient_le k K h
    have hadd := Submodule.finrank_quotient_add_finrank (Submodule.map qp.mkQ qt)
    rw [e2.finrank_eq, hsecond] at hadd
    exact (Nat.sub_eq_of_eq_add hadd.symm).symm
  have hfin := finrank_adeleFilt_quotient k K h
  have hdeg : 0 ≤ deg k K (D' - D) := deg_nonneg k K hE
  have htoNat : ((deg k K (D' - D)).toNat : ℤ) = deg k K (D' - D) :=
    Int.toNat_of_nonneg hdeg
  have hrr := finrankRRspaceDiff_add_ell k K h
  have hle : finrankRRspaceDiff k K D D' ≤ finrankAdeleFiltDiff k K D D' := by
    rw [hfin]
    exact finrank_RRspace_quotient_le k K h
  dsimp only [sandwichRank]
  have hmain :
      (Int.ofNat (Module.finrank k (↥(p + r) ⧸ Submodule.comap (p + r).subtype (s + r)))) =
        (finrankAdeleFiltDiff k K D D' - finrankRRspaceDiff k K D D') := by
    rw [hsand, hsplit]
    simp only [Int.ofNat_eq_natCast, Nat.cast_sub hle]
  rw [hmain, hfin, htoNat]
  have hrrZ : (finrankRRspaceDiff k K D D' : ℤ) = ell k K D' - ell k K D := by
    rw [finrankRRspaceDiff, ell, ell,
      ← (Submodule.comapSubtypeEquivOfLe (RRspace_mono k K h)).finrank_eq] at hrr ⊢
    omega
  rw [hrrZ, deg_sub k K D' D]
  omega
theorem sandwichDiagonal_inter {D D' : DivisorA k K} (h : D ≤ D') :
    adeleFilt k K D' ⊓ (adeleFilt k K D + diagonalSubmodule k K) =
      Submodule.map (diagonal k K) (RRspace k K D') ⊔ adeleFilt k K D := by
  let p := adeleFilt k K D'
  let s := adeleFilt k K D
  let r := diagonalSubmodule k K
  let l := Submodule.map (diagonal k K) (RRspace k K D')
  let t := l ⊔ s
  have hs_le_p : s ≤ p := adeleFilt_mono k K h
  have hmod : p ⊓ (s + r) = s + p ⊓ r := by
    apply le_antisymm
    · rintro x ⟨hxp, hxsr⟩
      rcases Submodule.mem_sup.mp hxsr with ⟨a, has, y, hy, rfl⟩
      obtain ⟨f, rfl⟩ := LinearMap.mem_range.mp hy
      refine Submodule.mem_sup.mpr ⟨a, has, (diagonal k K f), ?_, rfl⟩
      exact Submodule.mem_inf.mpr
        ⟨(by simpa [sub_add_cancel] using Submodule.sub_mem p hxp (hs_le_p has)), hy⟩
    · rintro x hx
      rcases Submodule.mem_sup.mp hx with ⟨a, has, y, hy, rfl⟩
      rcases Submodule.mem_inf.mp hy with ⟨hyp, hyr⟩
      refine ⟨Submodule.add_mem p (hs_le_p has) hyp,
        Submodule.add_mem (s + r) (Submodule.mem_sup_left has) (Submodule.mem_sup_right hyr)⟩
  have hpr : p ⊓ r = l := adeleFilt_inf_diagonal k K D'
  calc
    p ⊓ (s + r) = s + p ⊓ r := hmod
    _ = s + l := by rw [hpr]
    _ = t := by simp [t, Submodule.add_eq_sup, sup_comm]
theorem sandwichDiagonalSubmodule_eq_of_rank_zero {D D' : DivisorA k K} (hle : D ≤ D')
    (h0 : sandwichRank k K D D' hle = 0) :
    adeleFilt k K D' + diagonalSubmodule k K = adeleFilt k K D + diagonalSubmodule k K := by
  let p := adeleFilt k K D'
  let s := adeleFilt k K D
  let r := diagonalSubmodule k K
  let t := Submodule.map (diagonal k K) (RRspace k K D') ⊔ s
  let qp := Submodule.comap p.subtype s
  let qt := Submodule.comap p.subtype t
  have hqp_le : qp ≤ qt := Submodule.comap_mono le_sup_right
  have hE : IsEffective k K (D' - D) := (le_iff_sub_effective k K).mp hle
  have hdiv : D + (D' - D) = D' := by abel
  haveI : Module.Finite k (↥p ⧸ qp) :=
    finiteAdeleFiltDiff_quotient_add_eq k K (M := D) hdiv.symm hE
  have htp : t ≤ p := by
    rintro x hx
    rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
    rcases hy with ⟨f, hf, rfl⟩
    exact Submodule.add_mem p
      (by simpa [adeleFilt, memAdeleFilt, memRRspace, RRspace, diagonal, p] using hf)
      (adeleFilt_mono k K hle hz)
  letI : AddCommGroup ↥p := Submodule.addCommGroup _
  letI : Module k ↥p := Submodule.module _
  letI : AddCommGroup ↥(p + r) := Submodule.addCommGroup _
  letI : Module k ↥(p + r) := Submodule.module _
  letI : AddCommGroup ↥(adeleFilt k K D' + diagonalSubmodule k K) := Submodule.addCommGroup _
  letI : Module k ↥(adeleFilt k K D' + diagonalSubmodule k K) := Submodule.module _
  have hfin_qt : Module.finrank k (↥p ⧸ qt) = 0 := by
    have hfin_sandwich :
        Module.finrank k
            (↥(adeleFilt k K D' + diagonalSubmodule k K) ⧸
              Submodule.comap (adeleFilt k K D' + diagonalSubmodule k K).subtype
                (adeleFilt k K D + diagonalSubmodule k K)) = 0 :=
      Int.ofNat_eq_zero.mp (by simpa [sandwichRank] using h0)
    have hinter := sandwichDiagonal_inter k K hle
    have hinfl : Submodule.comap p.subtype p ⊓ Submodule.comap p.subtype (s + r) = qt := by
      rw [← Submodule.comap_inf, hinter]
    have hpsum : p ⊔ (s + r) = p + r := by
      rw [← Submodule.add_eq_sup]
      apply le_antisymm
      · refine sup_le le_sup_left (add_le_add (adeleFilt_mono k K hle) le_rfl)
      · intro x hx
        rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, rfl⟩
        have hb' : b ∈ s + r := Submodule.mem_sup_right hb
        exact Submodule.add_mem _ (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hb')
    have hsand :=
      (LinearMap.quotientInfEquivSupQuotient p (s + r)).symm.finrank_eq
    rw [hpsum, hinfl] at hsand
    exact hsand.symm.trans hfin_sandwich
  haveI : Module.Finite k (↥p ⧸ qt) :=
    Module.Finite.equiv (Submodule.quotientQuotientEquivQuotient qp qt hqp_le)
  have hrk : Module.rank k (↥p ⧸ qt) = 0 := by
    rw [← Module.finrank_eq_rank, hfin_qt, Nat.cast_zero]
  have hsub : Subsingleton (↥p ⧸ qt) := rank_zero_iff.mp hrk
  have htopqt : qt = ⊤ := Submodule.Quotient.subsingleton_iff.mp hsub
  have hp_le_t : p ≤ t := Submodule.comap_subtype_eq_top.mp htopqt
  have hp_eq_t : p = t := le_antisymm hp_le_t htp
  have hinter := sandwichDiagonal_inter k K hle
  have hp_le_sr : p ≤ s + r := by
    have h := inf_le_right (a := p) (b := s + r)
    rw [hinter] at h
    exact hp_eq_t.symm ▸ h
  have hsr_le_pr : s + r ≤ p + r := add_le_add (adeleFilt_mono k K hle) le_rfl
  have hpr_le_sr : p + r ≤ s + r := by
    intro x hx
    rcases Submodule.mem_sup.mp hx with ⟨a, hap, y, hyr, rfl⟩
    rcases Submodule.mem_sup.mp (hp_le_sr hap) with ⟨b, hbs, w, hwr, hbc⟩
    refine Submodule.mem_sup.mpr
      ⟨b, hbs, w + y, Submodule.add_mem r hwr hyr, by rw [← hbc, add_assoc]⟩
  exact le_antisymm hpr_le_sr hsr_le_pr
end FunctionField.Chart
end
end
end

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
variable [IsFullConstantField k K]
local instance instDecidableEqPlaceAAdeleQuotient : DecidableEq (PlaceA k K) := Classical.decEq _
def topAdeleSubmodule : Submodule k (AdeleSpace k K) := ⊤
omit [IsFullConstantField k K] in
theorem exceptionalFinite (α : AdeleSpace k K) :
    {v : PlaceA k K | ¬placeValuation k K v (α.val v) ≤ 1}.Finite :=
  (Filter.eventually_cofinite.mp α.property).subset (by
    intro v hv
    change α.val v ∉ placeValuationSubring k K v
    simpa [placeValuationSubring, Valuation.mem_valuationSubring_iff] using hv)
def exceptionalPlaces (α : AdeleSpace k K) : Finset (PlaceA k K) :=
  (exceptionalFinite k K α).toFinset
noncomputable def divisorOfAdele (α : AdeleSpace k K) : DivisorA k K :=
  Finsupp.onFinset (exceptionalPlaces k K α)
    (fun v =>
      if 1 < placeValuation k K v (α.val v) then
        WithZero.log (placeValuation k K v (α.val v))
      else 0)
    (by
      intro v hvne
      by_cases hlt : 1 < placeValuation k K v (α.val v)
      · dsimp [exceptionalPlaces]
        exact (exceptionalFinite k K α).mem_toFinset.mpr (not_le.mpr hlt)
      · simp [hlt] at hvne)
omit [IsFullConstantField k K] in
theorem mem_adeleFilt_divisorOfAdele (α : AdeleSpace k K) :
    α ∈ adeleFilt k K (divisorOfAdele k K α) := by
  intro v
  show placeValuation k K v (α.val v) ≤ WithZero.exp ((divisorOfAdele k K α) v)
  dsimp only [divisorOfAdele]
  rw [Finsupp.onFinset_apply]
  by_cases hv : placeValuation k K v (α.val v) ≤ 1
  · have hnotlt : ¬1 < placeValuation k K v (α.val v) := not_lt.mpr hv
    have hnotmem : v ∉ exceptionalPlaces k K α := by
      intro hmem
      have hgt := (exceptionalFinite k K α).mem_toFinset.mp (by
        dsimp [exceptionalPlaces] at hmem ⊢
        exact hmem)
      have hnotle : ¬placeValuation k K v (α.val v) ≤ 1 := by simpa using hgt
      exact absurd hv hnotle
    split_ifs with hlt
    · exfalso
      exact hnotlt hlt
    · simpa [WithZero.exp_zero] using hv
  · have hlt : 1 < placeValuation k K v (α.val v) := not_le.mp hv
    have hmem : v ∈ exceptionalPlaces k K α := by
      dsimp [exceptionalPlaces]
      exact (exceptionalFinite k K α).mem_toFinset.mpr (not_le.mpr hlt)
    have hval : placeValuation k K v (α.val v) ≠ 0 := ne_of_gt (zero_lt_one.trans hlt)
    split_ifs with hlt'
    · simp [WithZero.exp_log hval]
    · exfalso
      exact hlt' hlt
omit [IsFullConstantField k K] in
theorem exists_adeleFilt_mem (α : AdeleSpace k K) :
    ∃ D : DivisorA k K, α ∈ adeleFilt k K D :=
  ⟨divisorOfAdele k K α, mem_adeleFilt_divisorOfAdele k K α⟩
theorem defect_eq_genus_of_ge {D D' : DivisorA k K} (hle : D ≤ D')
    (hD : defect k K D = genus k K) : defect k K D' = genus k K := by
  have hle' : defect k K D ≤ defect k K D' := defect_mono' (k := k) (K := K) hle
  have hgen : defect k K D' ≤ genus k K := defect_le k K D'
  omega
theorem sandwichRank_eq_zero_of_defect_eq {D D' : DivisorA k K} (hle : D ≤ D')
    (hD : defect k K D = genus k K) :
    sandwichRank k K D D' hle = 0 := by
  have hD' : defect k K D' = genus k K := defect_eq_genus_of_ge (k := k) (K := K) hle hD
  have hs := sandwich (k := k) (K := K) hle
  dsimp only [defect] at hD hD' ⊢
  rw [hs]
  omega
omit [IsFullConstantField k K] in
theorem adeleFilt_add_diagonal_eq_of_sandwich_zero {D D' : DivisorA k K} (hle : D ≤ D')
    (h0 : sandwichRank k K D D' hle = 0) :
    adeleFilt k K D' + diagonalSubmodule k K = adeleFilt k K D + diagonalSubmodule k K :=
  sandwichDiagonalSubmodule_eq_of_rank_zero (k := k) (K := K) hle h0
theorem adeleSubmodule_top_eq_adeleFilt_add_diagonal {D : DivisorA k K}
    (hD : defect k K D = genus k K) :
    topAdeleSubmodule k K = adeleFilt k K D + diagonalSubmodule k K := by
  apply le_antisymm
  · intro α _
    obtain ⟨Dα, hDα⟩ := exists_adeleFilt_mem (k := k) (K := K) α
    let D' := D ⊔ Dα
    have hD' : defect k K D' = genus k K :=
      defect_eq_genus_of_ge (k := k) (K := K) (le_sup_left (a := D) (b := Dα)) hD
    have h0 := sandwichRank_eq_zero_of_defect_eq (k := k) (K := K) (D := D) (D' := D')
      (le_sup_left (a := D) (b := Dα)) hD
    have heq := adeleFilt_add_diagonal_eq_of_sandwich_zero (k := k) (K := K) (D := D) (D' := D')
      (le_sup_left (a := D) (b := Dα)) h0
    have hmem : α ∈ adeleFilt k K D' + diagonalSubmodule k K :=
      Submodule.mem_sup_left (adeleFilt_mono (k := k) (K := K) le_sup_right hDα)
    rw [heq] at hmem
    exact hmem
  · exact le_top
omit [IsFullConstantField k K] in
theorem finrankAdeleQuotient_eq_sandwichRank {D D' : DivisorA k K} (hle : D ≤ D')
    (hfull : topAdeleSubmodule k K = adeleFilt k K D' + diagonalSubmodule k K) :
    finrankAdeleQuotient k K D = (sandwichRank k K D D' hle).toNat := by
  classical
  let ssum := adeleFilt k K D + diagonalSubmodule k K
  let topMod := topAdeleSubmodule k K
  letI : AddCommGroup ↥topMod := Submodule.addCommGroup _
  letI : Module k ↥topMod := Submodule.module _
  let p := Submodule.comap topMod.subtype ssum
  let e : ↥topMod ≃ₗ[k] AdeleSpace k K :=
    Submodule.topEquiv (R := k) (M := AdeleSpace k K)
  have hmap := Submodule.map_comap_subtype (p := topMod) (p' := ssum)
  have heq_lm : (e : ↥topMod →ₗ[k] AdeleSpace k K) = topMod.subtype := by
    apply LinearMap.ext
    rintro ⟨f, _⟩
    apply Subtype.ext
    funext v
    rfl
  have hf : p.map (e : ↥topMod →ₗ[k] AdeleSpace k K) = ssum := by
    rw [show p.map (e : ↥topMod →ₗ[k] AdeleSpace k K) = p.map topMod.subtype from by
      rw [heq_lm], hmap, inf_eq_right]
    exact le_top
  dsimp only [finrankAdeleQuotient, sandwichRank, ssum]
  rw [← (Submodule.Quotient.equiv p ssum e hf).finrank_eq, hfull.symm]
  simp only [topMod, topAdeleSubmodule, ssum, p]
  simp
theorem finrank_adele_quotient (D : DivisorA k K) :
    finrankAdeleQuotient k K D = indexOfSpecialty k K D := by
  obtain ⟨D₁, hD₁⟩ := exists_defect_eq (k := k) (K := K)
  let D' := D ⊔ D₁
  have hle : D ≤ D' := le_sup_left (a := D) (b := D₁)
  have hD' : defect k K D' = genus k K :=
    defect_eq_genus_of_ge (k := k) (K := K) (le_sup_right (a := D) (b := D₁)) hD₁
  have hfull := adeleSubmodule_top_eq_adeleFilt_add_diagonal (k := k) (K := K) hD'
  have hsand := sandwich (k := k) (K := K) hle
  have hfin := finrankAdeleQuotient_eq_sandwichRank (k := k) (K := K) hle hfull
  have hdef : sandwichRank k K D D' hle = defect k K D' - defect k K D := by
    dsimp only [defect]
    rw [hsand]
    omega
  have hidx : (indexOfSpecialty k K D : ℤ) = genus k K - defect k K D := by
    have := indexOfSpecialty_eq (k := k) (K := K) D
    dsimp only [defect] at this ⊢
    omega
  have hD'gen : defect k K D' = genus k K := hD'
  calc finrankAdeleQuotient k K D
      _ = (sandwichRank k K D D' hle).toNat := hfin
      _ = (genus k K - defect k K D).toNat := by rw [hdef, hD'gen]
      _ = indexOfSpecialty k K D := by
        rw [← hidx]
        simp only [Int.toNat_natCast]
end FunctionField.Chart
end
end
end


