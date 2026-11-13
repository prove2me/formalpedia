-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03h_Thm38
-- name    : OddOrder_BG_Ch1_Preliminary_S03h_Thm38
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:03:38.933417+00:00
-- url     : https://prove2.me/theorems/20e287aa-f052-492d-b5b9-413edb65592d
-- title:
--   BG Theorem 3.8: $[K,R]\subseteq F(K)$ for a coprime action
-- statement:
--   Formalizes Theorem 3.8 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §3: let $G=KR$ be solvable of odd order with $K\trianglelefteq G$, $(|R|,|K|)=1$, $C_K(x)=C_K(R)$ for all $x\in R^\#$ and $C_{F(K)}(R)=1$; then $[K,R]\subseteq F(K)$. This is the §3 prerequisite of BG Theorem 15.2. The file includes the reduced case, the base case of the induction, the coprime branch of the chief-factor analysis and BG Proposition 1.5(d).
--
--   Main declarations: `commutator_le_chiefFactorCentralizer_via_thm34` (Coprime (`q ≠ p`) branch of BG Theorem 3.8's chief-factor analysis (leaf B)); `commutator_le_chiefFactorCentralizer_dichotomy_thm38`; `commutator_le_fitting_of_reduced`; `commutator_le_fitting_of_centralizes_fittingQuotient`; and 4 more.
--
--   The bundle also proves 14 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S03h_Thm38.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S03h_Thm38.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03c_Thm37
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03d_Thm34
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S06_Additional

namespace OddOrder.BG.Ch1.S03h

open scoped Pointwise

/-- **Abstract `q ≠ p` core for BG Theorem 3.8** (the `thm34`-analog of
`S03c.kernel_acts_trivially_of_coprime_fixedPointFree`).  Let `G = KR` be a finite solvable group
of odd order acting on a finite abelian group `M` that is an `𝔽_s`-vector space, with `K ⊴ G`
complementing the prime-order `R`, with `(|K|, |R|) = 1` and `s ∤ |G|`.  If `R` acts in a
fixed-point-free manner on `M` (`C_M(R) = 1`), then the commutator `⁅R, K⁆` acts trivially on `M`.

Proof: present the action as a representation `ρ : Representation (ZMod s) G (Additive M)`
(`Representation.ofDistribMulAction`); the fixed-point-freeness `C_M(R) = 1` becomes
`C_{Additive M}(R) = 0`, and **BG Theorem 3.4** (`S03d.thm34`) gives `ρ g = 1` for every
`g ∈ ⁅R, K⁆`, i.e. `g` acts trivially.  Mirrors
`S03c.kernel_acts_trivially_of_coprime_fixedPointFree` with the Frobenius input replaced by the
`(KR, R prime)` Theorem 3.4 hypotheses. -/
theorem commutator_acts_trivially_via_thm34 {s : ℕ} [Fact s.Prime]
    {G M : Type*} [Finite G] [Group G] [Group.IsSolvable G] [CommGroup M] [Finite M]
    [MulDistribMulAction G M] [Module (ZMod s) (Additive M)]
    {K R : Subgroup G} [K.Normal]
    (hcompl : K.IsComplement' R)
    (hHall : Nat.Coprime (Nat.card ↥K) (Nat.card ↥R))
    (hRp : ∃ p : ℕ, p.Prime ∧ Nat.card ↥R = p)
    (hodd : Odd (Nat.card G))
    (hchar : ¬ s ∣ Nat.card G)
    (hFPF : ∀ m : M, (∀ r : R, (r : G) • m = m) → m = 1) :
    ∀ x ∈ ⁅R, K⁆, ∀ m : M, (x : G) • m = m := by
  set ρ : Representation (ZMod s) G (Additive M) :=
    Representation.ofDistribMulAction (ZMod s) G (Additive M) with hρ
  have hρ_apply : ∀ (g : G) (a : Additive M), ρ g a = g • a := by
    intro g a; rw [hρ]; rfl
  have hchar' : (Nat.card G : ZMod s) ≠ 0 :=
    fun h => hchar ((ZMod.natCast_eq_zero_iff _ _).1 h)
  have : FiniteDimensional (ZMod s) (Additive M) := Module.Finite.of_finite
  -- `C_M(R) = 1` ⟹ the representation's `R`-invariants are `0`.
  have hCR : ∀ v : Additive M, (∀ r : R, ρ (r : G) v = v) → v = 0 := by
    intro v hv
    have hfix : ∀ r : R, (r : G) • Additive.toMul v = Additive.toMul v := by
      intro r
      have h := hv r
      rw [hρ_apply] at h
      exact congrArg Additive.toMul h
    have h0 : Additive.ofMul (Additive.toMul v) = Additive.ofMul (1 : M) :=
      congrArg Additive.ofMul (hFPF _ hfix)
    simpa using h0
  -- BG Theorem 3.4: every `g ∈ ⁅R, K⁆` acts as the identity on `M`.
  have hKtriv := S03d.thm34 ρ K R hcompl hHall hRp hodd hchar' hCR
  intro x hx m
  have happ : ρ (x : G) (Additive.ofMul m) = Additive.ofMul m := by
    rw [hKtriv x hx]; rfl
  rw [hρ_apply] at happ
  exact congrArg Additive.toMul happ

open OddOrder.GroupTheory in
/-- **Coprime (`q ≠ p`) branch of BG Theorem 3.8's chief-factor analysis** (leaf B).  For a
`G`-chief factor `X/Y` elementary abelian of prime `s`, with `L ⊴ G` centralizing `X/Y` and `R`
acting fixed-point-freely on `X/Y`, if `G = KR` modulo `L` satisfies the Theorem 3.4 hypotheses
(`K/L` complements the prime-order `R/L`, coprime orders, `G/L` odd, `s ∤ |G/L|`), then `⁅R, K⁆`
centralizes `X/Y` (i.e. `⁅R, K⁆ ≤ chiefFactorCentralizer X Y`).  The `q ≠ p` analog of
`S03c.coprime_kernel_le_chiefFactorCentralizer`, with the Frobenius argument replaced by Theorem
3.4 (`commutator_acts_trivially_via_thm34`).  Note the conclusion is on `⁅R, K⁆` (not `K`):
Theorem 3.4 only controls the commutator. -/
theorem commutator_le_chiefFactorCentralizer_via_thm34
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] {K R X Y : Subgroup G}
    [K.Normal] [X.Normal] [Y.Normal] {s : ℕ} [Fact s.Prime]
    (hVelem : IsElementaryAbelian s (↥X ⧸ Y.subgroupOf X))
    {L : Subgroup G} [L.Normal] (hLcent : L ≤ chiefFactorCentralizer X Y)
    (hcompl : (K.map (QuotientGroup.mk' L)).IsComplement' (R.map (QuotientGroup.mk' L)))
    (hHall : Nat.Coprime (Nat.card ↥(K.map (QuotientGroup.mk' L)))
      (Nat.card ↥(R.map (QuotientGroup.mk' L))))
    (hRp : ∃ p : ℕ, p.Prime ∧ Nat.card ↥(R.map (QuotientGroup.mk' L)) = p)
    (hodd : Odd (Nat.card (G ⧸ L)))
    (hchar : ¬ s ∣ Nat.card (G ⧸ L))
    (hFPF : letI := S03c.chiefFactorConjAction X Y
            ∀ v : ↥X ⧸ Y.subgroupOf X, (∀ r : R, (r : G) • v = v) → v = 1) :
    ⁅R, K⁆ ≤ chiefFactorCentralizer X Y := by
  have : NeZero s := ⟨(Fact.out : s.Prime).ne_zero⟩
  have : Group.IsSolvable (G ⧸ L) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective L)
  have : (K.map (QuotientGroup.mk' L)).Normal :=
    (inferInstance : K.Normal).map (QuotientGroup.mk' L) (QuotientGroup.mk'_surjective L)
  let : CommGroup (↥X ⧸ Y.subgroupOf X) :=
    { (inferInstance : Group (↥X ⧸ Y.subgroupOf X)) with mul_comm := hVelem.comm }
  let := hVelem.zmodModule
  let := S03c.chiefFactorConjAction X Y
  have hL : ∀ l : G, l ∈ L → ∀ v : ↥X ⧸ Y.subgroupOf X, l • v = v := by
    intro l hl v
    exact (S03c.chiefFactorConjAction_smul_eq_self_iff_mem l).mpr (hLcent hl) v
  let := mulDistribMulActionQuotientOfTrivial L hL
  have hFPF' : ∀ v : ↥X ⧸ Y.subgroupOf X,
      (∀ r : R.map (QuotientGroup.mk' L), (r : G ⧸ L) • v = v) → v = 1 := by
    intro v hv
    refine hFPF v (fun r => ?_)
    rw [← mulDistribMulActionQuotientOfTrivial_smul_mk hL (r : G) v]
    exact hv ⟨QuotientGroup.mk' L (r : G), ⟨r, r.2, rfl⟩⟩
  have hKtriv := commutator_acts_trivially_via_thm34 hcompl hHall hRp hodd hchar hFPF'
  intro x hx
  refine (S03c.chiefFactorConjAction_smul_eq_self_iff_mem x).mp (fun v => ?_)
  rw [← mulDistribMulActionQuotientOfTrivial_smul_mk hL (x : G) v]
  have hxmem : QuotientGroup.mk' L x ∈
      ⁅R.map (QuotientGroup.mk' L), K.map (QuotientGroup.mk' L)⁆ := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.mem_map_of_mem _ hx
  exact hKtriv (QuotientGroup.mk' L x) hxmem v

/-- **Fixed-point-freeness from condition (3) of BG Theorem 3.8** (the `hFPF` input to
`commutator_le_chiefFactorCentralizer_via_thm34`).  The `thm34`-analog of
`S03c.chiefFactor_fixedPointFree`: instead of a Frobenius structure, the fixed-point-freeness comes
from condition (3) `C_{F(K)}(R) = 1` (`hC3`).  For a chief factor `X/Y` with `X ⊆ F(K)` and `R` of
order coprime to `|K|`, `R` acts fixed-point-freely on `X/Y` (via `chiefFactorConjAction`).

Proof (mirrors `S03c.chiefFactor_fixedPointFree`): an `R`-fixed coset of `X/Y` lifts (coprime
action, `coprime_fixedPoints_quotient_of_coprime_normal`) to an `R`-fixed `c ∈ X ⊆ F(K)`; being
`R`-fixed means `c ∈ C_G(R)`, so `c ∈ C_{F(K)}(R) = 1` (`hC3`), whence `c = 1` and the coset is
trivial.  `F(K)` is written `(fitting ↥K).map K.subtype` (its `Ch2.S08.fittingInG` form would import
downstream into `Ch1`). -/
theorem chiefFactor_fixedPointFree_of_centralizer_fitting_eq_bot
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] {K R X Y : Subgroup G}
    [X.Normal] [Y.Normal]
    (hXF : X ≤ (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype)
    (hXK : X ≤ K) (hcop : Nat.Coprime (Nat.card ↥R) (Nat.card ↥K))
    (hC3 : Subgroup.centralizer (R : Set G) ⊓
      (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype = ⊥) :
    letI := S03c.chiefFactorConjAction X Y
    ∀ v : ↥X ⧸ Y.subgroupOf X, (∀ r : R, (r : G) • v = v) → v = 1 := by
  let := S03c.chiefFactorConjAction X Y
  set ψ : ↥R →* MulAut G := MulAut.conj.comp R.subtype with hψ
  have hXinv : OddOrder.Isaacs.Ch03.IsAInvariant ψ X :=
    fun a => Subgroup.Normal.conj_smul_eq_self (a : G) X
  have hYinv : OddOrder.Isaacs.Ch03.IsAInvariant ψ Y :=
    fun a => Subgroup.Normal.conj_smul_eq_self (a : G) Y
  have hN_inv : OddOrder.Isaacs.Ch03.IsAInvariant hXinv.restrict (Y.subgroupOf X) :=
    hXinv.subgroupOf hYinv
  have hcopX : Nat.Coprime (Nat.card ↥R) (Nat.card ↥X) :=
    hcop.coprime_dvd_right (Subgroup.card_dvd_of_le hXK)
  have hCop : Nat.Coprime (Nat.card ↥R) (Nat.card ↥(Y.subgroupOf X)) :=
    hcopX.coprime_dvd_right (Subgroup.card_subgroup_dvd_card (Y.subgroupOf X))
  have hSolv : Group.IsSolvable ↥R ∨ Group.IsSolvable ↥(Y.subgroupOf X) := Or.inr inferInstance
  have hrestrict : ∀ (a : ↥R) (x : ↥X),
      (hXinv.restrict a) x = ConjAct.toConjAct (a : G) • x := fun _ _ => rfl
  intro v hv
  induction v using QuotientGroup.induction_on with
  | _ x =>
    have hgfix : ∀ a : ↥R, ∃ n ∈ Y.subgroupOf X, (hXinv.restrict a) x = x * n := by
      intro a
      have hva := hv a
      rw [S03c.chiefFactorConjAction_smul_mk, QuotientGroup.eq] at hva
      refine ⟨x⁻¹ * (hXinv.restrict a) x, ?_, by group⟩
      rw [hrestrict]
      simpa using (Y.subgroupOf X).inv_mem hva
    obtain ⟨c, hc_fix, n, hn, hcn⟩ :=
      OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient_of_coprime_normal hCop hSolv hN_inv hgfix
    have hc_one : (c : G) = 1 := by
      have hcF : (c : G) ∈ (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype := hXF c.2
      have hcR : (c : G) ∈ Subgroup.centralizer (R : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        have hcr : ConjAct.toConjAct r • (c : ↥X) = c := by
          rw [← hrestrict ⟨r, hr⟩ c]; exact hc_fix ⟨r, hr⟩
        have hval : ConjAct.toConjAct r • (c : G) = (c : G) := congrArg Subtype.val hcr
        rw [ConjAct.toConjAct_smul] at hval
        -- `r * c * r⁻¹ = c` ⟹ `r * c = c * r`
        rw [mul_inv_eq_iff_eq_mul] at hval
        exact hval
      have hmem : (c : G) ∈ Subgroup.centralizer (R : Set G) ⊓
          (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype := ⟨hcR, hcF⟩
      rw [hC3, Subgroup.mem_bot] at hmem
      exact hmem
    have hc1 : c = 1 := Subtype.ext (by simpa using hc_one)
    have hx_eq : x = n⁻¹ := by
      rw [hc1] at hcn; rw [eq_comm, mul_eq_one_iff_eq_inv] at hcn; exact hcn
    rw [QuotientGroup.eq_one_iff, hx_eq]
    exact (Y.subgroupOf X).inv_mem hn

open OddOrder.GroupTheory in
/-- **Per-factor dichotomy for BG Theorem 3.8** (`thm34`-analog of
`S03c.kernel_le_chiefFactorCentralizer_dichotomy`).  For a `G`-chief factor `X/Y` (`X ⊆ K`)
elementary abelian of prime `s`, with `L ⊴ G` centralizing `X/Y`, `K/L` a `q`-group, `R` acting
fixed-point-freely on `X/Y`, and the `G/L = (K/L)(R/L)` Theorem 3.4 data, the commutator `⁅R, K⁆`
centralizes `X/Y`.

* `s = q`: `K/L` is an `s`-group, so `S03c.samePrime_kernel_le_chiefFactorCentralizer` gives
  `K ≤ chiefFactorCentralizer`, hence `⁅R, K⁆ ≤ K ≤ chiefFactorCentralizer`.
* `s ≠ q`: `commutator_le_chiefFactorCentralizer_via_thm34` (leaf B). -/
theorem commutator_le_chiefFactorCentralizer_dichotomy_thm38
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] {K R X Y : Subgroup G}
    [K.Normal] [X.Normal] [Y.Normal] {s q : ℕ} [Fact s.Prime] [Fact q.Prime]
    (hChief : IsChiefFactor X Y)
    (hVelem : IsElementaryAbelian s (↥X ⧸ Y.subgroupOf X))
    {L : Subgroup G} [L.Normal] (hLcent : L ≤ chiefFactorCentralizer X Y)
    (hKbar : IsPGroup q (K.map (QuotientGroup.mk' L)))
    (hcompl : (K.map (QuotientGroup.mk' L)).IsComplement' (R.map (QuotientGroup.mk' L)))
    (hHall : Nat.Coprime (Nat.card ↥(K.map (QuotientGroup.mk' L)))
      (Nat.card ↥(R.map (QuotientGroup.mk' L))))
    (hRp : ∃ r : ℕ, r.Prime ∧ Nat.card ↥(R.map (QuotientGroup.mk' L)) = r)
    (hodd : Odd (Nat.card (G ⧸ L)))
    (hchar : s ≠ q → ¬ s ∣ Nat.card (G ⧸ L))
    (hFPF : letI := S03c.chiefFactorConjAction X Y
            ∀ v : ↥X ⧸ Y.subgroupOf X, (∀ r : R, (r : G) • v = v) → v = 1) :
    ⁅R, K⁆ ≤ chiefFactorCentralizer X Y := by
  by_cases hsq : s = q
  · -- `s = q`: `K` centralizes `X/Y` (same-prime branch), so `⁅R, K⁆ ≤ K ≤ chiefFactorCentralizer`.
    subst hsq
    have hKcent := S03c.samePrime_kernel_le_chiefFactorCentralizer hChief hVelem hLcent hKbar
    have hRKle : ⁅R, K⁆ ≤ K := by
      rw [Subgroup.commutator_le]
      intro r _ k hk
      rw [commutatorElement_def]
      exact K.mul_mem (‹K.Normal›.conj_mem k hk r) (K.inv_mem hk)
    exact hRKle.trans hKcent
  · -- `s ≠ q`: the coprime (Theorem 3.4) branch.
    exact commutator_le_chiefFactorCentralizer_via_thm34 hVelem hLcent hcompl hHall hRp hodd
      (hchar hsq) hFPF

open OddOrder.GroupTheory in
/-- **BG Theorem 3.8, reduced case** (step 4 of mmd L1247-1259): if `G = KR` is solvable of odd
order with `K ⊴ G` complementing the prime-order `R`, `(|K|, |R|) = 1`, the quotient `K/F(K)` is a
`p`-group, and `C_{F(K)}(R) = 1` (condition (3)), then `⁅K, R⁆ ⊆ F(K)`.

Proof: for every `G`-chief factor `U/V` with `U ⊆ F(K)`, the per-factor dichotomy
(`commutator_le_chiefFactorCentralizer_dichotomy_thm38`) gives `⁅R, K⁆ ⊆ C_K(U/V)`.  Since `⁅K, R⁆`
need not be normal in `G`, take `N = ⟨⁅K, R⁆⟩^G` (its normal closure); each `chiefFactorCentralizer`
is normal in `G` and contains `⁅K, R⁆`, so `N ⊆ chiefFactorCentralizer U V`.  BG Proposition 1.2
reverse (`S01.chiefFactorCentralizer_subset_le_fitting_of_isSolvable`) then gives `N ⊆ F(K)`, whence
`⁅K, R⁆ ⊆ N ⊆ F(K)`.  `F(K) = (fitting ↥K).map K.subtype`. -/
theorem commutator_le_fitting_of_reduced
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] {K R : Subgroup G} [K.Normal]
    (hodd : Odd (Nat.card G))
    (hcompl : K.IsComplement' R)
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥R))
    (hRprime : ∃ r : ℕ, r.Prime ∧ Nat.card ↥R = r)
    {p : ℕ} [Fact p.Prime]
    (hKbar : IsPGroup p
      (K.map (QuotientGroup.mk' ((OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype))))
    (hC3 : Subgroup.centralizer (R : Set G) ⊓
      (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype = ⊥) :
    ⁅K, R⁆ ≤ (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype := by
  set L : Subgroup G := (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype with hLdef
  have hLnorm : L.Normal := ConjAct.normal_of_characteristic_of_normal
  have hLK : L ≤ K := by rw [hLdef]; exact Subgroup.map_subtype_le _
  have hRL_disj : Disjoint (R : Subgroup G) L :=
    hcompl.isCompl.disjoint.symm.mono_right hLK
  -- The `G/L = (K/L)(R/L)` Theorem 3.4 data (shared across chief factors).
  have hcompl' : (K.map (QuotientGroup.mk' L)).IsComplement' (R.map (QuotientGroup.mk' L)) :=
    hcompl.map_mk' hcop L
  have hHall' : Nat.Coprime (Nat.card ↥(K.map (QuotientGroup.mk' L)))
      (Nat.card ↥(R.map (QuotientGroup.mk' L))) :=
    (hcop.coprime_dvd_left (Subgroup.card_map_dvd K (QuotientGroup.mk' L))).coprime_dvd_right
      (Subgroup.card_map_dvd R (QuotientGroup.mk' L))
  -- `|R/L| = |R|` (prime): `|R/L|` divides `|R|` and is `≠ 1` (else `R ≤ L`, against `R ⊓ L = ⊥`).
  have hRcardL : Nat.card ↥(R.map (QuotientGroup.mk' L)) = Nat.card ↥R := by
    obtain ⟨r, hr, hrcard⟩ := hRprime
    have hdvd : Nat.card ↥(R.map (QuotientGroup.mk' L)) ∣ Nat.card ↥R :=
      Subgroup.card_map_dvd R (QuotientGroup.mk' L)
    rcases (Nat.dvd_prime hr).mp (hrcard ▸ hdvd) with h1 | hr'
    · exfalso
      have hRbot : R.map (QuotientGroup.mk' L) = ⊥ := Subgroup.card_eq_one.mp h1
      have hRL : (R : Subgroup G) ≤ L := by
        intro x hx
        have hxm : QuotientGroup.mk' L x ∈ R.map (QuotientGroup.mk' L) :=
          Subgroup.mem_map_of_mem _ hx
        rw [hRbot, Subgroup.mem_bot] at hxm
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxm
      have hReq : (R : Subgroup G) = ⊥ := by
        rw [disjoint_iff] at hRL_disj; rwa [inf_of_le_left hRL] at hRL_disj
      rw [hReq, Subgroup.card_bot] at hrcard
      exact hr.one_lt.ne' hrcard.symm
    · rw [hrcard]; exact hr'
  have hRp' : ∃ r : ℕ, r.Prime ∧ Nat.card ↥(R.map (QuotientGroup.mk' L)) = r := by
    obtain ⟨r, hr, hrcard⟩ := hRprime; exact ⟨r, hr, hRcardL.trans hrcard⟩
  have hodd' : Odd (Nat.card (G ⧸ L)) := Odd.of_dvd_nat hodd (Subgroup.card_quotient_dvd_card L)
  -- `F(K) ≤ F(G)`, hence `F(K)` centralizes every chief factor of `G` (Prop 1.2 forward).
  have hLfitG : L ≤ OddOrder.Isaacs.Ch01.fitting G :=
    OddOrder.Isaacs.Ch01.fitting_map_subtype_le_fitting
  -- `N = ⟨⁅K, R⁆⟩^G`: normal, `≤ K`.
  set N : Subgroup G := Subgroup.normalClosure ((⁅K, R⁆ : Subgroup G) : Set G) with hNdef
  have hNnorm : N.Normal := Subgroup.normalClosure_normal
  have hKR_le_K : (⁅K, R⁆ : Subgroup G) ≤ K := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_le]
    intro r _ k hk
    rw [commutatorElement_def]
    exact K.mul_mem (‹K.Normal›.conj_mem k hk r) (K.inv_mem hk)
  have hNK : N ≤ K := Subgroup.normalClosure_le_normal hKR_le_K
  -- `N ≤ F(K)` via Proposition 1.2 reverse: `N` centralizes every chief factor `U/V` with `U ⊆
  -- F(K)`.
  have hNF : N ≤ L := by
    refine OddOrder.BG.Ch1.S01.chiefFactorCentralizer_subset_le_fitting_of_isSolvable hNK ?_
    intro U V hVnorm hChief hUF
    have := hChief.normal_top
    have := hChief.normal_bot
    apply Subgroup.normalClosure_le_normal
    intro x hx
    obtain ⟨s, hs, hVelem⟩ := S03c.chiefFactor_isElementaryAbelian hChief
    have : Fact s.Prime := ⟨hs⟩
    have hUK : U ≤ K := hUF.trans hLK
    have hLcent : L ≤ OddOrder.GroupTheory.chiefFactorCentralizer U V :=
      hLfitG.trans (OddOrder.BG.Ch1.S01.fitting_le_chiefFactorCentralizer hChief)
    have hFPF := chiefFactor_fixedPointFree_of_centralizer_fitting_eq_bot (Y := V) hUF hUK
      hcop.symm hC3
    have hchar : s ≠ p → ¬ s ∣ Nat.card (G ⧸ L) := by
      intro hsp
      -- `|G/L| = |K/L| · |R/L|`, with `|K/L| = p^n` and `|R/L| = r` prime.
      have hGL : Nat.card (G ⧸ L) = Nat.card ↥(K.map (QuotientGroup.mk' L)) *
          Nat.card ↥(R.map (QuotientGroup.mk' L)) := hcompl'.card_mul_card.symm
      -- `s ∤ |K/L|` (a `p`-power, `s ≠ p`).
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp hKbar
      have hsK : ¬ s ∣ Nat.card ↥(K.map (QuotientGroup.mk' L)) := by
        rw [hn]
        exact (Nat.Prime.coprime_iff_not_dvd hs).mp
          (((Nat.coprime_primes hs Fact.out).mpr hsp).pow_right n)
      -- `s ∣ |U/V|` (nontrivial `s`-group), hence `s ∣ |K|`.
      have hUVnt : 1 < Nat.card (↥U ⧸ V.subgroupOf U) := by
        have hpos : 0 < Nat.card (↥U ⧸ V.subgroupOf U) := Nat.card_pos
        have hne1 : Nat.card (↥U ⧸ V.subgroupOf U) ≠ 1 := by
          rw [← Subgroup.index_eq_card, Ne, Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top]
          exact fun hUV => hChief.lt.ne (le_antisymm hChief.le hUV)
        omega
      have hsUV : s ∣ Nat.card (↥U ⧸ V.subgroupOf U) := by
        obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := s)).mp hVelem.isPGroup
        rw [hm] at hUVnt ⊢
        exact dvd_pow_self s (by rintro rfl; exact absurd hm.symm (by simpa using hUVnt.ne'))
      have hsK_dvd : s ∣ Nat.card ↥K :=
        hsUV.trans ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hUK))
      -- `s ∤ |R/L| = r` (else `s = r ∣ |K|`, against `(|K|, |R|) = 1`).
      have hsR : ¬ s ∣ Nat.card ↥(R.map (QuotientGroup.mk' L)) := by
        rw [hRcardL]
        intro hsr
        have hgcd : s ∣ Nat.gcd (Nat.card ↥K) (Nat.card ↥R) := Nat.dvd_gcd hsK_dvd hsr
        rw [hcop] at hgcd
        exact hs.one_lt.ne' (Nat.dvd_one.mp hgcd)
      rw [hGL]
      exact fun hd => (hs.prime.dvd_mul.mp hd).elim hsK hsR
    have hdich := commutator_le_chiefFactorCentralizer_dichotomy_thm38 hChief hVelem hLcent hKbar
      hcompl' hHall' hRp' hodd' hchar hFPF
    have hxRK : x ∈ (⁅R, K⁆ : Subgroup G) := by rw [Subgroup.commutator_comm] at hx; exact hx
    exact hdich hxRK
  exact fun y hy => hNF (Subgroup.subset_normalClosure hy)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **BG Theorem 3.8, step 1** (base case of the `|RK|` induction, mmd L1233): if `R` (normalizing
`K`) centralizes the Fitting subgroup of `K̄ = ↥K / F(K)`, then `R` centralizes `K̄` itself
(Proposition 1.4), i.e. `⁅K, R⁆ ⊆ F(K)`.

The conjugation action `φ : R → MulAut ↥K` descends to `K̄` (`quotientMulAutHom`); the centralizing
hypothesis is `F(K̄) ≤ fixedPoints`, so Proposition 1.4
(`actionCommutator_eq_bot_of_fitting_le_fixedPoints`) makes the action commutator on `K̄` trivial.
By `actionCommutator_quotient_eq_map` this is the image of `actionCommutator φ`, so
`actionCommutator φ ≤ F(K)`; finally `actionCommutator_conj_map_subtype` identifies its image under
`K.subtype` with `⁅K, R⁆`. -/
theorem commutator_le_fitting_of_centralizes_fittingQuotient
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] {K R : Subgroup G} [K.Normal]
    (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card ↥R) (Nat.card ↥K))
    (hcent : OddOrder.Isaacs.Ch01.fitting (↥K ⧸ OddOrder.Isaacs.Ch01.fitting ↥K) ≤
      Subgroup.fixedPointsOfMulAut (quotientMulAutHom
        (OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic
          ((Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hRK))))) :
    ⁅K, R⁆ ≤ (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype := by
  set φ : ↥R →* MulAut ↥K :=
    (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hRK) with hφ
  have hFinv : OddOrder.Isaacs.Ch03.IsAInvariant φ (OddOrder.Isaacs.Ch01.fitting ↥K) :=
    OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic φ
  have hcopK : Nat.Coprime (Nat.card ↥R)
      (Nat.card (↥K ⧸ OddOrder.Isaacs.Ch01.fitting ↥K)) :=
    hcop.coprime_dvd_right (Subgroup.card_quotient_dvd_card _)
  have hbot : OddOrder.Isaacs.Ch04.actionCommutator (quotientMulAutHom hFinv) = ⊥ :=
    OddOrder.BG.Ch1.S01.actionCommutator_eq_bot_of_fitting_le_fixedPoints hcopK hcent
  rw [OddOrder.Isaacs.Ch04.actionCommutator_quotient_eq_map] at hbot
  have hle : OddOrder.Isaacs.Ch04.actionCommutator φ ≤ OddOrder.Isaacs.Ch01.fitting ↥K := by
    rw [← QuotientGroup.ker_mk' (OddOrder.Isaacs.Ch01.fitting ↥K)]
    exact (Subgroup.map_eq_bot_iff _).mp hbot
  calc ⁅K, R⁆ = (OddOrder.Isaacs.Ch04.actionCommutator φ).map K.subtype :=
        (OddOrder.BG.Ch1.S06.actionCommutator_conj_map_subtype hRK).symm
    _ ≤ (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype := Subgroup.map_mono hle

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- **BG Proposition 1.5(d), subgroup form** (`C_{G/N}(A) = C_G(A)·N / N`): for a coprime action
`φ : A → MulAut G` and an `A`-invariant normal `N`, the fixed points of the induced action on
`G/N` are exactly the image of the fixed points in `G`.  The `⊇` direction is immediate; the `⊆`
direction is the lifting in `coprime_fixedPoints_quotient` (Proposition 1.5(d), element form). -/
theorem fixedPointsOfMulAut_quotientMulAutHom_eq_map
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] {φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) (hSolv : Group.IsSolvable A ∨ Group.IsSolvable G)
    {N : Subgroup G} [N.Normal] (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) :
    Subgroup.fixedPointsOfMulAut (quotientMulAutHom hN) =
      (Subgroup.fixedPointsOfMulAut φ).map (QuotientGroup.mk' N) := by
  refine le_antisymm ?_ ?_
  · intro q hq
    -- `q` fixed in `G/N` lifts to a fixed `c ≡ q (mod N)` (`coprime_fixedPoints_quotient`).
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    rw [Subgroup.mem_fixedPointsOfMulAut] at hq
    have hg_fix : ∀ a : A, ∃ n ∈ N, (φ a) g = g * n := by
      intro a
      have hga := hq a
      rw [quotientMulAutHom_apply_mk', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at hga
      exact ⟨g⁻¹ * (φ a) g, by simpa using N.inv_mem hga, by group⟩
    obtain ⟨c, hc_fix, n, hn, hcn⟩ :=
      OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient hCop hSolv hN hg_fix
    refine Subgroup.mem_map.mpr ⟨c, Subgroup.mem_fixedPointsOfMulAut.mpr hc_fix, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hcn]
    simpa using N.inv_mem hn
  · -- image of a fixed point is fixed (immediate).
    rw [Subgroup.map_le_iff_le_comap]
    intro c hc
    rw [Subgroup.mem_fixedPointsOfMulAut] at hc
    rw [Subgroup.mem_comap, Subgroup.mem_fixedPointsOfMulAut]
    intro a
    rw [quotientMulAutHom_apply_mk', hc a]

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **Converse of step 1** (mmd L1243, the `R₀`-centralizes-`K̄` direction): if `⁅K, R⁆ ⊆ F(K)`
(`R` centralizes `K̄`), then `R` fixes every element of `K̄ = ↥K / F(K)` (the induced action's
fixed points are `⊤`).  This is the reverse of
`commutator_le_fitting_of_centralizes_fittingQuotient`:
`⁅K, R⁆ = (actionCommutator φ).map K.subtype ⊆ F(K)` forces `actionCommutator φ ⊆ F(K) = ker`, so
the induced quotient action commutator is `⊥` (`actionCommutator_quotient_eq_map`), i.e. the action
on `K̄` is trivial (`actionCommutator_eq_bot_iff_acts_trivially`). -/
theorem fixedPoints_quotient_eq_top_of_commutator_le_fitting
    {G : Type*} [Group G] [Finite G] {K R : Subgroup G} [K.Normal]
    (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hcomm : ⁅K, R⁆ ≤ (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype) :
    Subgroup.fixedPointsOfMulAut (quotientMulAutHom
      (OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic
        (H := OddOrder.Isaacs.Ch01.fitting ↥K)
        ((Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hRK)))) = ⊤ := by
  set φ : ↥R →* MulAut ↥K :=
    (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hRK) with hφ
  have hFinv : OddOrder.Isaacs.Ch03.IsAInvariant φ (OddOrder.Isaacs.Ch01.fitting ↥K) :=
    OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic φ
  -- `actionCommutator φ ≤ F(K)`, by injectivity of `K.subtype` from `⁅K, R⁆ ⊆ F(K)`.
  have hac_le : OddOrder.Isaacs.Ch04.actionCommutator φ ≤ OddOrder.Isaacs.Ch01.fitting ↥K := by
    have h := OddOrder.BG.Ch1.S06.actionCommutator_conj_map_subtype hRK
    rw [← h] at hcomm
    exact Subgroup.map_le_map_iff_of_injective K.subtype_injective |>.mp hcomm
  -- The induced quotient action commutator is `⊥`.
  have hbot : OddOrder.Isaacs.Ch04.actionCommutator (quotientMulAutHom hFinv) = ⊥ := by
    rw [OddOrder.Isaacs.Ch04.actionCommutator_quotient_eq_map, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
    exact hac_le
  -- Trivial action ⟹ fixed points are `⊤`.
  rw [Subgroup.eq_top_iff']
  intro g
  rw [Subgroup.mem_fixedPointsOfMulAut]
  intro a
  exact (OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_iff_acts_trivially _).mp hbot a g

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **BG Theorem 3.8, step 3** (mmd L1241-1245, the condition-(2) reduction from `R₀` to `R`): if
`R₀` (normalizing `K`) already centralizes `K̄ = ↥K / F(K)` (`⁅K, R₀⁆ ⊆ F(K)`) and `R₀` has the
*same fixed points on `K`* as `R` — i.e. `C_G(R₀) ⊓ K = C_G(R) ⊓ K`, which is exactly condition (2)
`C_K(x) = C_K(R)` for `R₀ = ⟨x⟩` — then `R` itself centralizes `K̄`, i.e. `⁅K, R⁆ ⊆ F(K)`.

Chain: `fixedPoints_quotient_eq_top_of_commutator_le_fitting` turns `⁅K, R₀⁆ ⊆ F(K)` into
`fixedPoints(R₀ on K̄) = ⊤`; Proposition 1.5(d) (`fixedPointsOfMulAut_quotientMulAutHom_eq_map`)
rewrites both `R₀`- and `R`-quotient fixed points as push-forwards of the fixed points on `K`;
condition (2) (`fixedPointsOfMulAut_conj_map_subtype` + injectivity of `K.subtype`) identifies the
`R₀`- and `R`-fixed points on `K`, transporting `⊤` to the `R`-quotient; finally step 1
(`commutator_le_fitting_of_centralizes_fittingQuotient`, with `F(K̄) ≤ ⊤` trivial) concludes. -/
theorem commutator_le_fitting_of_sameFixedPoints
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] {K R R₀ : Subgroup G} [K.Normal]
    (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hR₀K : R₀ ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card ↥R) (Nat.card ↥K))
    (hcop₀ : Nat.Coprime (Nat.card ↥R₀) (Nat.card ↥K))
    (hCeq : Subgroup.centralizer (R₀ : Set G) ⊓ K = Subgroup.centralizer (R : Set G) ⊓ K)
    (hcent0 : ⁅K, R₀⁆ ≤ (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype) :
    ⁅K, R⁆ ≤ (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype := by
  have hsolvK : Group.IsSolvable ↥K := inferInstance
  -- `R₀` fixes all of `K̄` (converse of step 1).
  have htop0 := fixedPoints_quotient_eq_top_of_commutator_le_fitting hR₀K hcent0
  -- Proposition 1.5(d) for both `R₀` and `R`: quotient fixed points are push-forwards.
  have hmap0 := fixedPointsOfMulAut_quotientMulAutHom_eq_map
    (φ := (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hR₀K)) hcop₀ (Or.inr hsolvK)
    (OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic (H := OddOrder.Isaacs.Ch01.fitting ↥K)
      ((Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hR₀K)))
  have hmapR := fixedPointsOfMulAut_quotientMulAutHom_eq_map
    (φ := (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hRK)) hcop (Or.inr hsolvK)
    (OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic (H := OddOrder.Isaacs.Ch01.fitting ↥K)
      ((Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hRK)))
  -- Condition (2): `R₀`- and `R`-fixed points on `K` coincide.
  have hconj0 := OddOrder.BG.Ch1.S06.fixedPointsOfMulAut_conj_map_subtype hR₀K
  have hconjR := OddOrder.BG.Ch1.S06.fixedPointsOfMulAut_conj_map_subtype hRK
  have hfix_eq : Subgroup.fixedPointsOfMulAut
        ((Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hR₀K)) =
      Subgroup.fixedPointsOfMulAut
        ((Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hRK)) := by
    apply Subgroup.map_injective K.subtype_injective
    rw [hconj0, hconjR, hCeq]
  -- Transport `⊤` from the `R₀`-quotient to the `R`-quotient.
  rw [hmap0, hfix_eq, ← hmapR] at htop0
  exact commutator_le_fitting_of_centralizes_fittingQuotient hRK hcop (by rw [htop0]; exact le_top)

/-- **Condition (2) of BG Theorem 3.8, subgroup consequence** (mmd L1224, L1237-1239): from
`C_K(x) = C_K(R)` for all `x ∈ R^#` (in the `⊓ K` form), every nontrivial subgroup `R₀ ≤ R` has
the *same* fixed points on `K`, i.e. `C_K(R₀) = C_K(R)`.  (`⊆`: pick a witness `x ∈ R₀^#` and apply
condition (2) at `x`, using `C_K(R₀) ≤ C_K(x)`; `⊇`: antitonicity of the centralizer, `R₀ ≤ R`.) -/
theorem centralizer_inf_eq_of_le_of_cond2
    {G : Type*} [Group G] {K R R₀ : Subgroup G} (hR₀R : R₀ ≤ R) (hR₀ : R₀ ≠ ⊥)
    (hcond2 : ∀ x ∈ (R : Set G), x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ⊓ K = Subgroup.centralizer (R : Set G) ⊓ K) :
    Subgroup.centralizer (R₀ : Set G) ⊓ K = Subgroup.centralizer (R : Set G) ⊓ K := by
  have : Nontrivial ↥R₀ := (Subgroup.nontrivial_iff_ne_bot R₀).mpr hR₀
  obtain ⟨y, hy⟩ := exists_ne (1 : ↥R₀)
  refine le_antisymm ?_ ?_
  · calc Subgroup.centralizer (R₀ : Set G) ⊓ K
        ≤ Subgroup.centralizer ({(y : G)} : Set G) ⊓ K :=
          inf_le_inf_right K (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr y.2))
      _ = Subgroup.centralizer (R : Set G) ⊓ K :=
          hcond2 (y : G) (hR₀R y.2) (mt OneMemClass.coe_eq_one.mp hy)
  · exact inf_le_inf_right K (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hR₀R))

/-- **BG Theorem 3.8, step 2 algebraic core** (mmd L1235): if `F(H) ≤ P ⊴ H`, then the Fitting
subgroup of `P` equals that of `H` (both viewed inside `H`): `F(P) = F(H)`.  `F(P) ⊆ F(H)` is
`fitting_map_subtype_le_fitting` (`F(P) char P ⊴ H` is nilpotent normal); `F(H) ⊆ F(P)` because
`F(H)` is nilpotent and, being `≤ P` and normal in `H`, restricts to a nilpotent normal subgroup of
`P` — so `F(H).subgroupOf P ≤ F(P)`, and pushing forward gives `F(H) = F(H) ⊓ P ⊆ F(P)`. -/
theorem fitting_map_eq_of_normal_of_fitting_le
    {H : Type*} [Group H] [Finite H] {P : Subgroup H} [P.Normal]
    (hFP : OddOrder.Isaacs.Ch01.fitting H ≤ P) :
    (OddOrder.Isaacs.Ch01.fitting ↥P).map P.subtype = OddOrder.Isaacs.Ch01.fitting H := by
  refine le_antisymm OddOrder.Isaacs.Ch01.fitting_map_subtype_le_fitting ?_
  have : Group.IsNilpotent ↥(OddOrder.Isaacs.Ch01.fitting H) :=
    OddOrder.Isaacs.Ch01.fitting.isNilpotent
  have : Group.IsNilpotent ↥((OddOrder.Isaacs.Ch01.fitting H).subgroupOf P) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFP).symm
  have hle : (OddOrder.Isaacs.Ch01.fitting H).subgroupOf P ≤ OddOrder.Isaacs.Ch01.fitting ↥P :=
    OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
  calc OddOrder.Isaacs.Ch01.fitting H
      = OddOrder.Isaacs.Ch01.fitting H ⊓ P := (inf_eq_left.mpr hFP).symm
    _ = ((OddOrder.Isaacs.Ch01.fitting H).subgroupOf P).map P.subtype :=
        (Subgroup.subgroupOf_map_subtype _ P).symm
    _ ≤ (OddOrder.Isaacs.Ch01.fitting ↥P).map P.subtype := Subgroup.map_mono hle

/-- **Complement transport to a sup** (`|RK|`-induction plumbing for BG Theorem 3.8): if `A ⊴ G`
is disjoint from `B`, then inside `↥(A ⊔ B)` the restricted `A` complements the restricted `B`.
Used to feed both inductive sub-configurations (`P R` and `K R₀`) to the induction hypothesis. -/
theorem isComplement'_subgroupOf_sup_of_normal
    {G : Type*} [Group G] {A B : Subgroup G} [A.Normal] (hAB : Disjoint A B) :
    (A.subgroupOf (A ⊔ B)).IsComplement' (B.subgroupOf (A ⊔ B)) := by
  have hAB_bot : A ⊓ B = ⊥ := hAB.eq_bot
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · refine disjoint_iff.mpr (eq_bot_iff.mpr (fun x hx => ?_))
    rw [Subgroup.mem_inf] at hx
    simp only [Subgroup.mem_subgroupOf] at hx
    have hmem : (x : G) ∈ A ⊓ B := ⟨hx.1, hx.2⟩
    rw [hAB_bot, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact Subtype.ext (by simpa using hmem)
  · ext g
    simp only [Set.mem_mul, Set.mem_univ, iff_true]
    have hgset : (g : G) ∈ (↑A : Set G) * (↑B : Set G) := by
      rw [← Subgroup.normal_mul A B]; exact g.2
    obtain ⟨a, ha, b, hb, hab⟩ := hgset
    exact ⟨⟨a, (le_sup_left : A ≤ A ⊔ B) ha⟩, Subgroup.mem_subgroupOf.mpr ha,
      ⟨b, (le_sup_right : B ≤ A ⊔ B) hb⟩, Subgroup.mem_subgroupOf.mpr hb,
      Subtype.ext (by simpa using hab)⟩

/-- **Sylow extraction** (`|RK|`-induction plumbing for BG Theorem 3.8, mmd L1233): since
`F(Q) = ⨆_p O_p(Q)` (the Fitting subgroup is the join of the `p`-cores, by definition), if `F(Q)` is
*not* contained in a subgroup `S`, then some `p`-core `O_p(Q)` is not contained in `S` either.
(Applied with `Q = K̄`, `S = C_K̄(R)` to find a non-`R`-centralized Sylow of `F(K̄)`.) -/
theorem exists_opCore_not_le_of_fitting_not_le
    {Q : Type*} [Group Q] {S : Subgroup Q} (hS : ¬ OddOrder.Isaacs.Ch01.fitting Q ≤ S) :
    ∃ p : Nat.Primes, ¬ OddOrder.Isaacs.Ch01.opCore (p : ℕ) Q ≤ S := by
  by_contra h
  push Not at h
  exact hS (iSup_le h)

/-- The image of `F(A)` under an isomorphism `e : A ≃* B` is contained in `F(B)` (one direction of
`fitting_map_mulEquiv`): the image of the nilpotent normal `F(A)` is nilpotent and normal in `B`. -/
theorem fitting_map_mulEquiv_le {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) :
    (OddOrder.Isaacs.Ch01.fitting A).map e.toMonoidHom ≤ OddOrder.Isaacs.Ch01.fitting B := by
  have : Group.IsNilpotent (OddOrder.Isaacs.Ch01.fitting A) :=
    OddOrder.Isaacs.Ch01.fitting.isNilpotent
  have : Group.IsNilpotent ↥((OddOrder.Isaacs.Ch01.fitting A).map e.toMonoidHom) :=
    Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective)
  have : ((OddOrder.Isaacs.Ch01.fitting A).map e.toMonoidHom).Normal :=
    (OddOrder.Isaacs.Ch01.fitting.normal A).map e.toMonoidHom e.surjective
  exact OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting

/-- **Fitting subgroup is preserved by isomorphisms** (`|RK|`-induction plumbing for BG Theorem
3.8):
`e : A ≃* B` carries `F(A)` onto `F(B)`.  Used to identify the Fitting subgroup of an inductive
sub-configuration `K'.subgroupOf S` with that of `K'`. -/
theorem fitting_map_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] (e : A ≃* B) :
    (OddOrder.Isaacs.Ch01.fitting A).map e.toMonoidHom = OddOrder.Isaacs.Ch01.fitting B := by
  have : Finite B := Finite.of_equiv A e.toEquiv
  refine le_antisymm (fitting_map_mulEquiv_le e) (fun y hy => ?_)
  have hsy : e.symm y ∈ OddOrder.Isaacs.Ch01.fitting A :=
    fitting_map_mulEquiv_le e.symm (by simpa using Subgroup.mem_map_of_mem e.symm.toMonoidHom hy)
  simpa using Subgroup.mem_map_of_mem e.toMonoidHom hsy

/-- **`p`-group transfer across `K ↠ K/N`** (`|RK|`-induction plumbing for BG Theorem 3.8): if the
quotient `↥K / N` is a `p`-group, then so is the image `K · (N·K)/(N·K)` of `K` in `G / (N.map
K.subtype)`
(both are `↥K / N`).  Used to upgrade `K̄ = ↥K / F(K)` being a `p`-group to the form
`IsPGroup p (K.map (mk' (F(K).map K.subtype)))` required by `commutator_le_fitting_of_reduced`. -/
theorem isPGroup_map_mk'_subtype_of_isPGroup_quotient {G : Type*} [Group G] {K : Subgroup G}
    {N : Subgroup ↥K} [N.Normal] [(N.map K.subtype).Normal] {q : ℕ}
    (hq : IsPGroup q (↥K ⧸ N)) :
    IsPGroup q (K.map (QuotientGroup.mk' (N.map K.subtype))) := by
  intro x
  obtain ⟨g, hgK, hgx⟩ := x.2
  obtain ⟨n, hn⟩ := hq (QuotientGroup.mk' N ⟨g, hgK⟩)
  refine ⟨n, ?_⟩
  have hgN : (⟨g, hgK⟩ : ↥K) ^ q ^ n ∈ N := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
    exact hn
  have hgL : (g : G) ^ q ^ n ∈ N.map K.subtype := by
    simpa using Subgroup.mem_map_of_mem K.subtype hgN
  apply Subtype.ext
  change ((x : G ⧸ N.map K.subtype)) ^ q ^ n = 1
  rw [← hgx, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hgL

/-- **Conclusion transport from a sub-configuration** (`|RK|`-induction plumbing for BG Theorem
3.8):
if the induction hypothesis gives `⁅A', B'⁆ ⊆ F(A')` for the restrictions `A' = A.subgroupOf (A⊔B)`,
`B' = B.subgroupOf (A⊔B)` inside `↥(A⊔B)`, then pushing forward along `↥(A⊔B) ↪ G` yields
`⁅A, B⁆ ⊆ F(A)` in `G`.  The commutator side uses `map_commutator` + `subgroupOf_map_subtype`; the
Fitting side uses `map_map` and `fitting_map_mulEquiv` (via `↥A' ≃* ↥A`). -/
theorem commutator_le_fitting_of_subgroupOf_sup {G : Type*} [Group G] [Finite G]
    {A B : Subgroup G}
    (h : ⁅A.subgroupOf (A ⊔ B), B.subgroupOf (A ⊔ B)⁆ ≤
      (OddOrder.Isaacs.Ch01.fitting ↥(A.subgroupOf (A ⊔ B))).map (A.subgroupOf (A ⊔ B)).subtype) :
    ⁅A, B⁆ ≤ (OddOrder.Isaacs.Ch01.fitting ↥A).map A.subtype := by
  have hAS : A ≤ A ⊔ B := le_sup_left
  have hBS : B ≤ A ⊔ B := le_sup_right
  set e := Subgroup.subgroupOfEquivOfLe hAS with he
  have hcomp : (A ⊔ B).subtype.comp (A.subgroupOf (A ⊔ B)).subtype =
      A.subtype.comp e.toMonoidHom := by ext a'; rfl
  have key : ((OddOrder.Isaacs.Ch01.fitting ↥(A.subgroupOf (A ⊔ B))).map
        (A.subgroupOf (A ⊔ B)).subtype).map (A ⊔ B).subtype =
      (OddOrder.Isaacs.Ch01.fitting ↥A).map A.subtype := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, fitting_map_mulEquiv e]
  have hcomm : (⁅A.subgroupOf (A ⊔ B), B.subgroupOf (A ⊔ B)⁆).map (A ⊔ B).subtype = ⁅A, B⁆ := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hAS, inf_eq_left.mpr hBS]
  calc ⁅A, B⁆ = (⁅A.subgroupOf (A ⊔ B), B.subgroupOf (A ⊔ B)⁆).map (A ⊔ B).subtype := hcomm.symm
    _ ≤ ((OddOrder.Isaacs.Ch01.fitting ↥(A.subgroupOf (A ⊔ B))).map
          (A.subgroupOf (A ⊔ B)).subtype).map (A ⊔ B).subtype := Subgroup.map_mono h
    _ = (OddOrder.Isaacs.Ch01.fitting ↥A).map A.subtype := key

/-- **Centralizer in a subgroup, via `subgroupOf`** (`|RK|`-induction plumbing for BG Theorem 3.8):
the centralizer inside `↥S` of a set `T ⊆ ↥S` is the restriction to `↥S` of the ambient centralizer
of `T`'s image in `G`.  Lets the induction's conditions (2), (3) — equalities of `C_K(·)`'s — be
transported between `G` and a sub-configuration `↥(A ⊔ B)`. -/
theorem centralizer_subgroupOf {G : Type*} [Group G] {S : Subgroup G} (T : Set ↥S) :
    Subgroup.centralizer T = (Subgroup.centralizer (S.subtype '' T)).subgroupOf S := by
  ext s
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro hs g ⟨t, ht, rfl⟩
    simpa only [map_mul, Subgroup.subtype_apply] using congrArg (S.subtype) (hs t ht)
  · intro hs t ht
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact hs (S.subtype t) ⟨t, ht, rfl⟩

/-- **Fitting of a sub-configuration, via `subgroupOf`** (`|RK|`-induction plumbing for BG Theorem
3.8): for `A ≤ S`, the Fitting subgroup of `A.subgroupOf S` (pushed into `↥S`) is the restriction to
`↥S` of `F(A)` (pushed into `G`).  Lets condition (3) — `C_{F(A)}(·) = ⊥` — transport between `G`
and `↥S`.  Same `map_map` + `fitting_map_mulEquiv` argument as
`commutator_le_fitting_of_subgroupOf_sup`. -/
theorem fitting_subgroupOf_map_subtype_eq {G : Type*} [Group G] [Finite G] {A S : Subgroup G}
    (hAS : A ≤ S) :
    (OddOrder.Isaacs.Ch01.fitting ↥(A.subgroupOf S)).map (A.subgroupOf S).subtype =
      ((OddOrder.Isaacs.Ch01.fitting ↥A).map A.subtype).subgroupOf S := by
  apply Subgroup.map_injective S.subtype_injective
  have hLS : (OddOrder.Isaacs.Ch01.fitting ↥A).map A.subtype ≤ S :=
    (Subgroup.map_subtype_le _).trans hAS
  have hcomp : S.subtype.comp (A.subgroupOf S).subtype =
      A.subtype.comp (Subgroup.subgroupOfEquivOfLe hAS).toMonoidHom := by ext a'; rfl
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLS, Subgroup.map_map, hcomp,
    ← Subgroup.map_map, fitting_map_mulEquiv]

/-- **Fitting of a mapped subgroup** (`|RK|`-induction plumbing for BG Theorem 3.8): for
`P ≤ ↥K`, the Fitting subgroup of `P.map K.subtype` (the image of `P` in `G`) is `F(P)` pushed
through `K.subtype`.  Combined with `fitting_map_eq_of_normal_of_fitting_le` this identifies
`F(P_G)` with `F(K)` in step 2. -/
theorem fitting_map_map_subtype {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    {P : Subgroup ↥K} :
    (OddOrder.Isaacs.Ch01.fitting ↥(P.map K.subtype)).map (P.map K.subtype).subtype =
      ((OddOrder.Isaacs.Ch01.fitting ↥P).map P.subtype).map K.subtype := by
  have hcomp : (P.map K.subtype).subtype.comp
      (Subgroup.equivMapOfInjective P K.subtype K.subtype_injective).toMonoidHom =
      K.subtype.comp P.subtype := by ext a; rfl
  rw [← fitting_map_mulEquiv (Subgroup.equivMapOfInjective P K.subtype K.subtype_injective),
    Subgroup.map_map, hcomp, ← Subgroup.map_map]

open scoped commutatorElement in
open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- **BG Theorem 3.8** (`|RK|`-induction skeleton, mmd L1221-1259).  `G = KR` solvable of odd order,
`K ⊴ G`, conditions (1) `(|R|, |K|) = 1`, (2) `C_K(x) = C_K(R)` for all `x ∈ R^#`, (3)
`C_{F(K)}(R) = 1`.  Then `⁅K, R⁆ ⊆ F(K)`.

The induction is on `n = |G|`.  `by_cases` on whether `R` centralizes `F(K̄)` (`K̄ = K/F(K)`):
- yes ⟹ step 1 (`commutator_le_fitting_of_centralizes_fittingQuotient`, Proposition 1.4);
- no ⟹ step 2 (`P` = preimage of a non-centralized Sylow `P̄` of `F(K̄)`; if `P ≠ K`, IH on `PR`
  gives `⁅P, R⁆ ⊆ F(P) = F(K)`, so `R` centralizes `P̄`, contradiction — hence `K̄` is a `p`-group)
  then step 3 (`R₀ ≤ R` of prime order; if `R₀ ≠ R`, IH on `KR₀` + `commutator_le_fitting_of_…`
  reductions give the result — hence `R` is prime) then step 4
  (`commutator_le_fitting_of_reduced`). -/
private theorem thm38_aux : ∀ (n : ℕ) {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    (K R : Subgroup G), K.Normal → Odd (Nat.card G) → K.IsComplement' R →
    Nat.Coprime (Nat.card ↥R) (Nat.card ↥K) →
    (∀ x ∈ (R : Set G), x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ⊓ K = Subgroup.centralizer (R : Set G) ⊓ K) →
    Subgroup.centralizer (R : Set G) ⊓
      (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype = ⊥ →
    Nat.card G = n →
    ⁅K, R⁆ ≤ (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro G _ _ _ K R hKnorm hodd hcompl hcop hcond2 hC3 hn
    have := hKnorm
    have hRK : R ≤ Subgroup.normalizer (K : Set G) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hKnorm]; exact le_top
    by_cases hcent : OddOrder.Isaacs.Ch01.fitting (↥K ⧸ OddOrder.Isaacs.Ch01.fitting ↥K) ≤
        Subgroup.fixedPointsOfMulAut (quotientMulAutHom
          (OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic
            ((Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hRK))))
    · -- Step 1 (mmd L1233): `R` centralizes `F(K̄)`, hence (Prop 1.4) all of `K̄`.
      exact commutator_le_fitting_of_centralizes_fittingQuotient hRK hcop hcent
    · -- Steps 2-4 (mmd L1233-1259): `¬hcent`, i.e. `R` does not centralize `F(K̄)`.
      set L : Subgroup G := (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype with hLdef
      -- (A) a `p`-core `O_p(K̄)` of `K̄` not centralized by `R` (mmd L1233).
      obtain ⟨p, hp_not⟩ := exists_opCore_not_le_of_fitting_not_le hcent
      have : Fact ((p : ℕ).Prime) := ⟨p.2⟩
      -- (B) `P` = preimage of `O_p(K̄)` in `↥K`: characteristic, with `F(K) ≤ P_G ⊴ G`, `P_G ≤ K`.
      set P : Subgroup ↥K :=
        (OddOrder.Isaacs.Ch01.opCore (p : ℕ) (↥K ⧸ OddOrder.Isaacs.Ch01.fitting ↥K)).comap
          (QuotientGroup.mk' (OddOrder.Isaacs.Ch01.fitting ↥K)) with hPdef
      have hPchar : P.Characteristic :=
        Subgroup.Characteristic.comap_quotient_mk (OddOrder.Isaacs.Ch01.opCore.characteristic _ _)
      set PG : Subgroup G := P.map K.subtype with hPGdef
      have hPGnorm : PG.Normal := ConjAct.normal_of_characteristic_of_normal
      have hPGK : PG ≤ K := Subgroup.map_subtype_le _
      -- (1) `K̄` is a `p`-group (mmd L1235): otherwise IH on `PR` contradicts the choice of `P`.
      have hKbar : IsPGroup p (K.map (QuotientGroup.mk' L)) := by
        by_cases hPGeqK : PG = K
        · -- `P_G = K` ⟹ `P = ⊤` ⟹ `O_p(K̄) = ⊤` ⟹ `K̄` is a `p`-group.
          have : ((OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype).Normal :=
            ConjAct.normal_of_characteristic_of_normal
          have hPtop : P = ⊤ := by
            apply Subgroup.map_injective K.subtype_injective
            rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
            exact hPGeqK
          have hoc : OddOrder.Isaacs.Ch01.opCore (p : ℕ)
              (↥K ⧸ OddOrder.Isaacs.Ch01.fitting ↥K) = ⊤ := by
            rw [Subgroup.eq_top_iff']
            intro y
            obtain ⟨z, rfl⟩ :=
              QuotientGroup.mk'_surjective (OddOrder.Isaacs.Ch01.fitting ↥K) y
            have hzP : z ∈ P := by rw [hPtop]; exact Subgroup.mem_top z
            rw [hPdef, Subgroup.mem_comap] at hzP
            exact hzP
          have hKbar_pg : IsPGroup p (↥K ⧸ OddOrder.Isaacs.Ch01.fitting ↥K) := by
            have h1 := OddOrder.Isaacs.Ch01.opCore_isPGroup (p : ℕ)
              (↥K ⧸ OddOrder.Isaacs.Ch01.fitting ↥K)
            rw [hoc] at h1
            exact h1.of_equiv Subgroup.topEquiv
          exact isPGroup_map_mk'_subtype_of_isPGroup_quotient
            (N := OddOrder.Isaacs.Ch01.fitting ↥K) hKbar_pg
        · -- `P_G ≠ K` ⟹ IH on `PR` gives `⁅P_G, R⁆ ⊆ F(P_G) = F(K)`, so `R` centralizes `O_p(K̄)`.
          exfalso
          have hPnorm : P.Normal := inferInstance
          -- `F(K) ≤ P` (since `O_p(K̄) ∋ 1` pulls back the kernel `F(K)`).
          have hFP : OddOrder.Isaacs.Ch01.fitting ↥K ≤ P := by
            rw [hPdef]; intro z hz; rw [Subgroup.mem_comap]
            have hz1 : (QuotientGroup.mk' (OddOrder.Isaacs.Ch01.fitting ↥K)) z = 1 := by
              rw [QuotientGroup.mk'_apply]; exact (QuotientGroup.eq_one_iff z).mpr hz
            rw [hz1]; exact one_mem _
          -- `F(P_G) = F(K) = L`.
          have hFPGL : (OddOrder.Isaacs.Ch01.fitting ↥PG).map PG.subtype = L := by
            rw [hPGdef, fitting_map_map_subtype,
              fitting_map_eq_of_normal_of_fitting_le hFP, ← hLdef]
          have hdisjPG : Disjoint PG R := hcompl.disjoint.mono_left hPGK
          -- IH on `P_G R` (`|P_G ⊔ R| < |G|` since `P_G < K`) ⟹ `⁅P_G, R⁆ ⊆ L`.
          have hcommPG : ⁅PG, R⁆ ≤ L := by
            rw [← hFPGL]
            refine commutator_le_fitting_of_subgroupOf_sup
              (IH (Nat.card ↥(PG ⊔ R)) ?_ (PG.subgroupOf (PG ⊔ R)) (R.subgroupOf (PG ⊔ R))
                Subgroup.normal_subgroupOf
                (Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card _))
                (isComplement'_subgroupOf_sup_of_normal hdisjPG) ?_ ?_ ?_ rfl)
            · -- `|P_G ⊔ R| < |G|` (since `P_G < K`).
              have hcardlt : Nat.card ↥PG < Nat.card ↥K := by
                refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hPGK))
                  (fun heq => hPGeqK ?_)
                exact Subgroup.eq_of_le_of_card_ge hPGK heq.ge
              have hScard : Nat.card ↥(PG ⊔ R) = Nat.card ↥PG * Nat.card ↥R := by
                rw [← (isComplement'_subgroupOf_sup_of_normal hdisjPG).card_mul_card,
                  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : PG ≤ PG ⊔ R)).toEquiv,
                  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : R ≤ PG ⊔ R)).toEquiv]
              rw [← hn, hScard, ← hcompl.card_mul_card]
              exact mul_lt_mul_of_pos_right hcardlt Nat.card_pos
            · -- coprime `(|R'|, |P_G'|)`.
              rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : R ≤ PG ⊔ R)).toEquiv,
                Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : PG ≤ PG ⊔ R)).toEquiv]
              exact hcop.coprime_dvd_right (Subgroup.card_dvd_of_le hPGK)
            · -- condition (2) for `P_G` (`C_K(x) = C_K(R)`, then intersected with `P_G ≤ K`).
              intro x hx hx1
              have hxR : (↑x : G) ∈ (R : Set G) := Subgroup.mem_subgroupOf.mp hx
              have hx1' : (↑x : G) ≠ 1 := mt OneMemClass.coe_eq_one.mp hx1
              have key : Subgroup.centralizer ({(↑x : G)} : Set G) ⊓ PG =
                  Subgroup.centralizer (R : Set G) ⊓ PG := by
                calc Subgroup.centralizer ({(↑x : G)} : Set G) ⊓ PG
                    = (Subgroup.centralizer ({(↑x : G)} : Set G) ⊓ K) ⊓ PG := by
                      rw [inf_assoc, inf_eq_right.mpr hPGK]
                  _ = (Subgroup.centralizer (R : Set G) ⊓ K) ⊓ PG := by rw [hcond2 (↑x) hxR hx1']
                  _ = Subgroup.centralizer (R : Set G) ⊓ PG := by
                      rw [inf_assoc, inf_eq_right.mpr hPGK]
              have himg : (PG ⊔ R).subtype ''
                  ((R.subgroupOf (PG ⊔ R) : Subgroup ↥(PG ⊔ R)) : Set ↥(PG ⊔ R)) = (R : Set G) := by
                rw [← Subgroup.coe_map, Subgroup.subgroupOf_map_subtype,
                  inf_eq_left.mpr (le_sup_right : R ≤ PG ⊔ R)]
              have hdist : ∀ A : Subgroup G,
                  A.subgroupOf (PG ⊔ R) ⊓ (PG.subgroupOf (PG ⊔ R)) = (A ⊓ PG).subgroupOf (PG ⊔ R) :=
                fun A => (Subgroup.comap_inf A PG (PG ⊔ R).subtype).symm
              have hxv : (PG ⊔ R).subtype x = (↑x : G) := rfl
              rw [centralizer_subgroupOf ({x} : Set ↥(PG ⊔ R)), Set.image_singleton, hxv,
                centralizer_subgroupOf ((R.subgroupOf (PG ⊔ R) : Subgroup ↥(PG ⊔ R)) :
                  Set ↥(PG ⊔ R)), himg, hdist (Subgroup.centralizer ({(↑x : G)} : Set G)),
                hdist (Subgroup.centralizer (R : Set G)), key]
            · -- condition (3) for the `P_G`-configuration (`C_{F(P_G)}(R) = C_{F(K)}(R) = 1`).
              have himg : (PG ⊔ R).subtype ''
                  ((R.subgroupOf (PG ⊔ R) : Subgroup ↥(PG ⊔ R)) : Set ↥(PG ⊔ R)) = (R : Set G) := by
                rw [← Subgroup.coe_map, Subgroup.subgroupOf_map_subtype,
                  inf_eq_left.mpr (le_sup_right : R ≤ PG ⊔ R)]
              have hdistL : (Subgroup.centralizer (R : Set G)).subgroupOf (PG ⊔ R) ⊓
                  (L.subgroupOf (PG ⊔ R)) =
                  (Subgroup.centralizer (R : Set G) ⊓ L).subgroupOf (PG ⊔ R) :=
                (Subgroup.comap_inf _ L (PG ⊔ R).subtype).symm
              rw [fitting_subgroupOf_map_subtype_eq (le_sup_left : PG ≤ PG ⊔ R), hFPGL,
                centralizer_subgroupOf ((R.subgroupOf (PG ⊔ R) : Subgroup ↥(PG ⊔ R)) :
                  Set ↥(PG ⊔ R)), himg, hdistL, hC3, Subgroup.bot_subgroupOf]
          -- `R` centralizes `O_p(K̄)`, contradicting the choice of `P`.
          apply hp_not
          have hsurj := QuotientGroup.mk'_surjective (OddOrder.Isaacs.Ch01.fitting ↥K)
          have hopcore : P.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch01.fitting ↥K)) =
              OddOrder.Isaacs.Ch01.opCore (p : ℕ) (↥K ⧸ OddOrder.Isaacs.Ch01.fitting ↥K) := by
            rw [hPdef]; exact Subgroup.map_comap_eq_self_of_surjective hsurj _
          rw [← hopcore]
          intro x hx
          rw [Subgroup.mem_map] at hx
          obtain ⟨q, hqP, rfl⟩ := hx
          rw [Subgroup.mem_fixedPointsOfMulAut]
          intro a
          rw [quotientMulAutHom_apply_mk', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
            QuotientGroup.eq]
          set φ : ↥R →* MulAut ↥K :=
            (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hRK) with hφ
          have hphi : (K.subtype (φ a q) : G) = (↑a : G) * K.subtype q * (↑a : G)⁻¹ := rfl
          have hKsub : (K.subtype ((φ a q)⁻¹ * q) : G) =
              ⁅(↑a : G), (K.subtype q)⁻¹⁆ := by
            rw [commutatorElement_def, map_mul, map_inv, hphi]; group
          have hmemL : (K.subtype ((φ a q)⁻¹ * q) : G) ∈ L := by
            rw [hKsub, hLdef]
            apply hcommPG
            rw [Subgroup.commutator_comm]
            exact Subgroup.commutator_mem_commutator a.2
              (PG.inv_mem (Subgroup.mem_map_of_mem K.subtype hqP))
          exact (Subgroup.mem_map_iff_mem K.subtype_injective).mp hmemL
      -- (2) Pick `R₀ ≤ R` of prime order (mmd L1237).
      obtain ⟨R₀, hR₀R, r, hr, hR₀card⟩ :
          ∃ R₀ : Subgroup G, R₀ ≤ R ∧ ∃ r : ℕ, r.Prime ∧ Nat.card ↥R₀ = r := by
        -- `R ≠ ⊥` (else the trivial action fixes all of `K̄`, contradicting `hp_not`).
        have hRne_bot : R ≠ ⊥ := by
          intro hR0
          have : Subsingleton ↥R := by rw [hR0]; infer_instance
          refine hp_not (le_trans le_top ?_)
          rw [top_le_iff, Subgroup.eq_top_iff']
          intro x
          rw [Subgroup.mem_fixedPointsOfMulAut]
          intro a
          obtain rfl : a = 1 := Subsingleton.elim a 1
          rw [map_one]; rfl
        have hRne1 : Nat.card ↥R ≠ 1 := fun h => hRne_bot (Subgroup.card_eq_one.mp h)
        obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hRne1
        have : Fact r.Prime := ⟨hr⟩
        have : Fintype ↥R := Fintype.ofFinite _
        obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card (G := ↥R) r
          (by rwa [Nat.card_eq_fintype_card] at hrdvd)
        refine ⟨(Subgroup.zpowers g).map R.subtype, Subgroup.map_subtype_le _, r, hr, ?_⟩
        rw [← Nat.card_congr (Subgroup.equivMapOfInjective _ R.subtype R.subtype_injective).toEquiv,
          Nat.card_zpowers]
        exact hg
      by_cases hR₀eq : R₀ = R
      · -- `R = R₀` has prime order: the reduced case (step 4, mmd L1247-1259).
        subst hR₀eq
        exact commutator_le_fitting_of_reduced hodd hcompl hcop.symm ⟨r, hr, hR₀card⟩ hKbar hC3
      · -- `R₀ ≠ R`: IH on `KR₀` gives `⁅K, R₀⁆ ⊆ F(K)`, then step 3 (mmd L1241-1245).
        have hR₀K : R₀ ≤ Subgroup.normalizer (K : Set G) := hR₀R.trans hRK
        have hcop₀ : Nat.Coprime (Nat.card ↥R₀) (Nat.card ↥K) :=
          hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hR₀R)
        have hR₀bot : R₀ ≠ ⊥ := fun h => by
          rw [h, Subgroup.card_bot] at hR₀card; exact absurd hR₀card.symm hr.one_lt.ne'
        have hCeq := centralizer_inf_eq_of_le_of_cond2 hR₀R hR₀bot hcond2
        have hcent0 : ⁅K, R₀⁆ ≤ L := by
          have hdisj : Disjoint K R₀ := hcompl.disjoint.mono_right hR₀R
          refine commutator_le_fitting_of_subgroupOf_sup
            (IH (Nat.card ↥(K ⊔ R₀)) ?_ (K.subgroupOf (K ⊔ R₀)) (R₀.subgroupOf (K ⊔ R₀))
              Subgroup.normal_subgroupOf
              (Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card _))
              (isComplement'_subgroupOf_sup_of_normal hdisj) ?_ ?_ ?_ rfl)
          · -- `|K ⊔ R₀| < |G|` (since `R₀ < R`).
            have hcardlt : Nat.card ↥R₀ < Nat.card ↥R := by
              refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hR₀R))
                (fun heq => hR₀eq ?_)
              exact Subgroup.eq_of_le_of_card_ge hR₀R heq.ge
            have hScard : Nat.card ↥(K ⊔ R₀) = Nat.card ↥K * Nat.card ↥R₀ := by
              rw [← (isComplement'_subgroupOf_sup_of_normal hdisj).card_mul_card,
                Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : K ≤ K ⊔ R₀)).toEquiv,
                Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : R₀ ≤ K ⊔ R₀)).toEquiv]
            rw [← hn, hScard, ← hcompl.card_mul_card]
            exact mul_lt_mul_of_pos_left hcardlt Nat.card_pos
          · -- coprime `(|R₀'|, |K'|)`.
            rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : R₀ ≤ K ⊔ R₀)).toEquiv,
              Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : K ≤ K ⊔ R₀)).toEquiv]
            exact hcop₀
          · -- condition (2) for the `R₀`-configuration (transport via `centralizer_subgroupOf`).
            intro x hx hx1
            have hxR : (↑x : G) ∈ (R : Set G) := hR₀R (Subgroup.mem_subgroupOf.mp hx)
            have hx1' : (↑x : G) ≠ 1 := mt OneMemClass.coe_eq_one.mp hx1
            have key : Subgroup.centralizer ({(↑x : G)} : Set G) ⊓ K =
                Subgroup.centralizer (R₀ : Set G) ⊓ K := (hcond2 (↑x) hxR hx1').trans hCeq.symm
            have himg : (K ⊔ R₀).subtype ''
                ((R₀.subgroupOf (K ⊔ R₀) : Subgroup ↥(K ⊔ R₀)) : Set ↥(K ⊔ R₀)) = (R₀ : Set G) := by
              rw [← Subgroup.coe_map, Subgroup.subgroupOf_map_subtype,
                inf_eq_left.mpr (le_sup_right : R₀ ≤ K ⊔ R₀)]
            have hdist : ∀ A : Subgroup G,
                A.subgroupOf (K ⊔ R₀) ⊓ (K.subgroupOf (K ⊔ R₀)) = (A ⊓ K).subgroupOf (K ⊔ R₀) :=
              fun A => (Subgroup.comap_inf A K (K ⊔ R₀).subtype).symm
            have hxv : (K ⊔ R₀).subtype x = (↑x : G) := rfl
            rw [centralizer_subgroupOf ({x} : Set ↥(K ⊔ R₀)), Set.image_singleton, hxv,
              centralizer_subgroupOf
                ((R₀.subgroupOf (K ⊔ R₀) : Subgroup ↥(K ⊔ R₀)) : Set ↥(K ⊔ R₀)),
              himg, hdist (Subgroup.centralizer ({(↑x : G)} : Set G)),
              hdist (Subgroup.centralizer (R₀ : Set G)), key]
          · -- condition (3) for the `R₀`-configuration: `C_{F(K)}(R₀) = C_{F(K)}(R) = 1`.
            have hLK : L ≤ K := Subgroup.map_subtype_le _
            have hC3' : Subgroup.centralizer (R₀ : Set G) ⊓ L = ⊥ := by
              calc Subgroup.centralizer (R₀ : Set G) ⊓ L
                  = (Subgroup.centralizer (R₀ : Set G) ⊓ K) ⊓ L := by
                    rw [inf_assoc, inf_eq_right.mpr hLK]
                _ = (Subgroup.centralizer (R : Set G) ⊓ K) ⊓ L := by rw [hCeq]
                _ = Subgroup.centralizer (R : Set G) ⊓ L := by rw [inf_assoc, inf_eq_right.mpr hLK]
                _ = ⊥ := hC3
            have himg : (K ⊔ R₀).subtype ''
                ((R₀.subgroupOf (K ⊔ R₀) : Subgroup ↥(K ⊔ R₀)) : Set ↥(K ⊔ R₀)) = (R₀ : Set G) := by
              rw [← Subgroup.coe_map, Subgroup.subgroupOf_map_subtype,
                inf_eq_left.mpr (le_sup_right : R₀ ≤ K ⊔ R₀)]
            have hdistL : (Subgroup.centralizer (R₀ : Set G)).subgroupOf (K ⊔ R₀) ⊓
                (L.subgroupOf (K ⊔ R₀)) =
                (Subgroup.centralizer (R₀ : Set G) ⊓ L).subgroupOf (K ⊔ R₀) :=
              (Subgroup.comap_inf _ L (K ⊔ R₀).subtype).symm
            rw [fitting_subgroupOf_map_subtype_eq (le_sup_left : K ≤ K ⊔ R₀), ← hLdef,
              centralizer_subgroupOf ((R₀.subgroupOf (K ⊔ R₀) : Subgroup ↥(K ⊔ R₀)) :
                Set ↥(K ⊔ R₀)), himg, hdistL, hC3', Subgroup.bot_subgroupOf]
        exact commutator_le_fitting_of_sameFixedPoints hRK hR₀K hcop hcop₀ hCeq hcent0

/-- **BG Theorem 3.8** (Bender–Glauberman, LMS LNS 188, p. 17).  Let `G = KR` be a solvable group of
odd order with `K ⊴ G`, and suppose

1. `(|R|, |K|) = 1`;
2. `C_K(x) = C_K(R)` for all `x ∈ R^#` (here in the `⊓ K` form `C_G(x) ⊓ K = C_G(R) ⊓ K`); and
3. `C_{F(K)}(R) = 1`.

Then `⁅K, R⁆ ⊆ F(K)`.

The proof is `thm38_aux` specialised to `n = |G|`.  (Internally: induction on `|RK| = |G|`, reducing
— via the Fitting quotient `K̄ = K/F(K)` — to `K̄` a `p`-group and `R` of prime order, then a
chief-factor analysis split by `Theorem 3.4` and `G`-Lemma 2.6.3.) -/
theorem thm38 {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] {K R : Subgroup G}
    [hKnorm : K.Normal]
    (hodd : Odd (Nat.card G)) (hcompl : K.IsComplement' R)
    (hcop : Nat.Coprime (Nat.card ↥R) (Nat.card ↥K))
    (hcond2 : ∀ x ∈ (R : Set G), x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ⊓ K = Subgroup.centralizer (R : Set G) ⊓ K)
    (hC3 : Subgroup.centralizer (R : Set G) ⊓
      (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype = ⊥) :
    ⁅K, R⁆ ≤ (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype :=
  thm38_aux (Nat.card G) K R hKnorm hodd hcompl hcop hcond2 hC3 rfl

end OddOrder.BG.Ch1.S03h


