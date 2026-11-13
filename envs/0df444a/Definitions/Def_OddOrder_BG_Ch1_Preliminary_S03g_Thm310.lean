-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03g_Thm310
-- name    : OddOrder_BG_Ch1_Preliminary_S03g_Thm310
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:15:50.687698+00:00
-- url     : https://prove2.me/theorems/db09f1c6-e15d-49f4-8b92-2a0c3c5d89f3
-- title:
--   BG §3E: Proposition 3.9 and Theorem 3.10
-- statement:
--   Formalizes Proposition 3.9 and Theorem 3.10 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §3E ('Regular actions and nilpotent targets'), the last block of §3. Proposition 3.9 (a $p$-group acting regularly on a $q$-group is cyclic) is proved from Gorenstein 5.3.14 via formalized Isaacs results, and Theorem 3.10(a) ($|K|$ prime) is needed by Proposition 14.2(g).
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 1 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S03g_Thm310.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S03g_Thm310.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch02_Subnormality_Theorem211Wielandt
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Main
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_Main
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7D1_BurnsideSetup
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03g_Thm310Module

namespace OddOrder.BG.Ch1.S03

open OddOrder.GroupTheory

open OddOrder.Isaacs.Ch06

open scoped IsMulCommutative

variable {R H : Type*}

/-- **BG Theorem 3.10(a)** (concrete conjugation form).  Let `E = U ⋊ R` be a Frobenius group
(Frobenius kernel `U`, complement `R`) inside `G`, with `U` **abelian**, acting by conjugation on a
nonidentity nilpotent subgroup `M` that `E` normalizes, with `(|E|, |M|) = 1`.  Suppose
`C_M(U) = 1` and `R` acts in a *prime manner* on `M` (`C_M(x) = C_M(R)` for every `x ∈ R^#`).  Then
`|R|` is prime.

This is the conclusion `(a)` of BG Theorem 3.10 in the form used by Proposition 14.2(g) (where
`U = E₂E₃` is the abelian Frobenius kernel and `R = E₁` the cyclic complement).  The proof reduces
`M` to a minimal `E`-invariant normal (hence elementary abelian) subgroup `M₀`, views `M₀` as a
module via `prime_card_of_elemAbelian_mulDistrib`, and applies the abelian Frobenius weight
argument.

Note: `U` abelian lets us bypass BG's `K₀`-minimal-normal reduction (BG Case 2, first half), which
is unnecessary for the Proposition 14.2(g) application.

**Stronger than the book on the `M` axis**: BG Theorem 3.10 assumes `M` **nilpotent**, but with
`U` abelian the argument below never uses it — the reduction to a minimal `E`-invariant normal
subgroup `M₀` needs only that `M` is a nonidentity `E`-invariant subgroup with `(|E|,|M|) = 1`
inside the solvable `M ⊔ E`.  The nilpotence hypothesis was therefore dropped (it was already
inert, carried as `_hMnilp`). -/
theorem prime_card_complement_of_frobenius_conj {G : Type*} [Group G] [Finite G]
    {E U K M : Subgroup G} (hsolv : Group.IsSolvable ↥(M ⊔ E))
    (hUE : U ≤ E) (hKE : K ≤ E)
    (hUK_frob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥E (U.subgroupOf E) (K.subgroupOf E))
    (hUab : ∀ a b : ↥U, (a : G) * (b : G) = (b : G) * (a : G))
    (hEM : E ≤ Subgroup.normalizer M)
    (hMne : M ≠ ⊥)
    (hcop : Nat.Coprime (Nat.card ↥E) (Nat.card ↥M))
    (hCU : M ⊓ Subgroup.centralizer (U : Set G) = ⊥)
    (hcond3 : ∀ x ∈ K, x ≠ 1 →
        M ⊓ Subgroup.centralizer ({x} : Set G) = M ⊓ Subgroup.centralizer (K : Set G)) :
    ∃ p : ℕ, p.Prime ∧ Nat.card ↥K = p := by
  classical
  -- Set `L := M ⊔ E`.  We have `M ≤ L`, `E ≤ L`.
  set L : Subgroup G := M ⊔ E with hL_def
  have hML : M ≤ L := le_sup_left
  have hEL : E ≤ L := le_sup_right
  have : Finite ↥L := inferInstance
  have : Group.IsSolvable ↥L := hsolv
  -- STEP A: `M ⊴ L`.
  have hL_norm_M : L ≤ Subgroup.normalizer M :=
    sup_le (Subgroup.le_normalizer) hEM
  have hMsubL_normal : (M.subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hL_norm_M
  have hMsubL_ne : M.subgroupOf L ≠ ⊥ := by
    rw [Ne, Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hML]
    exact hMne
  -- STEP B: a minimal normal `M₀L : Subgroup ↥L` inside `M.subgroupOf L`.
  obtain ⟨M₀L, hM₀L_min, hM₀L_le⟩ :=
    OddOrder.Isaacs.Ch02.exists_isMinimalNormal_le_of_normal (M.subgroupOf L) hMsubL_ne
  obtain ⟨p, hp, hM₀L_ea⟩ :=
    OddOrder.Isaacs.Ch03.minimal_normal_isElementaryAbelian_of_isSolvable hM₀L_min
  have : Fact p.Prime := ⟨hp⟩
  -- `M₀L` is elementary abelian (TYPE form on `↥M₀L`); record its commutativity.
  have hM₀L_ea_type : OddOrder.GroupTheory.IsElementaryAbelian p ↥M₀L := hM₀L_ea
  -- STEP C: push down to `M₀ : Subgroup G`.
  set M₀ : Subgroup G := M₀L.map L.subtype with hM₀_def
  have hL_subtype_inj : Function.Injective L.subtype := L.subtype_injective
  -- `M₀ ≤ M`.
  have hM₀M : M₀ ≤ M := by
    rw [hM₀_def]
    refine (Subgroup.map_mono hM₀L_le).trans ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hML]
  -- `M₀ ≠ ⊥`.
  have hM₀ne : M₀ ≠ ⊥ := by
    rw [hM₀_def, Ne, Subgroup.map_eq_bot_iff_of_injective _ hL_subtype_inj]
    exact hM₀L_min.2.1
  -- `↥M₀ ≃* ↥M₀L`.
  have eM₀ : ↥M₀ ≃* ↥M₀L :=
    (Subgroup.equivMapOfInjective M₀L L.subtype hL_subtype_inj).symm
  -- Transport `Finite`, `Nontrivial`, `CommGroup`, EA to `↥M₀`.
  have : Finite ↥M₀ := Finite.of_equiv _ eM₀.symm.toEquiv
  have : Nontrivial ↥M₀L := (M₀L.nontrivial_iff_ne_bot).mpr hM₀L_min.2.1
  have : Nontrivial ↥M₀ := eM₀.symm.injective.nontrivial
  have hM₀_ea : OddOrder.GroupTheory.IsElementaryAbelian p ↥M₀ :=
    OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv eM₀.symm hM₀L_ea_type
  have : IsMulCommutative ↥M₀ :=
    (isMulCommutative_iff).mpr (fun a b => hM₀_ea.comm a b)
  -- `↥M₀` is a `CommGroup` (scoped instance from `IsMulCommutative`).
  let : CommGroup ↥M₀ := inferInstance
  -- `E ≤ N_G(M₀)`.
  have hM₀L_normal : M₀L.Normal := hM₀L_min.1
  have hEM₀ : E ≤ Subgroup.normalizer M₀ := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    -- `ε := ⟨e, hEL he⟩ : ↥L`, with `(ε : G) = e`.
    set ε : ↥L := ⟨e, hEL he⟩ with hε_def
    have hε_coe : (ε : G) = e := rfl
    intro x
    constructor
    · -- `x ∈ M₀ → e * x * e⁻¹ ∈ M₀`.
      intro hx
      rw [hM₀_def, Subgroup.mem_map] at hx ⊢
      obtain ⟨x₀, hx₀_mem, hx₀_eq⟩ := hx
      -- Conjugate `x₀` by `ε` inside `↥L`; normality keeps it in `M₀L`.
      refine ⟨ε * x₀ * ε⁻¹, hM₀L_normal.conj_mem x₀ hx₀_mem ε, ?_⟩
      rw [Subgroup.coe_subtype] at hx₀_eq ⊢
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hε_coe, hx₀_eq]
    · -- `e * x * e⁻¹ ∈ M₀ → x ∈ M₀`.
      intro hx
      rw [hM₀_def, Subgroup.mem_map] at hx ⊢
      obtain ⟨y₀, hy₀_mem, hy₀_eq⟩ := hx
      -- `x = e⁻¹ * (e x e⁻¹) * e`, conjugate `y₀` by `ε`.
      refine ⟨ε⁻¹ * y₀ * ε, hM₀L_normal.conj_mem' y₀ hy₀_mem ε, ?_⟩
      rw [Subgroup.coe_subtype] at hy₀_eq ⊢
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hε_coe, hy₀_eq]
      group
  -- STEP D: the conjugation action of `↥E` on `↥M₀`.
  let : MulDistribMulAction ↥E ↥M₀ :=
    OddOrder.Isaacs.Ch07.conjActionOfNormalizes E M₀ hEM₀
  have hact : ∀ (a : ↥E) (n : ↥M₀), ((a • n : ↥M₀) : G) = (a : G) * (n : G) * (a : G)⁻¹ :=
    fun _ _ => rfl
  -- STEP E: apply the module-level theorem with `K := U.subgroupOf E`, `R := K.subgroupOf E`.
  have hUsubE_normal : (U.subgroupOf E).Normal := hUK_frob.isNormal
  -- `hpK : ¬ p ∣ Nat.card ↥(U.subgroupOf E)`.
  have hpdvdM₀ : p ∣ Nat.card ↥M₀ := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := ↥M₀)).mp hM₀_ea.isPGroup
    rcases n with _ | n
    · simp only [pow_zero] at hn
      exact absurd hn (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne'
    · rw [hn]; exact dvd_pow_self p (Nat.succ_ne_zero n)
  have hpK : ¬ p ∣ Nat.card ↥(U.subgroupOf E) := by
    intro hpdvdU
    -- `card (U.subgroupOf E) = card U`.
    have hcardUE : Nat.card ↥(U.subgroupOf E) = Nat.card ↥U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUE).toEquiv
    rw [hcardUE] at hpdvdU
    have hpE : p ∣ Nat.card ↥E := hpdvdU.trans (Subgroup.card_dvd_of_le hUE)
    have hpM : p ∣ Nat.card ↥M := hpdvdM₀.trans (Subgroup.card_dvd_of_le hM₀M)
    have := Nat.eq_one_of_dvd_coprimes hcop hpE hpM
    exact hp.one_lt.ne' this
  -- `hKab` from `hUab`.
  have hKab : ∀ a b : ↥(U.subgroupOf E),
      (a : ↥E) * (b : ↥E) = (b : ↥E) * (a : ↥E) := by
    intro a b
    apply Subtype.ext
    -- The `G`-values of `(a : ↥E)` and `(b : ↥E)` lie in `U`.
    have ha : ((a : ↥E) : G) ∈ U := (Subgroup.mem_subgroupOf).mp a.2
    have hb : ((b : ↥E) : G) ∈ U := (Subgroup.mem_subgroupOf).mp b.2
    exact hUab ⟨_, ha⟩ ⟨_, hb⟩
  -- `hCK`.
  have hCK : ∀ m : ↥M₀, (∀ k : ↥(U.subgroupOf E), (k : ↥E) • m = m) → m = 1 := by
    intro m hm
    apply Subtype.ext
    -- `(m : G) ∈ M` and `(m : G) ∈ centralizer U`, so `(m : G) ∈ M ⊓ centralizer U = ⊥`.
    have hmM : (m : G) ∈ M := hM₀M m.2
    have hmCU : (m : G) ∈ Subgroup.centralizer (U : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      -- `u ∈ U`, so `⟨u, hu⟩ : ↥U`; view it inside `↥E` via `U.subgroupOf E`.
      have huE : u ∈ E := hUE hu
      have hkmem : (⟨u, huE⟩ : ↥E) ∈ U.subgroupOf E := (Subgroup.mem_subgroupOf).mpr hu
      set k : ↥(U.subgroupOf E) := ⟨⟨u, huE⟩, hkmem⟩ with hk_def
      -- `(k : ↥E) • m = m`, push to `G`: `u * (m:G) * u⁻¹ = (m:G)`.
      have hconj : u * (m : G) * u⁻¹ = (m : G) :=
        (hact (k : ↥E) m).symm.trans (congrArg Subtype.val (hm k))
      -- rearrange to `u * (m:G) = (m:G) * u`.
      rw [mul_inv_eq_iff_eq_mul] at hconj
      rw [hconj]
    have hmem : (m : G) ∈ M ⊓ Subgroup.centralizer (U : Set G) :=
      ⟨hmM, hmCU⟩
    rw [hCU] at hmem
    simpa using hmem
  -- `hFrob`.
  have hFrob : ∀ r ∈ K.subgroupOf E, r ≠ 1 → ∀ k ∈ U.subgroupOf E, k ≠ 1 →
      r * k * r⁻¹ ≠ k := hUK_frob.conj_frobenius
  -- `hcond3`.
  have hcond3' : ∀ x : ↥E, x ∈ K.subgroupOf E → x ≠ 1 →
      ∀ m : ↥M₀, ((x : ↥E) • m = m) ↔ (∀ s : ↥(K.subgroupOf E), (s : ↥E) • m = m) := by
    intro x hxK hx1 m
    -- `(x : G) ∈ K`, `(x : G) ≠ 1`.
    have hxG : (x : G) ∈ K := (Subgroup.mem_subgroupOf).mp hxK
    have hxG1 : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hmM : (m : G) ∈ M := hM₀M m.2
    -- The textbook condition for `(x : G)`.
    have hcondx := hcond3 (x : G) hxG hxG1
    constructor
    · -- LHS → RHS.
      intro hxm s
      -- From `hxm`: `(x:G) * (m:G) * (x:G)⁻¹ = (m:G)`.
      have hxm' : (x : G) * (m : G) * (x : G)⁻¹ = (m : G) :=
        (hact x m).symm.trans (congrArg Subtype.val hxm)
      -- Hence `(m:G) ∈ M ⊓ centralizer {(x:G)}`.
      have hmem_x : (m : G) ∈ M ⊓ Subgroup.centralizer ({(x : G)} : Set G) := by
        refine ⟨hmM, Subgroup.mem_centralizer_iff.mpr ?_⟩
        rintro y hy
        rw [Set.mem_singleton_iff] at hy; subst y
        -- `(x:G) * (m:G) = (m:G) * (x:G)`.
        rw [← mul_inv_eq_iff_eq_mul]; exact hxm'
      rw [hcondx] at hmem_x
      -- Now `(m:G) ∈ M ⊓ centralizer K`, so `(m:G)` centralizes `(s:G) ∈ K`.
      have hsG : (s : G) ∈ K := (Subgroup.mem_subgroupOf).mp s.2
      have hcomm : (s : G) * (m : G) = (m : G) * (s : G) :=
        Subgroup.mem_centralizer_iff.mp hmem_x.2 (s : G) hsG
      -- Conclude `(s : ↥E) • m = m`.
      apply Subtype.ext
      rw [hact s m, mul_inv_eq_iff_eq_mul, ← hcomm]
    · -- RHS → LHS: take `s := x`.
      intro h
      exact h ⟨x, hxK⟩
  -- Assemble.
  obtain ⟨p', hp'_prime, hp'_card⟩ :=
    prime_card_of_elemAbelian_mulDistrib (p := p) (H := ↥E) (M := ↥M₀) hM₀_ea
      (K := U.subgroupOf E) (R := K.subgroupOf E)
      (hUK_frob.ne_bot_complement) hKab hpK hCK hFrob hcond3'
  -- STEP F: convert `Nat.card ↥(K.subgroupOf E) = Nat.card ↥K`.
  refine ⟨p', hp'_prime, ?_⟩
  rw [← hp'_card]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKE).toEquiv).symm

end OddOrder.BG.Ch1.S03


