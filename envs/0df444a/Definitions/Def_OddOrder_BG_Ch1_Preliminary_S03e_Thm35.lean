-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03e_Thm35
-- name    : OddOrder_BG_Ch1_Preliminary_S03e_Thm35
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:03:40.181565+00:00
-- url     : https://prove2.me/theorems/b3132927-3d49-45b5-9784-667fe876a266
-- title:
--   BG §3: Theorem 3.5 (Frobenius action with one-dimensional fixed space)
-- statement:
--   Formalizes Theorem 3.5 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §3: let $G=KR$ be a Frobenius group with solvable kernel $K$ and cyclic complement $R$ of prime order, acting on a vector space $V$ over $F$ with $\mathrm{char}\,F\nmid|G|$. If $C_V(R)$ is one-dimensional then $K'\subseteq C_K(V)$. It is a sibling of Theorem 3.4 and upstream of Theorem 3.6.
--
--   The main declaration: `thm35` (BG Theorem 3.5 (general field)).
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S03e_Thm35.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S03e_Thm35.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03b_Lemma33
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03c_Thm37
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03d_Thm34
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03e_Thm35Prelim
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.Commutator.Basic

namespace OddOrder.BG.Ch1.S03e

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open scoped commutatorElement

/-- **BG Theorem 3.5, group-order strong-induction core** (algebraically closed `F`).

`Nat.card G = n` での強帰納法。結論 `∀ g ∈ ⁅K, K⁆, ρ g = 1` (= `K' ⊆ C_K(V)`)。
non-faithful 枝 (この induction backbone) は `C = ker ρ` で `G/C` に帰着 (Lemma 3.2)；
faithful 枝 ((3.4)/(3.5)/Clifford core) が hard core。詳細 = `notes/bg/s03_thm35.md`。 -/
private theorem thm35_aux : ∀ (n : ℕ)
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (K R : Subgroup G),
    IsFrobeniusGroup G K R → Group.IsSolvable ↥K →
    (∃ p : ℕ, p.Prime ∧ Nat.card ↥R = p) →
    (Nat.card G : F) ≠ 0 →
    Module.finrank F (Representation.invariants (ρ.comp R.subtype)) = 1 →
    Nat.card G = n →
    ∀ g ∈ ⁅K, K⁆, ρ g = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro F _ _ G _ _ V _ _ _ ρ K R hFrob hKsolv hRp hchar hCV1 hn
    have hKnorm : K.Normal := hFrob.isNormal
    -- `⁅K, K⁆ ≤ K`.
    have hKK_le : ⁅K, K⁆ ≤ K := Subgroup.commutator_le_right K K
    by_cases hfaithful : Function.Injective ρ
    · -- **faithful branch** (`C_G(V) = 1`): steps (3.4)/(3.5)/(Clifford core).
      obtain ⟨p, hp, hpcard⟩ := hRp
      have hRp' : (Nat.card ↥R).Prime := hpcard ▸ hp
      have : NeZero (Nat.card G : F) := ⟨hchar⟩
      have hkerbot : MonoidHom.ker ρ = ⊥ := (MonoidHom.ker_eq_bot_iff ρ).mpr hfaithful
      -- `char F ∤ |K|`, `char F ∤ |⁅K,K⁆ ⊔ R|`.
      have hcharK : (Nat.card ↥K : F) ≠ 0 := by
        obtain ⟨m, hm⟩ := K.card_subgroup_dvd_card
        intro h0; exact hchar (by rw [hm, Nat.cast_mul, h0, zero_mul])
      have hcharKR : (Nat.card ↥((⁅K, K⁆ : Subgroup G) ⊔ R) : F) ≠ 0 := by
        obtain ⟨m, hm⟩ := ((⁅K, K⁆ : Subgroup G) ⊔ R).card_subgroup_dvd_card
        intro h0; exact hchar (by rw [hm, Nat.cast_mul, h0, zero_mul])
      -- `R = ⟨x⟩` for a generator `x`; `closure (K ∪ {x}) = ⊤`.
      have hRne : R ≠ ⊥ := by
        intro hR; rw [hR, Subgroup.card_bot] at hpcard; exact hp.ne_one hpcard.symm
      have : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).mpr hRne
      obtain ⟨xr, hxr1⟩ := exists_ne (1 : ↥R)
      have hx1 : (xr : G) ≠ 1 := fun h => hxr1 (Subtype.ext (by rw [h]; rfl))
      set x := (xr : G) with hxdef
      have hxR : Subgroup.zpowers x = R :=
        OddOrder.BG.Ch1.S03d.zpowers_eq_of_prime_card hRp' xr.2 hx1
      have hgen : Subgroup.closure ((K : Set G) ∪ {x}) = ⊤ := by
        rw [Subgroup.closure_union, Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure, hxR]
        exact hFrob.isComplement.sup_eq_top
      have hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥R) := hFrob.coprime_card_kernel_complement
      rcases eq_or_ne (⁅K, K⁆ : Subgroup G) ⊥ with hK'eq | hK'ne
      · -- `⁅K, K⁆ = ⊥`: trivially `ρ g = 1` for `g ∈ ⁅K, K⁆`.
        intro g hg; rw [hK'eq, Subgroup.mem_bot] at hg; rw [hg]; exact map_one ρ
      · -- `⁅K, K⁆ ≠ ⊥`.
        have hKne : K ≠ ⊥ := fun h => hK'ne (by rw [h, Subgroup.commutator_bot_left])
        have hK'norm : (⁅K, K⁆ : Subgroup G).Normal := Subgroup.commutator_normal K K
        have hRnormK' : R ≤ Subgroup.normalizer (⁅K, K⁆ : Subgroup G) :=
          Subgroup.le_normalizer_of_normal
        -- **K' = ⁅K, K⁆ is abelian** (BG steps (3.4)+(5)): `⁅K, K⁆ < K` (solvable),
        -- apply IH to `K'R`.
        have hcomm : ∀ a b : ↥(⁅K, K⁆ : Subgroup G), (a : G) * (b : G) = (b : G) * (a : G) := by
          have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
          have hK'ltK : (⁅K, K⁆ : Subgroup G) < K := by
            have htop : (⊤ : Subgroup ↥K).map K.subtype = K := by
              rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
            have hmap : (⁅K, K⁆ : Subgroup G) = (commutator ↥K).map K.subtype := by
              rw [commutator_def, Subgroup.map_commutator, htop]
            rw [hmap]
            calc (commutator ↥K).map K.subtype
                < (⊤ : Subgroup ↥K).map K.subtype :=
                  (Subgroup.map_lt_map_iff_of_injective K.subtype_injective).mpr
                    (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥K)
              _ = K := htop
          have hFrobK' := isFrobeniusGroup_subgroupOf_sup hFrob hKK_le hRnormK' hK'ne
          -- `|K'R| < n` (from `|K'| < |K|`).
          have hK'cardlt : Nat.card ↥(⁅K, K⁆ : Subgroup G) < Nat.card ↥K := by
            refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hKK_le))
              (fun heq => (ne_of_lt hK'ltK) (Subgroup.eq_of_le_of_card_ge hKK_le heq.ge))
          have hlt : Nat.card ↥((⁅K, K⁆ : Subgroup G) ⊔ R) < n := by
            have e1 := hFrobK'.isComplement.card_mul_card
            have e2 := hFrob.isComplement.card_mul_card
            rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left)).toEquiv,
              Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv] at e1
            rw [← hn, ← e2, ← e1]
            exact mul_lt_mul_of_pos_right hK'cardlt Nat.card_pos
          -- solvability of the `K'`-kernel inside `K'R`.
          have hK'solv0 : Group.IsSolvable ↥(⁅K, K⁆ : Subgroup G) := by
            have : Group.IsSolvable ↥((⁅K, K⁆ : Subgroup G).subgroupOf K) := inferInstance
            exact Group.isSolvable_of_surjective
              (f := (Subgroup.subgroupOfEquivOfLe hKK_le).toMonoidHom)
              (Subgroup.subgroupOfEquivOfLe hKK_le).surjective
          have hK'solv :
              Group.IsSolvable ↥((⁅K, K⁆ : Subgroup G).subgroupOf ((⁅K, K⁆ : Subgroup G) ⊔ R)) := by
            have e : ↥(⁅K, K⁆ : Subgroup G) ≃*
                ↥((⁅K, K⁆ : Subgroup G).subgroupOf ((⁅K, K⁆ : Subgroup G) ⊔ R)) :=
              (Subgroup.subgroupOfEquivOfLe (le_sup_left)).symm
            exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
          have hRpK' : ∃ q : ℕ, q.Prime ∧
              Nat.card ↥(R.subgroupOf ((⁅K, K⁆ : Subgroup G) ⊔ R)) = q :=
            ⟨p, hp, (Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv).trans hpcard⟩
          -- `C_V(R')` is the same fixed space, still one-dimensional.
          have hCV1K' : Module.finrank F (Representation.invariants
              ((ρ.comp ((⁅K, K⁆ : Subgroup G) ⊔ R).subtype).comp
                (R.subgroupOf ((⁅K, K⁆ : Subgroup G) ⊔ R)).subtype)) = 1 := by
            have heqinv : Representation.invariants
                ((ρ.comp ((⁅K, K⁆ : Subgroup G) ⊔ R).subtype).comp
                  (R.subgroupOf ((⁅K, K⁆ : Subgroup G) ⊔ R)).subtype)
                = Representation.invariants (ρ.comp R.subtype) := by
              ext v
              rw [Representation.mem_invariants, Representation.mem_invariants]
              constructor
              · intro hv r
                have hrHR : (r : G) ∈ (⁅K, K⁆ : Subgroup G) ⊔ R := (le_sup_right : R ≤ _) r.2
                have hmem : (⟨(r : G), hrHR⟩ : ↥((⁅K, K⁆ : Subgroup G) ⊔ R))
                    ∈ R.subgroupOf ((⁅K, K⁆ : Subgroup G) ⊔ R) := by
                  rw [Subgroup.mem_subgroupOf]; exact r.2
                exact hv ⟨⟨(r : G), hrHR⟩, hmem⟩
              · intro hv r'
                have hr'R : ((r' : ↥((⁅K, K⁆ : Subgroup G) ⊔ R)) : G) ∈ R := by
                  have := r'.2; rwa [Subgroup.mem_subgroupOf] at this
                exact hv ⟨((r' : ↥((⁅K, K⁆ : Subgroup G) ⊔ R)) : G), hr'R⟩
            rw [heqinv]; exact hCV1
          have hIH := IH (Nat.card ↥((⁅K, K⁆ : Subgroup G) ⊔ R)) hlt
            (ρ.comp ((⁅K, K⁆ : Subgroup G) ⊔ R).subtype) ((⁅K, K⁆ : Subgroup G).subgroupOf _)
            (R.subgroupOf _) hFrobK' hK'solv hRpK' hcharKR hCV1K' rfl
          -- pull back: `⁅K', K'⁆ ≤ ker ρ = ⊥`, so `K'` is abelian.
          have hker : (⁅(⁅K, K⁆ : Subgroup G), (⁅K, K⁆ : Subgroup G)⁆ : Subgroup G) ≤
              MonoidHom.ker ρ := by
            intro g hg
            have hmap : (⁅(⁅K, K⁆ : Subgroup G), (⁅K, K⁆ : Subgroup G)⁆ : Subgroup G)
                = (⁅(⁅K, K⁆ : Subgroup G).subgroupOf ((⁅K, K⁆ : Subgroup G) ⊔ R),
                    (⁅K, K⁆ : Subgroup G).subgroupOf ((⁅K, K⁆ : Subgroup G) ⊔ R)⁆).map
                  ((⁅K, K⁆ : Subgroup G) ⊔ R).subtype := by
              rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
                inf_eq_left.mpr (le_sup_left)]
            rw [hmap, Subgroup.mem_map] at hg
            obtain ⟨g', hg'mem, hg'eq⟩ := hg
            rw [MonoidHom.mem_ker, ← hg'eq]; exact hIH g' hg'mem
          have hK'cbot : (⁅(⁅K, K⁆ : Subgroup G), (⁅K, K⁆ : Subgroup G)⁆ : Subgroup G) = ⊥ :=
            le_bot_iff.mp (hkerbot ▸ hker)
          intro a b
          have hab : ⁅(a : G), (b : G)⁆ ∈
              (⁅(⁅K, K⁆ : Subgroup G), (⁅K, K⁆ : Subgroup G)⁆ : Subgroup G) :=
            Subgroup.commutator_mem_commutator a.2 b.2
          rw [hK'cbot, Subgroup.mem_bot] at hab
          exact commutatorElement_eq_one_iff_commute.mp hab
        -- **main dichotomy**: `⁅K, K⁆` acts trivially on every irreducible subrepresentation.
        intro g hg
        by_contra hg1
        obtain ⟨U, hUirr, hUg⟩ := OddOrder.BG.Ch1.S03d.exists_irreducible_subrep_apply_ne ρ hg1
        apply hUg
        have := hUirr
        have : Nontrivial ↥U.toSubmodule := by
          by_contra hcon
          rw [not_nontrivial_iff_subsingleton] at hcon
          exact hUg (Subsingleton.elim _ _)
        by_cases hKtrivU : ∀ k : ↥K, U.toRepresentation (k : G) = 1
        · exact hKtrivU ⟨g, hKK_le hg⟩
        · push Not at hKtrivU
          have hCU1 := finrank_invariants_subrep_eq_one ρ hFrob hcharK hCV1 U hKtrivU
          have hCUK' := invariants_commutator_ne_bot_of_irreducible U.toRepresentation hFrob x hxR
            hRp' hgen hchar hcharK hcharKR hcop hK'ne hcomm hCU1
          exact trivial_of_invariants_comp_ne_bot U.toRepresentation (⁅K, K⁆ : Subgroup G)
            hCUK' g hg
    · -- **non-faithful branch**: `C = ker ρ ≠ ⊥`; reduce to `G/C` (Lemma 3.2).
      set C := MonoidHom.ker ρ with hCdef
      have hCnorm : C.Normal := MonoidHom.normal_ker _
      by_cases hKC : K ≤ C
      · -- `K ≤ C`: `⁅K, K⁆ ≤ K ≤ C = ker ρ`, so `ρ` kills `⁅K, K⁆`.
        intro g hg
        exact MonoidHom.mem_ker.mp (le_trans hKK_le hKC hg)
      · -- `¬ K ≤ C`: `C ⊆ K` (Frobenius normal ⊆ kernel) and `G/C` is Frobenius; apply IH.
        have hCK : C ≤ K := normal_le_kernel_of_not_kernel_le hFrob hKC
        -- `ρ` factors through `G/C` as `ρ̄ = ofQuotient ρ C`.
        have hIsTriv : Representation.IsTrivial (ρ.comp C.subtype) := by
          refine ⟨fun c => ?_⟩
          change ρ (c : G) = LinearMap.id
          rw [MonoidHom.mem_ker.mp c.2]; rfl
        set ρbar := Representation.ofQuotient ρ C with hρbar
        have : (K.map (QuotientGroup.mk' C)).Normal :=
          hKnorm.map (QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C)
        have hKbarsolv : Group.IsSolvable ↥(K.map (QuotientGroup.mk' C)) :=
          Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' C) K)
        -- `|G| = |G/C| · |C|`, so `|G/C| < |G|` (since `C ≠ ⊥`).
        have hCne : C ≠ ⊥ := fun h => hfaithful ((MonoidHom.ker_eq_bot_iff ρ).mp h)
        have hGcard : Nat.card G = Nat.card (G ⧸ C) * Nat.card ↥C :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup C
        have hGCdvd : Nat.card (G ⧸ C) ∣ Nat.card G := ⟨_, hGcard⟩
        have hCgt : 1 < Nat.card ↥C :=
          Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot C).mpr hCne)
        have hlt : Nat.card (G ⧸ C) < n := by
          rw [← hn, hGcard]; exact (Nat.lt_mul_iff_one_lt_right Nat.card_pos).mpr hCgt
        have hcharQ : (Nat.card (G ⧸ C) : F) ≠ 0 := by
          obtain ⟨m, hm⟩ := hGCdvd; intro h0; apply hchar; rw [hm, Nat.cast_mul, h0, zero_mul]
        -- `G/C` is Frobenius with kernel `K̄`, complement `R̄`.
        have hFrobQ : IsFrobeniusGroup (G ⧸ C) (K.map (QuotientGroup.mk' C))
            (R.map (QuotientGroup.mk' C)) :=
          OddOrder.BG.Ch1.S03c.frobenius_quotient_of_normal_lt_kernel hFrob hCK hKC hKsolv
        -- `C ⊓ R = ⊥` (since `C ≤ K` and `K ⊓ R = ⊥`), so `|R̄| = |R|` is prime.
        have hCR : C ⊓ R = ⊥ := by
          rw [eq_bot_iff]
          exact le_trans (inf_le_inf_right R hCK) (le_of_eq hFrob.isComplement.disjoint.eq_bot)
        obtain ⟨p, hp, hpcard⟩ := hRp
        have hRp' : (Nat.card ↥R).Prime := hpcard ▸ hp
        have hRQcard : Nat.card ↥(R.map (QuotientGroup.mk' C)) = Nat.card ↥R := by
          rcases (Nat.dvd_prime hRp').mp (Subgroup.card_map_dvd R (QuotientGroup.mk' C)) with h1 | h
          · exfalso
            have hbot : R.map (QuotientGroup.mk' C) = ⊥ := Subgroup.card_eq_one.mp h1
            rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
            have hRbot : R = ⊥ := by
              rw [eq_bot_iff]; intro x hx
              have : x ∈ C ⊓ R := ⟨hbot hx, hx⟩
              rwa [hCR, Subgroup.mem_bot] at this
            exact hp.ne_one (hpcard ▸ Subgroup.card_eq_one.mpr hRbot)
          · exact h
        have hRpQ : ∃ q : ℕ, q.Prime ∧ Nat.card ↥(R.map (QuotientGroup.mk' C)) = q :=
          ⟨p, hp, hRQcard.trans hpcard⟩
        -- `C_V(R̄) = C_V(R)` (same fixed subspace), so still one-dimensional.
        have heqinv : Representation.invariants (ρbar.comp (R.map (QuotientGroup.mk' C)).subtype)
            = Representation.invariants (ρ.comp R.subtype) := by
          ext v
          rw [Representation.mem_invariants, Representation.mem_invariants]
          constructor
          · intro hv r
            have hkey : ρbar ((r : G) : G ⧸ C) v = v :=
              hv ⟨QuotientGroup.mk' C (r : G), Subgroup.mem_map_of_mem _ r.2⟩
            rwa [hρbar, Representation.ofQuotient_coe_apply] at hkey
          · intro hv rbar
            obtain ⟨r', hr', hr'eq⟩ := rbar.2
            change ρbar (rbar : G ⧸ C) v = v
            rw [← hr'eq, hρbar, QuotientGroup.mk'_apply, Representation.ofQuotient_coe_apply]
            exact hv ⟨r', hr'⟩
        have hCV1Q : Module.finrank F
            (Representation.invariants (ρbar.comp (R.map (QuotientGroup.mk' C)).subtype)) = 1 := by
          rw [heqinv]; exact hCV1
        -- IH on `G/C`.
        have hIHconcl := IH (Nat.card (G ⧸ C)) hlt ρbar (K.map (QuotientGroup.mk' C))
          (R.map (QuotientGroup.mk' C)) hFrobQ hKbarsolv hRpQ hcharQ hCV1Q rfl
        -- pull `⁅K, K⁆` back: `mk g ∈ ⁅K̄, K̄⁆`, so `ρ̄ (mk g) = 1`, i.e. `ρ g = 1`.
        intro g hg
        have hgbar : (QuotientGroup.mk' C) g ∈
            ⁅K.map (QuotientGroup.mk' C), K.map (QuotientGroup.mk' C)⁆ := by
          rw [← Subgroup.map_commutator]; exact Subgroup.mem_map_of_mem _ hg
        have h1 := hIHconcl _ hgbar
        apply LinearMap.ext
        intro v
        have h2 : ρbar ((g : G) : G ⧸ C) v = (1 : Module.End F V) v :=
          congrFun (congrArg DFunLike.coe h1) v
        rwa [hρbar, Representation.ofQuotient_coe_apply] at h2

/-- **BG Theorem 3.5** (algebraically closed core).  `G = KR` a Frobenius group with solvable kernel
`K` and prime-order complement `R`, acting on `V/F` with `char F ∤ |G|` and `F` algebraically
closed.  If `dim C_V(R) = 1` then `K' ⊆ C_K(V)` (i.e. `ρ` kills every element of `⁅K, K⁆`).

Strong induction on `|G|` (`thm35_aux`); the hard core (step 9 of the faithful branch) is Clifford
theory over an algebraically closed field.  See `notes/bg/s03_thm35.md`. -/
theorem thm35_algClosed
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (K R : Subgroup G)
    (hFrob : IsFrobeniusGroup G K R) (hKsolv : Group.IsSolvable ↥K)
    (hRp : ∃ p : ℕ, p.Prime ∧ Nat.card ↥R = p)
    (hchar : (Nat.card G : F) ≠ 0)
    (hCV1 : Module.finrank F (Representation.invariants (ρ.comp R.subtype)) = 1) :
    ∀ g ∈ ⁅K, K⁆, ρ g = 1 :=
  thm35_aux (Nat.card G) ρ K R hFrob hKsolv hRp hchar hCV1 rfl

open OddOrder.RepresentationTheory in
/-- **BG Theorem 3.5** (general field).  `G = KR` a Frobenius group with solvable kernel `K` and
prime-order complement `R`, acting on `V/F` with `char F ∤ |G|` (any field `F`).  If `C_V(R)` is
one-dimensional then `K' ⊆ C_K(V)` (i.e. `ρ` kills every element of `⁅K, K⁆`).

Reduces to the algebraically closed core `thm35_algClosed` by base change to the algebraic closure
`F̄` (BG (2.9)): `char F̄ ∤ |G|`, and `dim C_{F̄⊗V}(R) = dim C_V(R) = 1` transfers along `F → F̄`
(`finrank_invariants_baseChangeRepresentation`); the conclusion `ρ̄ g = 1 ⟹ ρ g = 1` descends
because `v ↦ 1 ⊗ v` is injective (`F̄` is faithfully flat over `F`). -/
theorem thm35
    {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (K R : Subgroup G)
    (hFrob : IsFrobeniusGroup G K R) (hKsolv : Group.IsSolvable ↥K)
    (hRp : ∃ p : ℕ, p.Prime ∧ Nat.card ↥R = p)
    (hchar : (Nat.card G : F) ≠ 0)
    (hCV1 : Module.finrank F (Representation.invariants (ρ.comp R.subtype)) = 1) :
    ∀ g ∈ ⁅K, K⁆, ρ g = 1 := by
  -- `char F̄ ∤ |G|`.
  have hchar' : (Nat.card G : AlgebraicClosure F) ≠ 0 := by
    rw [← map_natCast (algebraMap F (AlgebraicClosure F))]
    rwa [Ne, map_eq_zero_iff _ (algebraMap F (AlgebraicClosure F)).injective]
  -- `dim C_{F̄⊗V}(R) = dim C_V(R) = 1`.
  have hCV1' : Module.finrank (AlgebraicClosure F) (Representation.invariants
      ((baseChangeRepresentation (AlgebraicClosure F) ρ).comp R.subtype)) = 1 := by
    rw [← baseChangeRepresentation_comp, finrank_invariants_baseChangeRepresentation]
    exact hCV1
  -- apply the algebraically closed core over `F̄`, then descend `v ↦ 1 ⊗ v`.
  intro g hg
  have hbar : baseChangeRepresentation (AlgebraicClosure F) ρ g = 1 :=
    thm35_algClosed (baseChangeRepresentation (AlgebraicClosure F) ρ) K R hFrob hKsolv hRp
      hchar' hCV1' g hg
  apply LinearMap.ext
  intro v
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := F) (B := AlgebraicClosure F) V
  have hmap := congrArg
    (fun f : TensorProduct F (AlgebraicClosure F) V →ₗ[AlgebraicClosure F]
      TensorProduct F (AlgebraicClosure F) V => f (1 ⊗ₜ[F] v)) hbar
  simpa using hmap

end OddOrder.BG.Ch1.S03e


