-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03f_Thm36
-- name    : OddOrder_BG_Ch1_Preliminary_S03f_Thm36
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:12:48.275846+00:00
-- url     : https://prove2.me/theorems/5fc9578f-cff8-4c8b-a645-6493cf48f5de
-- title:
--   BG §3: Theorem 3.6 (the $p$-length-one subprogram)
-- statement:
--   Formalizes Theorem 3.6 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §3: let $G$ be solvable of odd order, $H\lhd G$ a normal Hall subgroup with complement $R$, and $R_0\le R$ of prime order such that $C_H(R_0)$ is a Z-group; then a $p$-length-one conclusion holds. The file assembles the strong-induction minimal-counterexample argument from the phase lemmas.
--
--   The main declaration: `thm36_aux`.
--
--   The bundle also proves 1 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S03f_Thm36.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S03f_Thm36.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S01b_Prop116
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03_FrobeniusActions
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03f_OrbitParity
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03f_Endgame
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03f_R0Action
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03f_ComplementK
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03f_Prelim
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03d_Thm34
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03e_Thm35
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_PLengthTransfer
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_OperatorQuotientAction
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_OperatorMaschke
import Definitions.Def_OddOrder_GroupTheory_ZGroup

namespace OddOrder.BG.Ch1.S03f

open scoped commutatorElement Pointwise IsMulCommutative

open OddOrder.GroupTheory OddOrder.Isaacs.Ch04 OddOrder.BG.Ch1.OperatorQuotientAction

set_option maxHeartbeats 2400000 in
-- the `IsMulCommutative` scoped instances (priority 50) cycle with `CommMagma.to_isCommutative`;
-- failing class searches on `↥KG ⧸ commutator ↥KG` (Phase D, (3.29)–(3.30)) must exhaust that
-- branch, which overflows the default 20000 budget (results are cached per goal, so this is a
-- one-time cost per distinct search)
set_option synthInstance.maxHeartbeats 400000 in
/-- **BG Theorem 3.6, minimal-counterexample core** (strong induction on `|G|`, mmd L955).

The hypotheses are exactly those of `thm36`, with an extra `Nat.card G = n` so the strong induction
can apply the IH to proper subgroups (`⁅H,R⁆R` at (3.6), `VXPR₀` at (3.22)) and quotients (`G/X` at
(3.7)).  The proof opens with `by_contra hcounter` (the counterexample assumption
`¬ hasPLengthOne p ↥⁅H,R⁆`) and derives the chain (3.6)–(3.38); each place that proves "`H` has
`p`-length one" contradicts `hcounter` (via `H = ⁅H,R⁆` from (3.6)), and the orbit-parity argument
(3.38) is the final contradiction.

**状態**: ✅ Phase A–F ((3.6)–(3.38)) すべて完了, sorry-free.
消費済み大物: Thm 3.4 ×2 ((3.19),(3.30)), Thm 3.5 ((3.34)), Gor 5.3.7 ((3.25)),
**Thm 2.6(a) ×2 ((3.36) の `|K:Z|=q²` 枝, (3.37) の dim-2 枝)**, Prop 1.16(2) ((3.38)).
IH-free セグメント (Phase B/C, (3.29)–(3.38)) は `S03f_ComplementK` / `S03f_R0Action` /
`S03f_Endgame` に分離 — ここに残るのは IH を消費する Phase A/D と、各セグメントの
確立事実の受け渡しだけ.

(`maxHeartbeats`: equations (3.6)–(3.37) を 1 つの minimal-counterexample 証明で運ぶため宣言が
巨大で、既定の 200000 を超える。IH を消費する Phase A–E は誘導の内側から切り出せないため、
これ以上の分割は IH 自体の仮説化が要る。) -/
private theorem thm36_aux : ∀ (n : ℕ)
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G],
    Odd (Nat.card G) →
    ∀ {H R : Subgroup G} [H.Normal],
    Subgroup.IsComplement' H R →
    Nat.Coprime (Nat.card ↥H) (Nat.card ↥R) →
    ∀ {R₀ : Subgroup G}, R₀ ≤ R → (∃ r : ℕ, r.Prime ∧ Nat.card ↥R₀ = r) →
    OddOrder.GroupTheory.IsZGroup ↥(H ⊓ Subgroup.centralizer (R₀ : Set G)) →
    ∀ {p : ℕ}, p.Prime →
    Nat.card G = n →
    hasPLengthOne p ↥(⁅H, R⁆ : Subgroup G) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro G _ _ _ hodd H R _ hcompl hHall R₀ hR₀R hR₀p hZ p hp hn
    have : Fact p.Prime := ⟨hp⟩
    by_contra hcounter
    -- `⁅H,R⁆ ≤ H` (H normal).
    have hHR_le_H : (⁅H, R⁆ : Subgroup G) ≤ H := Subgroup.commutator_le_left H R
    -- **(3.6)** `H = ⁅H, R⁆`.  Suppose not; then `⁅H,R⁆R < G` and IH gives `⁅⁅H,R⁆,R⁆` `p`-length
    -- one, but `⁅⁅H,R⁆,R⁆ = ⁅H,R⁆` (Prop 1.6(b)), contradicting `hcounter`.
    have h36 : (⁅H, R⁆ : Subgroup G) = H := by
      by_contra h36ne
      have hHRlt : (⁅H, R⁆ : Subgroup G) < H := lt_of_le_of_ne hHR_le_H h36ne
      set S : Subgroup G := ⁅H, R⁆ ⊔ R with hS
      have hHR_le_S : (⁅H, R⁆ : Subgroup G) ≤ S := le_sup_left
      have hR_le_S : R ≤ S := le_sup_right
      -- `S ≤ N_G(⁅H,R⁆)`: `⁅H,R⁆` self-normalizes, `R` normalizes `⁅R,H⁆ = ⁅H,R⁆` (Isaacs Lem 4.1).
      have hSnorm : S ≤ Subgroup.normalizer (⁅H, R⁆ : Subgroup G) :=
        sup_le Subgroup.le_normalizer
          (Subgroup.commutator_comm R H ▸ subgroup_le_normalizer_commutator_self R H)
      have hH'normal : ((⁅H, R⁆ : Subgroup G).subgroupOf S).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer hSnorm
      -- card transport: `|⁅H,R⁆.subgroupOf S| = |⁅H,R⁆|`, `|R.subgroupOf S| = |R|`.
      have hHRcard : Nat.card ↥((⁅H, R⁆ : Subgroup G).subgroupOf S)
          = Nat.card ↥(⁅H, R⁆ : Subgroup G) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHR_le_S).toEquiv
      have hRcard : Nat.card ↥(R.subgroupOf S) = Nat.card ↥R :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR_le_S).toEquiv
      have hSdvd : Nat.card ↥S ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
      -- complement `⁅H,R⁆.subgroupOf S` ⋈ `R.subgroupOf S` inside `S`.
      have hcompl' :
          Subgroup.IsComplement' ((⁅H, R⁆ : Subgroup G).subgroupOf S) (R.subgroupOf S) := by
        refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
        · refine disjoint_iff.mpr (eq_bot_iff.mpr fun x hx => ?_)
          rw [Subgroup.mem_inf] at hx
          simp only [Subgroup.mem_subgroupOf] at hx
          have hmem : (x : G) ∈ (⁅H, R⁆ : Subgroup G) ⊓ R := ⟨hx.1, hx.2⟩
          have hdisj : Disjoint (⁅H, R⁆ : Subgroup G) R := hcompl.disjoint.mono_left hHR_le_H
          rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
          rw [Subgroup.mem_bot]; exact Subtype.ext (by simpa using hmem)
        · have hsup : ((⁅H, R⁆ : Subgroup G).subgroupOf S) ⊔ (R.subgroupOf S) = ⊤ := by
            rw [← Subgroup.subgroupOf_sup hHR_le_S hR_le_S, Subgroup.subgroupOf_self]
          have hmul := Subgroup.normal_mul ((⁅H, R⁆ : Subgroup G).subgroupOf S) (R.subgroupOf S)
          rw [hsup, Subgroup.coe_top] at hmul
          exact hmul.symm
      have hHall' : Nat.Coprime (Nat.card ↥((⁅H, R⁆ : Subgroup G).subgroupOf S))
          (Nat.card ↥(R.subgroupOf S)) := by
        rw [hHRcard, hRcard]
        exact hHall.coprime_dvd_left (Subgroup.card_dvd_of_le hHR_le_H)
      have hodd' : Odd (Nat.card ↥S) := by
        obtain ⟨m, hm⟩ := hSdvd; rw [hm, Nat.odd_mul] at hodd; exact hodd.1
      -- `R₀ ≤ R ≤ S`; transport `R₀` into `S`.
      have hR₀S : R₀ ≤ S := hR₀R.trans hR_le_S
      have hR₀R' : R₀.subgroupOf S ≤ R.subgroupOf S := Subgroup.subgroupOf_mono S hR₀R
      have hR₀card : Nat.card ↥(R₀.subgroupOf S) = Nat.card ↥R₀ :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀S).toEquiv
      have hR₀p' : ∃ r : ℕ, r.Prime ∧ Nat.card ↥(R₀.subgroupOf S) = r := by
        obtain ⟨r, hr, hrc⟩ := hR₀p; exact ⟨r, hr, hR₀card.trans hrc⟩
      -- **Z-group transport** (subgroup case): `C_S(R₀') ↪ C_H(R₀)` via `S.subtype`, then
      -- `IsZGroup.of_injective`.  `(C_S(R₀')).map S.subtype ≤ ⁅H,R⁆ ⊓ C_G(R₀) ≤ H ⊓ C_G(R₀)`.
      have hZ' : OddOrder.GroupTheory.IsZGroup
          ↥((⁅H, R⁆ : Subgroup G).subgroupOf S
            ⊓ Subgroup.centralizer (R₀.subgroupOf S : Set ↥S)) := by
        set A : Subgroup ↥S :=
          (⁅H, R⁆ : Subgroup G).subgroupOf S
            ⊓ Subgroup.centralizer (R₀.subgroupOf S : Set ↥S) with hA
        have hle : A.map S.subtype ≤ H ⊓ Subgroup.centralizer (R₀ : Set G) := by
          rintro _ ⟨a, ha, rfl⟩
          obtain ⟨haHR, hacent⟩ := Subgroup.mem_inf.mp ha
          rw [Subgroup.mem_subgroupOf] at haHR
          refine Subgroup.mem_inf.mpr
            ⟨hHR_le_H haHR, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
          have hgS : g ∈ S := hR₀S hg
          have hcomm := (Subgroup.mem_centralizer_iff.mp hacent) (⟨g, hgS⟩ : ↥S)
            (Subgroup.mem_subgroupOf.mpr hg)
          exact congrArg (Subtype.val) hcomm
        have : _root_.IsZGroup ↥(H ⊓ Subgroup.centralizer (R₀ : Set G)) :=
          isZGroup_iff_mathlib.mp hZ
        have : _root_.IsZGroup ↥(A.map S.subtype) :=
          IsZGroup.of_injective (Subgroup.inclusion_injective hle)
        have e := Subgroup.equivMapOfInjective A S.subtype (Subgroup.subtype_injective S)
        have : _root_.IsZGroup ↥A := IsZGroup.of_injective (f := e.toMonoidHom) e.injective
        exact isZGroup_iff_mathlib.mpr ‹_root_.IsZGroup ↥A›
      have hScard : Nat.card ↥S < n := by
        have e1 : Nat.card ↥((⁅H, R⁆ : Subgroup G).subgroupOf S) * Nat.card ↥(R.subgroupOf S)
            = Nat.card ↥S := hcompl'.card_mul_card
        have e2 : Nat.card ↥H * Nat.card ↥R = Nat.card G := hcompl.card_mul_card
        rw [hHRcard, hRcard] at e1
        have hHRltcard : Nat.card ↥(⁅H, R⁆ : Subgroup G) < Nat.card ↥H := by
          refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hHR_le_H))
            (fun heq => (ne_of_lt hHRlt) (Subgroup.eq_of_le_of_card_ge hHR_le_H heq.ge))
        rw [← hn, ← e2, ← e1]
        exact mul_lt_mul_of_pos_right hHRltcard Nat.card_pos
      -- apply IH to `S` with `(⁅H,R⁆.subgroupOf S, R.subgroupOf S, R₀.subgroupOf S)`.
      have hIH := IH (Nat.card ↥S) hScard hodd' hcompl' hHall' hR₀R' hR₀p' hZ' hp rfl
      -- conclusion bridge: `⁅H',R'⁆` in `S` ≅ `⁅⁅H,R⁆,R⁆` in `G` (map S.subtype), then Prop 1.6(b).
      have hmapeq : (⁅(⁅H, R⁆ : Subgroup G).subgroupOf S, R.subgroupOf S⁆ : Subgroup ↥S).map
          S.subtype = ⁅(⁅H, R⁆ : Subgroup G), R⁆ := by
        rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
          Subgroup.subgroupOf_map_subtype,
          inf_eq_left.mpr hHR_le_S, inf_eq_left.mpr hR_le_S]
      have hiso := Subgroup.equivMapOfInjective
        (⁅(⁅H, R⁆ : Subgroup G).subgroupOf S, R.subgroupOf S⁆) S.subtype
        (Subgroup.subtype_injective S)
      have hpl := hasPLengthOne_of_mulEquiv (p := p) hiso hIH
      rw [hmapeq, commutator_commutator_right_eq H R hHall] at hpl
      exact hcounter hpl
    -- **(3.7)** `H/X` has `p`-length one for nontrivial `X ⊴ G` with `X ≤ H` (`R`-invariance is
    -- automatic from `X ⊴ G`).  Apply IH to `G ⧸ X`; the quotient `Z`-group hypothesis is
    -- Prop 1.5(d) (`coprime_fixedPoints_quotient`), and `⁅HQ,RQ⁆ = H.map(mk' X)` by (3.6).
    have h37 : ∀ (X : Subgroup G) [X.Normal], X ≠ ⊥ → X ≤ H →
        hasPLengthOne p (↥H ⧸ X.subgroupOf H) := by
      intro X _ hXne hXH
      have hcardX : 1 < Nat.card ↥X := by
        have hne1 : Nat.card ↥X ≠ 1 := fun h => hXne (Subgroup.eq_bot_of_card_eq X h)
        have hpos : 0 < Nat.card ↥X := Nat.card_pos
        omega
      have hcardG : Nat.card G = Nat.card (G ⧸ X) * Nat.card ↥X :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup X
      have hcardQ : Nat.card (G ⧸ X) < n := by
        rw [← hn, hcardG]
        exact (lt_mul_iff_one_lt_right Nat.card_pos).mpr hcardX
      have hoddQ : Odd (Nat.card (G ⧸ X)) := by
        rw [hcardG, Nat.odd_mul] at hodd; exact hodd.1
      have hHQnorm : (H.map (QuotientGroup.mk' X)).Normal :=
        (inferInstance : H.Normal).map (QuotientGroup.mk' X) (QuotientGroup.mk'_surjective X)
      have hcomplQ : Subgroup.IsComplement' (H.map (QuotientGroup.mk' X))
          (R.map (QuotientGroup.mk' X)) :=
        OddOrder.BG.Ch1.S03.quotient_complement_of_normal_le_kernel hcompl hXH
      have hHallQ : Nat.Coprime (Nat.card ↥(H.map (QuotientGroup.mk' X)))
          (Nat.card ↥(R.map (QuotientGroup.mk' X))) := by
        refine (hHall.coprime_dvd_left ?_).coprime_dvd_right ?_
        · exact Subgroup.card_map_dvd _ _
        · exact Subgroup.card_map_dvd _ _
      have hR₀RQ : R₀.map (QuotientGroup.mk' X) ≤ R.map (QuotientGroup.mk' X) :=
        Subgroup.map_mono hR₀R
      have hR₀pQ : ∃ r : ℕ, r.Prime ∧ Nat.card ↥(R₀.map (QuotientGroup.mk' X)) = r := by
        obtain ⟨r, hr, hrc⟩ := hR₀p
        refine ⟨r, hr, ?_⟩
        -- `mk' X` is injective on `R₀` since `R₀ ⊓ X ≤ R ⊓ H = ⊥`.
        have hdisj : Disjoint R₀ X := hcompl.disjoint.symm.mono hR₀R hXH
        have hinj : Function.Injective ⇑((QuotientGroup.mk' X).comp R₀.subtype) := by
          rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
          intro x hx
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
            QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
          have hmem : (x : G) ∈ R₀ ⊓ X := ⟨x.2, hx⟩
          rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
          rw [Subgroup.mem_bot]; exact Subtype.ext hmem
        have hrange : ((QuotientGroup.mk' X).comp R₀.subtype).range
            = R₀.map (QuotientGroup.mk' X) := by
          rw [MonoidHom.range_comp, R₀.range_subtype]
        rw [← hrc, ← hrange]
        exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      have hZQ : OddOrder.GroupTheory.IsZGroup ↥((H.map (QuotientGroup.mk' X)) ⊓
          Subgroup.centralizer
            ((R₀.map (QuotientGroup.mk' X) : Subgroup (G ⧸ X)) : Set (G ⧸ X))) := by
        -- **Prop 1.5(d) transport**: `C_{H/X}(R₀) ≤ (H ⊓ C_G(R₀)).map (mk' X)` (image of the
        -- `Z`-group), via `coprime_fixedPoints_quotient` on the conjugation action of `R₀` on `H`.
        set φ : ↥R₀ →* MulAut ↥H := (MulAut.conjNormal (G := G) (H := H)).comp R₀.subtype with hφ
        have hval : ∀ (a : ↥R₀) (k : ↥H), (((φ a) k : ↥H) : G) = (a : G) * (k : G) * (a : G)⁻¹ := by
          intro a k
          simp only [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply]
        have hN_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ (X.subgroupOf H) := by
          rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
          intro a k hk
          rw [Subgroup.mem_subgroupOf] at hk ⊢
          rw [hval]
          exact (inferInstance : X.Normal).conj_mem (k : G) hk (a : G)
        have hCopR₀ : Nat.Coprime (Nat.card ↥R₀) (Nat.card ↥H) :=
          (hHall.coprime_dvd_right (Subgroup.card_dvd_of_le hR₀R)).symm
        have hle : (H.map (QuotientGroup.mk' X)) ⊓ Subgroup.centralizer
            ((R₀.map (QuotientGroup.mk' X) : Subgroup (G ⧸ X)) : Set (G ⧸ X))
            ≤ (H ⊓ Subgroup.centralizer (R₀ : Set G)).map (QuotientGroup.mk' X) := by
          rintro _ hq
          obtain ⟨hqH, hqcent⟩ := Subgroup.mem_inf.mp hq
          obtain ⟨h, hhH, rfl⟩ := hqH
          have hcomm : ∀ a : ↥R₀, (QuotientGroup.mk' X) (a : G) * (QuotientGroup.mk' X) h
              = (QuotientGroup.mk' X) h * (QuotientGroup.mk' X) (a : G) :=
            fun a => (Subgroup.mem_centralizer_iff.mp hqcent) _ ⟨(a : G), a.2, rfl⟩
          have hg_fix : ∀ a : ↥R₀, ∃ nn ∈ X.subgroupOf H, (φ a) ⟨h, hhH⟩ = ⟨h, hhH⟩ * nn := by
            intro a
            refine ⟨⟨h, hhH⟩⁻¹ * (φ a) ⟨h, hhH⟩, ?_, by group⟩
            have hnnval : ((⟨h, hhH⟩⁻¹ * (φ a) ⟨h, hhH⟩ : ↥H) : G)
                = h⁻¹ * ((a : G) * h * (a : G)⁻¹) := by
              rw [Subgroup.coe_mul, Subgroup.coe_inv, hval]
            rw [Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply,
              hnnval]
            simp only [map_mul, map_inv]
            rw [hcomm a]
            group
          obtain ⟨c, hc_fix, nn, hnnN, hcnn⟩ :=
            OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient hCopR₀ (Or.inr inferInstance)
              hN_inv hg_fix
          refine ⟨(c : G), Subgroup.mem_inf.mpr ⟨c.2, ?_⟩, ?_⟩
          · rw [Subgroup.mem_centralizer_iff]
            intro g hg
            have hcc : (g : G) * (c : G) * (g : G)⁻¹ = (c : G) := by
              have hh := congrArg (Subtype.val) (hc_fix ⟨g, hg⟩)
              rwa [hval] at hh
            exact mul_inv_eq_iff_eq_mul.mp hcc
          · have hcval : (c : G) = h * (nn : G) := by
              have hh := congrArg (Subtype.val) hcnn
              rwa [Subgroup.coe_mul] at hh
            rw [hcval, map_mul, show (QuotientGroup.mk' X) (nn : G) = 1 from
              (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mp hnnN), mul_one]
        have : _root_.IsZGroup ↥(H ⊓ Subgroup.centralizer (R₀ : Set G)) :=
          isZGroup_iff_mathlib.mp hZ
        have : _root_.IsZGroup
            ↥((H ⊓ Subgroup.centralizer (R₀ : Set G)).map (QuotientGroup.mk' X)) :=
          IsZGroup.of_surjective (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' X) _)
        exact isZGroup_iff_mathlib.mpr (IsZGroup.of_injective (Subgroup.inclusion_injective hle))
      have hIH := IH (Nat.card (G ⧸ X)) hcardQ hoddQ hcomplQ hHallQ hR₀RQ hR₀pQ hZQ hp rfl
      -- bridge: `⁅HQ,RQ⁆ = ⁅H,R⁆.map(mk' X) = H.map(mk' X)` by (3.6).
      have hbridge : (⁅H.map (QuotientGroup.mk' X), R.map (QuotientGroup.mk' X)⁆ : Subgroup (G ⧸ X))
          = H.map (QuotientGroup.mk' X) := by
        rw [← Subgroup.map_commutator, h36]
      rw [hbridge] at hIH
      -- iso `↥H ⧸ X.subgroupOf H ≃* ↥(H.map (mk' X))`, transport `p`-length one.
      have hker : ((QuotientGroup.mk' X).comp H.subtype).ker = X.subgroupOf H := by
        ext x
        simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
          QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      have hrange : ((QuotientGroup.mk' X).comp H.subtype).range = H.map (QuotientGroup.mk' X) := by
        rw [MonoidHom.range_comp, H.range_subtype]
      have hiso : (↥H ⧸ X.subgroupOf H) ≃* ↥(H.map (QuotientGroup.mk' X)) :=
        (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
          ((QuotientGroup.quotientKerEquivRange _).trans (MulEquiv.subgroupCongr hrange))
      exact hasPLengthOne_of_mulEquiv (p := p) hiso.symm hIH
    -- **(3.8)** `O_{p'}(H) = ⊥`.  Else `X := O_{p'}(H)` lifted to `G` feeds (3.7) + Lemma 1.21(b)
    -- to make `H = ⁅H,R⁆` have `p`-length one, contradicting `hcounter`.
    have h38 : OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ) ↥H = ⊥ := by
      by_contra h38ne
      -- capture the `oPiCore` instances, then make `N` opaque (avoids `set`+`rw` motive errors).
      set N : Subgroup ↥H := OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ) ↥H with hN
      have hNnormal : N.Normal := OddOrder.Isaacs.Ch03.oPiCore.normal ({p}ᶜ : Set ℕ) ↥H
      have hNchar : N.Characteristic := OddOrder.Isaacs.Ch03.oPiCore.characteristic ({p}ᶜ) ↥H
      have hNpi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p}ᶜ : Set ℕ) N :=
        OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := ↥H) ({p}ᶜ : Set ℕ)
      clear_value N
      have hkerbot : (H.subtype).ker = ⊥ :=
        (MonoidHom.ker_eq_bot_iff H.subtype).mpr H.subtype_injective
      have hXH : N.map H.subtype ≤ H := Subgroup.map_subtype_le N
      have hsubgroupOf : (N.map H.subtype).subgroupOf H = N :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective N
      -- `N.map H.subtype ⊴ G`: characteristic in the normal `H` (conjugation = `conjNormal`).
      have hXnormal : (N.map H.subtype).Normal := by
        refine ⟨fun n hn g => ?_⟩
        have hnH : n ∈ H := hXH hn
        have hmemN : (⟨n, hnH⟩ : ↥H) ∈ N := by
          have hm : (⟨n, hnH⟩ : ↥H) ∈ (N.map H.subtype).subgroupOf H := by
            rw [Subgroup.mem_subgroupOf]; exact hn
          rwa [hsubgroupOf] at hm
        have hfix : N.map (MulAut.conjNormal g).toMonoidHom = N :=
          Subgroup.characteristic_iff_map_eq.mp hNchar (MulAut.conjNormal g)
        have himg : MulAut.conjNormal g (⟨n, hnH⟩ : ↥H) ∈ N := by
          rw [← hfix]; exact Subgroup.mem_map_of_mem _ hmemN
        exact ⟨MulAut.conjNormal g ⟨n, hnH⟩, himg, by
          rw [Subgroup.coe_subtype, MulAut.conjNormal_apply]⟩
      have hXne : N.map H.subtype ≠ ⊥ := by
        intro h
        rw [Subgroup.map_eq_bot_iff, hkerbot, le_bot_iff] at h
        exact h38ne h
      have h37N := h37 (N.map H.subtype) hXne hXH
      replace h37N := hasPLengthOne_of_mulEquiv (p := p)
        (QuotientGroup.quotientMulEquivOfEq hsubgroupOf) h37N
      have hNp' : ¬ p ∣ Nat.card ↥N := by
        intro hdvd
        have hpmem := hNpi p (Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩)
        simp at hpmem
      apply hcounter
      rw [h36]
      exact hasPLengthOne_of_isPiPrime_normal_quotient hNp' h37N
    -- **(3.9)** `V := F(H) = O_p(H)` is an elementary abelian `p`-group.
    -- Part 1: `F(H) = O_p(H)` — since `O_{p'}(H) = ⊥` (3.8), every `O_q(H)` (`q ≠ p`) is `⊥`.
    have hfit : OddOrder.Isaacs.Ch01.fitting ↥H = OddOrder.Isaacs.Ch01.opCore p ↥H :=
      fitting_eq_opCore_of_oPiCore_compl_eq_bot hp h38
    have hVp : IsPGroup p ↥(OddOrder.Isaacs.Ch01.fitting ↥H) := by
      rw [hfit]; exact OddOrder.Isaacs.Ch01.opCore_isPGroup p ↥H
    -- `Φ(V)` lifted to `↥H` is characteristic (hence normal, and its further `G`-lift is normal).
    have hPhiChar :
        ((_root_.frattini ↥(OddOrder.Isaacs.Ch01.fitting ↥H)).map
          (OddOrder.Isaacs.Ch01.fitting ↥H).subtype).Characteristic :=
      frattini_fitting_map_characteristic
    -- **(3.9) Part 2-4**: `Φ(V) = ⊥`, hence (Lemma 1.7(c)) `V` is elementary abelian.  If
    -- `Φ(V) ≠ ⊥`, its `G`-lift `X` feeds (3.7) + Lemma 1.21(c) (`O_{p'}(H/Φ(V)) = ⊥` from
    -- `S03f_Prelim`) to make `H` have `p`-length one, contradicting `hcounter` via (3.6).
    have hΦbot : _root_.frattini ↥(OddOrder.Isaacs.Ch01.fitting ↥H) = ⊥ := by
      by_contra hΦne
      set Phi : Subgroup ↥H := (_root_.frattini ↥(OddOrder.Isaacs.Ch01.fitting ↥H)).map
        (OddOrder.Isaacs.Ch01.fitting ↥H).subtype with hPhidef
      have hPhi_le_V : Phi ≤ OddOrder.Isaacs.Ch01.fitting ↥H := Subgroup.map_subtype_le _
      have hPhiP : IsPGroup p ↥Phi :=
        hVp.of_injective (Subgroup.inclusion hPhi_le_V) (Subgroup.inclusion_injective hPhi_le_V)
      have hkerbotV : ((OddOrder.Isaacs.Ch01.fitting ↥H).subtype).ker = ⊥ :=
        (MonoidHom.ker_eq_bot_iff _).mpr (Subgroup.subtype_injective _)
      have hPhi_ne : Phi ≠ ⊥ := by
        intro h
        rw [hPhidef, Subgroup.map_eq_bot_iff, hkerbotV, le_bot_iff] at h
        exact hΦne h
      -- lift `Phi` to `G`: `X := Phi.map H.subtype` — normal (char-in-normal), `≤ H`, `≠ ⊥`.
      set X : Subgroup G := Phi.map H.subtype with hXdef
      have hX_le_H : X ≤ H := Subgroup.map_subtype_le _
      have hkerbot : (H.subtype).ker = ⊥ :=
        (MonoidHom.ker_eq_bot_iff H.subtype).mpr H.subtype_injective
      have hX_ne : X ≠ ⊥ := by
        intro h
        rw [hXdef, Subgroup.map_eq_bot_iff, hkerbot, le_bot_iff] at h
        exact hPhi_ne h
      have hX_subgroupOf : X.subgroupOf H = Phi :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective Phi
      have h37X := h37 X hX_ne hX_le_H
      replace h37X := hasPLengthOne_of_mulEquiv (p := p)
        (QuotientGroup.quotientMulEquivOfEq hX_subgroupOf) h37X
      have hOp' : OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ)
          (↥H ⧸ Phi) = ⊥ := oPiCore_compl_quotient_frattini_fitting_eq_bot hVp
      have hHpl : hasPLengthOne p ↥H :=
        hasPLengthOne_of_isPGroup_normal_quotient hPhiP hOp' h37X
      apply hcounter
      rw [h36]; exact hHpl
    -- **(3.9)** `V` is elementary abelian.
    have hVelem : OddOrder.GroupTheory.IsElementaryAbelian p ↥(OddOrder.Isaacs.Ch01.fitting ↥H) :=
      (OddOrder.BG.Ch1.S01.frattini_eq_bot_iff_isElementaryAbelian hVp).mp hΦbot
    -- **(3.10)** `C_H(V) = V` (Proposition 1.3 `centralizer_fitting_le_fitting` + `V` abelian).
    have hCHV : Subgroup.centralizer ((OddOrder.Isaacs.Ch01.fitting ↥H : Subgroup ↥H) : Set ↥H)
        = OddOrder.Isaacs.Ch01.fitting ↥H := by
      refine le_antisymm OddOrder.GroupTheory.centralizer_fitting_le_fitting ?_
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      simpa using congrArg (Subtype.val) (hVelem.1 ⟨w, hw⟩ ⟨v, hv⟩)
    -- **(3.11)** `V` contains a unique minimal normal subgroup of `G`.  In the form needed
    -- downstream (3.14, Phase F): two normal subgroups of `G` inside `H` that intersect trivially
    -- cannot both be nontrivial — else (3.7) on each quotient + Lemma 1.21(e) make `H` have
    -- `p`-length one.
    have h311 : ∀ (A B : Subgroup G) [A.Normal] [B.Normal], A ≤ H → B ≤ H →
        A ⊓ B = ⊥ → A = ⊥ ∨ B = ⊥ := by
      intro A B _ _ hAH hBH hAB
      by_contra hcon
      push Not at hcon
      have hplA := h37 A hcon.1 hAH
      have hplB := h37 B hcon.2 hBH
      have hinf : (A.subgroupOf H) ⊓ (B.subgroupOf H) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_inf] at hx
        simp only [Subgroup.mem_subgroupOf] at hx
        have hmem : (x : G) ∈ A ⊓ B := ⟨hx.1, hx.2⟩
        rw [hAB, Subgroup.mem_bot] at hmem
        rw [Subgroup.mem_bot]; exact Subtype.ext (by simpa using hmem)
      have hHpl : hasPLengthOne p ↥H := hasPLengthOne_of_inf_eq_bot hinf hplA hplB
      apply hcounter; rw [h36]; exact hHpl
    -- ===== Phase B (3.12)–(3.16): the complement `K` =====
    -- Abbreviate `V := F(H)` (folding the (3.9)/(3.10) facts) and record `V = O_p(H)`.
    -- ===== Phase B ((3.12)–(3.16)): split off to `S03f_ComplementK` (issue 0149) =====
    -- The segment consumes no induction hypothesis; `K`, `P` and the (3.12)–(3.16) facts
    -- come back from `complement_structure`, and `V`, `N` are re-`set` here so the
    -- returned spelled-out types fold into the local names consumed by Phase D.
    obtain ⟨K, P, hK_inv, hP_inv, hV_inv, hKp_ndvd, hVK_inf, hP_le_N, hPp, hp_ndvd,
      hfalse_of_pndvd, hKmap, h313, h314C, hVN_inf, hKN_fit, h316⟩ :=
      complement_structure hp hcompl hHall hcounter h36 h38 hfit hVp hVelem hCHV h311
    set V : Subgroup ↥H := OddOrder.Isaacs.Ch01.fitting ↥H with hVdef
    have hVnorm : V.Normal := by rw [hVdef]; infer_instance
    have hVchar : V.Characteristic := by rw [hVdef]; infer_instance
    obtain ⟨a, hVa⟩ := hVp.exists_card_eq
    set N : Subgroup ↥H := Subgroup.normalizer (K : Set ↥H) with hNdef
    have hK_le_N : K ≤ N := Subgroup.le_normalizer
    -- ===== Phase C (3.17)–(3.21): the action of `R₀` =====
    -- **(3.17)** `K` does not centralize `R₀`.  Otherwise `K` (lifted to `G`) lies in the
    -- `Z`-group `H ⊓ C_G(R₀)`; being nilpotent (`K ≅ F(N)`, (3.15)), `K` is cyclic, hence so is
    -- `F(H/V) = KV/V`.  The `R`-action on `H/V` then has its action commutator inside
    -- `C_{H/V}(F(H/V)) ≤ F(H/V)` (cyclic normal invariant + Prop 1.3); but by (3.6) the action
    -- commutator is everything, so `H/V = F(H/V)` is a `p'`-group — contradiction (as in (3.13)).
    -- ===== Phase C ((3.17)–(3.21)): split off to `S03f_R0Action` (issue 0149) =====
    -- The segment consumes no induction hypothesis; `V_G, K_G, S₁` and the derived facts
    -- come back from `r0_action_facts` and are folded into `set` variables here.
    obtain ⟨r, hr_prime, hr_card⟩ := hR₀p
    obtain ⟨h317, hr_ndvd_K, hVGnorm', h318, hV_ne_bot, hpr, hVGelem, h319, h321G⟩ :=
      r0_action_facts hodd hp hr_prime hcompl hHall hR₀R hr_card hZ hcounter h36 hVdef
        hVelem hCHV hVa hp_ndvd hfalse_of_pndvd hKmap hKp_ndvd hVK_inf hK_inv hV_inv hP_inv
        hK_le_N hP_le_N hVN_inf hKN_fit hPp
    set VG : Subgroup G := V.map H.subtype with hVG
    set KG : Subgroup G := K.map H.subtype with hKG
    set S₁ : Subgroup G := KG ⊔ R₀ with hS₁
    have hKG_le_S₁ : KG ≤ S₁ := le_sup_left
    have hR₀_le_S₁ : R₀ ≤ S₁ := le_sup_right
    have hKG_le_H : KG ≤ H := Subgroup.map_subtype_le K
    have hdisjKR : Disjoint KG R₀ := hcompl.disjoint.mono hKG_le_H hR₀R
    have hVGnorm : VG.Normal := hVGnorm'
    -- ===== Phase D (3.22)–(3.31): the structure of `G` =====
    -- **(3.22)** `[X, P] = ⊥` for every `PR₀`-invariant `X ≤ K` with `VXPR₀ ≠ G`.  Set
    -- `HX := VXP` and `S₂ := HX·R₀ < G`.  By minimality (IH on `S₂`), `[HX, R₀]` has `p`-length
    -- one.  `O_{p'}(HX) = ⊥` since `V ≤ HX` is a self-centralizing ((3.10)) normal `p`-subgroup;
    -- `O_{p'}([HX,R₀]) char [HX,R₀] ⊴ HX` forces `O_{p'}([HX,R₀]) = ⊥`, so `p`-subgroups of
    -- `[HX,R₀]` lie in `O_p([HX,R₀])`.  By (3.21), `P = [P,R₀] ≤ [HX,R₀]`, so
    -- `[X,P] ≤ [X, O_p([HX,R₀])] ≤ X ⊓ O_p([HX,R₀]) = ⊥` (`X` is a `p'`-group).
    have h322 : ∀ X : Subgroup G, X ≤ KG →
        R₀ ≤ Subgroup.normalizer (X : Set G) →
        (P.map H.subtype : Subgroup G) ≤ Subgroup.normalizer (X : Set G) →
        VG ⊔ X ⊔ (P.map H.subtype) ⊔ R₀ ≠ ⊤ →
        (⁅X, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) = ⊥ := by
      intro X hXK hXR₀ hXP hne
      set HX : Subgroup G := VG ⊔ X ⊔ P.map H.subtype with hHXdef
      set S₂ : Subgroup G := HX ⊔ R₀ with hS₂def
      set WG : Subgroup G := ⁅HX, R₀⁆ with hWGdef
      -- basic inclusions
      have hX_le_H : X ≤ H := hXK.trans hKG_le_H
      have hHX_le_H : HX ≤ H := by
        rw [hHXdef]
        exact sup_le (sup_le (Subgroup.map_subtype_le V) hX_le_H) (Subgroup.map_subtype_le P)
      have hHX_le_S₂ : HX ≤ S₂ := by rw [hS₂def]; exact le_sup_left
      have hR₀_le_S₂ : R₀ ≤ S₂ := by rw [hS₂def]; exact le_sup_right
      have hVG_le_HX : VG ≤ HX := by rw [hHXdef]; exact le_sup_left.trans le_sup_left
      have hX_le_HX : X ≤ HX := by rw [hHXdef]; exact le_sup_right.trans le_sup_left
      have hPG_le_HX : (P.map H.subtype : Subgroup G) ≤ HX := by
        rw [hHXdef]; exact le_sup_right
      have hX_le_S₂ : X ≤ S₂ := hX_le_HX.trans hHX_le_S₂
      -- `S₂ ≤ N_G(HX)`: `R₀` normalizes `V` (normal in `G`), `X` (hypothesis), `P` (`R`-invariant)
      have hS₂_le_NHX : S₂ ≤ Subgroup.normalizer (HX : Set G) := by
        rw [hS₂def]
        refine sup_le Subgroup.le_normalizer ?_
        intro g hg
        have hgV : g ∈ Subgroup.normalizer (VG : Set G) := by
          rw [Subgroup.normalizer_eq_top]
          trivial
        have hgX : g ∈ Subgroup.normalizer (X : Set G) := hXR₀ hg
        have hgP : g ∈ Subgroup.normalizer ((P.map H.subtype : Subgroup G) : Set G) :=
          mem_normalizer_map_subtype_of_isAInvariant hP_inv (hR₀R hg)
        rw [hHXdef]
        exact mem_normalizer_sup (mem_normalizer_sup hgV hgX) hgP
      have hHX'normal : ((HX.subgroupOf S₂) : Subgroup ↥S₂).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer hS₂_le_NHX
      -- complement/Hall/odd/Z-group transports for the IH on `S₂` (the (3.6) battery)
      have hdisjHX : Disjoint HX R₀ := hcompl.disjoint.mono hHX_le_H hR₀R
      have hcompl₂ : Subgroup.IsComplement' (HX.subgroupOf S₂) (R₀.subgroupOf S₂) := by
        refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
        · refine disjoint_iff.mpr (eq_bot_iff.mpr fun x hx => ?_)
          rw [Subgroup.mem_inf] at hx
          simp only [Subgroup.mem_subgroupOf] at hx
          have hmem : (x : G) ∈ HX ⊓ R₀ := ⟨hx.1, hx.2⟩
          rw [hdisjHX.eq_bot, Subgroup.mem_bot] at hmem
          rw [Subgroup.mem_bot]
          exact Subtype.ext (by simpa using hmem)
        · have hsup : ((HX.subgroupOf S₂) : Subgroup ↥S₂) ⊔ (R₀.subgroupOf S₂) = ⊤ := by
            rw [← Subgroup.subgroupOf_sup hHX_le_S₂ hR₀_le_S₂, Subgroup.subgroupOf_self]
          have hmul := Subgroup.normal_mul ((HX.subgroupOf S₂) : Subgroup ↥S₂)
            (R₀.subgroupOf S₂)
          rw [hsup, Subgroup.coe_top] at hmul
          exact hmul.symm
      have hHXcard : Nat.card ↥(HX.subgroupOf S₂) = Nat.card ↥HX :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHX_le_S₂).toEquiv
      have hR₀card₂ : Nat.card ↥(R₀.subgroupOf S₂) = Nat.card ↥R₀ :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀_le_S₂).toEquiv
      have hHall₂ : Nat.Coprime (Nat.card ↥(HX.subgroupOf S₂))
          (Nat.card ↥(R₀.subgroupOf S₂)) := by
        rw [hHXcard, hR₀card₂]
        exact (hHall.coprime_dvd_left (Subgroup.card_dvd_of_le hHX_le_H)).coprime_dvd_right
          (Subgroup.card_dvd_of_le hR₀R)
      have hodd₂ : Odd (Nat.card ↥S₂) := by
        obtain ⟨m, hm⟩ := Subgroup.card_subgroup_dvd_card S₂
        rw [hm, Nat.odd_mul] at hodd
        exact hodd.1
      have hR₀p₂ : ∃ r' : ℕ, r'.Prime ∧ Nat.card ↥(R₀.subgroupOf S₂) = r' :=
        ⟨r, hr_prime, hR₀card₂.trans hr_card⟩
      have hZ₂ : OddOrder.GroupTheory.IsZGroup
          ↥(HX.subgroupOf S₂ ⊓ Subgroup.centralizer (R₀.subgroupOf S₂ : Set ↥S₂)) := by
        set A : Subgroup ↥S₂ :=
          HX.subgroupOf S₂ ⊓ Subgroup.centralizer (R₀.subgroupOf S₂ : Set ↥S₂) with hA
        have hle : A.map S₂.subtype ≤ H ⊓ Subgroup.centralizer (R₀ : Set G) := by
          rintro _ ⟨a, ha, rfl⟩
          obtain ⟨haHX, hacent⟩ := Subgroup.mem_inf.mp ha
          rw [Subgroup.mem_subgroupOf] at haHX
          refine Subgroup.mem_inf.mpr
            ⟨hHX_le_H haHX, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
          have hgS : g ∈ S₂ := hR₀_le_S₂ hg
          have hcomm := (Subgroup.mem_centralizer_iff.mp hacent) (⟨g, hgS⟩ : ↥S₂)
            (Subgroup.mem_subgroupOf.mpr hg)
          exact congrArg (Subtype.val) hcomm
        have : _root_.IsZGroup ↥(H ⊓ Subgroup.centralizer (R₀ : Set G)) :=
          isZGroup_iff_mathlib.mp hZ
        have : _root_.IsZGroup ↥(A.map S₂.subtype) :=
          IsZGroup.of_injective (Subgroup.inclusion_injective hle)
        have e := Subgroup.equivMapOfInjective A S₂.subtype (Subgroup.subtype_injective S₂)
        have : _root_.IsZGroup ↥A := IsZGroup.of_injective (f := e.toMonoidHom) e.injective
        exact isZGroup_iff_mathlib.mpr ‹_root_.IsZGroup ↥A›
      have hcard₂ : Nat.card ↥S₂ < n := by
        have hdvd : Nat.card ↥S₂ ∣ Nat.card G := Subgroup.card_subgroup_dvd_card S₂
        rw [← hn]
        exact lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd)
          (fun heq => hne (Subgroup.eq_top_of_card_eq S₂ heq))
      -- IH on `S₂` and the bridge down to `WG = [HX, R₀] ≤ G`
      have hIH := IH (Nat.card ↥S₂) hcard₂ hodd₂ hcompl₂ hHall₂
        (le_refl (R₀.subgroupOf S₂)) hR₀p₂ hZ₂ hp rfl
      have hmapeq : (⁅HX.subgroupOf S₂, R₀.subgroupOf S₂⁆ : Subgroup ↥S₂).map S₂.subtype
          = WG := by
        rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
          Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hHX_le_S₂,
          inf_eq_left.mpr hR₀_le_S₂, hWGdef]
      have hiso := Subgroup.equivMapOfInjective
        (⁅HX.subgroupOf S₂, R₀.subgroupOf S₂⁆) S₂.subtype (Subgroup.subtype_injective S₂)
      have hplWG : hasPLengthOne p ↥WG := by
        have hpl := hasPLengthOne_of_mulEquiv (p := p) hiso hIH
        rwa [hmapeq] at hpl
      -- `S₂ ≤ N_G(WG)` (Isaacs Lemma 4.1 on both factors) and `WG ≤ HX`
      have hS₂_le_NWG : S₂ ≤ Subgroup.normalizer (WG : Set G) := by
        rw [hS₂def, hWGdef]
        exact sup_le (subgroup_le_normalizer_commutator_self HX R₀)
          (subgroup_le_normalizer_commutator_self_right HX R₀)
      have hWG_le_HX : WG ≤ HX := by
        rw [hWGdef, Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        have hg₂n : g₂ ∈ Subgroup.normalizer (HX : Set G) := hS₂_le_NHX (hR₀_le_S₂ hg₂)
        rw [Subgroup.mem_normalizer_iff] at hg₂n
        have h2 : g₂ * g₁⁻¹ * g₂⁻¹ ∈ HX := (hg₂n g₁⁻¹).mp (HX.inv_mem hg₁)
        have heq : ⁅g₁, g₂⁆ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by
          rw [commutatorElement_def]; group
        rw [heq]
        exact HX.mul_mem hg₁ h2
      -- `O_{p'}(HX) = ⊥`: `V ≤ HX` is a self-centralizing ((3.10)) normal `p`-subgroup
      have hOp'HX : OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ) ↥HX = ⊥ := by
        have hVHXp : IsPGroup p ↥(VG.subgroupOf HX) :=
          (hVp.map H.subtype).of_injective (Subgroup.subgroupOfEquivOfLe hVG_le_HX).toMonoidHom
            (Subgroup.subgroupOfEquivOfLe hVG_le_HX).injective
        have hCent : Subgroup.centralizer ((VG.subgroupOf HX : Subgroup ↥HX) : Set ↥HX)
            ≤ VG.subgroupOf HX := by
          intro w hw
          rw [Subgroup.mem_subgroupOf]
          have hwH : (w : G) ∈ H := hHX_le_H w.2
          have hwC : (⟨(w : G), hwH⟩ : ↥H)
              ∈ Subgroup.centralizer ((V : Subgroup ↥H) : Set ↥H) := by
            rw [Subgroup.mem_centralizer_iff]
            intro v hv
            have hvVG : (v : G) ∈ VG := by rw [hVG]; exact ⟨v, hv, rfl⟩
            have h1 := Subgroup.mem_centralizer_iff.mp hw (⟨(v : G), hVG_le_HX hvVG⟩ : ↥HX)
              (Subgroup.mem_subgroupOf.mpr hvVG)
            have h2 := congrArg Subtype.val h1
            simp only [Subgroup.coe_mul] at h2
            exact Subtype.ext (by simpa using h2)
          rw [hCHV] at hwC
          rw [hVG]
          exact ⟨⟨(w : G), hwH⟩, hwC, rfl⟩
        exact oPiCore_compl_eq_bot_of_isPGroup_centralizer_le hVHXp hCent
      -- `O_{p'}(WG) = ⊥` (`WG ⊴ HX` in context, characteristic-in-normal transfer)
      have hOp'WG : OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ) ↥WG = ⊥ := by
        have hWGnorm : ((WG.subgroupOf HX) : Subgroup ↥HX).Normal :=
          Subgroup.normal_subgroupOf_of_le_normalizer (hHX_le_S₂.trans hS₂_le_NWG)
        exact oPiCore_eq_bot_of_subgroupOf_normal hWG_le_HX hWGnorm hOp'HX
      -- `P ≤ O_p(WG)` (kernel argument; `P = [P,R₀] ≤ WG` by (3.21))
      have hPG_le_WG : (P.map H.subtype : Subgroup G) ≤ WG := by
        rw [hWGdef]
        calc (P.map H.subtype : Subgroup G) = ⁅P.map H.subtype, R₀⁆ := h321G.symm
          _ ≤ ⁅HX, R₀⁆ := Subgroup.commutator_mono hPG_le_HX le_rfl
      have hQp : IsPGroup p ↥((P.map H.subtype).subgroupOf WG) :=
        (hPp.map H.subtype).of_injective (Subgroup.subgroupOfEquivOfLe hPG_le_WG).toMonoidHom
          (Subgroup.subgroupOfEquivOfLe hPG_le_WG).injective
      have hPG_le_Op : (P.map H.subtype).subgroupOf WG ≤ OddOrder.Isaacs.Ch01.opCore p ↥WG :=
        le_opCore_of_hasPLengthOne_of_oPiCore_compl_eq_bot hplWG hOp'WG hQp
      -- `[X, P] ≤ X ⊓ O_p(WG)-lift = ⊥`
      set OpG : Subgroup G := (OddOrder.Isaacs.Ch01.opCore p ↥WG).map WG.subtype with hOpGdef
      have hPG_le_OpG : (P.map H.subtype : Subgroup G) ≤ OpG := by
        rw [hOpGdef]
        intro x hx
        exact ⟨⟨x, hPG_le_WG hx⟩, hPG_le_Op (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
      have hOpGp : IsPGroup p ↥OpG := by
        rw [hOpGdef]
        exact (OddOrder.Isaacs.Ch01.opCore_isPGroup p ↥WG).map WG.subtype
      have hcomm_le : (⁅X, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) ≤ X ⊓ OpG := by
        rw [Subgroup.commutator_le]
        intro x hx q hq
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have hqn := hXP hq
          rw [Subgroup.mem_normalizer_iff] at hqn
          have h2 : q * x⁻¹ * q⁻¹ ∈ X := (hqn x⁻¹).mp (X.inv_mem hx)
          have heq : ⁅x, q⁆ = x * (q * x⁻¹ * q⁻¹) := by
            rw [commutatorElement_def]; group
          rw [heq]
          exact X.mul_mem hx h2
        · have hxn : x ∈ Subgroup.normalizer (OpG : Set G) := by
            rw [hOpGdef]
            exact mem_normalizer_map_subtype_of_characteristic (hS₂_le_NWG (hX_le_S₂ hx))
          rw [Subgroup.mem_normalizer_iff] at hxn
          have h2 : x * q * x⁻¹ ∈ OpG := (hxn q).mp (hPG_le_OpG hq)
          have heq : ⁅x, q⁆ = (x * q * x⁻¹) * q⁻¹ := by
            rw [commutatorElement_def]
          rw [heq]
          exact OpG.mul_mem h2 (OpG.inv_mem (hPG_le_OpG hq))
      have hXp' : ¬ p ∣ Nat.card ↥X := by
        intro hd
        have h2 : Nat.card ↥X ∣ Nat.card ↥KG := Subgroup.card_dvd_of_le hXK
        rw [hKG, Subgroup.card_map_of_injective H.subtype_injective] at h2
        exact hKp_ndvd (hd.trans h2)
      have hinf_bot : X ⊓ OpG = ⊥ := by
        refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
        obtain ⟨k, hk⟩ := hOpGp.exists_card_eq
        rw [hk]
        exact Nat.Coprime.pow_right k (hp.coprime_iff_not_dvd.mpr hXp').symm
      rw [eq_bot_iff, ← hinf_bot]
      exact hcomm_le
    -- **(3.23)** `G = VKPR₀` (else (3.22) with `X = K` gives `[K,P] = ⊥`, contrary to (3.13));
    -- hence `H = VKP` (Dedekind: the `R₀`-part of `h = a·r₀` lies in `H ⊓ R = ⊥`) and `R = R₀`
    -- (the `VKP`-part of `r = a·r₀` lies in `H ⊓ R = ⊥`).
    have hR₀_le_NKG : R₀ ≤ Subgroup.normalizer (KG : Set G) := fun g hg =>
      mem_normalizer_map_subtype_of_isAInvariant hK_inv (hR₀R hg)
    have hPG_le_NKG : (P.map H.subtype : Subgroup G) ≤ Subgroup.normalizer (KG : Set G) := by
      rintro _ ⟨x, hxP, rfl⟩
      have hxN : x ∈ N := hP_le_N hxP
      rw [hNdef] at hxN
      have h2 : H.subtype x ∈ (Subgroup.normalizer (K : Set ↥H)).map H.subtype :=
        Subgroup.mem_map_of_mem _ hxN
      rw [hKG]
      exact Subgroup.le_normalizer_map H.subtype h2
    -- `G`-level form of (3.13): `[K_G, P_G] ≠ ⊥`
    have h313G : (⁅KG, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) ≠ ⊥ := by
      intro hbot
      apply h313
      have hmap : (⁅K, P⁆ : Subgroup ↥H).map H.subtype
          = ⁅KG, (P.map H.subtype : Subgroup G)⁆ := by
        rw [Subgroup.map_commutator, hKG]
      have h3 : (⁅K, P⁆ : Subgroup ↥H).map H.subtype = (⊥ : Subgroup ↥H).map H.subtype := by
        rw [Subgroup.map_bot, hmap]
        exact hbot
      exact Subgroup.map_injective (Subgroup.subtype_injective H) h3
    have h323G : VG ⊔ KG ⊔ (P.map H.subtype) ⊔ R₀ = ⊤ := by
      by_contra hne
      exact h313G (h322 KG (le_refl KG) hR₀_le_NKG hPG_le_NKG hne)
    -- Dedekind step: for `R₀`-normalized `Y ≤ K_G`, `VYPR₀ = G` forces `H = VYP`
    have hDedekind : ∀ Y : Subgroup G, Y ≤ KG → R₀ ≤ Subgroup.normalizer (Y : Set G) →
        VG ⊔ Y ⊔ (P.map H.subtype) ⊔ R₀ = ⊤ → VG ⊔ Y ⊔ (P.map H.subtype) = H := by
      intro Y hYK hYR₀ htop
      have hVYP_le_H : VG ⊔ Y ⊔ (P.map H.subtype) ≤ H :=
        sup_le (sup_le (Subgroup.map_subtype_le V) (hYK.trans hKG_le_H))
          (Subgroup.map_subtype_le P)
      have hR₀_le_NVYP : R₀ ≤ Subgroup.normalizer
          ((VG ⊔ Y ⊔ (P.map H.subtype) : Subgroup G) : Set G) := by
        intro g hg
        have hgV : g ∈ Subgroup.normalizer (VG : Set G) := by
          rw [Subgroup.normalizer_eq_top]; trivial
        have hgP : g ∈ Subgroup.normalizer ((P.map H.subtype : Subgroup G) : Set G) :=
          mem_normalizer_map_subtype_of_isAInvariant hP_inv (hR₀R hg)
        exact mem_normalizer_sup (mem_normalizer_sup hgV (hYR₀ hg)) hgP
      have hVYPset : ((VG ⊔ Y ⊔ (P.map H.subtype) ⊔ R₀ : Subgroup G) : Set G)
          = ((VG ⊔ Y ⊔ (P.map H.subtype) : Subgroup G) : Set G) * (R₀ : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left _ _ hR₀_le_NVYP
      refine le_antisymm hVYP_le_H ?_
      intro h hh
      have hmem : h ∈ ((VG ⊔ Y ⊔ (P.map H.subtype) ⊔ R₀ : Subgroup G) : Set G) := by
        rw [htop]; trivial
      rw [hVYPset] at hmem
      obtain ⟨a, ha, r₀, hr₀, heq⟩ := hmem
      have hr₀H : r₀ ∈ H := by
        have h1 : r₀ = a⁻¹ * h := by rw [← heq]; group
        rw [h1]
        exact H.mul_mem (H.inv_mem (hVYP_le_H ha)) hh
      have hr₀bot : r₀ ∈ H ⊓ R := ⟨hr₀H, hR₀R hr₀⟩
      rw [hcompl.disjoint.eq_bot, Subgroup.mem_bot] at hr₀bot
      rw [hr₀bot] at heq
      simp only [mul_one] at heq
      rwa [← heq]
    have h323H : VG ⊔ KG ⊔ (P.map H.subtype) = H :=
      hDedekind KG (le_refl KG) hR₀_le_NKG h323G
    have hHXK_le_H : VG ⊔ KG ⊔ (P.map H.subtype) ≤ H := le_of_eq h323H
    have h323R : R = R₀ := by
      refine le_antisymm ?_ hR₀R
      intro x hx
      have hR₀_le_NVKP : R₀ ≤ Subgroup.normalizer
          ((VG ⊔ KG ⊔ (P.map H.subtype) : Subgroup G) : Set G) := by
        intro g hg
        have hgV : g ∈ Subgroup.normalizer (VG : Set G) := by
          rw [Subgroup.normalizer_eq_top]; trivial
        have hgP : g ∈ Subgroup.normalizer ((P.map H.subtype : Subgroup G) : Set G) :=
          mem_normalizer_map_subtype_of_isAInvariant hP_inv (hR₀R hg)
        exact mem_normalizer_sup (mem_normalizer_sup hgV (hR₀_le_NKG hg)) hgP
      have hVKPset : ((VG ⊔ KG ⊔ (P.map H.subtype) ⊔ R₀ : Subgroup G) : Set G)
          = ((VG ⊔ KG ⊔ (P.map H.subtype) : Subgroup G) : Set G) * (R₀ : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left _ _ hR₀_le_NVKP
      have hmem : x ∈ ((VG ⊔ KG ⊔ (P.map H.subtype) ⊔ R₀ : Subgroup G) : Set G) := by
        rw [h323G]; trivial
      rw [hVKPset] at hmem
      obtain ⟨a, ha, r₀, hr₀, heq⟩ := hmem
      have habot : a ∈ H ⊓ R := by
        refine ⟨hHXK_le_H ha, ?_⟩
        have h1 : a = x * r₀⁻¹ := by rw [← heq]; group
        rw [h1]
        exact R.mul_mem hx (R.inv_mem (hR₀R hr₀))
      rw [hcompl.disjoint.eq_bot, Subgroup.mem_bot] at habot
      rw [habot] at heq
      simp only [one_mul] at heq
      rwa [← heq]
    -- **(3.22), unconditional form**: `[X, P] = ⊥` for `PR₀`-invariant `X` **properly** below `K`
    -- (if `VXPR₀ = G` then `H = VXP` by Dedekind, and `|VXP| = |V|·|X|·|P|` against
    -- `|H| = |V|·|K|·|P|` forces `X = K`).
    have hcop_KG_PG : ∀ Y : Subgroup G, Y ≤ KG →
        Nat.Coprime (Nat.card ↥Y) (Nat.card ↥(P.map H.subtype : Subgroup G)) := by
      intro Y hYK
      obtain ⟨k, hk⟩ := (hPp.map H.subtype).exists_card_eq
      rw [hk]
      refine Nat.Coprime.pow_right k (Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr ?_))
      intro hd
      have h3 : Nat.card ↥Y ∣ Nat.card ↥K := by
        have h4 : Nat.card ↥Y ∣ Nat.card ↥KG := Subgroup.card_dvd_of_le hYK
        rwa [hKG, Subgroup.card_map_of_injective H.subtype_injective] at h4
      exact hKp_ndvd (hd.trans h3)
    have hPG_p'_disj : ∀ Y : Subgroup G, Y ≤ KG →
        Disjoint Y (P.map H.subtype : Subgroup G) := fun Y hYK =>
      Subgroup.disjoint_of_coprime_natCard (hcop_KG_PG Y hYK)
    have hVG_disj : ∀ Y : Subgroup G, Y ≤ KG →
        Disjoint VG (Y ⊔ (P.map H.subtype) : Subgroup G) := by
      intro Y hYK
      have hNG : Y ⊔ (P.map H.subtype) ≤ N.map H.subtype :=
        sup_le (hYK.trans (by rw [hKG]; exact Subgroup.map_mono hK_le_N))
          (Subgroup.map_mono hP_le_N)
      have hVN : VG ⊓ N.map H.subtype = ⊥ := by
        rw [hVG, ← Subgroup.map_inf _ _ H.subtype H.subtype_injective, hVN_inf,
          Subgroup.map_bot]
      exact (disjoint_iff.mpr hVN).mono_right hNG
    have hcard_VYP : ∀ Y : Subgroup G, Y ≤ KG →
        (P.map H.subtype : Subgroup G) ≤ Subgroup.normalizer (Y : Set G) →
        Nat.card ↥(VG ⊔ Y ⊔ (P.map H.subtype) : Subgroup G)
          = Nat.card ↥VG * (Nat.card ↥Y * Nat.card ↥(P.map H.subtype : Subgroup G)) := by
      intro Y hYK hYP
      rw [sup_assoc, card_sup_of_le_normalizer_of_disjoint
          (by rw [Subgroup.normalizer_eq_top]; exact le_top) (hVG_disj Y hYK),
        card_sup_of_le_normalizer_of_disjoint hYP (hPG_p'_disj Y hYK)]
    have h322' : ∀ X : Subgroup G, X ≤ KG → X ≠ KG →
        R₀ ≤ Subgroup.normalizer (X : Set G) →
        (P.map H.subtype : Subgroup G) ≤ Subgroup.normalizer (X : Set G) →
        (⁅X, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) = ⊥ := by
      intro X hXK hXne hXR₀ hXP
      refine h322 X hXK hXR₀ hXP ?_
      intro htop
      apply hXne
      have hH_eq := hDedekind X hXK hXR₀ htop
      have h1 := hcard_VYP X hXK hXP
      have h2 := hcard_VYP KG (le_refl KG) hPG_le_NKG
      rw [hH_eq] at h1
      rw [h323H] at h2
      have h3 := h1.symm.trans h2
      have h4 := Nat.eq_of_mul_eq_mul_left Nat.card_pos h3
      have hX_eq := Nat.eq_of_mul_eq_mul_right Nat.card_pos h4
      exact Subgroup.eq_of_le_of_card_ge hXK hX_eq.ge
    -- **(3.24)** `K = [K, P]` (at the `G` level).  Else `[K,P]` is a proper `PR₀`-invariant
    -- subgroup of `K`, so the unconditional (3.22) gives `[[K,P],P] = ⊥`; but
    -- `[[K,P],P] = [K,P]` (Prop 1.6(b), applied inside `KP = K·P` where `K` is normal),
    -- contradicting (3.13).
    have h16bKP : (⁅⁅KG, (P.map H.subtype : Subgroup G)⁆, P.map H.subtype⁆ : Subgroup G)
        = ⁅KG, (P.map H.subtype : Subgroup G)⁆ := by
      set KP : Subgroup G := KG ⊔ (P.map H.subtype) with hKPdef
      have hKG_le_KP : KG ≤ KP := by rw [hKPdef]; exact le_sup_left
      have hPG_le_KP : (P.map H.subtype : Subgroup G) ≤ KP := by
        rw [hKPdef]; exact le_sup_right
      have hKPnorm : KP ≤ Subgroup.normalizer (KG : Set G) := by
        rw [hKPdef]
        exact sup_le Subgroup.le_normalizer hPG_le_NKG
      have : ((KG.subgroupOf KP) : Subgroup ↥KP).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer hKPnorm
      have hcop : Nat.Coprime (Nat.card ↥(KG.subgroupOf KP))
          (Nat.card ↥((P.map H.subtype).subgroupOf KP)) := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKG_le_KP).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPG_le_KP).toEquiv]
        exact hcop_KG_PG KG (le_refl KG)
      have h2 := commutator_commutator_right_eq (KG.subgroupOf KP)
        ((P.map H.subtype).subgroupOf KP) hcop
      have hKmap : (KG.subgroupOf KP).map KP.subtype = KG := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKG_le_KP]
      have hPmap : ((P.map H.subtype).subgroupOf KP).map KP.subtype = P.map H.subtype := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPG_le_KP]
      have h3 := congrArg (Subgroup.map KP.subtype) h2
      simp only [Subgroup.map_commutator] at h3
      rw [hKmap, hPmap] at h3
      exact h3
    have h324 : (⁅KG, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) = KG := by
      by_contra hne24
      have hle : (⁅KG, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) ≤ KG := by
        rw [Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        have hg₂n := hPG_le_NKG hg₂
        rw [Subgroup.mem_normalizer_iff] at hg₂n
        have h2 : g₂ * g₁⁻¹ * g₂⁻¹ ∈ KG := (hg₂n g₁⁻¹).mp (KG.inv_mem hg₁)
        have heq : ⁅g₁, g₂⁆ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by
          rw [commutatorElement_def]; group
        rw [heq]
        exact KG.mul_mem hg₁ h2
      have hR₀inv : R₀ ≤ Subgroup.normalizer
          ((⁅KG, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) : Set G) := fun g hg =>
        mem_normalizer_commutator (hR₀_le_NKG hg)
          (mem_normalizer_map_subtype_of_isAInvariant hP_inv (hR₀R hg))
      have hPinv : (P.map H.subtype : Subgroup G) ≤ Subgroup.normalizer
          ((⁅KG, (P.map H.subtype : Subgroup G)⁆ : Subgroup G) : Set G) :=
        subgroup_le_normalizer_commutator_self_right KG (P.map H.subtype)
      have hbot := h322' _ hle hne24 hR₀inv hPinv
      rw [h16bKP] at hbot
      exact h313G hbot
    -- **(3.25), first half**: `K` is a `q`-group for a prime `q ∉ {p, r}`.  `K ≅ F(N)` is
    -- nilpotent, so `K = ⨆_ℓ O_ℓ(K)`; if no single prime carries all of `K`, every `O_ℓ(K)` is a
    -- proper characteristic (hence `PR₀`-invariant) subgroup of `K`, centralized by `P` by the
    -- unconditional (3.22) — so `[K,P] = ⊥`, contradicting (3.13).
    have hKG_nilp : Group.IsNilpotent ↥KG := by
      have e1 := Subgroup.equivMapOfInjective K H.subtype H.subtype_injective
      have e2 := Subgroup.subgroupOfEquivOfLe hK_le_N
      have : Group.IsNilpotent ↥(K.subgroupOf N) := by
        rw [hKN_fit]
        infer_instance
      refine Group.nilpotent_of_surjective (e1.toMonoidHom.comp e2.toMonoidHom) ?_
      rw [MonoidHom.coe_comp]
      exact e1.surjective.comp e2.surjective
    obtain ⟨q, hq_prime, hq_ne_p, hq_ne_r, hKGq⟩ :
        ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ≠ r ∧ IsPGroup q ↥KG := by
      have hKG_ne_bot : KG ≠ ⊥ := by
        intro hbot
        apply h313G
        rw [hbot, Subgroup.commutator_bot_left]
      have hcard_ne : Nat.card ↥KG ≠ 1 := fun h =>
        hKG_ne_bot (Subgroup.eq_bot_of_card_eq _ h)
      obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hcard_ne
      have : Fact q.Prime := ⟨hq_prime⟩
      have hKGK : Nat.card ↥KG = Nat.card ↥K := by
        rw [hKG, Subgroup.card_map_of_injective H.subtype_injective]
      refine ⟨q, hq_prime, ?_, ?_, ?_⟩
      · intro hqp
        have h2 : q ∣ Nat.card ↥K := hKGK ▸ hq_dvd
        exact hKp_ndvd (hqp ▸ h2)
      · intro hqr
        have h2 : q ∣ Nat.card ↥K := hKGK ▸ hq_dvd
        exact hr_ndvd_K (hqr ▸ h2)
      · by_contra hnotq
        apply h313G
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        -- every `O_ℓ(K)`-lift is proper (else `K` is an `ℓ`-group with `q ∣ |K|`, so `ℓ = q`)
        have hproper : ∀ ℓ : (Nat.card ↥KG).primeFactors,
            (OddOrder.Isaacs.Ch01.opCore (ℓ : ℕ) ↥KG).map KG.subtype ≠ KG := by
          intro ℓ heq
          have : Fact (ℓ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors ℓ.2⟩
          have h2 : Nat.card ↥((OddOrder.Isaacs.Ch01.opCore (ℓ : ℕ) ↥KG).map KG.subtype)
              = Nat.card ↥(OddOrder.Isaacs.Ch01.opCore (ℓ : ℕ) ↥KG) :=
            Subgroup.card_map_of_injective (Subgroup.subtype_injective KG)
          rw [heq] at h2
          obtain ⟨m, hm⟩ :=
            (OddOrder.Isaacs.Ch01.opCore_isPGroup (ℓ : ℕ) ↥KG).exists_card_eq
          have hKℓ : IsPGroup (ℓ : ℕ) ↥KG := IsPGroup.of_card (h2.trans hm)
          obtain ⟨m', hm'⟩ := hKℓ.exists_card_eq
          have hq_eq : q = (ℓ : ℕ) :=
            (Nat.prime_dvd_prime_iff_eq hq_prime (Nat.prime_of_mem_primeFactors ℓ.2)).mp
              (hq_prime.dvd_of_dvd_pow (hm' ▸ hq_dvd))
          exact hnotq (hq_eq ▸ hKℓ)
        -- hence every `O_ℓ(K)`-lift is centralized by `P` ((3.22), unconditional form)
        have hOl_cent : ∀ ℓ : (Nat.card ↥KG).primeFactors,
            (OddOrder.Isaacs.Ch01.opCore (ℓ : ℕ) ↥KG).map KG.subtype
              ≤ Subgroup.centralizer ((P.map H.subtype : Subgroup G) : Set G) := by
          intro ℓ
          have : Fact (ℓ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors ℓ.2⟩
          refine Subgroup.commutator_eq_bot_iff_le_centralizer.mp ?_
          refine h322' _ (Subgroup.map_subtype_le _) (hproper ℓ) ?_ ?_
          · exact fun g hg => mem_normalizer_map_subtype_of_characteristic (hR₀_le_NKG hg)
          · exact fun g hg => mem_normalizer_map_subtype_of_characteristic (hPG_le_NKG hg)
        -- nilpotency: `F(K) = ⊤`, so `K = ⨆_ℓ O_ℓ(K)` and the centralizer absorbs all of `K`
        have hfit_top : OddOrder.Isaacs.Ch01.fitting ↥KG = ⊤ := by
          refine le_antisymm le_top ?_
          have : Group.IsNilpotent ↥(⊤ : Subgroup ↥KG) :=
            Group.nilpotent_of_surjective (Subgroup.topEquiv (G := ↥KG)).symm.toMonoidHom
              (Subgroup.topEquiv (G := ↥KG)).symm.surjective
          exact OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
        have hC : ∀ y : ↥KG, y ∈ (⨆ ℓ : (Nat.card ↥KG).primeFactors,
            OddOrder.Isaacs.Ch01.opCore (ℓ : ℕ) ↥KG : Subgroup ↥KG) →
            (y : G) ∈ Subgroup.centralizer ((P.map H.subtype : Subgroup G) : Set G) := by
          intro y hy
          exact Subgroup.iSup_induction
            (C := fun w : ↥KG => (w : G) ∈ Subgroup.centralizer
              ((P.map H.subtype : Subgroup G) : Set G))
            (fun ℓ : (Nat.card ↥KG).primeFactors => OddOrder.Isaacs.Ch01.opCore (ℓ : ℕ) ↥KG)
            hy (fun ℓ z hz => hOl_cent ℓ ⟨z, hz, rfl⟩)
            (by simp)
            (fun z w hz hw => by
              change (z : G) * (w : G) ∈ _
              exact Subgroup.mul_mem _ hz hw)
        intro x hx
        refine hC ⟨x, hx⟩ ?_
        rw [← OddOrder.Isaacs.Ch01.fitting_eq_iSup_primeFactors, hfit_top]
        trivial
    -- **(3.25)+(3.26)** `K` is a **special `q`-group of exponent `q`**.  Apply Gorenstein 5.3.7
    -- (`S04e`) to the conjugation action of `A := P·R₀ ≤ N_G(K)` on `K`: there is a minimal
    -- `A`-invariant `Q ≤ K` on which some `ψ ∈ P` acts nontrivially, and `Q` is special of
    -- exponent `q`.  If `Q` were proper, the unconditional (3.22) would make `P` centralize it,
    -- contradicting the nontrivial `ψ`-action; so `Q = K`.
    -- the conjugation action of `A := P·R₀ ≤ N_G(K)` on `K` (used at (3.25), (3.28), (3.29))
    have hA_le_N : (P.map H.subtype : Subgroup G) ⊔ R₀ ≤ Subgroup.normalizer (KG : Set G) :=
      sup_le hPG_le_NKG hR₀_le_NKG
    set A : Subgroup G := (P.map H.subtype) ⊔ R₀ with hAdef
    set φA : ↥A →* MulAut ↥KG :=
      KG.normalizerMonoidHom.comp (Subgroup.inclusion hA_le_N) with hφA
    have hφA_val : ∀ (a : ↥A) (k : ↥KG),
        ((φA a k : ↥KG) : G) = (a : G) * (k : G) * (a : G)⁻¹ := fun a k => rfl
    have hAcard : Nat.card ↥A
        = Nat.card ↥(P.map H.subtype : Subgroup G) * Nat.card ↥R₀ := by
      rw [hAdef]
      exact card_sup_of_le_normalizer_of_disjoint
        (fun g hg => mem_normalizer_map_subtype_of_isAInvariant hP_inv (hR₀R hg))
        (hcompl.disjoint.mono (Subgroup.map_subtype_le P) hR₀R)
    obtain ⟨hK_special, hK_exp⟩ : IsSpecial q ↥KG ∧ Monoid.exponent ↥KG = q := by
      have : Fact q.Prime := ⟨hq_prime⟩
      -- `q` is odd (`q ∣ |K| ∣ |G|` and `|G|` is odd)
      have hKG_ne_bot : KG ≠ ⊥ := by
        intro hbot
        apply h313G
        rw [hbot, Subgroup.commutator_bot_left]
      have hq_dvd_KG : q ∣ Nat.card ↥KG := by
        obtain ⟨m, hm⟩ := hKGq.exists_card_eq
        rcases Nat.eq_zero_or_pos m with hm0 | hmpos
        · exact absurd (Subgroup.eq_bot_of_card_eq _ (by rw [hm, hm0, pow_zero])) hKG_ne_bot
        · rw [hm]
          exact dvd_pow_self q hmpos.ne'
      have hq_odd : Odd q := by
        rcases hq_prime.eq_two_or_odd' with h2 | hodd_q
        · exfalso
          have h3 : (2 : ℕ) ∣ Nat.card G :=
            (h2 ▸ hq_dvd_KG).trans (Subgroup.card_subgroup_dvd_card KG)
          rcases hodd with ⟨t, ht⟩
          omega
        · exact hodd_q
      -- `|A| = |P|·|R₀|` is coprime to `|K|`
      have hCop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥KG) := by
        rw [hAcard]
        refine Nat.coprime_mul_iff_left.mpr ⟨?_, ?_⟩
        · exact (hcop_KG_PG KG (le_refl KG)).symm
        · rw [hr_card]
          refine (Nat.Prime.coprime_iff_not_dvd hr_prime).mpr ?_
          intro hd
          apply hr_ndvd_K
          have hKGK : Nat.card ↥KG = Nat.card ↥K := by
            rw [hKG, Subgroup.card_map_of_injective H.subtype_injective]
          exact hKGK ▸ hd
      -- some `ψ₀ ∈ P` acts nontrivially on `K` ((3.13))
      obtain ⟨ψ₀, hψ₀P, k₀, hk₀K, hψ₀k₀⟩ :
          ∃ ψ₀ ∈ (P.map H.subtype : Subgroup G), ∃ k₀ ∈ KG, ψ₀ * k₀ * ψ₀⁻¹ ≠ k₀ := by
        by_contra hall
        push Not at hall
        apply h313G
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        rw [Subgroup.mem_bot]
        have h2 := hall g₂ hg₂ g₁ hg₁
        have h3 : g₂ * g₁ = g₁ * g₂ := by
          calc g₂ * g₁ = (g₂ * g₁ * g₂⁻¹) * g₂ := by group
            _ = g₁ * g₂ := by rw [h2]
        rw [commutatorElement_def,
          show g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = (g₁ * g₂) * (g₂ * g₁)⁻¹ by group, ← h3]
        group
      have hψ₀A : ψ₀ ∈ A := by rw [hAdef]; exact Subgroup.mem_sup_left hψ₀P
      have hψ_nt : ¬ ∀ g : ↥KG, φA ⟨ψ₀, hψ₀A⟩ g = g := by
        intro hall
        apply hψ₀k₀
        have h2 := congrArg Subtype.val (hall ⟨k₀, hk₀K⟩)
        rw [hφA_val] at h2
        exact h2
      -- Gorenstein 5.3.7 with minimality
      obtain ⟨Q, hQ_inv, hQ_nt, hQ_special, hQ_exp, _⟩ :=
        OddOrder.BG.Ch1.S04.exists_minimal_aInvariant_isExpPSpecial_of_pprimeAction_with_minimality
          hq_odd φA hKGq hCop hψ_nt
      -- `Q = ⊤`: a proper lift would be `PR₀`-invariant below `K`, hence `P`-central by (3.22)
      have hQ_top : Q = ⊤ := by
        by_contra hQne
        have hQlift_ne : Q.map KG.subtype ≠ KG := by
          intro heq
          apply hQne
          have h2 : Q.map KG.subtype = (⊤ : Subgroup ↥KG).map KG.subtype := by
            rw [heq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
          exact Subgroup.map_injective (Subgroup.subtype_injective KG) h2
        have hQR₀ : R₀ ≤ Subgroup.normalizer ((Q.map KG.subtype : Subgroup G) : Set G) := by
          intro g hg
          have hgA : g ∈ A := by rw [hAdef]; exact Subgroup.mem_sup_right hg
          exact mem_normalizer_map_subtype_of_smul_val hQ_inv (hφA_val ⟨g, hgA⟩)
        have hQP : (P.map H.subtype : Subgroup G)
            ≤ Subgroup.normalizer ((Q.map KG.subtype : Subgroup G) : Set G) := by
          intro g hg
          have hgA : g ∈ A := by rw [hAdef]; exact Subgroup.mem_sup_left hg
          exact mem_normalizer_map_subtype_of_smul_val hQ_inv (hφA_val ⟨g, hgA⟩)
        have hbot := h322' (Q.map KG.subtype) (Subgroup.map_subtype_le Q) hQlift_ne hQR₀ hQP
        obtain ⟨g0, hg0Q, hg0ne⟩ := hQ_nt
        apply hg0ne
        have hcent : (Q.map KG.subtype : Subgroup G)
            ≤ Subgroup.centralizer ((P.map H.subtype : Subgroup G) : Set G) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
        have h2 := Subgroup.mem_centralizer_iff.mp (hcent ⟨g0, hg0Q, rfl⟩) ψ₀ hψ₀P
        apply Subtype.ext
        rw [hφA_val]
        change ψ₀ * (KG.subtype g0) * ψ₀⁻¹ = KG.subtype g0
        rw [mul_inv_eq_iff_eq_mul]
        exact h2
      constructor
      · exact IsSpecial.of_mulEquiv (Subgroup.topEquiv (G := ↥KG)) (hQ_top ▸ hQ_special)
      · exact (Monoid.exponent_eq_of_mulEquiv (Subgroup.topEquiv (G := ↥KG))).symm.trans
          (hQ_top ▸ hQ_exp)
    -- **(3.27)** `C_P(K) = ⊥`: a `P`-element centralizing `K` lies in `C_H(K) ≤ K` ((3.16)),
    -- and `P ⊓ K = ⊥` (`p` vs `p'`).
    have h327 : (P.map H.subtype : Subgroup G) ⊓ Subgroup.centralizer (KG : Set G) = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxP, hxC⟩
      obtain ⟨xh, hxhP, rfl⟩ := hxP
      have hxhC : xh ∈ Subgroup.centralizer (K : Set ↥H) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        have hkKG : (H.subtype k) ∈ KG := by
          rw [hKG]
          exact ⟨k, hk, rfl⟩
        have h2 := Subgroup.mem_centralizer_iff.mp hxC (H.subtype k) hkKG
        exact Subtype.ext (by simpa using h2)
      have hmem : (H.subtype xh) ∈ KG ⊓ (P.map H.subtype : Subgroup G) :=
        ⟨by rw [hKG]; exact ⟨xh, h316 hxhC, rfl⟩, ⟨xh, hxhP, rfl⟩⟩
      rw [(hPG_p'_disj KG (le_refl KG)).eq_bot] at hmem
      exact hmem
    -- **(3.28)** `C_{PR₀}(K) = ⊥`: a `p`-element of the centralizer lies in the normal Sylow
    -- `P` of `A = P·R₀`, hence in `C_P(K) = ⊥` ((3.27)); an `r`-element generates a Sylow
    -- `r`-subgroup of `A` conjugate to `R₀` (Sylow II), and its `K`-centralizing property
    -- transfers to `R₀` — contrary to (3.17).
    have h328 : A ⊓ Subgroup.centralizer (KG : Set G) = ⊥ := by
      by_contra hne
      obtain ⟨ℓ, hℓ_prime, hℓ_dvd⟩ := Nat.exists_prime_and_dvd
        (fun h1 => hne (Subgroup.eq_bot_of_card_eq _ h1))
      have : Fact ℓ.Prime := ⟨hℓ_prime⟩
      obtain ⟨y, hy_ord⟩ := exists_prime_orderOf_dvd_card' ℓ hℓ_dvd
      have hyMem := Subgroup.mem_inf.mp y.2
      have hy_ordG : orderOf ((y : G)) = ℓ := by
        rw [← hy_ord]
        exact orderOf_injective (A ⊓ Subgroup.centralizer (KG : Set G)).subtype
          (Subgroup.subtype_injective _) y
      have hℓ_pr : ℓ = p ∨ ℓ = r := by
        have h3 : ℓ ∣ Nat.card ↥A :=
          hℓ_dvd.trans (Subgroup.card_dvd_of_le inf_le_left)
        rw [hAcard] at h3
        rcases (Nat.Prime.dvd_mul hℓ_prime).mp h3 with h4 | h4
        · left
          obtain ⟨k, hk⟩ := (hPp.map H.subtype).exists_card_eq
          rw [hk] at h4
          exact (Nat.prime_dvd_prime_iff_eq hℓ_prime hp).mp (hℓ_prime.dvd_of_dvd_pow h4)
        · right
          rw [hr_card] at h4
          exact (Nat.prime_dvd_prime_iff_eq hℓ_prime hr_prime).mp h4
      have hPG_le_A : (P.map H.subtype : Subgroup G) ≤ A := by
        rw [hAdef]; exact le_sup_left
      have hR₀_le_A : R₀ ≤ A := by
        rw [hAdef]; exact le_sup_right
      rcases hℓ_pr with hℓeq | hℓeq <;> rw [hℓeq] at hy_ordG
      · -- `ℓ = p`: `y ∈ P` via the normal Sylow `P ⊴ A`, then `(3.27)` kills it
        have hA_le_NPG : A ≤ Subgroup.normalizer
            ((P.map H.subtype : Subgroup G) : Set G) := by
          rw [hAdef]
          exact sup_le Subgroup.le_normalizer
            (fun g hg => mem_normalizer_map_subtype_of_isAInvariant hP_inv (hR₀R hg))
        have hPGnormA : (((P.map H.subtype).subgroupOf A) : Subgroup ↥A).Normal :=
          Subgroup.normal_subgroupOf_of_le_normalizer hA_le_NPG
        have hPGpos : 0 < Nat.card ↥(P.map H.subtype : Subgroup G) := Nat.card_pos
        have hquot_card : Nat.card
            (↥A ⧸ (((P.map H.subtype).subgroupOf A) : Subgroup ↥A)) = r := by
          have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
            (((P.map H.subtype).subgroupOf A) : Subgroup ↥A)
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPG_le_A).toEquiv] at h2
          have h3 : Nat.card (↥A ⧸ (((P.map H.subtype).subgroupOf A) : Subgroup ↥A))
              * Nat.card ↥(P.map H.subtype : Subgroup G)
              = r * Nat.card ↥(P.map H.subtype : Subgroup G) := by
            rw [← h2, hAcard, hr_card, mul_comm]
          exact Nat.eq_of_mul_eq_mul_right hPGpos h3
        set yA : ↥A := ⟨(y : G), hyMem.1⟩ with hyAdef
        have hyA_ord : orderOf yA = p := by
          rw [← hy_ordG]
          exact (orderOf_injective A.subtype (Subgroup.subtype_injective A) yA).symm
        have himg : (QuotientGroup.mk' (((P.map H.subtype).subgroupOf A) : Subgroup ↥A)) yA
            = 1 := by
          have h4 : orderOf ((QuotientGroup.mk'
              (((P.map H.subtype).subgroupOf A) : Subgroup ↥A)) yA) ∣ p := by
            rw [← hyA_ord]
            exact orderOf_map_dvd _ _
          have h5 : orderOf ((QuotientGroup.mk'
              (((P.map H.subtype).subgroupOf A) : Subgroup ↥A)) yA) ∣ r := by
            rw [← hquot_card]
            exact orderOf_dvd_natCard _
          rcases (Nat.dvd_prime hp).mp h4 with h6 | h6
          · exact orderOf_eq_one_iff.mp h6
          · exfalso
            rw [h6] at h5
            exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr_prime).mp h5)
        have hyPG : (y : G) ∈ (P.map H.subtype : Subgroup G) := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at himg
          exact Subgroup.mem_subgroupOf.mp himg
        have hybot : (y : G) ∈ (P.map H.subtype : Subgroup G)
            ⊓ Subgroup.centralizer (KG : Set G) := ⟨hyPG, hyMem.2⟩
        rw [h327, Subgroup.mem_bot] at hybot
        rw [hybot, orderOf_one] at hy_ordG
        exact hp.one_lt.ne' hy_ordG.symm
      · -- `ℓ = r`: Sylow II inside `A` transfers `K`-centralizing from `⟨y⟩` to `R₀`
        have : Fact r.Prime := ⟨hr_prime⟩
        set yA : ↥A := ⟨(y : G), hyMem.1⟩ with hyAdef
        have hyA_ord : orderOf yA = r := by
          rw [← hy_ordG]
          exact (orderOf_injective A.subtype (Subgroup.subtype_injective A) yA).symm
        -- the `r`-part of `|A| = |P|·r` is `r¹`
        have hfact : (Nat.card ↥A).factorization r = 1 := by
          obtain ⟨k, hk⟩ := (hPp.map H.subtype).exists_card_eq
          rw [hAcard, hk, hr_card, Nat.factorization_mul (pow_ne_zero k hp.ne_zero)
            hr_prime.ne_zero, Finsupp.add_apply, hp.factorization_pow,
            Finsupp.single_apply, if_neg hpr, hr_prime.factorization_self]
        have hYcard : Nat.card ↥(Subgroup.zpowers yA)
            = r ^ (Nat.card ↥A).factorization r := by
          rw [hfact, pow_one, Nat.card_zpowers, hyA_ord]
        have hRcard' : Nat.card ↥(R₀.subgroupOf A)
            = r ^ (Nat.card ↥A).factorization r := by
          rw [hfact, pow_one]
          exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀_le_A).toEquiv).trans hr_card
        obtain ⟨a, ha⟩ := MulAction.exists_smul_eq ↥A
          (Sylow.ofCard (Subgroup.zpowers yA) hYcard)
          (Sylow.ofCard (R₀.subgroupOf A) hRcard')
        have ha2 : MulAut.conj a • (Subgroup.zpowers yA) = R₀.subgroupOf A := by
          have h2 := congrArg (fun S : Sylow r ↥A => (S : Subgroup ↥A)) ha
          simpa [Sylow.smul_def, Sylow.pointwise_smul_def, Sylow.coe_ofCard] using h2
        have hR₀cent : R₀ ≤ Subgroup.centralizer (KG : Set G) := by
          intro r₀ hr₀
          have hr₀A : r₀ ∈ A := hR₀_le_A hr₀
          have hr₀mem : (⟨r₀, hr₀A⟩ : ↥A) ∈ MulAut.conj a • (Subgroup.zpowers yA) := by
            rw [ha2]
            exact Subgroup.mem_subgroupOf.mpr hr₀
          rw [Subgroup.mem_smul_pointwise_iff_exists] at hr₀mem
          obtain ⟨s, hs, hseq⟩ := hr₀mem
          have hsC : (s : G) ∈ Subgroup.centralizer (KG : Set G) := by
            obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hs
            have h3 : (s : G) = (y : G) ^ n := by
              rw [← hn, Subgroup.coe_zpow]
            rw [h3]
            exact Subgroup.zpow_mem _ hyMem.2 n
          have hseq2 : r₀ = (a : G) * (s : G) * (a : G)⁻¹ := by
            have h4 := congrArg Subtype.val hseq
            simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul,
              Subgroup.coe_inv] at h4
            exact h4.symm
          rw [Subgroup.mem_centralizer_iff]
          intro k hk
          have hk2 : (a : G)⁻¹ * k * (a : G) ∈ KG := by
            have h5 : (a : G)⁻¹ ∈ Subgroup.normalizer (KG : Set G) :=
              hA_le_N (A.inv_mem a.2)
            rw [Subgroup.mem_normalizer_iff] at h5
            have h6 := (h5 k).mp hk
            rwa [inv_inv] at h6
          have h7 := Subgroup.mem_centralizer_iff.mp hsC _ hk2
          rw [hseq2]
          calc k * ((a : G) * (s : G) * (a : G)⁻¹)
              = (a : G) * ((a : G)⁻¹ * k * (a : G) * (s : G)) * (a : G)⁻¹ := by group
            _ = (a : G) * ((s : G) * ((a : G)⁻¹ * k * (a : G))) * (a : G)⁻¹ := by rw [h7]
            _ = ((a : G) * (s : G) * (a : G)⁻¹) * k := by group
        apply h317
        intro k hk
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        exact (Subgroup.mem_centralizer_iff.mp (hR₀cent hg) k hk).symm
    -- ===== (3.29)–(3.38): the endgame — split off to `S03f_Endgame` (issue 0149) =====
    -- The remaining equations consume no induction hypothesis, so they live in the standalone
    -- lemma `endgame_contradiction`; two small context facts are derived here first.
    have hR₀_le_NPG : R₀ ≤ Subgroup.normalizer ((P.map H.subtype : Subgroup G) : Set G) :=
      fun _g hg => mem_normalizer_map_subtype_of_isAInvariant hP_inv (hR₀R hg)
    have hdisjPR : Disjoint (P.map H.subtype : Subgroup G) R₀ :=
      hcompl.disjoint.mono (Subgroup.map_subtype_le P) hR₀R
    exact endgame_contradiction hp hq_prime hr_prime hq_ne_p hq_ne_r hpr hodd hVG hKG hZ
      hVGelem hV_ne_bot hVK_inf h314C hCHV hPp hr_card hKGq hK_special hK_exp hAdef φA
      hφA_val hAcard hA_le_N h311 h313G h317 hKG_le_S₁ hR₀_le_S₁ hdisjKR h318 h319 h321G
      h322' h323G h324 h328 hR₀_le_NKG hPG_le_NKG hR₀_le_NPG hdisjPR

/-- **BG Theorem 3.6** (mmd L955).  `G` solvable of odd order, `H ◁ G` a normal Hall subgroup, `R` a
complement of `H`, `R₀ ≤ R` of prime order with `C_H(R₀)` a `Z`-group.  Then `[H, R]` has `p`-length
one, for every prime `p`.

The vertex of the §3 subprogram (engine of BG Theorem 10.6); proved by a minimal-counterexample
argument (equations (3.6)–(3.38)) that consumes Lemma 1.21, Theorems 3.4 and 3.5, Gorenstein 5.3.7,
and many §1 propositions.  See `notes/bg/s03_thm36_plan.md` for the phase-by-phase plan. -/
theorem thm36
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] (hodd : Odd (Nat.card G))
    {H R : Subgroup G} [H.Normal] (hcompl : Subgroup.IsComplement' H R)
    (hHall : Nat.Coprime (Nat.card ↥H) (Nat.card ↥R))
    {R₀ : Subgroup G} (hR₀R : R₀ ≤ R) (hR₀p : ∃ r : ℕ, r.Prime ∧ Nat.card ↥R₀ = r)
    (hZ : OddOrder.GroupTheory.IsZGroup ↥(H ⊓ Subgroup.centralizer (R₀ : Set G)))
    {p : ℕ} (hp : p.Prime) :
    hasPLengthOne p ↥(⁅H, R⁆ : Subgroup G) :=
  thm36_aux (Nat.card G) hodd hcompl hHall hR₀R hR₀p hZ hp rfl

end OddOrder.BG.Ch1.S03f


