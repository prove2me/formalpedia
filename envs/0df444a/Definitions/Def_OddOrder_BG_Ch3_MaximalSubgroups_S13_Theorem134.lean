-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S13_Theorem134
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S13_Theorem134
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:35:09.449681+00:00
-- url     : https://prove2.me/theorems/660104c2-6dcd-47f0-8c03-aa4ee505c3d1
-- title:
--   BG §13: Theorem 13.4 (the main step, $C_{M_\sigma}(P)\subseteq C_{M_\sigma}(R)$)
-- statement:
--   Formalizes Theorem 13.4 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §13: for $p\in\tau_1(M)$, $P\in\mathcal{E}_p^1(E)$, $r\in\pi(E)$ and $R\in\mathcal{E}_r^1(C_E(P))$, $C_{M_\sigma}(P)\subseteq C_{M_\sigma}(R)$. This is the central result of the prime-action analysis.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S13_Theorem134.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S13_Theorem134.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S13_Corollary132
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Lemma1218
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem1213
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Proposition1215

namespace OddOrder.BG.Ch3.S13

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open scoped Pointwise

variable {G : Type*} [Group G]

/-- Extend a `q`-subgroup `Q ≤ H` to a maximal `q`-subgroup `S` of `H` (a Sylow `q` of `↥H`,
pulled back to `G`). Supplies the `S` and Sylow-maximality hypotheses of Proposition 12.15. -/
theorem exists_maximal_pSubgroup_le_of_le {q : ℕ} [Fact q.Prime] [Finite G]
    {Q H : Subgroup G} (hQH : Q ≤ H) (hQq : IsPGroup q ↥Q) :
    ∃ S : Subgroup G, S ≤ H ∧ IsPGroup q ↥S ∧ Q ≤ S ∧
      ∀ T : Subgroup G, T ≤ H → IsPGroup q ↥T → S ≤ T → S = T := by
  -- `Q.subgroupOf H` is a `q`-group inside `↥H`; extend to a Sylow `P` of `↥H`.
  have hpg : IsPGroup q ↥(Q.subgroupOf H) := by
    obtain ⟨n, hn⟩ := hQq.exists_card_eq
    exact IsPGroup.of_card
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv]; exact hn)
  obtain ⟨P, hP⟩ := hpg.exists_le_sylow
  refine ⟨(P : Subgroup ↥H).map H.subtype, Subgroup.map_subtype_le _, P.isPGroup'.map _, ?_, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hQH]; exact Subgroup.map_mono hP
  · intro T hTH hTq hST
    have hTHpg : IsPGroup q ↥(T.subgroupOf H) := by
      obtain ⟨n, hn⟩ := hTq.exists_card_eq
      exact IsPGroup.of_card
        (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv]; exact hn)
    have hPT : (P : Subgroup ↥H) ≤ T.subgroupOf H := Subgroup.map_le_iff_le_comap.mp hST
    have e : (P : Subgroup ↥H) = T.subgroupOf H := by
      have hm := P.is_maximal' hTHpg hPT
      first | exact hm | exact hm.symm
    rw [e]
    exact Subgroup.map_subgroupOf_eq_of_le hTH

/-- **Uniform exclusion** — the engine of BG Theorem 13.4's first half, made uniform in the
`σ`-prime `s`. If `a ∈ τ₁(M)`, `A₀ ∈ ℰ_a¹(E)`, `b ∈ π(E)`, `B₀ ∈ ℰ_b¹(C_E(A₀))`, and `T` is an
`A₀B₀`-invariant Sylow `s`-subgroup of `C_{M_σ}(A₀)` (`s` prime) with `⁅T, B₀⁆ ≠ ⊥`, then
`s ∉ α(M)`. This is exactly BG's M*-passage (Cor 13.2 → `T` abelian by Thm 12.13 → ℳ(N_G(Y))={M†}
by Lemma 12.18(a) → `q ∈ σ(M†)` by Prop 12.15 (case (e) excluded) → `s ∉ α(M)` by Lemma 10.12(a)),
which never uses that `s` is the specific prime of Theorem 13.4's final contradiction. -/
theorem uniform_exclusion [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {a : ℕ} [Fact a.Prime]
    (ha : a ∈ tau1 M) {A₀ : Subgroup G} (hA₀ : A₀ ∈ elemAbelianOfRank G a 1) (hA₀E : A₀ ≤ E)
    {b : ℕ} [Fact b.Prime] (hb : b ∈ (Nat.card ↥E).primeFactors)
    {B₀ : Subgroup G} (hB₀ : B₀ ∈ elemAbelianOfRank G b 1)
    (hB₀C : B₀ ≤ E ⊓ Subgroup.centralizer (A₀ : Set G)) {s : ℕ} (hs : s.Prime) {T : Subgroup G}
    (hTN : T ≤ S10.Msigma M ⊓ Subgroup.centralizer (A₀ : Set G)) (hTpg : IsPGroup s ↥T)
    (hTinv : (A₀ ⊔ B₀) ≤ Subgroup.normalizer (T : Set G)) (hYne : ⁅T, B₀⁆ ≠ ⊥) :
    s ∉ S10.alpha M := by
  classical
  have : Fact s.Prime := ⟨hs⟩
  obtain ⟨hA₀ea, hA₀card⟩ := mem_elemAbelianOfRank.mp hA₀
  obtain ⟨hB₀ea, hB₀card⟩ := mem_elemAbelianOfRank.mp hB₀
  have hA₀M : A₀ ≤ M := hA₀E.trans h.E_le
  have hA₀p : IsPGroup a ↥A₀ := hA₀ea.isPGroup
  have hA₀ne : A₀ ≠ ⊥ := by
    intro hbot; rw [hbot, Subgroup.card_bot, pow_one] at hA₀card
    exact (Fact.out : a.Prime).ne_one hA₀card.symm
  have hB₀b : IsPGroup b ↥B₀ := hB₀ea.isPGroup
  have hB₀ne : B₀ ≠ ⊥ := by
    intro hbot; rw [hbot, Subgroup.card_bot, pow_one] at hB₀card
    exact (Fact.out : b.Prime).ne_one hB₀card.symm
  have hB₀E : B₀ ≤ E := hB₀C.trans inf_le_left
  have hB₀CA : B₀ ≤ Subgroup.centralizer (A₀ : Set G) := hB₀C.trans inf_le_right
  -- `M† ∈ ℳ(N_G(A₀))`.
  have hNA₀ne : Subgroup.normalizer (A₀ : Set G) ≠ ⊤ := by
    intro htop
    have : A₀.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hG.simple.eq_bot_or_eq_top_of_normal A₀ inferInstance with hbot | ht
    · exact hA₀ne hbot
    · exact (mem_maximalSubgroups.mp h.mem_maximal).1 (top_le_iff.mp (ht ▸ hA₀M))
  obtain ⟨Mdag, hMdagCo, hNA₀⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (A₀ : Set G))).resolve_left hNA₀ne
  have hMdag : Mdag ∈ maximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨hMdagCo, hNA₀⟩
  have hMdagMax : Mdag ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMdagCo
  have hA₀Mdag : A₀ ≤ Mdag := Subgroup.le_normalizer.trans hNA₀
  have hB₀Mdag : B₀ ≤ Mdag := hB₀CA.trans ((Subgroup.centralizer_le_normalizer _).trans hNA₀)
  have hTMsig : T ≤ S10.Msigma M := hTN.trans inf_le_left
  have hTMdag : T ≤ Mdag :=
    (hTN.trans inf_le_right).trans ((Subgroup.centralizer_le_normalizer _).trans hNA₀)
  have hTMsigMdag : T ≤ S10.Msigma M ⊓ Mdag := le_inf hTMsig hTMdag
  have hB₀MMdag : B₀ ≤ M ⊓ Mdag := le_inf (hB₀E.trans h.E_le) hB₀Mdag
  have hYsub : ⁅T, B₀⁆ ≤ ⁅S10.Msigma M ⊓ Mdag, B₀⁆ :=
    Subgroup.commutator_mono hTMsigMdag le_rfl
  have hcor132 := tau13_pSubgroup_centralizes hG h (Or.inl ha) hA₀M hA₀ne hA₀p hMdag
  -- `b ∈ τ₁(M†)`.
  have hbτ1 : b ∈ tau1 Mdag := by
    by_contra hbnot
    have hB₀pi : Subgroup.IsPiSubgroup (tau1 Mdag)ᶜ B₀ := by
      intro t ht
      have htb : t = b := by
        have htd := (Nat.mem_primeFactors.mp ht).2.1
        rw [hB₀card, pow_one] at htd
        exact (Nat.prime_dvd_prime_iff_eq (Nat.mem_primeFactors.mp ht).1 (Fact.out : b.Prime)).mp
          htd
      rw [htb]; exact hbnot
    have hB₀cent := hcor132.2.1 B₀ (le_inf hB₀E hB₀Mdag) hB₀pi
    have hcomm0 : ⁅S10.Msigma M ⊓ Mdag, B₀⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hB₀cent
    exact hYne (le_bot_iff.mp (hYsub.trans hcomm0.le))
  -- `a ∈ β(M†)`.
  have hint : ⁅S10.Msigma M ⊓ Mdag, M ⊓ Mdag⁆ ≠ ⊥ := fun hbot =>
    hYne (le_bot_iff.mp (hYsub.trans (Subgroup.commutator_mono le_rfl hB₀MMdag |>.trans hbot.le)))
  have haβ : a ∈ S10.beta Mdag := (hcor132.2.2 hint).2 ha
  have hnc : ¬ ∃ g : G, MulAut.conj g • M = Mdag :=
    not_conj_of_mem_tau1_union_tau3_of_normalizer_le hG h.mem_maximal (Or.inl ha) hA₀M hA₀ne hA₀p
      hNA₀
  have hMdagNe : Mdag ≠ M := fun heq => hnc ⟨1, by rw [map_one, one_smul]; exact heq.symm⟩
  -- `T` abelian (Theorem 12.13).
  have hTab : IsMulCommutative ↥T := by
    by_contra hnab
    exact hMdagNe ((nonabelian_pgroup_isUniquelyMaximal hG hTpg hnab).eq_of_isCoatom_of_le
      (mem_maximalSubgroups.mp h.mem_maximal) (hTMsig.trans (S10.Msigma_le M))
      hMdagCo hTMdag).symm
  have hTne : T ≠ ⊥ := fun hbot => hYne (by rw [hbot, Subgroup.commutator_bot_left])
  have hsσ : s ∈ S10.sigma M :=
    S10.Msigma_isPiGroup M s (mem_primeFactors_of_isPGroup_le hs hTMsig hTne hTpg)
  have hbs : b ≠ s := fun heq =>
    h.not_mem_sigma_of_mem_primeFactors hG hb (heq.symm ▸ hsσ)
  have hcop_TB : Nat.Coprime (Nat.card ↥B₀) (Nat.card ↥T) :=
    Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := (S10.sigma M)ᶜ)
      Nat.card_pos.ne' Nat.card_pos.ne'
      (fun t ht => h.isPiGroup_sigma_compl hG t (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp ht).1,
          (Nat.mem_primeFactors.mp ht).2.1.trans (Subgroup.card_dvd_of_le hB₀E), Nat.card_pos.ne'⟩))
      (fun t ht htc => htc (S10.Msigma_isPiGroup M t (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp ht).1,
          (Nat.mem_primeFactors.mp ht).2.1.trans (Subgroup.card_dvd_of_le hTMsig),
            Nat.card_pos.ne'⟩)))
  have hB₀T_norm : B₀ ≤ Subgroup.normalizer (T : Set G) := le_sup_right.trans hTinv
  have hCYB : ⁅T, B₀⁆ ⊓ Subgroup.centralizer (B₀ : Set G) = ⊥ :=
    commutator_inf_centralizer_eq_bot_of_isCommutative
      (fun x hx y hy => congrArg Subtype.val (hTab.is_comm.comm (⟨x, hx⟩ : ↥T) ⟨y, hy⟩))
      hB₀T_norm hcop_TB
  have hYT : ⁅T, B₀⁆ ≤ T := Ch04.commutator_le_of_le_normalizer hB₀T_norm
  have hYq : IsPGroup s ↥(⁅T, B₀⁆ : Subgroup G) := hTpg.to_le hYT
  have hYMdag : (⁅T, B₀⁆ : Subgroup G) ≤ Mdag := hYT.trans hTMdag
  have hB₀NY : B₀ ≤ Subgroup.normalizer ((⁅T, B₀⁆ : Subgroup G) : Set G) :=
    Ch04.le_normalizer_of_commutator_le (Subgroup.commutator_mono hYT le_rfl)
  have hTCA : T ≤ Subgroup.centralizer (A₀ : Set G) := hTN.trans inf_le_right
  have hA₀cBY : A₀ ≤ Subgroup.centralizer ((B₀ ⊔ ⁅T, B₀⁆ : Subgroup G) : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (sup_le hB₀CA (hYT.trans hTCA))
  have hnc' : ¬ ∃ g : G, MulAut.conj g • Mdag = M := by
    rintro ⟨g, hg⟩
    exact hnc ⟨g⁻¹, by rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]⟩
  have hsαdag : s ∉ S10.alpha Mdag := fun ha' =>
    Set.eq_empty_iff_forall_notMem.mp
      ((S10.disjoint_of_not_conj hG hMdagMax h.mem_maximal hnc').1.2) s ⟨ha', hsσ⟩
  have haαdag : a ∈ S10.alpha Mdag := S10.beta_subset_alpha Mdag haβ
  have hA₀α : Ch03.Subgroup.IsPiGroup (S10.alpha Mdag) A₀ := by
    intro t ht
    obtain ⟨n, hn⟩ := hA₀p.exists_card_eq
    rw [hn, Nat.mem_primeFactors] at ht
    exact ((Nat.prime_dvd_prime_iff_eq ht.1 Fact.out).mp (ht.1.dvd_of_dvd_pow ht.2.1)) ▸ haαdag
  have hA₀Mα : A₀ ≤ S10.Malpha Mdag :=
    S10.alpha_subgroup_le_Malpha_of_isHall (S10.Malpha_isHall hG hMdagMax) hA₀Mdag hA₀α
  have hMdagα_ne : S10.Malpha Mdag ≠ ⊥ := fun hbot => hA₀ne (le_bot_iff.mp (hbot ▸ hA₀Mα))
  -- `ℳ(N_G(Y)) = {M†}`.
  have hMNYdag :
      maximalSubgroupsContaining (Subgroup.normalizer ((⁅T, B₀⁆ : Subgroup G) : Set G))
        = {Mdag} := by
    by_contra hne
    obtain ⟨_, hCBY⟩ :=
      (tau1_Malpha_interaction hG hMdagMax hbs.symm hbτ1 hB₀ hB₀Mdag hYMdag hYne hYq hB₀NY hCYB
        hne).1 hMdagα_ne hsαdag
    exact hA₀ne (le_bot_iff.mp (hCBY ▸ le_inf hA₀Mα hA₀cBY))
  -- Prop 12.15 (`X = Y`) excludes case (e), giving `s ∈ σ(M†)`.
  have hYM : (⁅T, B₀⁆ : Subgroup G) ≤ M := hYT.trans (hTMsig.trans (S10.Msigma_le M))
  obtain ⟨T', hT'le, hT'q, hYT', hT'max⟩ :=
    exists_maximal_pSubgroup_le_of_le (le_inf hYM hYMdag) hYq
  have hMdagMem :
      Mdag ∈ maximalSubgroupsContaining (Subgroup.normalizer ((⁅T, B₀⁆ : Subgroup G) : Set G)) := by
    rw [hMNYdag]; rfl
  have hprop := sigma_subgroup_maximal_interaction hG h.mem_maximal hsσ hYM hYne hYq
    hMdagMem hMdagNe hT'le hYT' hT'q hT'max
  have haσdag : a ∈ S10.sigma Mdag := S10.alpha_subset_sigma hG hMdagMax haαdag
  have hA₀σ : Ch03.Subgroup.IsPiGroup (S10.sigma Mdag) A₀ := by
    intro t ht
    obtain ⟨n, hn⟩ := hA₀p.exists_card_eq
    rw [hn, Nat.mem_primeFactors] at ht
    exact ((Nat.prime_dvd_prime_iff_eq ht.1 Fact.out).mp (ht.1.dvd_of_dvd_pow ht.2.1)) ▸ haσdag
  have hA₀Mσdag : A₀ ≤ S10.Msigma Mdag :=
    S10.sigma_subgroup_le_Msigma_of_isHall (S10.Msigma_isHall hG hMdagMax) hA₀Mdag hA₀σ
  have hsσdag : s ∈ S10.sigma Mdag := by
    by_contra hsns
    have he := hprop.2.2.2.2 hsns
    have hA₀bot : A₀ ≤ S10.Msigma Mdag ⊓ (M ⊓ Mdag) := le_inf hA₀Mσdag (le_inf hA₀M hA₀Mdag)
    rw [he.2.2.1] at hA₀bot
    exact hA₀ne (le_bot_iff.mp hA₀bot)
  -- Lemma 10.12(a): `α(M) ∩ σ(M†) = ∅`, so `s ∉ α(M)`.
  exact fun ha' =>
    Set.eq_empty_iff_forall_notMem.mp
      ((S10.disjoint_of_not_conj hG h.mem_maximal hMdagMax hnc).1.2) s ⟨ha', hsσdag⟩

/-- **BG Theorem 13.4's elided inclusion** (the "we can conclude" step), via uniform exclusion:
`C_{M_α}(A₀) ⊆ C_{M_α}(B₀)` for `a ∈ τ₁(M)`, `A₀ ∈ ℰ_a¹(E)`, `b ∈ π(E)`, `B₀ ∈ ℰ_b¹(C_E(A₀))`.
Each prime `ℓ ∣ |C_{M_α}(A₀)|` lies in `α(M)` (as `M_α` is an `α(M)`-group); the `A₀B₀`-invariant
Sylow `ℓ` of `C_{M_α}(A₀)` is a (full) `ℓ`-subgroup of `C_{M_σ}(A₀)`, so `uniform_exclusion`
(contrapositive, `ℓ ∈ α(M)`) forces it to be centralized by `B₀`. The `B₀`-invariant Sylows
exhaust `C_{M_α}(A₀)` (`eq_of_le_of_forall_full_prime_pow`), giving the inclusion. -/
theorem alpha_fixed_le_fixed [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {a : ℕ} [Fact a.Prime]
    (ha : a ∈ tau1 M) {A₀ : Subgroup G} (hA₀ : A₀ ∈ elemAbelianOfRank G a 1) (hA₀E : A₀ ≤ E)
    {b : ℕ} [Fact b.Prime] (hb : b ∈ (Nat.card ↥E).primeFactors)
    {B₀ : Subgroup G} (hB₀ : B₀ ∈ elemAbelianOfRank G b 1)
    (hB₀C : B₀ ≤ E ⊓ Subgroup.centralizer (A₀ : Set G)) :
    S10.Malpha M ⊓ Subgroup.centralizer (A₀ : Set G) ≤
      S10.Malpha M ⊓ Subgroup.centralizer (B₀ : Set G) := by
  classical
  set N : Subgroup G := S10.Malpha M ⊓ Subgroup.centralizer (A₀ : Set G) with hNdef
  have hB₀E : B₀ ≤ E := hB₀C.trans inf_le_left
  have hB₀CA : B₀ ≤ Subgroup.centralizer (A₀ : Set G) := hB₀C.trans inf_le_right
  have hMle : M ≤ Subgroup.normalizer ((S10.Malpha M : Subgroup G) : Set G) :=
    le_normalizer_opiCoreInG (S10.alpha M) M
  have hABE : A₀ ⊔ B₀ ≤ E := sup_le hA₀E hB₀E
  have hNMα : N ≤ S10.Malpha M := inf_le_left
  have hNMσ : N ≤ S10.Msigma M := hNMα.trans (S10.Malpha_le_Msigma hG h.mem_maximal)
  have hAN : (A₀ ⊔ B₀) ≤ Subgroup.normalizer (N : Set G) := by
    rw [hNdef]
    refine le_normalizer_inf (sup_le ((hA₀E.trans h.E_le).trans hMle)
      ((hB₀E.trans h.E_le).trans hMle)) (sup_le ?_ (hB₀CA.trans Subgroup.le_normalizer))
    exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_centralizer A₀)
  have hcop : Nat.Coprime (Nat.card ↥(A₀ ⊔ B₀)) (Nat.card ↥N) := by
    refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := (S10.sigma M)ᶜ)
      Nat.card_pos.ne' Nat.card_pos.ne' ?_ ?_
    · exact fun q hq => h.isPiGroup_sigma_compl hG q
        (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hq).1,
          (Nat.mem_primeFactors.mp hq).2.1.trans (Subgroup.card_dvd_of_le hABE), Nat.card_pos.ne'⟩)
    · exact fun q hq hqc => hqc (S10.Msigma_isPiGroup M q
        (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hq).1,
          (Nat.mem_primeFactors.mp hq).2.1.trans (Subgroup.card_dvd_of_le hNMσ), Nat.card_pos.ne'⟩))
  have hNM : N ≤ M := hNMα.trans (S10.Malpha_le M)
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups h.mem_maximal
  have hNsolv : Group.IsSolvable ↥N :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hNM).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNM).surjective
  -- order argument: every prime `ℓ` admits a `B₀`-invariant Sylow `ℓ` of `N` inside `N ⊓ C_G(B₀)`.
  have hkey : N ⊓ Subgroup.centralizer (B₀ : Set G) = N := by
    refine eq_of_le_of_forall_full_prime_pow inf_le_left (fun ℓ hℓ => ?_)
    have : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨S, hSN, hSpg, hSinv, hScard⟩ :=
      exists_aInvariant_sylow_subgroup hAN hcop (Or.inr hNsolv) ℓ
    refine ⟨S, le_inf hSN ?_, hScard⟩
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    by_contra hSB
    have hSne : S ≠ ⊥ := fun hb' => hSB (by rw [hb', Subgroup.commutator_bot_left])
    have hℓα : ℓ ∈ S10.alpha M :=
      S10.Malpha_isPiGroup M ℓ (mem_primeFactors_of_isPGroup_le hℓ (hSN.trans hNMα) hSne hSpg)
    have hSMσCA : S ≤ S10.Msigma M ⊓ Subgroup.centralizer (A₀ : Set G) :=
      hSN.trans (le_inf hNMσ inf_le_right)
    exact uniform_exclusion hG h ha hA₀ hA₀E hb hB₀ hB₀C hℓ hSMσCA hSpg hSinv hSB hℓα
  exact le_inf hNMα (by rw [← hkey]; exact inf_le_right)

/-- **Thm 13.4 per-q core** (mmd L3576-3597): for a `(P ⊔ R)`-invariant `q`-subgroup `S` of
`C_{M_σ}(P)`, `R` centralizes `S` (i.e. `⁅S, R⁆ = ⊥`). Assume `Q := ⁅S, R⁆ ≠ ⊥`; then via
Cor 13.2(b)(c) `r ∈ τ₁(M*)` and `p ∈ β(M*)` for `M* ∈ ℳ(N_G(P))`, and Prop 12.15 / Lemma 12.18
yield `C_{M_α}(P) = C_{M_α}(R) = C_{M_α}(RQ)` against `ℳ(N_G(Q)) ≠ {M}` — contradiction.
**✅ COMPLETE**: step 7 (`C_{M_α}(P) = C_{M_α}(R)`, BG's elided "we can conclude") is now proven by
`alpha_fixed_le_fixed` (uniform exclusion) in both directions; the whole 9-step contradiction is
sorry-free (sorryAx only from §12 scaffolds). -/
theorem per_q_centralizes [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p r : ℕ}
    [Fact p.Prime] [Fact r.Prime] (hp : p ∈ tau1 M) (hr : r ∈ (Nat.card ↥E).primeFactors)
    {P R : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1) (hPE : P ≤ E)
    (hR : R ∈ elemAbelianOfRank G r 1) (hRC : R ≤ E ⊓ Subgroup.centralizer (P : Set G))
    {q : ℕ} (hq : q.Prime) {S : Subgroup G}
    (hSN : S ≤ S10.Msigma M ⊓ Subgroup.centralizer (P : Set G)) (hSpg : IsPGroup q ↥S)
    (hSinv : (P ⊔ R) ≤ Subgroup.normalizer (S : Set G)) :
    S ≤ Subgroup.centralizer (R : Set G) := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  by_contra hQne
  -- `P`, `R` basics.
  obtain ⟨hPea, hPcard⟩ := mem_elemAbelianOfRank.mp hP
  obtain ⟨hRea, hRcard⟩ := mem_elemAbelianOfRank.mp hR
  have hPM : P ≤ M := hPE.trans h.E_le
  have hPp : IsPGroup p ↥P := hPea.isPGroup
  have hPne : P ≠ ⊥ := by
    intro hb; rw [hb, Subgroup.card_bot, pow_one] at hPcard
    exact (Fact.out : p.Prime).ne_one hPcard.symm
  have hRr : IsPGroup r ↥R := hRea.isPGroup
  have hRne : R ≠ ⊥ := by
    intro hb; rw [hb, Subgroup.card_bot, pow_one] at hRcard
    exact (Fact.out : r.Prime).ne_one hRcard.symm
  have hRE : R ≤ E := hRC.trans inf_le_left
  have hRCP : R ≤ Subgroup.centralizer (P : Set G) := hRC.trans inf_le_right
  -- `M* ∈ ℳ(N_G(P))`: `N_G(P) ≠ ⊤` (else `P ⊴ G`), so a coatom lies above it.
  have hNPne : Subgroup.normalizer (P : Set G) ≠ ⊤ := by
    intro htop
    have : P.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hG.simple.eq_bot_or_eq_top_of_normal P inferInstance with hb | ht
    · exact hPne hb
    · exact (mem_maximalSubgroups.mp h.mem_maximal).1 (top_le_iff.mp (ht ▸ hPM))
  obtain ⟨Mstar, hMstarCo, hNP⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (P : Set G))).resolve_left hNPne
  have hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (P : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨hMstarCo, hNP⟩
  have hMstarMax : Mstar ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMstarCo
  have hPMstar : P ≤ Mstar := Subgroup.le_normalizer.trans hNP
  have hRMstar : R ≤ Mstar := hRCP.trans ((Subgroup.centralizer_le_normalizer _).trans hNP)
  have hSMsig : S ≤ S10.Msigma M := hSN.trans inf_le_left
  have hSMstar : S ≤ Mstar :=
    (hSN.trans inf_le_right).trans ((Subgroup.centralizer_le_normalizer _).trans hNP)
  have hSMsigMstar : S ≤ S10.Msigma M ⊓ Mstar := le_inf hSMsig hSMstar
  -- `⁅S, R⁆ ⊆ ⁅M_σ ⊓ M*, R⁆ ⊆ ⁅M_σ ⊓ M*, M ⊓ M*⁆`.
  have hRMMstar : R ≤ M ⊓ Mstar := le_inf (hRE.trans h.E_le) hRMstar
  have hQsub : ⁅S, R⁆ ≤ ⁅S10.Msigma M ⊓ Mstar, R⁆ :=
    Subgroup.commutator_mono hSMsigMstar le_rfl
  -- Cor 13.2 for `p ∈ τ₁(M)`, `P`, `M*`.
  have hcor132 := tau13_pSubgroup_centralizes hG h (Or.inl hp) hPM hPne hPp hMstar
  -- step 2: `r ∈ τ₁(M*)` (else Cor 13.2(b) makes `R` centralize `M_σ ⊓ M*`, killing `⁅S,R⁆`).
  have hrτ1 : r ∈ tau1 Mstar := by
    by_contra hrnot
    have hRpi : Subgroup.IsPiSubgroup (tau1 Mstar)ᶜ R := by
      intro s hs
      have hsr : s = r := by
        have hsd := (Nat.mem_primeFactors.mp hs).2.1
        rw [hRcard, pow_one] at hsd
        exact (Nat.prime_dvd_prime_iff_eq (Nat.mem_primeFactors.mp hs).1 (Fact.out : r.Prime)).mp
          hsd
      rw [hsr]; exact hrnot
    have hRcent := hcor132.2.1 R (le_inf hRE hRMstar) hRpi
    have hcomm0 : ⁅S10.Msigma M ⊓ Mstar, R⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hRcent
    exact hQne (le_bot_iff.mp (hQsub.trans hcomm0.le))
  -- step 3: `p ∈ β(M*)`.
  have hint : ⁅S10.Msigma M ⊓ Mstar, M ⊓ Mstar⁆ ≠ ⊥ := fun hb =>
    hQne (le_bot_iff.mp (hQsub.trans (Subgroup.commutator_mono le_rfl hRMMstar |>.trans hb.le)))
  have hpβ : p ∈ S10.beta Mstar := (hcor132.2.2 hint).2 hp
  -- `M* ≠ M` (else `M*` is conjugate to `M` via `g = 1`).
  have hnc : ¬ ∃ g : G, MulAut.conj g • M = Mstar :=
    not_conj_of_mem_tau1_union_tau3_of_normalizer_le hG h.mem_maximal (Or.inl hp) hPM hPne hPp hNP
  have hMstarNe : Mstar ≠ M := fun heq => hnc ⟨1, by rw [map_one, one_smul]; exact heq.symm⟩
  -- step 4a: `S` is abelian (Theorem 12.13: a nonabelian `q`-subgroup would be uniquely maximal,
  -- contradicting `S ≤ M` and `S ≤ M*` with `M ≠ M*`).
  have hSab : IsMulCommutative ↥S := by
    by_contra hnab
    exact hMstarNe ((nonabelian_pgroup_isUniquelyMaximal hG hSpg hnab).eq_of_isCoatom_of_le
      (mem_maximalSubgroups.mp h.mem_maximal) (hSMsig.trans (S10.Msigma_le M))
      hMstarCo hSMstar).symm
  -- step 4b: `C_⁅S,R⁆(R) = 1` (coprime FPF on the abelian `S`).
  have hSne : S ≠ ⊥ := fun hb => hQne (by rw [hb, Subgroup.commutator_bot_left])
  have hqσ : q ∈ S10.sigma M :=
    S10.Msigma_isPiGroup M q (mem_primeFactors_of_isPGroup_le hq hSMsig hSne hSpg)
  have hrq : r ≠ q := fun heq =>
    h.not_mem_sigma_of_mem_primeFactors hG hr (heq.symm ▸ hqσ)
  have hcop_SR : Nat.Coprime (Nat.card ↥R) (Nat.card ↥S) :=
    Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := (S10.sigma M)ᶜ)
      Nat.card_pos.ne' Nat.card_pos.ne'
      (fun s hs => h.isPiGroup_sigma_compl hG s (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hs).1,
          (Nat.mem_primeFactors.mp hs).2.1.trans (Subgroup.card_dvd_of_le hRE), Nat.card_pos.ne'⟩))
      (fun s hs hsc => hsc (S10.Msigma_isPiGroup M s (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hs).1,
          (Nat.mem_primeFactors.mp hs).2.1.trans (Subgroup.card_dvd_of_le hSMsig),
            Nat.card_pos.ne'⟩)))
  have hRS_norm : R ≤ Subgroup.normalizer (S : Set G) := le_sup_right.trans hSinv
  have hCQR : ⁅S, R⁆ ⊓ Subgroup.centralizer (R : Set G) = ⊥ :=
    commutator_inf_centralizer_eq_bot_of_isCommutative
      (fun a ha b hb => congrArg Subtype.val (hSab.is_comm.comm (⟨a, ha⟩ : ↥S) ⟨b, hb⟩))
      hRS_norm hcop_SR
  -- ===== structural facts for `Q := ⁅S, R⁆` (step 5 prep) =====
  -- `Q ≤ S` (`R` normalizes `S`), so `Q` is a `q`-group and `Q ≤ M*`.
  have hQS : ⁅S, R⁆ ≤ S := Ch04.commutator_le_of_le_normalizer hRS_norm
  have hQq : IsPGroup q ↥(⁅S, R⁆ : Subgroup G) := hSpg.to_le hQS
  have hQMstar : (⁅S, R⁆ : Subgroup G) ≤ Mstar := hQS.trans hSMstar
  -- `R` normalizes `Q` since `⁅Q, R⁆ ≤ ⁅S, R⁆ = Q`.
  have hRNQ : R ≤ Subgroup.normalizer ((⁅S, R⁆ : Subgroup G) : Set G) :=
    Ch04.le_normalizer_of_commutator_le (Subgroup.commutator_mono hQS le_rfl)
  -- `P` centralizes `R ⊔ Q` (both `R ≤ C(P)` and `Q ≤ S ≤ C(P)`, then symmetry).
  have hSCP : S ≤ Subgroup.centralizer (P : Set G) := hSN.trans inf_le_right
  have hPcRQ : P ≤ Subgroup.centralizer ((R ⊔ ⁅S, R⁆ : Subgroup G) : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (sup_le hRCP (hQS.trans hSCP))
  -- `q ∉ α(M*)`: Lemma 10.12(a) gives `σ(M) ∩ α(M*) = ∅` as `M*` is not conjugate to `M`.
  have hnc' : ¬ ∃ g : G, MulAut.conj g • Mstar = M := by
    rintro ⟨g, hg⟩
    exact hnc ⟨g⁻¹, by rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]⟩
  have hqαstar : q ∉ S10.alpha Mstar := fun ha =>
    Set.eq_empty_iff_forall_notMem.mp
      ((S10.disjoint_of_not_conj hG hMstarMax h.mem_maximal hnc').1.2) q ⟨ha, hqσ⟩
  -- `p ∈ α(M*)` (from `p ∈ β(M*)`): `P ≤ M*_α`, hence `M*_α ≠ ⊥`.
  have hpαstar : p ∈ S10.alpha Mstar := S10.beta_subset_alpha Mstar hpβ
  have hPα : Ch03.Subgroup.IsPiGroup (S10.alpha Mstar) P := by
    intro s hs
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    rw [hn, Nat.mem_primeFactors] at hs
    exact ((Nat.prime_dvd_prime_iff_eq hs.1 Fact.out).mp (hs.1.dvd_of_dvd_pow hs.2.1)) ▸ hpαstar
  have hPMα : P ≤ S10.Malpha Mstar :=
    S10.alpha_subgroup_le_Malpha_of_isHall (S10.Malpha_isHall hG hMstarMax) hPMstar hPα
  have hMαstar_ne : S10.Malpha Mstar ≠ ⊥ := fun hb => hPne (le_bot_iff.mp (hb ▸ hPMα))
  -- ===== step 5: `ℳ(N_G(Q)) = {M*}` (Lemma 12.18(a) with `(r, R, M*)` for `(p, P, M)`) =====
  -- If `ℳ(N_G(Q)) ≠ {M*}`, Lemma 12.18(a) forces `M*_α ⊓ C(R ⊔ Q) = ⊥`; but `1 ⊂ P` lies there.
  have hMNQstar :
      maximalSubgroupsContaining (Subgroup.normalizer ((⁅S, R⁆ : Subgroup G) : Set G))
        = {Mstar} := by
    by_contra hne
    obtain ⟨_, hCRQ⟩ :=
      (tau1_Malpha_interaction hG hMstarMax hrq.symm hrτ1 hR hRMstar hQMstar hQne hQq hRNQ hCQR
        hne).1 hMαstar_ne hqαstar
    exact hPne (le_bot_iff.mp (hCRQ ▸ le_inf hPMα hPcRQ))
  -- ===== step 6: Prop 12.15 (`X = Q`) → `q ∈ σ(M*)`, `τ₁(M*) ⊆ τ₁(M) ∪ α(M)`, `M_α ≠ ⊥` =====
  have hQM : (⁅S, R⁆ : Subgroup G) ≤ M := hQS.trans (hSMsig.trans (S10.Msigma_le M))
  obtain ⟨S', hS'le, hS'q, hQS', hS'max⟩ :=
    exists_maximal_pSubgroup_le_of_le (le_inf hQM hQMstar) hQq
  have hMstarMem :
      Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer ((⁅S, R⁆ : Subgroup G) : Set G)) := by
    rw [hMNQstar]; rfl
  have hprop := sigma_subgroup_maximal_interaction hG h.mem_maximal hqσ hQM hQne hQq
    hMstarMem hMstarNe hS'le hQS' hS'q hS'max
  -- `P ≤ M*_σ` (since `p ∈ β(M*) ⊆ σ(M*)`), used to exclude case (e).
  have hpσstar : p ∈ S10.sigma Mstar := S10.alpha_subset_sigma hG hMstarMax hpαstar
  have hPσ : Ch03.Subgroup.IsPiGroup (S10.sigma Mstar) P := by
    intro s hs
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    rw [hn, Nat.mem_primeFactors] at hs
    exact ((Nat.prime_dvd_prime_iff_eq hs.1 Fact.out).mp (hs.1.dvd_of_dvd_pow hs.2.1)) ▸ hpσstar
  have hPMσstar : P ≤ S10.Msigma Mstar :=
    S10.sigma_subgroup_le_Msigma_of_isHall (S10.Msigma_isHall hG hMstarMax) hPMstar hPσ
  -- case (e) `q ∉ σ(M*)` is impossible: `1 ⊂ P ⊆ M*_σ ⊓ (M ⊓ M*) = ⊥`.
  have hqσstar : q ∈ S10.sigma Mstar := by
    by_contra hqns
    have he := hprop.2.2.2.2 hqns
    have hPbot : P ≤ S10.Msigma Mstar ⊓ (M ⊓ Mstar) := le_inf hPMσstar (le_inf hPM hPMstar)
    rw [he.2.2.1] at hPbot
    exact hPne (le_bot_iff.mp hPbot)
  -- Prop 12.15(d): `τ₁(M*) ⊆ τ₁(M) ∪ α(M)` and `M_α ≠ ⊥`.
  obtain ⟨_, hτ1sub, _, hMαne⟩ := hprop.2.2.2.1 hqσstar
  -- `q ∉ α(M)`: Lemma 10.12(a) gives `α(M) ∩ σ(M*) = ∅` and `q ∈ σ(M*)`.
  have hqαM : q ∉ S10.alpha M := fun ha =>
    Set.eq_empty_iff_forall_notMem.mp
      ((S10.disjoint_of_not_conj hG h.mem_maximal hMstarMax hnc).1.2) q ⟨ha, hqσstar⟩
  -- ===== steps 7-9: `C_{M_α}(P) = C_{M_α}(R)` → three-subgroups → Lemma 12.18(a) contradiction
  -- =====
  -- `r ∈ τ₁(M)`: `τ₁(M*) ⊆ τ₁(M) ∪ α(M)`, `r ∈ π(E) ⟹ r ∉ σ(M) ⊇ α(M)`.
  have hrτ1M : r ∈ tau1 M := by
    rcases hτ1sub r Fact.out hrτ1 with h1 | h1
    · exact h1
    · exact absurd (S10.alpha_subset_sigma hG h.mem_maximal h1)
        (h.not_mem_sigma_of_mem_primeFactors hG hr)
  -- `ℳ(N_G(Q)) ≠ {M}` (since `M* ≠ M`).
  have hMNQne :
      maximalSubgroupsContaining (Subgroup.normalizer ((⁅S, R⁆ : Subgroup G) : Set G)) ≠ {M} := by
    rw [hMNQstar]; intro heq; exact hMstarNe (Set.singleton_injective heq)
  -- Lemma 12.18(a) on `(r, R, q, Q)`: `C_{M_α}(R) ≠ 1` and `C_{M_α}(RQ) = 1`.
  obtain ⟨hCR_ne, hCRQ_bot⟩ :=
    (tau1_Malpha_interaction hG h.mem_maximal hrq.symm hrτ1M hR (hRE.trans h.E_le) hQM hQne hQq
      hRNQ hCQR hMNQne).1 hMαne hqαM
  -- step 7 (BG's "we can conclude"): `C_{M_α}(P) = C_{M_α}(R)` from `alpha_fixed_le_fixed`
  -- (uniform exclusion) applied both ways — `(p, P, r, R)` and `(r, R, p, P)`, the latter using
  -- `r ∈ τ₁(M)` (`hrτ1M`) and `P ≤ C_E(R)`.
  have hpE : p ∈ (Nat.card ↥E).primeFactors :=
    mem_primeFactors_of_isPGroup_le (Fact.out : p.Prime) hPE hPne hPp
  have hPCR : P ≤ Subgroup.centralizer (R : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hRCP
  have hCeq : S10.Malpha M ⊓ Subgroup.centralizer (P : Set G)
      = S10.Malpha M ⊓ Subgroup.centralizer (R : Set G) :=
    le_antisymm
      (alpha_fixed_le_fixed hG h hp hP hPE hr hR hRC)
      (alpha_fixed_le_fixed hG h hrτ1M hR hRE hpE hP (le_inf hPE hPCR))
  -- step 8: `A := C_{M_α}(P)` is `S`-invariant (`S ⊆ C(P)`, `M_α ⊴ M`) and `⊆ C(R)`
  -- (`= C_{M_α}(R)`),
  -- so by three-subgroups it is centralized by `Q = ⁅S, R⁆`.
  have hMNMα : M ≤ Subgroup.normalizer ((S10.Malpha M : Subgroup G) : Set G) :=
    le_normalizer_opiCoreInG (S10.alpha M) M
  have hSNA : S ≤ Subgroup.normalizer
      ((S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf ((hSMsig.trans (S10.Msigma_le M)).trans hMNMα)
      (hSCP.trans Subgroup.le_normalizer)
  have hAleCR : S10.Malpha M ⊓ Subgroup.centralizer (P : Set G)
      ≤ Subgroup.centralizer (R : Set G) := by rw [hCeq]; exact inf_le_right
  have hAcQ : S10.Malpha M ⊓ Subgroup.centralizer (P : Set G)
      ≤ Subgroup.centralizer ((⁅S, R⁆ : Subgroup G) : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    refine commutator_commutator_eq_bot_of_le_of_commutator_bot
      (Ch04.commutator_le_of_le_normalizer hSNA) ?_
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]; exact hAleCR
  -- step 9: `A ⊆ M_α ⊓ C(R ⊔ Q) = ⊥`, but `A = C_{M_α}(R) ≠ ⊥`. Contradiction.
  have hRQcA : (R ⊔ ⁅S, R⁆ : Subgroup G) ≤ Subgroup.centralizer
      ((S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_ <;>
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
        Subgroup.commutator_eq_bot_iff_le_centralizer]
    · exact hAleCR
    · exact hAcQ
  have hAbot : S10.Malpha M ⊓ Subgroup.centralizer (P : Set G)
      ≤ S10.Malpha M ⊓ Subgroup.centralizer ((R ⊔ ⁅S, R⁆ : Subgroup G) : Set G) := by
    refine le_inf inf_le_left ?_
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
      Subgroup.commutator_eq_bot_iff_le_centralizer]; exact hRQcA
  rw [hCRQ_bot, le_bot_iff, hCeq] at hAbot
  exact hCR_ne hAbot

/-- **BG Theorem 13.4** (mmd L3576): `p ∈ τ₁(M)`, `P ∈ ℰ_p¹(E)`, `r ∈ π(E)`, `R ∈ ℰ_r¹(C_E(P))`
なら `C_{M_σ}(P) ⊆ C_{M_σ}(R)`。✅ **完全証明** (2026-06-14): outer reduction
`msigma_centralizer_le_of_invariant_sylow_centralized` + per-q core `per_q_centralizes` (step 7 の
`C_{M_α}(P)=C_{M_α}(R)` は `alpha_fixed_le_fixed` [uniform exclusion] で解決)。axiom-clean。
上流引用は §12 の Cor 12.16 / Prop 12.15 / Thm 12.13 のみで、いずれも証明済。 -/
theorem centralizer_le_centralizer_of_tau1 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p r : ℕ}
    [Fact p.Prime] [Fact r.Prime] (hp : p ∈ tau1 M) (hr : r ∈ (Nat.card ↥E).primeFactors)
    {P R : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1) (hPE : P ≤ E)
    (hR : R ∈ elemAbelianOfRank G r 1) (hRC : R ≤ E ⊓ Subgroup.centralizer (P : Set G)) :
    S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) ≤
      S10.Msigma M ⊓ Subgroup.centralizer (R : Set G) :=
  msigma_centralizer_le_of_invariant_sylow_centralized hG h hPE hRC
    (fun _q hq _S hSN hSpg hSinv => per_q_centralizes hG h hp hr hP hPE hR hRC hq hSN hSpg hSinv)

end OddOrder.BG.Ch3.S13


