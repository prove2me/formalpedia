-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S10_HallStructureCore
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S10_HallStructureCore
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:44:01.439898+00:00
-- url     : https://prove2.me/theorems/00f22245-37d6-413d-91ab-6412dec932fd
-- title:
--   BG §10: the subgroups $M_\alpha$ and $M_\sigma$, core (definitions, Theorem 10.1, first half of Theorem 10.2)
-- statement:
--   Formalizes the first part of Chapter III §10 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*: the definition layer and basic API for $\alpha(M)$, $\beta(M)$, $\sigma(M)$, $M_\alpha$, $M_\beta$ and $M_\sigma$, then Theorem 10.1 (fusion control) and the first half of Theorem 10.2 (up to $M_\sigma\le M'$). The second half of Theorem 10.2 is in the companion Hall-structure file.
--
--   Main definitions: `idealPrime` (a prime $p$ is ideal if $r_p(G)\ge 3$ and a condition on all Sylow $p$-subgroups holds); `alpha` ($\alpha(M)=\{p\in\pi(M): r_p(M)\ge 3\}$); `beta` ($\beta(M)=\{p\in\alpha(M): p \text{ ideal}\}$); `sigma` ($\sigma(M)$, the primes $p\in\pi(M)$ with a Sylow $p$-subgroup $P$ of $M$ such that $N_G(P)\subseteq M$); `Malpha` ($M_\alpha=O_{\alpha(M)}(M)$); `Mbeta` ($M_\beta=O_{\beta(M)}(M)$); and 5 more.
--
--   The bundle also proves 58 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S10_HallStructureCore.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S10_HallStructureCore.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_Setup
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_PLength
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04_PGroupsSmallRank
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Transitivity
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S08_FittingOfMaximal
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S09_Uniqueness
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroup
import Definitions.Def_OddOrder_GroupTheory_PRank
import Definitions.Def_OddOrder_GroupTheory_NarrowPGroup
import Definitions.Def_OddOrder_GroupTheory_CentralProduct
import Definitions.Def_OddOrder_GroupTheory_IsExtraspecial
import Definitions.Def_OddOrder_GroupTheory_OmegaSubgroup
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelianFamily
import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Main

namespace OddOrder.BG.Ch3.S10

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG ideal prime** (mmd L2643): `p` が *ideal* とは、`r_p(G) ≥ 3` かつ 全シロー `p`-部分群 `P`
で `ℰ²(P) ∩ ℰ*(P) = ∅` (位数 `p²` の極大 elem-ab 部分群が無い) こと。Thm 5.3 により「`G` の
Sylow `p` が narrow でない」と同値だが、定義としては BG の literal 形を採る。 -/
def idealPrime (p : ℕ) (G : Type*) [Group G] : Prop :=
  3 ≤ pRank G p ∧
    ∀ P : Sylow p G, ¬ ∃ A : Subgroup ↥(P : Subgroup G),
      Nat.card ↥A = p ^ 2 ∧ IsMaximalElementaryAbelian p A

/-- **BG `α(M)`** (mmd L2647): `{p ∈ π(M) | r_p(M) ≥ 3}`。 -/
def alpha (M : Subgroup G) : Set ℕ :=
  {p | p ∈ (Nat.card ↥M).primeFactors ∧ 3 ≤ pRank ↥M p}

/-- **BG `β(M)`** (mmd L2647): `{p ∈ α(M) | p ideal}`。 -/
def beta (M : Subgroup G) : Set ℕ :=
  {p | p ∈ alpha M ∧ idealPrime p G}

/-- **BG `σ(M)`** (mmd L2647): `{p ∈ π(M) | あるシロー p-部分群 P of M で N_G(P) ⊆ M}`。 -/
def sigma (M : Subgroup G) : Set ℕ :=
  {p | p ∈ (Nat.card ↥M).primeFactors ∧
    ∃ P : Sylow p ↥M, Subgroup.normalizer ((P : Subgroup ↥M).map M.subtype) ≤ M}

/-- **BG `M_α = O_{α(M)}(M)`**。 -/
noncomputable def Malpha (M : Subgroup G) : Subgroup G := opiCoreInG (alpha M) M

/-- **BG `M_β = O_{β(M)}(M)`**。 -/
noncomputable def Mbeta (M : Subgroup G) : Subgroup G := opiCoreInG (beta M) M

/-- **BG `M_σ = O_{σ(M)}(M)`**。 -/
noncomputable def Msigma (M : Subgroup G) : Subgroup G := opiCoreInG (sigma M) M

/-- `X ∈ ℰ_p^n(H)` encoded in the ambient group `G`: `X` is elementary abelian of
rank `n` in `G` and lies in `H`. BG Lemma 10.13 uses this mainly as `X ∈ ℰ¹(A)`. -/
def elemAbelianOfRankIn (p n : ℕ) (H X : Subgroup G) : Prop :=
  X ∈ elemAbelianOfRank G p n ∧ X ≤ H

/-- `Ω₁(Z(P))` for a subgroup `P ≤ G`, mapped back to the ambient group `G`.

The center of `P` is abelian, so this uses the set-form `omega1OfAbelian` rather than the
generated subgroup `Omega`. This is the `Z₀` notation in BG Lemma 10.13. -/
def omega1CenterInG (P : Subgroup G) (p : ℕ) : Subgroup G :=
  (omega1OfAbelian ↥P (Subgroup.center ↥P) p
    (fun _ hx y _ => (Subgroup.mem_center_iff.mp hx y).symm)).map P.subtype

@[simp] theorem mem_idealPrime_iff (p : ℕ) (G : Type*) [Group G] :
    idealPrime p G ↔
      3 ≤ pRank G p ∧
        ∀ P : Sylow p G, ¬ ∃ A : Subgroup ↥(P : Subgroup G),
          Nat.card ↥A = p ^ 2 ∧ IsMaximalElementaryAbelian p A :=
  Iff.rfl

@[simp] theorem mem_alpha_iff (M : Subgroup G) (p : ℕ) :
    p ∈ alpha M ↔ p ∈ (Nat.card ↥M).primeFactors ∧ 3 ≤ pRank ↥M p :=
  Iff.rfl

@[simp] theorem mem_beta_iff (M : Subgroup G) (p : ℕ) :
    p ∈ beta M ↔ p ∈ alpha M ∧ idealPrime p G :=
  Iff.rfl

@[simp] theorem mem_sigma_iff (M : Subgroup G) (p : ℕ) :
    p ∈ sigma M ↔
      p ∈ (Nat.card ↥M).primeFactors ∧
        ∃ P : Sylow p ↥M, Subgroup.normalizer ((P : Subgroup ↥M).map M.subtype) ≤ M :=
  Iff.rfl

theorem alpha_subset_primeFactors (M : Subgroup G) :
    alpha M ⊆ (Nat.card ↥M).primeFactors :=
  fun _ hp => hp.1

theorem beta_subset_alpha (M : Subgroup G) :
    beta M ⊆ alpha M :=
  fun _ hp => hp.1

theorem Malpha_le (M : Subgroup G) : Malpha M ≤ M :=
  Subgroup.map_subtype_le _

theorem Mbeta_le (M : Subgroup G) : Mbeta M ≤ M :=
  Subgroup.map_subtype_le _

theorem Msigma_le (M : Subgroup G) : Msigma M ≤ M :=
  Subgroup.map_subtype_le _

@[simp] theorem opiCoreInG_subgroupOf (π : Set ℕ) (M : Subgroup G) :
    (opiCoreInG π M).subgroupOf M = Ch03.oPiCore π ↥M := by
  rw [Subgroup.subgroupOf, OddOrder.GroupTheory.opiCoreInG,
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective]

@[simp] theorem Malpha_subgroupOf (M : Subgroup G) :
    (Malpha M).subgroupOf M = Ch03.oPiCore (alpha M) ↥M := by
  simp [Malpha]

instance Malpha_subgroupOf_normal (M : Subgroup G) :
    ((Malpha M).subgroupOf M).Normal := by
  rw [Malpha_subgroupOf]
  infer_instance

@[simp] theorem Mbeta_subgroupOf (M : Subgroup G) :
    (Mbeta M).subgroupOf M = Ch03.oPiCore (beta M) ↥M := by
  simp [Mbeta]

@[simp] theorem Msigma_subgroupOf (M : Subgroup G) :
    (Msigma M).subgroupOf M = Ch03.oPiCore (sigma M) ↥M := by
  simp [Msigma]

theorem Malpha_isPiGroup [Finite G] (M : Subgroup G) :
    Ch03.Subgroup.IsPiGroup (alpha M) (Malpha M) := by
  intro r hr
  have hcard : Nat.card ↥(Malpha M) = Nat.card ↥(Ch03.oPiCore (alpha M) ↥M) := by
    rw [Malpha, OddOrder.GroupTheory.opiCoreInG,
      Subgroup.card_map_of_injective M.subtype_injective]
  rw [hcard] at hr
  exact Ch03.oPiCore.isPiGroup (alpha M) r hr

theorem Mbeta_isPiGroup [Finite G] (M : Subgroup G) :
    Ch03.Subgroup.IsPiGroup (beta M) (Mbeta M) := by
  intro r hr
  have hcard : Nat.card ↥(Mbeta M) = Nat.card ↥(Ch03.oPiCore (beta M) ↥M) := by
    rw [Mbeta, OddOrder.GroupTheory.opiCoreInG,
      Subgroup.card_map_of_injective M.subtype_injective]
  rw [hcard] at hr
  exact Ch03.oPiCore.isPiGroup (beta M) r hr

theorem Msigma_isPiGroup [Finite G] (M : Subgroup G) :
    Ch03.Subgroup.IsPiGroup (sigma M) (Msigma M) := by
  intro r hr
  have hcard : Nat.card ↥(Msigma M) = Nat.card ↥(Ch03.oPiCore (sigma M) ↥M) := by
    rw [Msigma, OddOrder.GroupTheory.opiCoreInG,
      Subgroup.card_map_of_injective M.subtype_injective]
  rw [hcard] at hr
  exact Ch03.oPiCore.isPiGroup (sigma M) r hr

/-- A normal `π`-Hall subgroup absorbs every `π`-subgroup. -/
theorem isPiGroup_le_of_normal_isHallSubgroup {H : Type*} [Group H] [Finite H]
    {π : Set ℕ} {K L : Subgroup H} [K.Normal] (hK : Ch03.IsHallSubgroup π K)
    (hL : Ch03.Subgroup.IsPiGroup π L) : L ≤ K := by
  -- `L ⊔ K` is a `π`-group: its order divides `|L| * |K|`, and `K` is normal.
  have hSup_pi : Ch03.Subgroup.IsPiGroup π (L ⊔ K : Subgroup H) := by
    intro r hr
    rw [Nat.mem_primeFactors] at hr
    obtain ⟨hr_prime, hr_dvd, _⟩ := hr
    have h_card_eq : Nat.card ↥(L ⊔ K : Subgroup H) * Nat.card ↥(L ⊓ K : Subgroup H)
        = Nat.card ↥L * Nat.card ↥K := by
      have h_hk := Subgroup.card_HK_mul_card_inf_eq_card_mul_card L K
      rwa [show (↑L * ↑K : Set H) = ↑(L ⊔ K : Subgroup H) from
        (Subgroup.mul_normal L K).symm] at h_hk
    have h_dvd_prod : r ∣ Nat.card ↥L * Nat.card ↥K := by
      rw [← h_card_eq]
      exact hr_dvd.mul_right _
    rcases hr_prime.dvd_mul.mp h_dvd_prod with hL_dvd | hK_dvd
    · exact hL r (Nat.mem_primeFactors.mpr ⟨hr_prime, hL_dvd, Nat.card_pos.ne'⟩)
    · exact hK.1 r (Nat.mem_primeFactors.mpr ⟨hr_prime, hK_dvd, Nat.card_pos.ne'⟩)
  -- Hall divisibility forces `L ⊔ K` to have the same order as `K`.
  have h_card_dvd : Nat.card ↥(L ⊔ K : Subgroup H) ∣ Nat.card ↥K :=
    hK.card_dvd_of_isPiGroup hSup_pi
  have hK_le_sup : K ≤ L ⊔ K := le_sup_right
  have h_card_ge : Nat.card ↥K ≤ Nat.card ↥(L ⊔ K : Subgroup H) :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hK_le_sup)
  have h_sup_eq : (L ⊔ K : Subgroup H) = K :=
    (Subgroup.eq_of_le_of_card_ge hK_le_sup
      (Nat.le_antisymm (Nat.le_of_dvd Nat.card_pos h_card_dvd) h_card_ge).le).symm
  intro x hx
  have hx_sup : x ∈ (L ⊔ K : Subgroup H) := Subgroup.mem_sup_left hx
  rwa [h_sup_eq] at hx_sup

/-- If `O_π(M)` is `π`-Hall in `G`, then its internal copy is `π`-Hall in `M`. -/
theorem opiCoreInG_subgroupOf_isHall_of_isHall [Finite G] {π : Set ℕ} {M : Subgroup G}
    (hHall : Ch03.IsHallSubgroup π (opiCoreInG π M)) :
    Ch03.IsHallSubgroup π ((opiCoreInG π M).subgroupOf M) := by
  refine ⟨?_, ?_⟩
  · intro r hr
    rw [opiCoreInG_subgroupOf] at hr
    exact Ch03.oPiCore.isPiGroup π r hr
  · intro r hr
    have hidx : ((opiCoreInG π M).subgroupOf M).index ∣ (opiCoreInG π M).index := by
      have htower : ((opiCoreInG π M).subgroupOf M).index * M.index =
          (opiCoreInG π M).index :=
        Subgroup.relIndex_mul_index (opiCoreInG_le π M)
      exact ⟨M.index, htower.symm⟩
    exact hHall.2 r (Nat.mem_primeFactors.mpr
      ⟨(Nat.mem_primeFactors.mp hr).1,
        dvd_trans (Nat.mem_primeFactors.mp hr).2.1 hidx, Subgroup.index_ne_zero_of_finite⟩)

/-- A `π`-subgroup of `M` lies in `O_π(M)`, provided `O_π(M)` is `π`-Hall in `G`. -/
theorem piSubgroup_le_opiCoreInG_of_isHall [Finite G] {π : Set ℕ} {M L : Subgroup G}
    (hHall : Ch03.IsHallSubgroup π (opiCoreInG π M)) (hLM : L ≤ M)
    (hLpi : Ch03.Subgroup.IsPiGroup π L) : L ≤ opiCoreInG π M := by
  have : ((opiCoreInG π M).subgroupOf M).Normal := by
    rw [opiCoreInG_subgroupOf]
    infer_instance
  have hHallM : Ch03.IsHallSubgroup π ((opiCoreInG π M).subgroupOf M) :=
    opiCoreInG_subgroupOf_isHall_of_isHall hHall
  have hLsubOf : Ch03.Subgroup.IsPiGroup π (L.subgroupOf M) :=
    Ch03.Subgroup.IsPiGroup.subgroupOf hLM hLpi
  have hle : L.subgroupOf M ≤ (opiCoreInG π M).subgroupOf M :=
    isPiGroup_le_of_normal_isHallSubgroup hHallM hLsubOf
  intro x hx
  have hxM : x ∈ M := hLM hx
  have : (⟨x, hxM⟩ : ↥M) ∈ (opiCoreInG π M).subgroupOf M := hle hx
  rwa [Subgroup.mem_subgroupOf] at this

/-- If `M_α` is `α(M)`-Hall in `G`, then its internal copy is `α(M)`-Hall in `M`. -/
theorem Malpha_subgroupOf_isHall_of_isHall [Finite G] {M : Subgroup G}
    (hHall : Ch03.IsHallSubgroup (alpha M) (Malpha M)) :
    Ch03.IsHallSubgroup (alpha M) ((Malpha M).subgroupOf M) := by
  simpa [Malpha] using
    opiCoreInG_subgroupOf_isHall_of_isHall (π := alpha M) (M := M) hHall

/-- If `M_σ` is `σ(M)`-Hall in `G`, then its internal copy is `σ(M)`-Hall in `M`. -/
theorem Msigma_subgroupOf_isHall_of_isHall [Finite G] {M : Subgroup G}
    (hHall : Ch03.IsHallSubgroup (sigma M) (Msigma M)) :
    Ch03.IsHallSubgroup (sigma M) ((Msigma M).subgroupOf M) := by
  simpa [Msigma] using
    opiCoreInG_subgroupOf_isHall_of_isHall (π := sigma M) (M := M) hHall

/-- An `α(M)`-subgroup of `M` lies in `M_α`, provided `M_α` is `α(M)`-Hall in `G`. -/
theorem alpha_subgroup_le_Malpha_of_isHall [Finite G] {M L : Subgroup G}
    (hHall : Ch03.IsHallSubgroup (alpha M) (Malpha M)) (hLM : L ≤ M)
    (hLpi : Ch03.Subgroup.IsPiGroup (alpha M) L) : L ≤ Malpha M := by
  simpa [Malpha] using
    piSubgroup_le_opiCoreInG_of_isHall (π := alpha M) (M := M) hHall hLM hLpi

/-- A `σ(M)`-subgroup of `M` lies in `M_σ`, provided `M_σ` is `σ(M)`-Hall in `G`. -/
theorem sigma_subgroup_le_Msigma_of_isHall [Finite G] {M L : Subgroup G}
    (hHall : Ch03.IsHallSubgroup (sigma M) (Msigma M)) (hLM : L ≤ M)
    (hLpi : Ch03.Subgroup.IsPiGroup (sigma M) L) : L ≤ Msigma M := by
  simpa [Msigma] using
    piSubgroup_le_opiCoreInG_of_isHall (π := sigma M) (M := M) hHall hLM hLpi

@[simp] theorem mem_elemAbelianOfRankIn_iff (p n : ℕ) (H X : Subgroup G) :
    elemAbelianOfRankIn p n H X ↔ X ∈ elemAbelianOfRank G p n ∧ X ≤ H :=
  Iff.rfl

theorem omega1CenterInG_le (P : Subgroup G) (p : ℕ) :
    omega1CenterInG P p ≤ P :=
  Subgroup.map_subtype_le _

/-- **BG Theorem 10.6, low-rank branch for maximal subgroups**:
if `p ∉ α(M)`, then the maximal subgroup `M` has `p`-length one.  When
`p ∈ π(M)`, this is the rank-`≤ 2` case of BG Theorem 4.18(e); when
`p ∉ π(M)`, the quotient by `O_{p',p}(M)` has order dividing `|M|`, so no
`p` can divide it. -/
theorem maximal_hasPLengthOne_of_not_mem_alpha [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} [Fact p.Prime] (hpα : p ∉ alpha M) :
    Ch1.hasPLengthOne p ↥M := by
  classical
  by_cases hpM : p ∈ (Nat.card ↥M).primeFactors
  · have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
    have hoddM : Odd (Nat.card ↥M) :=
      hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
    have hp_dvd : p ∣ Nat.card ↥M := (Nat.mem_primeFactors.mp hpM).2.1
    have hnot_rank : ¬ 3 ≤ pRank ↥M p := by
      intro h3
      exact hpα ⟨hpM, h3⟩
    have hrank : pRank ↥M p ≤ 2 := by omega
    exact (Ch1.S04.solvable_structure_of_pRank_le_two hoddM hp_dvd hrank).2.2.2.2.2
  · rw [Ch1.hasPLengthOne]
    intro hpquot
    exact hpM (Nat.mem_primeFactors.mpr
      ⟨Fact.out, hpquot.trans (Subgroup.card_quotient_dvd_card
        (Ch03.oPiPrimePiCore ({p} : Set ℕ) ↥M)), Nat.card_pos.ne'⟩)

/-- Conjugation by `c ∈ M` commutes with the inclusion `M.subtype`: `(c • K)` mapped into `G`
equals `↑c`-conjugation of `K` mapped into `G`. The basic equivariance used throughout §10
to move between conjugation inside `↥M` and conjugation in `G`. -/
private theorem map_subtype_conj_smul {M : Subgroup G} (c : ↥M) (K : Subgroup ↥M) :
    (MulAut.conj c • K).map M.subtype = MulAut.conj (c : G) • (K.map M.subtype) := by
  have hcomp : (MulAut.conj (c : G)).toMonoidHom.comp M.subtype
      = M.subtype.comp (MulAut.conj c).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
  change (K.map (MulAut.conj c).toMonoidHom).map M.subtype
      = (K.map M.subtype).map (MulAut.conj (c : G)).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map, hcomp]

/-- **σ basic fact** (mmd L2655): if `p ∈ σ(M)`, then for *every* Sylow `p`-subgroup `Q` of `M`
the `G`-normalizer of its image lies in `M`. The definition of `σ(M)` provides one such Sylow `P`;
every other `Q` is `M`-conjugate to it (`Q = m • P`, `m ∈ M`), and `N_G(·)` is
conjugation-equivariant. (De-private で公開 — BG Prop 12.15(b) の cyclic-case `S = Syl_q(M)` で再利用。) -/
theorem normalizer_sylow_map_le_of_mem_sigma [Finite G]
    {M : Subgroup G} {p : ℕ} [Fact p.Prime] (hp : p ∈ sigma M) (Q : Sylow p ↥M) :
    Subgroup.normalizer (((Q : Subgroup ↥M).map M.subtype : Subgroup G) : Set G) ≤ M := by
  classical
  obtain ⟨-, P, hP⟩ := hp
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (↥M) P Q
  -- `Q̄ = conj ↑m • P̄ = P̄.map (conj ↑m)`: conjugation commutes with `M.subtype`.
  have hQeq : ((Q : Subgroup ↥M).map M.subtype : Subgroup G)
      = ((P : Subgroup ↥M).map M.subtype).map (MulAut.conj (m : G)).toMonoidHom := by
    have hQ : (Q : Subgroup ↥M) = MulAut.conj m • (P : Subgroup ↥M) := by
      rw [← hm]; exact Sylow.coe_subgroup_smul
    rw [hQ, map_subtype_conj_smul]; rfl
  -- `N_G(Q̄) = N_G(P̄).map (conj ↑m) ≤ M.map (conj ↑m) = M`.
  have hbij : Function.Bijective (MulAut.conj (m : G)).toMonoidHom :=
    (MulAut.conj (m : G)).bijective
  have hnorm : Subgroup.normalizer (((Q : Subgroup ↥M).map M.subtype : Subgroup G) : Set G)
      = (Subgroup.normalizer (((P : Subgroup ↥M).map M.subtype : Subgroup G) : Set G)).map
          (MulAut.conj (m : G)).toMonoidHom := by
    rw [hQeq, ← Subgroup.map_normalizer_eq_of_bijective _ hbij]
  rw [hnorm]
  intro g hg
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hg
  have hnM : n ∈ M := hP hn
  -- `(conj ↑m).toMonoidHom n = ↑m * n * ↑m⁻¹ ∈ M`
  have : (MulAut.conj (m : G)).toMonoidHom n = (m : G) * n * (m : G)⁻¹ := by
    simp [MulAut.conj_apply]
  rw [this]
  exact M.mul_mem (M.mul_mem m.2 hnM) (M.inv_mem m.2)

/-- **BG Theorem 10.1(d)** (mmd L2665): for `p ∈ σ(M)` and `X = P̄` a Sylow `p`-subgroup of `M`,
if a `G`-conjugate `X^g` lies in `M` then `g ∈ M`. Both `X` and `X^g` are Sylow `p`-subgroups of
`M`, hence `M`-conjugate; the conjugating discrepancy normalizes `X`, and `N_G(X) ≤ M` (σ). -/
private theorem fusion_d_of_mem_sigma [Finite G]
    {M : Subgroup G} {p : ℕ} [Fact p.Prime] (hp : p ∈ sigma M)
    (P : Sylow p ↥M) {g : G}
    (hg : MulAut.conj g • ((P : Subgroup ↥M).map M.subtype) ≤ M) : g ∈ M := by
  classical
  set X : Subgroup G := (P : Subgroup ↥M).map M.subtype with hXdef
  have hcardX : Nat.card ↥X = p ^ (Nat.card ↥M).factorization p := by
    rw [hXdef, Subgroup.card_map_of_injective M.subtype_injective]
    exact P.card_eq_multiplicity
  -- `Ȳ = (conj g • X).subgroupOf M` is a Sylow-`p` of `↥M`.
  have hcardConj : Nat.card ↥(MulAut.conj g • X) = Nat.card ↥X :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hcardY : Nat.card ↥((MulAut.conj g • X).subgroupOf M)
      = p ^ (Nat.card ↥M).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hg).toEquiv, hcardConj, hcardX]
  let PY : Sylow p ↥M := Sylow.ofCard ((MulAut.conj g • X).subgroupOf M) hcardY
  -- Sylow conjugacy in `↥M`: `c • P = PY` for some `c ∈ M`.
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥M) P PY
  have hPY : ((PY : Subgroup ↥M).map M.subtype : Subgroup G) = MulAut.conj g • X := by
    change (((MulAut.conj g • X).subgroupOf M : Subgroup ↥M).map M.subtype) = MulAut.conj g • X
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hg]
  -- transport to `G`: `conj ↑c • X = conj g • X`.
  have hconj : MulAut.conj (c : G) • X = MulAut.conj g • X := by
    have h1 : (PY : Subgroup ↥M) = MulAut.conj c • (P : Subgroup ↥M) := by
      rw [← hc]; exact Sylow.coe_subgroup_smul
    rw [← hPY, h1, map_subtype_conj_smul, ← hXdef]
  -- `↑c⁻¹ * g` normalizes `X`, so lies in `N_G(X) ≤ M`; and `↑c ∈ M`.
  have hstab : MulAut.conj ((c : G)⁻¹ * g) • X = X := by
    rw [map_mul, mul_smul, ← hconj, ← mul_smul, ← map_mul]
    simp
  have hnM : ((c : G)⁻¹ * g) ∈ M :=
    normalizer_sylow_map_le_of_mem_sigma hp P (mem_normalizer_of_conj_smul_eq_self hstab)
  have hg_eq : g = (c : G) * ((c : G)⁻¹ * g) := by group
  rw [hg_eq]
  exact M.mul_mem c.2 hnM

/-- A maximal subgroup of a minimal simple group is self-normalizing: `N_G(M) ≤ M`.
(`M` is a coatom; if `M < N_G(M)` then `N_G(M) = ⊤`, so `M ⊴ G`, forcing `M ∈ {⊥, ⊤}` by
simplicity — both impossible: `M = ⊤` contradicts the coatom, and `M = ⊥` makes `G` cyclic of
prime order, contradicting non-solvability.) -/
theorem maximal_normalizer_le_self [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Subgroup.normalizer (M : Set G) ≤ M := by
  have hco : IsCoatom M := mem_maximalSubgroups.mp hM
  rcases eq_or_lt_of_le (Subgroup.le_normalizer (H := M)) with heq | hlt
  · exact heq.ge
  · exfalso
    have hnorm : M.Normal := Subgroup.normalizer_eq_top_iff.mp (hco.2 _ hlt)
    rcases hG.simple.eq_bot_or_eq_top_of_normal M hnorm with hbot | htop'
    · -- `M = ⊥`: every nontrivial subgroup is `⊤`, so `G` is cyclic, hence solvable.
      have hco' : ∀ b : Subgroup G, ⊥ < b → b = ⊤ := by rw [← hbot]; exact hco.2
      have : Nontrivial G := hG.simple.toNontrivial
      obtain ⟨g, hg1⟩ := exists_ne (1 : G)
      have hgtop : Subgroup.zpowers g = ⊤ :=
        hco' _ (bot_lt_iff_ne_bot.mpr (fun h => hg1 (Subgroup.zpowers_eq_bot.mp h)))
      have hcomm : ∀ a b : G, a * b = b * a := by
        intro a b
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgtop ▸ Subgroup.mem_top a)
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgtop ▸ Subgroup.mem_top b)
        rw [← zpow_add, ← zpow_add, add_comm]
      exact hG.notSolvable (Group.isSolvable_of_comm hcomm)
    · exact hco.1 htop'

/-- **BG Theorem 10.1 part-(b) input** (mmd L2697-2699): for a proper subgroup `L < ⊤` and a
Sylow `p`-subgroup `P` of `L` with `rank P ≤ 2`, the Frattini decomposition
`L = O_{p'}(L) · N_L(P)` holds. `L` is solvable (proper subgroup of a minimal simple group),
so Theorem 4.18(e) gives `L` `p`-length one, and the §6 Frattini lemma applies. -/
private theorem frattini_decomp_of_rank_le_two [Finite G] (hG : IsMinimalSimpleOdd G)
    {L : Subgroup G} (hL : L < ⊤) {p : ℕ} [Fact p.Prime] (P : Sylow p ↥L)
    (hp_dvd : p ∣ Nat.card ↥L) (hrank : rank ↥(P : Subgroup ↥L) ≤ 2) :
    (⊤ : Subgroup ↥L)
      = Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} ↥L ⊔ Subgroup.normalizer (P : Subgroup ↥L) := by
  have : Group.IsSolvable ↥L := hG.isSolvable_of_lt_top L hL
  have hodd : Odd (Nat.card ↥L) := by
    rcases Nat.even_or_odd (Nat.card ↥L) with he | ho
    · exact absurd (he.two_dvd.trans (Subgroup.card_subgroup_dvd_card L))
        (by have := hG.odd; rw [Nat.odd_iff] at this; omega)
    · exact ho
  have hpr : pRank ↥L p ≤ 2 := by
    rw [← pRank_sylow_eq P]; exact (pRank_le_rank p).trans hrank
  have hpl1 : Ch1.hasPLengthOne p ↥L :=
    (Ch1.S04.solvable_structure_of_pRank_le_two hodd hp_dvd hpr).2.2.2.2.2
  exact Ch1.S06.top_eq_oPiPrimeCore_sup_normalizer_sylow P hpl1

/-- **Normalizer growth in a `p`-group**: if `X < S` with `S` a `p`-group, then `X` is properly
contained in `N_G(X) ⊓ S` (some element of `S` normalizes `X` without lying in `X`). This is the
nilpotent normalizer condition applied inside `↥S`, transported back to `G` via
`subgroupOf_normalizer_eq`. Used to show a non-Sylow `p`-subgroup grows inside its normalizer. -/
private theorem lt_inf_normalizer_of_lt_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    {X S : Subgroup G} (hXS : X < S) (hS : IsPGroup p ↥S) :
    X < Subgroup.normalizer X ⊓ S := by
  have : Group.IsNilpotent ↥S := hS.isNilpotent
  have hNC : NormalizerCondition ↥S := Group.normalizerCondition_of_isNilpotent (G := ↥S)
  have hsub_lt : X.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hXS.ne (le_antisymm hXS.le htop)
  obtain ⟨t, ht_norm, ht_not⟩ := SetLike.exists_of_lt (hNC _ hsub_lt)
  rw [← Subgroup.subgroupOf_normalizer_eq hXS.le, Subgroup.mem_subgroupOf] at ht_norm
  rw [Subgroup.mem_subgroupOf] at ht_not
  refine lt_of_le_of_ne (le_inf Subgroup.le_normalizer hXS.le) (fun heq => ht_not ?_)
  exact heq ▸ Subgroup.mem_inf.mpr ⟨ht_norm, t.2⟩

/-- **σ basic fact, Sylow side** (mmd L2655): if `p ∈ σ(M)`, then `M` contains a Sylow
`p`-subgroup of `G`. The defining Sylow `P` of `M` has `N_G(P̄) ≤ M`; if `P̄` were a proper
`p`-subgroup of a Sylow `S` of `G`, then `N_G(P̄) ⊓ S` (a `p`-subgroup of `M`) would strictly
contain `P̄`, contradicting that `P̄` is a Sylow `p`-subgroup of `M`. Hence `P̄ = S ≤ M`. -/
private theorem exists_sylow_le_of_mem_sigma [Finite G]
    {M : Subgroup G} {p : ℕ} [Fact p.Prime] (hp : p ∈ sigma M) :
    ∃ Q : Sylow p G, (Q : Subgroup G) ≤ M := by
  obtain ⟨-, P, hP⟩ := hp
  set Pbar : Subgroup G := (P : Subgroup ↥M).map M.subtype with hPbar
  have hPbar_pg : IsPGroup p ↥Pbar :=
    P.2.of_equiv (Subgroup.equivMapOfInjective _ _ M.subtype_injective)
  have hPbar_le_M : Pbar ≤ M := Subgroup.map_subtype_le _
  have hPbar_subOf : Pbar.subgroupOf M = (P : Subgroup ↥M) := by
    rw [hPbar, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  obtain ⟨S, hPS⟩ := hPbar_pg.exists_le_sylow
  have hPeqS : (S : Subgroup G) = Pbar := by
    by_contra hne
    have hlt : Pbar < (S : Subgroup G) := lt_of_le_of_ne hPS (Ne.symm hne)
    have hgrow : Pbar < Subgroup.normalizer Pbar ⊓ (S : Subgroup G) :=
      lt_inf_normalizer_of_lt_of_isPGroup hlt S.2
    set Y : Subgroup G := Subgroup.normalizer Pbar ⊓ (S : Subgroup G) with hY
    have hYM : Y ≤ M := le_trans inf_le_left hP
    have hYpg : IsPGroup p ↥Y :=
      S.2.of_injective (Subgroup.inclusion (inf_le_right)) (Subgroup.inclusion_injective _)
    -- `Y.subgroupOf M` is a `p`-group `⊇ P`, hence `= P` by Sylow maximality; mapping back,
    -- `Y = P̄`.
    have hPle : (P : Subgroup ↥M) ≤ Y.subgroupOf M :=
      hPbar_subOf ▸ Subgroup.comap_mono (f := M.subtype) hgrow.le
    have hYsubM_pg : IsPGroup p ↥(Y.subgroupOf M) :=
      hYpg.of_equiv (Subgroup.subgroupOfEquivOfLe hYM).symm
    have hYeq : Y.subgroupOf M = (P : Subgroup ↥M) := P.3 hYsubM_pg hPle
    have : Y = Pbar := by
      have := congrArg (Subgroup.map M.subtype) hYeq
      rwa [Subgroup.map_subgroupOf_eq_of_le hYM, ← hPbar] at this
    exact absurd this hgrow.ne'
  exact ⟨S, hPeqS ▸ hPbar_le_M⟩

/-- **σ basic fact, index form** (mmd L2655): if `p ∈ σ(M)`, then `M` contains a
Sylow `p`-subgroup of `G`, so `p` does not divide `[G : M]`. -/
theorem not_dvd_index_of_mem_sigma [Finite G]
    {M : Subgroup G} {p : ℕ} [Fact p.Prime] (hp : p ∈ sigma M) :
    ¬ p ∣ M.index := by
  obtain ⟨Q, hQM⟩ := exists_sylow_le_of_mem_sigma hp
  intro hpidx
  exact Q.not_dvd_index (hpidx.trans (Subgroup.index_dvd_of_le hQM))

/-- Conjugation by `g` as an order isomorphism of the subgroup lattice of `G`. -/
private def conjOrderIso (g : G) : Subgroup G ≃o Subgroup G where
  toFun H := MulAut.conj g • H
  invFun H := MulAut.conj g⁻¹ • H
  left_inv H := by
    change MulAut.conj g⁻¹ • (MulAut.conj g • H) = H
    rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  right_inv H := by
    change MulAut.conj g • (MulAut.conj g⁻¹ • H) = H
    rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  map_rel_iff' := Subgroup.pointwise_smul_le_pointwise_smul_iff

/-- A conjugate of a maximal subgroup is maximal. -/
private theorem isCoatom_conj_smul {g : G} {M : Subgroup G} (h : IsCoatom M) :
    IsCoatom (MulAut.conj g • M) :=
  (OrderIso.isCoatom_iff (conjOrderIso g) M).mpr h

/-- The conjugation/inclusion adjunction: `gXg⁻¹ ≤ M ↔ X ≤ g⁻¹Mg`. -/
private theorem conj_smul_le_iff {g : G} {X M : Subgroup G} :
    MulAut.conj g • X ≤ M ↔ X ≤ MulAut.conj g⁻¹ • M :=
  (OrderIso.le_symm_apply (conjOrderIso g)).symm

/-- Conjugation commutes with `map`: `g • H = H.map (conj g)`. -/
private theorem mulAut_smul_eq_map (φ : MulAut G) (H : Subgroup G) :
    φ • H = H.map (φ : G →* G) := rfl

/-- Conjugation preserves cardinality. -/
private theorem card_conj_smul (g : G) (H : Subgroup G) :
    Nat.card ↥(MulAut.conj g • H) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

/-- Conjugation commutes with the normalizer. -/
private theorem normalizer_conj_smul (g : G) (H : Subgroup G) :
    MulAut.conj g • Subgroup.normalizer (H : Set G)
      = Subgroup.normalizer ((MulAut.conj g • H : Subgroup G) : Set G) := by
  rw [mulAut_smul_eq_map, mulAut_smul_eq_map]
  exact Subgroup.map_normalizer_eq_of_bijective H (MulAut.conj g).bijective

/-- **σ is conjugation-equivariant**: `p ∈ σ(M) ⟹ p ∈ σ(M^g)`. The Sylow `P` witnessing
`σ(M)` conjugates to a Sylow of `M^g`, and `N_G(P̄) ≤ M` conjugates to `N_G(P̄^g) ≤ M^g`.
(Public: §12 uses this to rule out conjugacy of maximal subgroups with distinct σ-sets,
e.g. in Lemmas 12.2(b) and 12.3.) -/
theorem sigma_conj [Finite G] {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (g : G) (hp : p ∈ sigma M) : p ∈ sigma (MulAut.conj g • M) := by
  rw [mem_sigma_iff] at hp ⊢
  obtain ⟨hpf, P, hP⟩ := hp
  refine ⟨by rw [card_conj_smul]; exact hpf, ?_⟩
  set Pbar : Subgroup G := (P : Subgroup ↥M).map M.subtype with hPbar
  have hle : MulAut.conj g • Pbar ≤ MulAut.conj g • M :=
    Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (Subgroup.map_subtype_le _)
  have hcard : Nat.card ↥((MulAut.conj g • Pbar).subgroupOf (MulAut.conj g • M))
      = p ^ (Nat.card ↥(MulAut.conj g • M)).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_conj_smul, card_conj_smul,
      hPbar, Subgroup.card_map_of_injective M.subtype_injective]
    exact P.card_eq_multiplicity
  refine ⟨Sylow.ofCard ((MulAut.conj g • Pbar).subgroupOf (MulAut.conj g • M)) hcard, ?_⟩
  have hP'bar : (((Sylow.ofCard ((MulAut.conj g • Pbar).subgroupOf (MulAut.conj g • M)) hcard :
        Sylow p ↥(MulAut.conj g • M)) : Subgroup ↥(MulAut.conj g • M)).map
          (MulAut.conj g • M).subtype : Subgroup G) = MulAut.conj g • Pbar := by
    change ((MulAut.conj g • Pbar).subgroupOf (MulAut.conj g • M)).map (MulAut.conj g • M).subtype
      = _
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle]
  rw [hP'bar, ← normalizer_conj_smul]
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hP

/-- A proper subgroup has strictly smaller cardinality (finite group). -/
private theorem card_lt_card_of_lt [Finite G] {H K : Subgroup G} (h : H < K) :
    Nat.card ↥H < Nat.card ↥K := by
  refine lt_of_le_of_ne (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective h.le)) ?_
  intro hcard
  exact h.ne (Subgroup.eq_of_le_of_card_ge h.le hcard.ge)

/-- **BG Theorem 10.1 part (b)** (mmd L2679-2711): `C_G(X)` acts transitively by conjugation on
`{M^g | X ≤ M^g}`. Proved by contradiction, taking `X` a counterexample of maximal order
(strong induction on `Nat.card G - Nat.card X`). The maximal choice promotes `X` to strictly
larger `p`-subgroups `X₁ ≤ M₁ ∩ L`, `X₂ ≤ M₂ ∩ L` (where `L = N_G(X)`), for which the inductive
hypothesis applies, reducing the non-conjugacy `(10.1)` to `(10.2)`: a conjugate `M^s ⊇ P`
(`P ∈ Syl_p(L)`) and `(M^s)^t` are not `C_G(X)`-conjugate. The rank of `P` then yields a
contradiction: `r(P) ≥ 3` via the Uniqueness Theorem (9.6), `r(P) ≤ 2` via Theorem 4.18(e) and
a Frattini decomposition of `L`. -/
private theorem fusion_b [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime] (hp : p ∈ sigma M) :
    ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup p X →
    ∀ g₁ g₂ : G, X ≤ MulAut.conj g₁ • M → X ≤ MulAut.conj g₂ • M →
      ∃ c ∈ Subgroup.centralizer (X : Set G),
        MulAut.conj c • (MulAut.conj g₁ • M) = MulAut.conj g₂ • M := by
  classical
  have hMc : IsCoatom M := mem_maximalSubgroups.mp hM
  suffices key : ∀ n : ℕ, ∀ X : Subgroup G, Nat.card G - Nat.card ↥X = n →
      X ≠ ⊥ → IsPGroup p X → ∀ g₁ g₂ : G, X ≤ MulAut.conj g₁ • M → X ≤ MulAut.conj g₂ • M →
        ∃ c ∈ Subgroup.centralizer (X : Set G),
          MulAut.conj c • (MulAut.conj g₁ • M) = MulAut.conj g₂ • M by
    intro X hXne hXp g₁ g₂ h1 h2
    exact key _ X rfl hXne hXp g₁ g₂ h1 h2
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro X hmeas hXne hXp g₁ g₂ h1 h2
    by_contra hcon
    push Not at hcon
    set M₁ := MulAut.conj g₁ • M with hM₁def
    set M₂ := MulAut.conj g₂ • M with hM₂def
    set L := Subgroup.normalizer (X : Set G) with hLdef
    set C := Subgroup.centralizer (X : Set G) with hCdef
    have hM1c : IsCoatom M₁ := isCoatom_conj_smul hMc
    have hM2c : IsCoatom M₂ := isCoatom_conj_smul hMc
    -- `L = N_G(X) < ⊤`: else `X ⊴ G`, forcing `X ∈ {⊥,⊤}`, both impossible.
    have hL_lt : L < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      rw [hLdef] at htop
      have hXnorm : X.Normal := Subgroup.normalizer_eq_top_iff.mp htop
      rcases hG.simple.eq_bot_or_eq_top_of_normal X hXnorm with hbot | htopX
      · exact hXne hbot
      · have hGpg : IsPGroup p G := hXp.of_equiv (htopX ▸ Subgroup.topEquiv)
        have : Group.IsNilpotent G := hGpg.isNilpotent
        exact hG.notSolvable inferInstance
    have hXcardG : Nat.card ↥X ≤ Nat.card G :=
      Nat.le_of_dvd Nat.card_pos X.card_subgroup_dvd_card
    -- Promote `X` to a strictly larger `p`-subgroup inside `(conj a•M) ∩ L`, given that
    -- `conj a•M` and `conj b•M` are not `C_G(X)`-conjugate (so `X` is not Sylow in `conj a•M`).
    have promote : ∀ a b : G, X ≤ MulAut.conj a • M → X ≤ MulAut.conj b • M →
        (∀ c ∈ C, MulAut.conj c • (MulAut.conj a • M) ≠ MulAut.conj b • M) →
        ∃ Y : Subgroup G, X < Y ∧ Y ≤ MulAut.conj a • M ∧ Y ≤ L ∧ IsPGroup p ↥Y := by
      intro a b ha hb hne
      have hXpa : IsPGroup p ↥(X.subgroupOf (MulAut.conj a • M)) :=
        hXp.of_equiv (Subgroup.subgroupOfEquivOfLe ha).symm
      obtain ⟨Q, hQ⟩ := hXpa.exists_le_sylow
      set S₁ := (Q : Subgroup ↥(MulAut.conj a • M)).map (MulAut.conj a • M).subtype with hS₁def
      have hXS₁ : X ≤ S₁ := by
        rw [hS₁def, ← Subgroup.map_subgroupOf_eq_of_le ha]; exact Subgroup.map_mono hQ
      have hS₁M : S₁ ≤ MulAut.conj a • M := Subgroup.map_subtype_le _
      have hS₁p : IsPGroup p ↥S₁ :=
        Q.2.of_equiv (Subgroup.equivMapOfInjective _ _ (MulAut.conj a • M).subtype_injective)
      have hXS₁lt : X < S₁ := by
        rcases lt_or_eq_of_le hXS₁ with hlt | heq
        · exact hlt
        · exfalso
          have hgbg : MulAut.conj (a * b⁻¹) • (MulAut.conj b • M) = MulAut.conj a • M := by
            rw [← mul_smul, ← map_mul, inv_mul_cancel_right]
          have hdle : MulAut.conj (a * b⁻¹) • S₁ ≤ MulAut.conj a • M := by
            rw [← heq]
            calc MulAut.conj (a * b⁻¹) • X
                  ≤ MulAut.conj (a * b⁻¹) • (MulAut.conj b • M) :=
                    Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hb
              _ = MulAut.conj a • M := hgbg
          have hd : (a * b⁻¹) ∈ MulAut.conj a • M :=
            fusion_d_of_mem_sigma (M := MulAut.conj a • M) (sigma_conj a hp) Q (hS₁def ▸ hdle)
          have hself : MulAut.conj (a * b⁻¹) • (MulAut.conj a • M) = MulAut.conj a • M :=
            conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hd)
          have key : MulAut.conj (a * b⁻¹) • (MulAut.conj a • M)
              = MulAut.conj (a * b⁻¹) • (MulAut.conj b • M) := hself.trans hgbg.symm
          have hab : MulAut.conj a • M = MulAut.conj b • M :=
            le_antisymm (Subgroup.pointwise_smul_le_pointwise_smul_iff.mp key.le)
              (Subgroup.pointwise_smul_le_pointwise_smul_iff.mp key.ge)
          exact hne 1 (Subgroup.one_mem C) (by rw [map_one, one_smul]; exact hab)
      refine ⟨Subgroup.normalizer X ⊓ S₁, lt_inf_normalizer_of_lt_of_isPGroup hXS₁lt hS₁p,
        le_trans inf_le_right hS₁M, inf_le_left,
        hS₁p.of_injective (Subgroup.inclusion inf_le_right) (Subgroup.inclusion_injective _)⟩
    obtain ⟨X₁, hXX₁, hX₁M₁, hX₁L, hX₁p⟩ := promote g₁ g₂ h1 h2 hcon
    obtain ⟨X₂, hXX₂, hX₂M₂, hX₂L, hX₂p⟩ := promote g₂ g₁ h2 h1 (by
      intro c hc heq
      refine hcon c⁻¹ (Subgroup.inv_mem C hc) ?_
      rw [hM₁def, hM₂def, ← heq, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul])
    -- `P ∈ Syl_p(L)` containing `X₁`; its image `P̄ ≤ L`.
    obtain ⟨P, hX₁P⟩ : ∃ P : Sylow p ↥L, X₁ ≤ (P : Subgroup ↥L).map L.subtype := by
      obtain ⟨P, hP⟩ := (hX₁p.of_equiv (Subgroup.subgroupOfEquivOfLe hX₁L).symm).exists_le_sylow
      exact ⟨P, by rw [← Subgroup.map_subgroupOf_eq_of_le hX₁L]; exact Subgroup.map_mono hP⟩
    set Pbar := ((P : Subgroup ↥L).map L.subtype) with hPbardef
    have hPbarL : Pbar ≤ L := Subgroup.map_subtype_le _
    have hPbarp : IsPGroup p ↥Pbar :=
      P.2.of_equiv (Subgroup.equivMapOfInjective _ _ L.subtype_injective)
    -- WLOG choose `s` with `P̄ ≤ M^s := conj s • M` (uses `σ ⟹ M ⊇ Sylow of G`).
    obtain ⟨s, hPs⟩ : ∃ s : G, Pbar ≤ MulAut.conj s • M := by
      obtain ⟨Q, hQM⟩ := exists_sylow_le_of_mem_sigma hp
      obtain ⟨S', hPbarS'⟩ := hPbarp.exists_le_sylow
      obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G Q S'
      refine ⟨a, hPbarS'.trans ?_⟩
      calc (S' : Subgroup G) = MulAut.conj a • (Q : Subgroup G) := by
              rw [← ha, Sylow.coe_subgroup_smul]
        _ ≤ MulAut.conj a • M := Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hQM
    set Ms := MulAut.conj s • M with hMsdef
    have hMsc : IsCoatom Ms := isCoatom_conj_smul hMc
    -- `t ∈ L` with `X₂ ≤ P̄^t`.
    obtain ⟨t, htL, hX₂t⟩ : ∃ t : G, t ∈ L ∧ X₂ ≤ MulAut.conj t • Pbar := by
      obtain ⟨S'', hX₂S''⟩ :=
        (hX₂p.of_equiv (Subgroup.subgroupOfEquivOfLe hX₂L).symm).exists_le_sylow
      obtain ⟨t', ht'⟩ := MulAction.exists_smul_eq (↥L) P S''
      refine ⟨(t' : G), t'.2, ?_⟩
      calc X₂ = (X₂.subgroupOf L).map L.subtype := (Subgroup.map_subgroupOf_eq_of_le hX₂L).symm
        _ ≤ (S'' : Subgroup ↥L).map L.subtype := Subgroup.map_mono hX₂S''
        _ = (MulAut.conj t' • (P : Subgroup ↥L)).map L.subtype := by
              rw [← ht', Sylow.coe_subgroup_smul]
        _ = MulAut.conj (t' : G) • Pbar := by rw [map_subtype_conj_smul, ← hPbardef]
    -- (10.2): `M^s` and `(M^s)^t` are not `C_G(X)`-conjugate.
    have h102 : ∀ c ∈ C, MulAut.conj c • Ms ≠ MulAut.conj t • Ms := by
      -- rel1: `M₁` and `M^s` are `C_G(X₁)`-conjugate (IH at `X₁`), hence `C_G(X)`-conjugate.
      obtain ⟨c₁, hc₁C, hc₁⟩ : ∃ c₁ ∈ C, MulAut.conj c₁ • M₁ = Ms := by
        have hmeas₁ : Nat.card G - Nat.card ↥X₁ < n := by
          have h1 : Nat.card ↥X < Nat.card ↥X₁ := card_lt_card_of_lt hXX₁
          have h2 : Nat.card ↥X₁ ≤ Nat.card G :=
            Nat.le_of_dvd Nat.card_pos X₁.card_subgroup_dvd_card
          omega
        obtain ⟨c, hcC₁, hc⟩ :=
          IH _ hmeas₁ X₁ rfl (bot_le.trans_lt hXX₁).ne' hX₁p g₁ s hX₁M₁ (hX₁P.trans hPs)
        exact ⟨c, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXX₁.le) hcC₁, hc⟩
      -- rel2: `M₂` and `(M^s)^t` are `C_G(X₂)`-conjugate (IH at `X₂`), hence `C_G(X)`-conjugate.
      obtain ⟨c₂, hc₂C, hc₂⟩ : ∃ c₂ ∈ C, MulAut.conj c₂ • M₂ = MulAut.conj t • Ms := by
        have hmeas₂ : Nat.card G - Nat.card ↥X₂ < n := by
          have h1 : Nat.card ↥X < Nat.card ↥X₂ := card_lt_card_of_lt hXX₂
          have h2 : Nat.card ↥X₂ ≤ Nat.card G :=
            Nat.le_of_dvd Nat.card_pos X₂.card_subgroup_dvd_card
          omega
        have hX₂ts : X₂ ≤ MulAut.conj (t * s) • M := by
          rw [map_mul, mul_smul]
          exact hX₂t.trans (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hPs)
        obtain ⟨c, hcC₂, hc⟩ :=
          IH _ hmeas₂ X₂ rfl (bot_le.trans_lt hXX₂).ne' hX₂p g₂ (t * s) hX₂M₂ hX₂ts
        refine ⟨c, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXX₂.le) hcC₂, ?_⟩
        have hbridge : MulAut.conj (t * s) • M = MulAut.conj t • Ms := by
          rw [hMsdef, map_mul, mul_smul]
        rw [hM₂def]; exact hc.trans hbridge
      intro c hcC heqcc
      refine hcon (c₂⁻¹ * c * c₁) (C.mul_mem (C.mul_mem (C.inv_mem hc₂C) hcC) hc₁C) ?_
      rw [map_mul, map_mul, mul_smul, mul_smul, hc₁, heqcc, ← hc₂, ← mul_smul, ← map_mul,
        inv_mul_cancel, map_one, one_smul]
    -- Case on `r(P̄)`.
    by_cases hrank : 3 ≤ rank ↥Pbar
    · -- `r(P) ≥ 3`: `P̄ ∈ 𝒰` (Thm 9.6); `P̄ ≤ L ∩ M^s ⟹ L ≤ M^s ⟹ t ∈ M^s`, contra (10.2).
      have hPbar_lt : Pbar < ⊤ := lt_of_le_of_lt hPbarL hL_lt
      have hPbarU : IsUniquelyMaximal Pbar :=
        OddOrder.BG.Ch2.S09.uniquenessTheorem hG hPbar_lt (by omega) (Or.inl hrank)
      obtain ⟨N, hNc, hLN⟩ := (IsCoatomic.eq_top_or_exists_le_coatom L).resolve_left hL_lt.ne
      have hMsN : Ms = N := hPbarU.eq_of_isCoatom_of_le hMsc hPs hNc (hPbarL.trans hLN)
      have hLMs : L ≤ Ms := hLN.trans hMsN.ge
      have hconjt : MulAut.conj t • Ms = Ms :=
        conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer (hLMs htL))
      exact h102 1 (Subgroup.one_mem C) (by rw [map_one, one_smul, hconjt])
    · -- `r(P) ≤ 2`: Thm 4.18(e) + Frattini ⟹ `t = c·m`, contra (10.2).
      have hrankP : rank ↥(P : Subgroup ↥L) ≤ 2 := by
        have hle : rank ↥(P : Subgroup ↥L) ≤ rank ↥Pbar :=
          rank_le_of_injective (f := (Subgroup.equivMapOfInjective (P : Subgroup ↥L) L.subtype
            L.subtype_injective).toMonoidHom)
            (Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective).injective
        omega
      have hp_dvd_L : p ∣ Nat.card ↥L := by
        obtain ⟨k, hk⟩ := hX₁p.exists_card_eq
        have hcard1 : Nat.card ↥X < Nat.card ↥X₁ := card_lt_card_of_lt hXX₁
        have hk0 : k ≠ 0 := by
          rintro rfl; rw [pow_zero] at hk; have := Nat.card_pos (α := ↥X); omega
        refine (hk ▸ dvd_pow_self p hk0).trans ?_
        rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₁L).toEquiv]
        exact (X₁.subgroupOf L).card_subgroup_dvd_card
      have hfd := frattini_decomp_of_rank_le_two hG hL_lt P hp_dvd_L hrankP
      have : (Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} ↥L).Normal := Ch03.oPiCore.normal _ _
      obtain ⟨o, ho, w, hw, how⟩ :=
        Subgroup.mem_sup_of_normal_left.mp (hfd ▸ Subgroup.mem_top (⟨t, htL⟩ : ↥L))
      have hXL : X ≤ L := Subgroup.le_normalizer
      have hXsubL_normal : (X.subgroupOf L).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hXL).mpr le_rfl
      have hdisj : Disjoint (Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} ↥L) (X.subgroupOf L) := by
        rw [disjoint_iff, inf_comm]
        exact inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl
          (isPiSubgroup_singleton_of_isPGroup
            (hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXL).symm))
          (Ch03.oPiCore.isPiGroup _)
      -- `↑o ∈ C_G(X)`: the `p'`-core centralizes the normal `p`-subgroup `X`.
      have ho_cent : (o : G) ∈ C := by
        rw [hCdef, Subgroup.mem_centralizer_iff]
        intro x hx
        have hxL : x ∈ L := hXL hx
        have hcomm : Commute o (⟨x, hxL⟩ : ↥L) :=
          Subgroup.commute_of_normal_of_disjoint _ _ (Ch03.oPiCore.normal _ _) hXsubL_normal hdisj
            o ⟨x, hxL⟩ ho (Subgroup.mem_subgroupOf.mpr hx)
        have hval := congrArg (Subgroup.subtype L) hcomm.eq
        simpa using hval.symm
      -- `↑n ∈ N_G(P̄)`.
      have hn_norm : MulAut.conj (w : G) • Pbar = Pbar := by
        have h1 : MulAut.conj w • (P : Subgroup ↥L) = (P : Subgroup ↥L) :=
          conj_smul_eq_self_of_mem_normalizer hw
        have h2 := congrArg (Subgroup.map L.subtype) h1
        rwa [map_subtype_conj_smul, ← hPbardef] at h2
      -- IH applied to `P̄` (strictly larger than `X`): `M^s` and `(M^s)^n` are `C_G(P̄)`-conjugate.
      have hXPbar : X < Pbar := lt_of_lt_of_le hXX₁ hX₁P
      have hmeasP : Nat.card G - Nat.card ↥Pbar < n := by
        have h1 : Nat.card ↥X < Nat.card ↥Pbar := card_lt_card_of_lt hXPbar
        have h2 : Nat.card ↥Pbar ≤ Nat.card G :=
          Nat.le_of_dvd Nat.card_pos Pbar.card_subgroup_dvd_card
        omega
      have hPbarns : Pbar ≤ MulAut.conj ((w : G) * s) • M := by
        rw [map_mul, mul_smul]
        exact hn_norm.symm.le.trans (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hPs)
      obtain ⟨x, hxC, hx⟩ :=
        IH _ hmeasP Pbar rfl (bot_le.trans_lt hXPbar).ne' hPbarp s ((w : G) * s) hPs hPbarns
      have hx' : MulAut.conj x • Ms = MulAut.conj (w : G) • Ms :=
        hx.trans (by rw [hMsdef, map_mul, mul_smul])
      -- `↑n = x · m` with `x ∈ C_G(P̄) ⊆ C_G(X)` and `m ∈ M^s`.
      have hMs_selfnorm : Subgroup.normalizer (Ms : Set G) ≤ Ms :=
        maximal_normalizer_le_self hG (mem_maximalSubgroups.mpr hMsc)
      have hnm : MulAut.conj ((w : G)⁻¹ * x) • Ms = Ms := by
        rw [map_mul, mul_smul, hx', ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      have hnx_mem : (w : G)⁻¹ * x ∈ Ms :=
        hMs_selfnorm (mem_normalizer_of_conj_smul_eq_self hnm)
      -- assemble `t = c · m`, `c = ↑o · x ∈ C`, `m ∈ M^s`.
      have ht_eq : t = (o : G) * (w : G) := by
        have := congrArg (Subgroup.subtype L) how
        simpa using this.symm
      set c := (o : G) * x with hcdef
      have hxX_cent : x ∈ C := Subgroup.centralizer_le
        (SetLike.coe_subset_coe.mpr (hXPbar.le)) hxC
      have hc_mem : c ∈ C := C.mul_mem ho_cent hxX_cent
      have hct : c⁻¹ * t ∈ Ms := by
        have hval : c⁻¹ * t = ((w : G)⁻¹ * x)⁻¹ := by rw [hcdef, ht_eq]; group
        rw [hval]; exact Ms.inv_mem hnx_mem
      refine h102 c hc_mem ?_
      have hfix : MulAut.conj (c⁻¹ * t) • Ms = Ms :=
        conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hct)
      calc MulAut.conj c • Ms
          = MulAut.conj c • (MulAut.conj (c⁻¹ * t) • Ms) := by rw [hfix]
        _ = MulAut.conj (c * (c⁻¹ * t)) • Ms := by rw [← mul_smul, ← map_mul]
        _ = MulAut.conj t • Ms := by rw [mul_inv_cancel_left]

/-- **BG Theorem 10.1** (mmd L2657): `M ∈ ℳ`, `p ∈ σ(M)`, `X` を `G` の非自明 `p`-部分群とする。
(a) `X, X^g ⊆ M ⇒ g = cm` (`c∈C_G(X)`, `m∈M`); (b) `C_G(X)` は `{M^g | X⊆M^g}` 上推移的;
(c) `X⊆M ⇒ N_G(X)=N_M(X)C_G(X)`; (d) `X∈Syl_p(M), X^g⊆M ⇒ g∈M`; (e) `X⊆M, C_G(X)⊆M, X^g⊆M ⇒ g∈M`。
共役 `X^g` は `MulAut.conj g • X`、(c) の積分解は要素形で述べる。BG は (a) を `g = cm` と書くが、
left-conj 規約 `conj g • X = gXg⁻¹` の下では `g = mc` (`m∈M`, `c∈C_G(X)`) が導かれるので、その形で述べる。
(e) は BG では `C_G(X)⊆M` のみだが、本質的に `X⊆M` を暗黙前提とする (a) の系なので `X⊆M` を明示する
(`C_G(X)⊆M` だけからは `X⊆M` が一般には従わない: `X` 非可換だと `X⊄C_G(X)`)。 -/
theorem fusion_control_of_mem_sigma [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime] (hp : p ∈ sigma M)
    {X : Subgroup G} (hXne : X ≠ ⊥) (hXp : IsPGroup p X) :
    (X ≤ M → ∀ g : G, MulAut.conj g • X ≤ M →
      ∃ m ∈ M, ∃ c ∈ Subgroup.centralizer (X : Set G), g = m * c) ∧
    (∀ g₁ g₂ : G, X ≤ MulAut.conj g₁ • M → X ≤ MulAut.conj g₂ • M →
      ∃ c ∈ Subgroup.centralizer (X : Set G),
        MulAut.conj c • (MulAut.conj g₁ • M) = MulAut.conj g₂ • M) ∧
    (X ≤ M → ∀ n ∈ Subgroup.normalizer X,
      ∃ a ∈ Subgroup.normalizer X ⊓ M, ∃ c ∈ Subgroup.centralizer (X : Set G), n = a * c) ∧
    ((∃ P : Sylow p ↥M, X = (P : Subgroup ↥M).map M.subtype) →
      ∀ g : G, MulAut.conj g • X ≤ M → g ∈ M) ∧
    (X ≤ M → Subgroup.centralizer (X : Set G) ≤ M →
      ∀ g : G, MulAut.conj g • X ≤ M → g ∈ M) := by
  have hb : ∀ g₁ g₂ : G, X ≤ MulAut.conj g₁ • M → X ≤ MulAut.conj g₂ • M →
      ∃ c ∈ Subgroup.centralizer (X : Set G),
        MulAut.conj c • (MulAut.conj g₁ • M) = MulAut.conj g₂ • M :=
    fusion_b hG hM hp X hXne hXp
  have ha : X ≤ M → ∀ g : G, MulAut.conj g • X ≤ M →
      ∃ m ∈ M, ∃ c ∈ Subgroup.centralizer (X : Set G), g = m * c := by
    intro hXM g hgM
    obtain ⟨c, hcC, hc⟩ :=
      hb 1 g⁻¹ (by rw [map_one, one_smul]; exact hXM) (conj_smul_le_iff.mp hgM)
    rw [map_one, one_smul] at hc
    have hgc : MulAut.conj (g * c) • M = M := by
      rw [map_mul, mul_smul, hc, ← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
    exact ⟨g * c, maximal_normalizer_le_self hG hM (mem_normalizer_of_conj_smul_eq_self hgc),
      c⁻¹, Subgroup.inv_mem _ hcC, by group⟩
  refine ⟨ha, hb, ?_, ?_, ?_⟩
  · -- (c): `N_G(X) = N_M(X)·C_G(X)`, from (a) applied to `n ∈ N_G(X)`.
    intro hXM n hn
    have hnXM : MulAut.conj n • X ≤ M := by
      rw [conj_smul_eq_self_of_mem_normalizer hn]; exact hXM
    obtain ⟨m, hmM, c, hcC, hnmc⟩ := ha hXM n hnXM
    refine ⟨m, ?_, c, hcC, hnmc⟩
    rw [Subgroup.mem_inf]
    refine ⟨?_, hmM⟩
    have hmeq : m = n * c⁻¹ := by rw [hnmc]; group
    rw [hmeq]
    exact Subgroup.mul_mem _ hn
      (Subgroup.centralizer_le_normalizer _ (Subgroup.inv_mem _ hcC))
  · -- (d): `X` Sylow of `M`, `X^g ⊆ M ⟹ g ∈ M`.
    rintro ⟨P, hPX⟩ g hg
    exact fusion_d_of_mem_sigma hp P (hPX ▸ hg)
  · -- (e): `X ⊆ M` (BG の暗黙前提), `C_G(X) ⊆ M`, `X^g ⊆ M ⟹ g ∈ M`, from (a).
    intro hXM hCM g hgM
    obtain ⟨m, hmM, c, hcC, hgmc⟩ := ha hXM g hgM
    rw [hgmc]
    exact M.mul_mem hmM (hCM hcC)

/-- **BG Theorem 10.2, step 1** (mmd L2721): `α(M) ⊆ σ(M)`. For `p ∈ α(M)` (so `r_p(M) ≥ 3`),
any Sylow `p`-subgroup `P` of `M` has `r(P̄) ≥ 3`, so by the Uniqueness Theorem (9.6) `P̄ ∈ 𝒰`;
since `P̄ ≤ M` (a coatom) and `N_G(P̄) < ⊤`, the unique maximal overgroup forces `N_G(P̄) ≤ M`,
i.e. `p ∈ σ(M)`. (Self-contained; needs no quotient machinery. Yields `Malpha M ≤ Msigma M`.) -/
theorem alpha_subset_sigma [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) : alpha M ⊆ sigma M := by
  intro p hp
  rw [mem_alpha_iff] at hp
  obtain ⟨hpf, hpr⟩ := hp
  obtain ⟨hp_prime, hp_dvd, -⟩ := Nat.mem_primeFactors.mp hpf
  have : Fact p.Prime := ⟨hp_prime⟩
  have hMc : IsCoatom M := mem_maximalSubgroups.mp hM
  have hM_lt : M < ⊤ := lt_top_iff_ne_top.mpr hMc.1
  obtain ⟨P⟩ : Nonempty (Sylow p ↥M) := inferInstance
  set Pbar : Subgroup G := (P : Subgroup ↥M).map M.subtype with hPbardef
  have hPbar_le_M : Pbar ≤ M := Subgroup.map_subtype_le _
  -- `r(P̄) ≥ 3`.
  have hPe := Subgroup.equivMapOfInjective (P : Subgroup ↥M) M.subtype M.subtype_injective
  have hrank3 : 3 ≤ rank ↥Pbar :=
    le_trans (le_trans (le_trans hpr (pRank_sylow_eq P).ge) (pRank_le_rank p))
      (rank_le_of_injective (f := hPe.toMonoidHom) hPe.injective)
  -- `P̄ ≠ ⊥` (its order is divisible by `p`).
  have hlt1 : 1 < Nat.card ↥Pbar := by
    rw [hPbardef, Subgroup.card_map_of_injective M.subtype_injective, P.card_eq_multiplicity]
    exact Nat.one_lt_pow
      (hp_prime.factorization_pos_of_dvd Nat.card_pos.ne' hp_dvd).ne' hp_prime.one_lt
  have hPbar_ne : Pbar ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hlt1
    exact lt_irrefl 1 hlt1
  -- `P̄ ∈ 𝒰` (Uniqueness Theorem), then `N_G(P̄) ≤ M`.
  have hPbar_lt : Pbar < ⊤ := lt_of_le_of_lt hPbar_le_M hM_lt
  have hPbarU : IsUniquelyMaximal Pbar :=
    OddOrder.BG.Ch2.S09.uniquenessTheorem hG hPbar_lt (by omega) (Or.inl hrank3)
  have hN_lt : Subgroup.normalizer (Pbar : Set G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rcases hG.simple.eq_bot_or_eq_top_of_normal Pbar
      (Subgroup.normalizer_eq_top_iff.mp htop) with hbot | htopP
    · exact hPbar_ne hbot
    · exact hMc.1 (top_le_iff.mp (htopP ▸ hPbar_le_M))
  obtain ⟨N, hNc, hNleN⟩ := (IsCoatomic.eq_top_or_exists_le_coatom _).resolve_left hN_lt.ne
  have hMN : M = N :=
    hPbarU.eq_of_isCoatom_of_le hMc hPbar_le_M hNc (Subgroup.le_normalizer.trans hNleN)
  rw [mem_sigma_iff]
  exact ⟨hpf, P, hNleN.trans hMN.ge⟩

/-- A Hall subgroup of `M`, viewed as a subgroup of `G`, remains Hall in `G` when
no prime in `π` divides the outer index `[G : M]`. -/
theorem isHallSubgroup_of_subgroupOf_isHall_of_forall_not_dvd_index [Finite G]
    {π : Set ℕ} {M A : Subgroup G} (hAM : A ≤ M)
    (hHall : Ch03.IsHallSubgroup π (A.subgroupOf M))
    (hidx : ∀ p : ℕ, p ∈ π → p.Prime → ¬ p ∣ M.index) :
    Ch03.IsHallSubgroup π A := by
  refine ⟨?_, ?_⟩
  · intro r hr
    have hrSub : r ∈ (Nat.card ↥(A.subgroupOf M)).primeFactors := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv]
    exact hHall.1 r hrSub
  · intro r hridx hrπ
    obtain ⟨hr_prime, hr_dvd, -⟩ := Nat.mem_primeFactors.mp hridx
    have htower : (A.subgroupOf M).index * M.index = A.index :=
      Subgroup.relIndex_mul_index hAM
    have hr_dvd_prod : r ∣ (A.subgroupOf M).index * M.index := by
      rw [htower]
      exact hr_dvd
    rcases hr_prime.dvd_mul.mp hr_dvd_prod with hr_dvd_rel | hr_dvd_M
    · exact hHall.2 r
        (Nat.mem_primeFactors.mpr ⟨hr_prime, hr_dvd_rel, Subgroup.index_ne_zero_of_finite⟩) hrπ
    · exact hidx r hrπ hr_prime hr_dvd_M

/-- **BG Theorem 10.2, Hall-`α` transport**: any `α(M)`-Hall subgroup of `M`,
viewed inside `G`, is already an `α(M)`-Hall subgroup of `G`. The point is that
`α(M) ⊆ σ(M)`, and σ-primes do not divide `[G : M]`. -/
theorem hallAlphaSubgroup_isHallInG [Finite G] (hG : IsMinimalSimpleOdd G)
    {M A : Subgroup G} (hM : M ∈ maximalSubgroups G) (hAM : A ≤ M)
    (hHall : Ch03.IsHallSubgroup (alpha M) (A.subgroupOf M)) :
    Ch03.IsHallSubgroup (alpha M) A := by
  refine isHallSubgroup_of_subgroupOf_isHall_of_forall_not_dvd_index hAM hHall ?_
  intro p hpα hp_prime
  have : Fact p.Prime := ⟨hp_prime⟩
  exact not_dvd_index_of_mem_sigma (alpha_subset_sigma hG hM hpα)

/-- Every `p`-subgroup of the Fitting subgroup lies in `O_p(G)`. The point is that
`F(G)` is nilpotent, hence its Sylow `p`-subgroup is characteristic in `F(G)` and
therefore normal in `G`. -/
theorem pSubgroup_le_opCore_of_le_fitting [Finite G] {p : ℕ} [Fact p.Prime]
    {W : Subgroup G} (hW : IsPGroup p ↥W) (hWF : W ≤ Ch01.fitting G) :
    W ≤ Ch01.opCore p G := by
  classical
  have hW'_pg : IsPGroup p ↥(W.subgroupOf (Ch01.fitting G)) :=
    hW.of_injective (Subgroup.subgroupOfEquivOfLe hWF).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hWF).injective
  obtain ⟨P, hWP⟩ := hW'_pg.exists_le_sylow
  have hPnorm : P.Normal := Ch01.Sylow.normal_of_isNilpotent P
  have : (P : Subgroup ↥(Ch01.fitting G)).Characteristic :=
    Sylow.characteristic_of_normal P hPnorm
  have : ((P : Subgroup ↥(Ch01.fitting G)).map (Ch01.fitting G).subtype).Normal :=
    inferInstance
  have hPmap_pg :
      IsPGroup p ↥((P : Subgroup ↥(Ch01.fitting G)).map (Ch01.fitting G).subtype) :=
    P.2.map _
  calc W = (W.subgroupOf (Ch01.fitting G)).map (Ch01.fitting G).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hWF).symm
    _ ≤ (P : Subgroup ↥(Ch01.fitting G)).map (Ch01.fitting G).subtype :=
        Subgroup.map_mono hWP
    _ ≤ Ch01.opCore p G := Ch01.normal_pgroup_le_opCore hPmap_pg

/-- Quotienting by `O_π(G)` makes the Fitting subgroup a `π'`-group. If a
`π`-prime divided `F(G/O_π(G))`, a nontrivial Sylow subgroup of that Fitting subgroup
would lie in the corresponding `O_p`, hence in the π-core of the quotient, contradicting
`O_π(G/O_π(G)) = 1`. -/
theorem fitting_quotient_oPiCore_isPiGroup_compl [Finite G] (π : Set ℕ) :
    Ch03.Subgroup.IsPiGroup πᶜ (Ch01.fitting (G ⧸ Ch03.oPiCore π G)) := by
  classical
  let Q : Type _ := G ⧸ Ch03.oPiCore π G
  intro p hpF hpπ
  have hp_prime : p.Prime := (Nat.mem_primeFactors.mp hpF).1
  have : Fact p.Prime := ⟨hp_prime⟩
  have hp_dvd_F : p ∣ Nat.card ↥(Ch01.fitting Q) :=
    (Nat.mem_primeFactors.mp hpF).2.1
  obtain ⟨P⟩ : Nonempty (Sylow p ↥(Ch01.fitting Q)) := inferInstance
  let Pbar : Subgroup Q := (P : Subgroup ↥(Ch01.fitting Q)).map (Ch01.fitting Q).subtype
  have hPbar_pg : IsPGroup p ↥Pbar := by
    exact P.2.map _
  have hPbar_le_F : Pbar ≤ Ch01.fitting Q := Subgroup.map_subtype_le _
  have hPbar_le_op : Pbar ≤ Ch01.opCore p Q :=
    pSubgroup_le_opCore_of_le_fitting hPbar_pg hPbar_le_F
  have hPbar_ne : Pbar ≠ ⊥ := by
    have hcard_gt : 1 < Nat.card ↥Pbar := by
      dsimp [Pbar]
      rw [Subgroup.card_map_of_injective (Ch01.fitting Q).subtype_injective,
        P.card_eq_multiplicity]
      exact Nat.one_lt_pow
        (hp_prime.factorization_pos_of_dvd Nat.card_pos.ne' hp_dvd_F).ne' hp_prime.one_lt
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard_gt
    exact lt_irrefl 1 hcard_gt
  have hop_pi : Ch03.Subgroup.IsPiGroup π (Ch01.opCore p Q) := by
    intro r hr
    have hr_singleton : r ∈ ({p} : Set ℕ) :=
      Ch1.S04.isPiGroup_singleton_of_isPGroup (Ch01.opCore_isPGroup p Q) r hr
    rwa [Set.mem_singleton_iff.mp hr_singleton]
  have hop_le_oPi : Ch01.opCore p Q ≤ Ch03.oPiCore π Q :=
    Ch03.Subgroup.IsPiGroup.le_oPiCore hop_pi
  have hoPi_bot : Ch03.oPiCore π Q = ⊥ := by
    change Ch03.oPiCore π (G ⧸ Ch03.oPiCore π G) = ⊥
    exact Ch03.oPiCore_quotient_self_eq_bot π
  have hPbar_bot : Pbar = ⊥ :=
    le_bot_iff.mp (hPbar_le_op.trans (hop_le_oPi.trans_eq hoPi_bot))
  exact hPbar_ne hPbar_bot

/-- Variant of `fitting_quotient_oPiCore_isPiGroup_compl` for a quotient whose
denominator is known to be `O_π(G)`. Keeping the denominator as a variable avoids
dependent rewriting through the normality instance of `QuotientGroup`. -/
theorem fitting_quotient_eq_oPiCore_isPiGroup_compl [Finite G] {π : Set ℕ}
    {N : Subgroup G} [N.Normal] (hN : N = Ch03.oPiCore π G) :
    Ch03.Subgroup.IsPiGroup πᶜ (Ch01.fitting (G ⧸ N)) := by
  subst N
  exact fitting_quotient_oPiCore_isPiGroup_compl (G := G) (π := π)

/-- **BG Theorem 10.2(d), Fitting quotient α′ part**: `F(M/M_α)` is an
`α(M)'`-group. This is the preceding general π-core quotient theorem with
`π = α(M)`, using `(M_α).subgroupOf M = O_{α(M)}(M)`. -/
theorem fitting_quotient_Malpha_isPiGroup_alphaCompl [Finite G] (M : Subgroup G) :
    Ch03.Subgroup.IsPiGroup (alpha M)ᶜ
      (Ch01.fitting (↥M ⧸ (Malpha M).subgroupOf M)) :=
  fitting_quotient_eq_oPiCore_isPiGroup_compl
    (G := ↥M) (π := alpha M) (N := (Malpha M).subgroupOf M) (Malpha_subgroupOf M)

/-- **BG Theorem 10.2(c), inclusion `M_α ⊆ M_σ`**: immediate from `α(M) ⊆ σ(M)`
(`alpha_subset_sigma`) and monotonicity of the `π`-core. -/
theorem Malpha_le_Msigma [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) : Malpha M ≤ Msigma M :=
  Subgroup.map_mono (Ch03.oPiCore_mono (alpha_subset_sigma hG hM) ↥M)

/-- A finite group is generated by all of its Sylow subgroups. This is the non-nilpotent
variant needed for `M_σ`: unlike the Fitting subgroup, `O_π(M)` is not known nilpotent at this
point of §10. -/
private lemma iSup_sylow_eq_top {M : Type*} [Group M] [Finite M] :
    (⨆ p : (Nat.card M).primeFactors, ⨆ P : Sylow p.val M, (P : Subgroup M)) = ⊤ := by
  classical
  set sup := ⨆ p : (Nat.card M).primeFactors, ⨆ P : Sylow p.val M, (P : Subgroup M)
    with hsup_def
  have h_sup_dvd : Nat.card sup ∣ Nat.card M := Subgroup.card_subgroup_dvd_card sup
  have h_pow_dvd : ∀ p ∈ (Nat.card M).primeFactors,
      p ^ (Nat.card M).factorization p ∣ Nat.card sup := by
    intro p hp
    have hp_prime : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    have hP_le : ((default : Sylow p M) : Subgroup M) ≤ sup := by
      rw [hsup_def]
      refine le_trans ?_ (le_iSup (fun q : (Nat.card M).primeFactors =>
        ⨆ Q : Sylow q.val M, (Q : Subgroup M)) ⟨p, hp⟩)
      exact le_iSup (fun Q : Sylow p M => (Q : Subgroup M)) default
    have h_dvd := Subgroup.card_dvd_of_le hP_le
    rwa [Sylow.card_eq_multiplicity] at h_dvd
  have h_factorization_le : ∀ p, (Nat.card M).factorization p ≤
      (Nat.card sup).factorization p := by
    intro p
    rcases Nat.eq_zero_or_pos ((Nat.card M).factorization p) with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · have hp_in : p ∈ (Nat.card M).primeFactors := by
        rw [← Nat.support_factorization]
        exact Finsupp.mem_support_iff.mpr (by omega)
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_in
      exact (hp_prime.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp
        (h_pow_dvd p hp_in)
  have h_factorization_le' : ∀ p, (Nat.card sup).factorization p ≤
      (Nat.card M).factorization p :=
    fun p => (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr h_sup_dvd p
  have h_eq : Nat.card sup = Nat.card M := by
    apply Nat.eq_of_factorization_eq Nat.card_pos.ne' Nat.card_pos.ne'
    intro p
    exact le_antisymm (h_factorization_le' p) (h_factorization_le p)
  exact Subgroup.eq_top_of_card_eq sup h_eq

/-- If every Sylow subgroup of a finite ambient subgroup `K` maps into `X`, then `K ≤ X`. -/
private theorem le_of_sylow_le [Finite G] {K X : Subgroup G}
    (hSyl : ∀ r : (Nat.card ↥K).primeFactors, ∀ P : Sylow r.val ↥K,
      ((P : Subgroup ↥K).map K.subtype : Subgroup G) ≤ X) :
    K ≤ X := by
  have htop_map : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← htop_map, ← iSup_sylow_eq_top, Subgroup.map_iSup]
  exact iSup_le fun r => by
    rw [Subgroup.map_iSup]
    exact iSup_le (hSyl r)

/-- **σ basic fact, every Sylow** (mmd L2655): for `p ∈ σ(M)` and *any* Sylow `p`-subgroup `P` of
`M`, its image `P̄` is a Sylow `p`-subgroup of `G`. Same argument as `exists_sylow_le_of_mem_sigma`
but for an arbitrary Sylow `P`, using `normalizer_sylow_map_le_of_mem_sigma`. -/
theorem isSylow_sylowMap_of_mem_sigma [Finite G]
    {M : Subgroup G} {p : ℕ} [Fact p.Prime] (hp : p ∈ sigma M) (P : Sylow p ↥M) :
    ∃ S : Sylow p G, (S : Subgroup G) = (P : Subgroup ↥M).map M.subtype := by
  set Pbar : Subgroup G := (P : Subgroup ↥M).map M.subtype with hPbar
  have hPbar_pg : IsPGroup p ↥Pbar :=
    P.2.of_equiv (Subgroup.equivMapOfInjective _ _ M.subtype_injective)
  have hP : Subgroup.normalizer (Pbar : Set G) ≤ M := normalizer_sylow_map_le_of_mem_sigma hp P
  have hPbar_subOf : Pbar.subgroupOf M = (P : Subgroup ↥M) := by
    rw [hPbar, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  obtain ⟨S, hPS⟩ := hPbar_pg.exists_le_sylow
  refine ⟨S, ?_⟩
  by_contra hne
  have hlt : Pbar < (S : Subgroup G) := lt_of_le_of_ne hPS (Ne.symm hne)
  have hgrow : Pbar < Subgroup.normalizer Pbar ⊓ (S : Subgroup G) :=
    lt_inf_normalizer_of_lt_of_isPGroup hlt S.2
  set Y : Subgroup G := Subgroup.normalizer Pbar ⊓ (S : Subgroup G) with hY
  have hYM : Y ≤ M := le_trans inf_le_left hP
  have hYpg : IsPGroup p ↥Y :=
    S.2.of_injective (Subgroup.inclusion inf_le_right) (Subgroup.inclusion_injective _)
  have hPle : (P : Subgroup ↥M) ≤ Y.subgroupOf M :=
    hPbar_subOf ▸ Subgroup.comap_mono (f := M.subtype) hgrow.le
  have hYsubM_pg : IsPGroup p ↥(Y.subgroupOf M) :=
    hYpg.of_equiv (Subgroup.subgroupOfEquivOfLe hYM).symm
  have hYeq : Y.subgroupOf M = (P : Subgroup ↥M) := P.3 hYsubM_pg hPle
  have hYP : Y = Pbar := by
    have := congrArg (Subgroup.map M.subtype) hYeq
    rwa [Subgroup.map_subgroupOf_eq_of_le hYM, ← hPbar] at this
  exact absurd hYP hgrow.ne'

/-- **Public packaging (for the §10 leaves)**: for `p ∈ σ(M)` there is a Sylow `p`-subgroup
`S` of `G` lying in `M` whose `G`-normalizer also lies in `M`. Combines the per-Sylow
`isSylow_sylowMap_of_mem_sigma` and `normalizer_sylow_map_le_of_mem_sigma`; exposed so the
local-lemma leaf `S10_LocalLemmas` can build the common Sylow used in BG Lemma 10.12. -/
theorem exists_sylow_le_normalizer_le_of_mem_sigma [Finite G]
    {M : Subgroup G} {p : ℕ} [Fact p.Prime] (hp : p ∈ sigma M) :
    ∃ S : Sylow p G,
      (S : Subgroup G) ≤ M ∧ Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ M := by
  obtain ⟨P, -⟩ := hp.2
  obtain ⟨S, hS⟩ := isSylow_sylowMap_of_mem_sigma hp P
  refine ⟨S, ?_, ?_⟩
  · rw [hS]; exact Subgroup.map_subtype_le _
  · rw [hS]; exact normalizer_sylow_map_le_of_mem_sigma hp P

/-- **BG Theorem 10.2, step 2 (per-Sylow)** (mmd L2725-2731): for `p ∈ σ(M)` and a Sylow
`p`-subgroup `P` of `M`, the image `P̄ ≤ M'`. `P̄ ∈ Syl_p(G)` (σ) and `G' = G`, so the Focal
Subgroup Theorem gives `P̄.focalSubgroup = G' ⊓ P̄ = P̄`; Theorem 10.1(a) (with `X = ⟨x⟩`) shows
`M` controls `G`-fusion in `P̄`, so the focal subgroup computed inside `M` agrees, yielding
`M' ⊓ P̄ = P̄`, i.e. `P̄ ≤ M'`. -/
theorem sylow_le_derived_of_mem_sigma [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ sigma M) (P : Sylow p ↥M) :
    (P : Subgroup ↥M).map M.subtype ≤ derivedInG M := by
  set Pbar : Subgroup G := (P : Subgroup ↥M).map M.subtype with hPbar
  have hPbar_le_M : Pbar ≤ M := Subgroup.map_subtype_le _
  have hPbar_pg : IsPGroup p ↥Pbar :=
    P.2.of_equiv (Subgroup.equivMapOfInjective _ _ M.subtype_injective)
  have hPbar_subOf : Pbar.subgroupOf M = (P : Subgroup ↥M) := by
    rw [hPbar, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  -- `M` controls `G`-fusion in `P̄` (Theorem 10.1(a) applied to `⟨x⟩`).
  have hctrl : M.ControlsFusionIn Pbar := by
    intro x y hxP hyP hxy
    obtain ⟨g, hg⟩ := hxy
    by_cases hx1 : x = 1
    · refine ⟨1, M.one_mem, ?_⟩
      have hy1 : y = 1 := by rw [hx1, mul_one, mul_inv_cancel] at hg; exact hg.symm
      rw [hx1, hy1]; group
    · set X := Subgroup.zpowers x with hXdef
      have hxX : x ∈ X := Subgroup.mem_zpowers x
      have hXleP : X ≤ Pbar := Subgroup.zpowers_le.mpr hxP
      have hXne : X ≠ ⊥ := by rw [hXdef]; exact mt Subgroup.zpowers_eq_bot.mp hx1
      have hXp : IsPGroup p ↥X :=
        hPbar_pg.of_injective (Subgroup.inclusion hXleP) (Subgroup.inclusion_injective _)
      have hXM : X ≤ M := hXleP.trans hPbar_le_M
      have hconjX : MulAut.conj g • X = Subgroup.zpowers y := by
        have hgx : (MulAut.conj g : G →* G) x = y := by
          simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hg
        rw [hXdef, mulAut_smul_eq_map, MonoidHom.map_zpowers, hgx]
      have hconjg : MulAut.conj g • X ≤ M := by
        rw [hconjX]; exact Subgroup.zpowers_le.mpr (hPbar_le_M hyP)
      obtain ⟨m, hmM, c, hcC, hgmc⟩ :=
        (fusion_control_of_mem_sigma hG hM hp hXne hXp).1 hXM g hconjg
      refine ⟨m, hmM, ?_⟩
      have hxc : x * c = c * x := Subgroup.mem_centralizer_iff.mp hcC x hxX
      have hcx : c * x * c⁻¹ = x := by rw [← hxc]; group
      calc m * x * m⁻¹ = m * (c * x * c⁻¹) * m⁻¹ := by rw [hcx]
        _ = m * c * x * (m * c)⁻¹ := by group
        _ = g * x * g⁻¹ := by rw [← hgmc]
        _ = y := hg
  -- focal subgroups agree (`M`-focal maps to `G`-focal).
  have hfa := Subgroup.focalSubgroup_subgroupOf_map_eq_of_controlsFusionIn hPbar_le_M hctrl
  -- `P̄.focalSubgroup = P̄` (Focal Thm for `P̄ ∈ Syl_p(G)` + `G' = G`).
  obtain ⟨S, hS⟩ := isSylow_sylowMap_of_mem_sigma hp P
  have hPbar_focal : Pbar.focalSubgroup = Pbar := by
    have h := Subgroup.commutator_inf_eq_focalSubgroup S
    rw [hS] at h
    rw [← h, hG.commutator_eq_top, top_inf_eq]
  -- `(P̄.subgroupOf M).focalSubgroup = M' ⊓ P̄` (Focal Thm inside `↥M`).
  have hP_focal : (Pbar.subgroupOf M).focalSubgroup = commutator ↥M ⊓ (P : Subgroup ↥M) := by
    rw [hPbar_subOf, ← Subgroup.commutator_inf_eq_focalSubgroup P]
  rw [hP_focal, hPbar_focal, Subgroup.map_inf _ _ M.subtype M.subtype_injective] at hfa
  exact inf_eq_right.mp hfa

/-- **BG Theorem 10.2, step 2** (mmd L2725-2731): any Hall `σ(M)`-subgroup
of `M`, viewed in `G`, lies in `M'`. This is the Hall-subgroup version of the per-Sylow
focal-subgroup argument. -/
theorem hallSigmaSubgroup_le_derived [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {S : Subgroup G}
    (hSM : S ≤ M) (hHall : Ch03.IsHallSubgroup (sigma M) (S.subgroupOf M)) :
    S ≤ derivedInG M := by
  refine le_of_sylow_le ?_
  intro r P
  have : Fact (r : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors r.property⟩
  set Pbar : Subgroup G := (P : Subgroup ↥S).map S.subtype with hPbar
  have hPbar_le_S : Pbar ≤ S := Subgroup.map_subtype_le _
  have hPbar_le_M : Pbar ≤ M := hPbar_le_S.trans hSM
  have hPbar_pg : IsPGroup (r : ℕ) ↥Pbar := by
    rw [hPbar]
    exact P.2.of_equiv (Subgroup.equivMapOfInjective _ _ S.subtype_injective)
  have hPsub_pg : IsPGroup (r : ℕ) ↥(Pbar.subgroupOf M) :=
    hPbar_pg.of_equiv (Subgroup.subgroupOfEquivOfLe hPbar_le_M).symm
  obtain ⟨Q, hPQ⟩ := hPsub_pg.exists_le_sylow
  have hr_sub : (r : ℕ) ∈ (Nat.card ↥(S.subgroupOf M)).primeFactors := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv]
    exact r.property
  have hr_sigma : (r : ℕ) ∈ sigma M := hHall.1 (r : ℕ) hr_sub
  calc
    ((P : Subgroup ↥S).map S.subtype : Subgroup G) = Pbar := hPbar.symm
    _ = (Pbar.subgroupOf M).map M.subtype := by
      rw [Subgroup.map_subgroupOf_eq_of_le hPbar_le_M]
    _ ≤ (Q : Subgroup ↥M).map M.subtype := Subgroup.map_mono hPQ
    _ ≤ derivedInG M := sylow_le_derived_of_mem_sigma hG hM hr_sigma Q

/-- **BG Theorem 10.2(c), inclusion `M_σ ⊆ M'`**: each Sylow subgroup of `M_σ`
has prime in `σ(M)`, hence lies in a Sylow subgroup of `M`; `sylow_le_derived_of_mem_sigma`
puts that Sylow subgroup inside `M'`, and the finite Sylow-generation helper assembles the
containment. -/
theorem Msigma_le_derived [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) : Msigma M ≤ derivedInG M := by
  refine le_of_sylow_le ?_
  intro r P
  have : Fact (r : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors r.property⟩
  set Pbar : Subgroup G := (P : Subgroup ↥(Msigma M)).map (Msigma M).subtype with hPbar
  have hPbar_le_Msigma : Pbar ≤ Msigma M := Subgroup.map_subtype_le _
  have hPbar_le_M : Pbar ≤ M := hPbar_le_Msigma.trans (Msigma_le M)
  have hPbar_pg : IsPGroup (r : ℕ) ↥Pbar := by
    rw [hPbar]
    exact P.2.of_equiv
      (Subgroup.equivMapOfInjective _ _ (Msigma M).subtype_injective)
  have hPsub_pg : IsPGroup (r : ℕ) ↥(Pbar.subgroupOf M) :=
    hPbar_pg.of_equiv (Subgroup.subgroupOfEquivOfLe hPbar_le_M).symm
  obtain ⟨Q, hPQ⟩ := hPsub_pg.exists_le_sylow
  have hr_sigma : (r : ℕ) ∈ sigma M := Msigma_isPiGroup M (r : ℕ) r.property
  calc
    ((P : Subgroup ↥(Msigma M)).map (Msigma M).subtype : Subgroup G) = Pbar := hPbar.symm
    _ = (Pbar.subgroupOf M).map M.subtype := by
      rw [Subgroup.map_subgroupOf_eq_of_le hPbar_le_M]
    _ ≤ (Q : Subgroup ↥M).map M.subtype := Subgroup.map_mono hPQ
    _ ≤ derivedInG M := sylow_le_derived_of_mem_sigma hG hM hr_sigma Q

end OddOrder.BG.Ch3.S10


