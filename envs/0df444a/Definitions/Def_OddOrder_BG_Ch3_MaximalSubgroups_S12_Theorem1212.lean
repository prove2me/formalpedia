-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem1212
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem1212
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:01:34.811248+00:00
-- url     : https://prove2.me/theorems/2f545fba-965b-4713-ab1c-3843c4331b21
-- title:
--   BG §12: Theorem 12.12, Frobenius factorization in the regular case
-- statement:
--   Formalizes Theorem 12.12 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §12: under the $E$-setup, if every $(\tau_1(M)\cup\tau_3(M))$-element $e\in E^\#$ satisfies $C_{M_\sigma}(e)=1$ (regular), then (a) $E$ contains an abelian normal $A_0$ with $C_E(x)\subseteq A_0$ for $x\in M_\sigma^\#$, and (b) $E$ contains a complement $E_0$ of the same exponent with $M_\sigma E_0$ a Frobenius group with kernel $M_\sigma$. The file also formalizes Proposition 3.9 (coprime fixed-point-free $p$-action implies cyclic) and starts the three cases.
--
--   The main declaration: `FrobFactConclusion`.
--
--   The bundle also proves 10 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S12_Theorem1212.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S12_Theorem1212.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Lemma1211
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S01b_Prop116

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.Isaacs.Ch06

open scoped Pointwise

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- The two-part conclusion of **Theorem 12.12** for a maximal `M` with `σ`-complement `E`:
(a) `E` has an abelian normal subgroup `A₀` swallowing every `C_E(x)` (`x ∈ M_σ#`), and
(b) `E` has a same-exponent subgroup `E₀` with `M_σ E₀` Frobenius of kernel `M_σ`. -/
def FrobFactConclusion (M E : Subgroup G) : Prop :=
  (∃ A₀ : Subgroup G, A₀ ≤ E ∧ IsMulCommutative ↥A₀ ∧
    E ≤ Subgroup.normalizer ((A₀ : Subgroup G) : Set G) ∧
    ∀ x ∈ S10.Msigma M, x ≠ 1 → E ⊓ Subgroup.centralizer ({x} : Set G) ≤ A₀) ∧
  (∃ E₀ : Subgroup G, E₀ ≤ E ∧ Monoid.exponent ↥E₀ = Monoid.exponent ↥E ∧
    Ch06.IsFrobeniusGroup ↥(S10.Msigma M ⊔ E₀)
      ((S10.Msigma M).subgroupOf (S10.Msigma M ⊔ E₀))
      (E₀.subgroupOf (S10.Msigma M ⊔ E₀)))

/-- **Proposition 3.9** (Gorenstein 5.3.14): a finite `p`-group `R` (`p` odd) acting
coprimely and fixed-point-freely on a nontrivial finite group `H` is cyclic.

If `R` were not cyclic it would contain an elementary abelian subgroup `B` of order `p²`
(`exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic`); `B` is abelian and not cyclic,
so Isaacs 6.21 (`nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'`) gives
`⟨ C_H(b) | b ∈ B^# ⟩ = H`. But the action is fixed-point-free, so each `C_H(b) = 1`,
forcing `H = 1`, a contradiction. The `12.12` application is the conjugation action of
`Q/Q₀` on a Sylow subgroup `S`, where `Q₀ = C_Q(S)` is the kernel. -/
theorem isCyclic_of_coprime_fpf_pgroup_action
    {R H : Type*} [Group R] [Group H] [Finite R] [Finite H] {p : ℕ} [Fact p.Prime]
    [Nontrivial H] (hR : IsPGroup p R) (hp_odd : Odd p)
    (hcop : Nat.Coprime (Nat.card R) (Nat.card H)) (φ : R →* MulAut H)
    (hfpf : ∀ a : R, a ≠ 1 → actionFixedBy φ a = ⊥) :
    IsCyclic R := by
  by_contra hnc
  obtain ⟨B, hB_elem, hB_card⟩ :=
    OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic hR hp_odd hnc
  have : IsMulCommutative ↥B := ⟨⟨hB_elem.comm⟩⟩
  have hBnc : ¬ IsCyclic ↥B :=
    OddOrder.GroupTheory.IsElementaryAbelian.not_isCyclic_of_card_prime_sq Fact.out hB_elem hB_card
  have hcop' : Nat.Coprime (Nat.card ↥B) (Nat.card H) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card B) hcop
  have htop : nontrivialActionFixedByClosure (φ.comp B.subtype) = ⊤ :=
    OddOrder.BG.Ch1.S01.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'
      (φ.comp B.subtype) hcop' hBnc
  have hbot : nontrivialActionFixedByClosure (φ.comp B.subtype) ≤ ⊥ := by
    rw [nontrivialActionFixedByClosure_le_iff]
    intro b hb
    have hb' : B.subtype b ≠ 1 :=
      fun h => hb (B.subtype_injective (h.trans (map_one B.subtype).symm))
    exact (hfpf (B.subtype b) hb').le
  rw [htop, top_le_iff] at hbot
  obtain ⟨x, hx⟩ := exists_ne (1 : H)
  exact hx (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_top x))

/-- If `E₀ ≤ E` (finite) and, for every prime `r`, some element of `E₀` attains the `r`-part of
`exp(E)` (i.e. `v_r(exp E) ≤ v_r(ord g₀)` for some `g₀ ∈ E₀`), then `exp(E₀) = exp(E)`.

`exp(E₀) ∣ exp(E)` holds for any subgroup; the converse is checked prime-by-prime via
`Nat.factorization`, using that the `r`-part of `exp(E)` is realized by an element
(`Nat.Prime.exists_orderOf_eq_pow_factorization_exponent`) which the hypothesis lifts to `E₀`. -/
theorem exponent_eq_of_forall_factorization_le [Finite G] {E E₀ : Subgroup G}
    (hle : E₀ ≤ E)
    (hattain : ∀ r : ℕ, r.Prime →
      ∃ g₀ : ↥E₀, (Monoid.exponent ↥E).factorization r ≤ (orderOf g₀).factorization r) :
    Monoid.exponent ↥E₀ = Monoid.exponent ↥E := by
  have hExpE_ne : Monoid.exponent ↥E ≠ 0 := fun hz =>
    (Nat.card_pos (α := ↥E)).ne' (Nat.eq_zero_of_zero_dvd (hz ▸ Group.exponent_dvd_nat_card))
  have hExpE₀_ne : Monoid.exponent ↥E₀ ≠ 0 := fun hz =>
    (Nat.card_pos (α := ↥E₀)).ne' (Nat.eq_zero_of_zero_dvd (hz ▸ Group.exponent_dvd_nat_card))
  refine dvd_antisymm
    (Monoid.exponent_dvd_of_monoidHom (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle))
    ?_
  rw [← Nat.factorization_le_iff_dvd hExpE_ne hExpE₀_ne, Finsupp.le_def]
  intro r
  by_cases hr : r.Prime
  · obtain ⟨g₀, hg₀⟩ := hattain r hr
    refine hg₀.trans ?_
    exact (Finsupp.le_def.mp ((Nat.factorization_le_iff_dvd (orderOf_pos g₀).ne'
      hExpE₀_ne).mpr (Monoid.order_dvd_exponent g₀))) r
  · rw [Nat.factorization_eq_zero_of_not_prime _ hr]
    exact Nat.zero_le _

/-- **Frobenius packaging** for Theorem 12.12(b): if `E₀ ≤ E` is a nontrivial subgroup acting
regularly on `M_σ` (`M_σ ⊓ C_G(a) = 1` for every `a ∈ E₀#`), then `M_σ E₀` is a Frobenius group
with Frobenius kernel `M_σ` and complement `E₀`. `M_σ ⊴ M ⊇ M_σ E₀` gives normality and the
complement relation (`M_σ ⊓ E₀ = 1` from the `SubgroupESetup`), `M_σ ≠ 1` by Theorem 10.2(e),
and the regularity is precisely the Frobenius condition `a n a⁻¹ ≠ n`. -/
theorem isFrobeniusGroup_of_regular [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {E₀ : Subgroup G} (hE₀E : E₀ ≤ E) (hE₀ne : E₀ ≠ ⊥)
    (hreg₀ : ∀ a ∈ E₀, a ≠ 1 → S10.Msigma M ⊓ Subgroup.centralizer ({a} : Set G) = ⊥) :
    Ch06.IsFrobeniusGroup ↥(S10.Msigma M ⊔ E₀)
      ((S10.Msigma M).subgroupOf (S10.Msigma M ⊔ E₀))
      (E₀.subgroupOf (S10.Msigma M ⊔ E₀)) := by
  have hMσne : S10.Msigma M ≠ ⊥ := S10.Msigma_ne_bot hG h.mem_maximal
  -- `M_σ E₀ ≤ M ≤ N_G(M_σ)`, so `M_σ` is normal in the ambient `M_σ E₀`.
  have hMσM_normal : ((S10.Msigma M).subgroupOf M).Normal := by
    rw [S10.Msigma_subgroupOf]; infer_instance
  have hM_le_N : M ≤ Subgroup.normalizer (S10.Msigma M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (S10.Msigma_le M)).mp hMσM_normal
  have hsup_le_M : S10.Msigma M ⊔ E₀ ≤ M := sup_le (S10.Msigma_le M) (hE₀E.trans h.E_le)
  have hsup_le_N : S10.Msigma M ⊔ E₀ ≤ Subgroup.normalizer (S10.Msigma M : Set G) :=
    hsup_le_M.trans hM_le_N
  have hinfbot : S10.Msigma M ⊓ E₀ = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_left (S10.Msigma M) hE₀E).trans h.E_compl_inf.le)
  refine
    { isNormal := (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hsup_le_N
      isComplement := ?_
      ne_bot_kernel := ?_
      ne_bot_complement := ?_
      conj_frobenius := ?_ }
  · -- `M_σ` and `E₀` are complements inside `↥(M_σ E₀)`.
    have : ((S10.Msigma M).subgroupOf (S10.Msigma M ⊔ E₀)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hsup_le_N
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [disjoint_iff]
      have hinf : (S10.Msigma M).subgroupOf (S10.Msigma M ⊔ E₀) ⊓
          E₀.subgroupOf (S10.Msigma M ⊔ E₀)
          = (S10.Msigma M ⊓ E₀).subgroupOf (S10.Msigma M ⊔ E₀) := rfl
      rw [hinf, hinfbot, Subgroup.bot_subgroupOf]
    · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
        Subgroup.subgroupOf_self, Subgroup.coe_top]
  · rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hMσne (hd.eq_bot_of_le le_sup_left)
  · rw [ne_eq, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hE₀ne (hd.eq_bot_of_le le_sup_right)
  · -- the regularity `M_σ ⊓ C_G(a) = 1` is the Frobenius condition.
    intro a ha hane n hn hne hfix
    have ha_mem : (a : G) ∈ E₀ := Subgroup.mem_subgroupOf.mp ha
    have hn_mem : (n : G) ∈ S10.Msigma M := Subgroup.mem_subgroupOf.mp hn
    have ha_ne : (a : G) ≠ 1 := fun hc => hane (by exact_mod_cast hc)
    have hfixG : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) := by
      have := Subtype.ext_iff.mp hfix
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
    have hncent : (n : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      rw [Set.mem_singleton_iff] at hm; subst hm
      exact mul_inv_eq_iff_eq_mul.mp hfixG
    have hmem : (n : G) ∈ S10.Msigma M ⊓ Subgroup.centralizer ({(a : G)} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hn_mem, hncent⟩
    rw [hreg₀ (a : G) ha_mem ha_ne, Subgroup.mem_bot] at hmem
    exact hne (by exact_mod_cast hmem)

/-- **Theorem 12.12, case `E = E₁E₃`** (i.e. every element of `E#` is a `(τ₁∪τ₃)`-element, so the
regularity hypothesis applies to all of `E`): take `A₀ = 1` and `E₀ = E`. Part (a) is immediate
(`C_E(x) = 1` for `x ∈ M_σ#`: any `1 ≠ e ∈ E ⊓ C_G(x)` would put `x ∈ M_σ ⊓ C_G(e) = 1`), and
part (b) is the Frobenius packaging with `E₀ = E`. -/
theorem frobFact_of_regular_all [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) (hEne : E ≠ ⊥)
    (hregAll : ∀ e ∈ E, e ≠ 1 → S10.Msigma M ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) :
    FrobFactConclusion M E := by
  refine ⟨⟨⊥, bot_le, ?_, ?_, ?_⟩,
    ⟨E, le_rfl, rfl, isFrobeniusGroup_of_regular hG h le_rfl hEne hregAll⟩⟩
  · exact IsMulCommutative.of_comm (fun a b => Subsingleton.elim _ _)
  · -- `E ≤ N_G(1) = G`.
    intro a _
    rw [Subgroup.mem_normalizer_iff]
    intro z
    simp only [Subgroup.mem_bot]
    constructor
    · rintro rfl; group
    · intro hz
      have : z = a⁻¹ * 1 * a := by rw [← (hz : a * z * a⁻¹ = 1)]; group
      simpa using this
  · -- `C_E(x) = 1`: a nontrivial `e ∈ E ⊓ C_G(x)` forces `x ∈ M_σ ⊓ C_G(e) = 1`.
    intro x hx hxne e he
    rw [Subgroup.mem_bot]
    by_contra hene
    have heE := (Subgroup.mem_inf.mp he).1
    have heC := (Subgroup.mem_inf.mp he).2
    have hxCe : x ∈ Subgroup.centralizer ({e} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      rw [Set.mem_singleton_iff] at hm; subst hm
      exact (Subgroup.mem_centralizer_iff.mp heC x (Set.mem_singleton x)).symm
    have hmem : x ∈ S10.Msigma M ⊓ Subgroup.centralizer ({e} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hx, hxCe⟩
    rw [hregAll e heE hene, Subgroup.mem_bot] at hmem
    exact hxne hmem

/-- **Dedekind/modular identity** for a subgroup `H` sandwiched `A₀ ≤ H ≤ A₀ ⊔ E₀` when
`E₀` normalizes `A₀`: `H = A₀ ⊔ (H ⊓ E₀)`. We write `h ∈ H ≤ A₀ ⊔ E₀ = E₀·A₀` (set product,
valid as `E₀ ≤ N_G(A₀)`) as `h = e·a`; then `e = h·a⁻¹ ∈ H` (since `A₀ ≤ H`) lands in `H ⊓ E₀`,
so `h = e·a ∈ (H ⊓ E₀) ⊔ A₀`. -/
theorem eq_sup_inf_of_le_normalizer {A₀ E₀ H : Subgroup G}
    (hN : E₀ ≤ Subgroup.normalizer (A₀ : Set G)) (hA₀H : A₀ ≤ H) (hHsup : H ≤ A₀ ⊔ E₀) :
    H = A₀ ⊔ (H ⊓ E₀) := by
  refine le_antisymm (fun h hh => ?_) (sup_le hA₀H inf_le_left)
  have hmem : (h : G) ∈ (↑E₀ * ↑A₀ : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right E₀ A₀ hN, SetLike.mem_coe, sup_comm]
    exact hHsup hh
  obtain ⟨e, he, a, ha, hea⟩ := Set.mem_mul.mp hmem
  have heH : e ∈ H := by
    have hrw : e = h * a⁻¹ := by rw [← hea]; group
    rw [hrw]; exact H.mul_mem hh (H.inv_mem (hA₀H ha))
  rw [← hea]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨heH, he⟩))
    (Subgroup.mem_sup_left ha)

/-- **Centralizer-disjointness is symmetric** between subgroups `N`, `K`: if no nontrivial
element of `K` commutes with any nontrivial element of `N` (`K ⊓ C_G(x) = 1` for all `x ∈ N#`),
the same holds with the roles swapped (`N ⊓ C_G(a) = 1` for all `a ∈ K#`). -/
theorem inf_centralizer_bot_symm {N K : Subgroup G}
    (h : ∀ x ∈ N, x ≠ 1 → K ⊓ Subgroup.centralizer ({x} : Set G) = ⊥) :
    ∀ a ∈ K, a ≠ 1 → N ⊓ Subgroup.centralizer ({a} : Set G) = ⊥ := by
  intro a ha ha1
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxN, hxC⟩ := hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have haCx : a ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    rw [Set.mem_singleton_iff] at hm; subst hm
    exact (Subgroup.mem_centralizer_iff.mp hxC a (Set.mem_singleton a)).symm
  have hmem : a ∈ K ⊓ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_inf.mpr ⟨ha, haCx⟩
  rw [h x hxN hx1, Subgroup.mem_bot] at hmem
  exact ha1 hmem

/-- **`r ≠ p` exponent realisation in the complement.** If `A₀ ⊴ E` (here as the normal
`A₀.subgroupOf E`) with complement `E₀` (`(E₀.subgroupOf E).IsComplement' (A₀.subgroupOf E)`),
then for a prime `r` coprime to `|A₀|`, the full `r`-part of `exp(E)` is realised inside `E₀`:
a maximal-`r`-order element `g : ↥E` has `⟨g⟩ ⊓ A₀.subgroupOf E = 1` (coprime orders), so its
image under `↥E ⧸ A₀.subgroupOf E ≃* ↥(E₀.subgroupOf E) ≃* ↥E₀` keeps order `r^{ν_r(exp E)}`. -/
theorem exists_orderOf_eq_rpow_in_complement [Finite G] {E E₀ A₀ : Subgroup G}
    (hA₀E : A₀ ≤ E) (hE₀E : E₀ ≤ E) [(A₀.subgroupOf E).Normal]
    (hcompl : (E₀.subgroupOf E).IsComplement' (A₀.subgroupOf E))
    {r : ℕ} (hr : r.Prime) (hcop : Nat.Coprime r (Nat.card ↥A₀)) :
    ∃ g₀ : ↥E₀, orderOf g₀ = r ^ (Monoid.exponent ↥E).factorization r := by
  have := Fact.mk hr
  obtain ⟨g, hg⟩ := hr.exists_orderOf_eq_pow_factorization_exponent ↥E
  have hcardA₀sub : Nat.card ↥(A₀.subgroupOf E) = Nat.card ↥A₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀E).toEquiv
  have hg_inf : Subgroup.zpowers g ⊓ A₀.subgroupOf E = ⊥ := by
    apply Disjoint.eq_bot
    apply Subgroup.disjoint_of_coprime_natCard
    rw [Nat.card_zpowers, hg, hcardA₀sub]
    exact hcop.pow_left _
  -- the quotient map injects `⟨g⟩` (coprime to `A₀`), so it preserves the order of `g`.
  have hord_mk : orderOf (QuotientGroup.mk' (A₀.subgroupOf E) g) = orderOf g := by
    refine Nat.dvd_antisymm (orderOf_map_dvd (QuotientGroup.mk' (A₀.subgroupOf E)) g)
      (orderOf_dvd_of_pow_eq_one ?_)
    have hk : (QuotientGroup.mk' (A₀.subgroupOf E))
        (g ^ orderOf (QuotientGroup.mk' (A₀.subgroupOf E) g)) = 1 := by
      rw [map_pow, pow_orderOf_eq_one]
    have hmemker : g ^ orderOf (QuotientGroup.mk' (A₀.subgroupOf E) g) ∈ A₀.subgroupOf E := by
      have hker := MonoidHom.mem_ker.mpr hk
      rwa [QuotientGroup.ker_mk'] at hker
    have hmem : g ^ orderOf (QuotientGroup.mk' (A₀.subgroupOf E) g)
        ∈ Subgroup.zpowers g ⊓ A₀.subgroupOf E :=
      Subgroup.mem_inf.mpr ⟨pow_mem (Subgroup.mem_zpowers g) _, hmemker⟩
    rwa [hg_inf, Subgroup.mem_bot] at hmem
  refine ⟨(Subgroup.subgroupOfEquivOfLe hE₀E)
    (hcompl.QuotientMulEquiv (QuotientGroup.mk' (A₀.subgroupOf E) g)), ?_⟩
  exact (MulEquiv.orderOf_eq _ _).trans
    ((MulEquiv.orderOf_eq _ _).trans (hord_mk.trans hg))

/-- **A Sylow `p`-subgroup carries the full `p`-part of the exponent.** If `E₂ ≤ E` with
`E₂.subgroupOf E` a Sylow `p`-subgroup of `↥E` (`|E₂| = p^{ν_p|E|}`), then
`ν_p(exp E) ≤ ν_p(exp E₂)`: a maximal `p`-power-order element of `↥E` is conjugate into `E₂`. -/
theorem factorization_exponent_le_of_sylow [Finite G] {E E₂ : Subgroup G} {p : ℕ}
    [Fact p.Prime] (hE₂E : E₂ ≤ E)
    (hcard : Nat.card ↥(E₂.subgroupOf E) = p ^ (Nat.card ↥E).factorization p) :
    (Monoid.exponent ↥E).factorization p ≤ (Monoid.exponent ↥E₂).factorization p := by
  obtain ⟨g, hg⟩ := (Fact.out : p.Prime).exists_orderOf_eq_pow_factorization_exponent ↥E
  set SE₂ : Sylow p ↥E := Sylow.ofCard (E₂.subgroupOf E) hcard with hSE₂
  have hgpg : IsPGroup p ↥(Subgroup.zpowers g) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hg])
  obtain ⟨Q, hgQ⟩ := hgpg.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (↥E) Q SE₂
  have hmem : (MulAut.conj x) g ∈ E₂.subgroupOf E := by
    have hgQ' : g ∈ (Q : Subgroup ↥E) := hgQ (Subgroup.mem_zpowers g)
    have hconj : (MulAut.conj x) g ∈ (SE₂ : Subgroup ↥E) := by
      rw [← hx, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul g (MulAut.conj x) (Q : Subgroup ↥E) hgQ'
    rwa [hSE₂, Sylow.coe_ofCard] at hconj
  set y : ↥(E₂.subgroupOf E) := ⟨(MulAut.conj x) g, hmem⟩ with hy
  have hord : orderOf ((Subgroup.subgroupOfEquivOfLe hE₂E) y)
      = p ^ (Monoid.exponent ↥E).factorization p := by
    have e1 := MulEquiv.orderOf_eq (Subgroup.subgroupOfEquivOfLe hE₂E) y
    have e2 := (orderOf_injective (E₂.subgroupOf E).subtype (Subgroup.subtype_injective _) y).symm
    have e3 := MulEquiv.orderOf_eq (MulAut.conj x) g
    exact e1.trans (e2.trans (e3.trans hg))
  have hexp_ne : Monoid.exponent ↥E₂ ≠ 0 := fun hz =>
    (Nat.card_pos (α := ↥E₂)).ne' (Nat.eq_zero_of_zero_dvd (hz ▸ Group.exponent_dvd_nat_card))
  have hdvd : p ^ (Monoid.exponent ↥E).factorization p ∣ Monoid.exponent ↥E₂ := by
    rw [← hord]; exact Monoid.order_dvd_exponent _
  rwa [Nat.Prime.pow_dvd_iff_le_factorization Fact.out hexp_ne] at hdvd

/-- **`r = p` exponent realisation in the complement.** With `A₀ ⊴ E` of order `p` inside the
abelian Sylow `p`-subgroup `E₂` of `E`, complement `E₀`, and `C := E₂ ⊓ E₀` nontrivial: the
abelian `E₂ = A₀ × C` has `exp E₂ ∣ lcm(exp A₀, exp C)` (surjective `A₀ × C → E₂`), and since
`ν_p(exp A₀) ≤ 1 ≤ ν_p(exp C)` (`C` a nontrivial `p`-group) while `ν_p(exp E) ≤ ν_p(exp E₂)`
(Sylow), the full `p`-part of `exp E` is realised by an exponent-element of `C ≤ E₀`. -/
theorem exists_factorization_le_at_prime [Finite G] {E E₀ A₀ E₂ : Subgroup G} {p : ℕ}
    [Fact p.Prime] (hA₀E₂ : A₀ ≤ E₂) (hE₂E : E₂ ≤ E)
    (hE₀NA₀ : E₀ ≤ Subgroup.normalizer (A₀ : Set G)) (hE₂ab : IsMulCommutative ↥E₂)
    (hA₀card : Nat.card ↥A₀ = p) (hE₂sup : E₂ ≤ A₀ ⊔ E₀) (_hA₀E₀ : A₀ ⊓ E₀ = ⊥)
    (hcard : Nat.card ↥(E₂.subgroupOf E) = p ^ (Nat.card ↥E).factorization p)
    (hCne : E₂ ⊓ E₀ ≠ ⊥) :
    ∃ g₀ : ↥E₀, (Monoid.exponent ↥E).factorization p ≤ (orderOf g₀).factorization p := by
  set C : Subgroup G := E₂ ⊓ E₀ with hCdef
  have hCE₂ : C ≤ E₂ := inf_le_left
  have hCE₀ : C ≤ E₀ := inf_le_right
  -- abelian `E₂ = A₀ ⊔ C`.
  have hE₂eq : E₂ = A₀ ⊔ C := eq_sup_inf_of_le_normalizer hE₀NA₀ hA₀E₂ hE₂sup
  -- nonzero exponents.
  have hne : ∀ H : Subgroup G, Monoid.exponent ↥H ≠ 0 := fun H hz =>
    (Nat.card_pos (α := ↥H)).ne' (Nat.eq_zero_of_zero_dvd (hz ▸ Group.exponent_dvd_nat_card))
  -- `exp E₂ ∣ lcm (exp A₀) (exp C)`: every `w = c·a ∈ E₂` (`c ∈ C`, `a ∈ A₀`, commuting) has
  -- `orderOf w ∣ lcm(orderOf c, orderOf a) ∣ lcm(exp C, exp A₀)`.
  have hdvd : Monoid.exponent ↥E₂ ∣ Nat.lcm (Monoid.exponent ↥A₀) (Monoid.exponent ↥C) := by
    rw [Monoid.exponent_dvd]
    intro w
    have hwCA : (w : G) ∈ (↑C * ↑A₀ : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right C A₀ (hCE₀.trans hE₀NA₀),
        SetLike.mem_coe, sup_comm, ← hE₂eq]
      exact w.2
    obtain ⟨c, hc, a, ha, hca⟩ := Set.mem_mul.mp hwCA
    have hwG : orderOf w = orderOf ((c : G) * a) := by rw [← Subgroup.orderOf_coe w, hca]
    have hcomm_ca : Commute (c : G) (a : G) :=
      congrArg Subtype.val (hE₂ab.is_comm.comm (⟨c, hCE₂ hc⟩ : ↥E₂) ⟨a, hA₀E₂ ha⟩)
    rw [hwG]
    refine hcomm_ca.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd ?_ ?_)
    · refine dvd_trans ?_ (Nat.dvd_lcm_right _ _)
      have hd : orderOf (⟨c, hc⟩ : ↥C) ∣ Monoid.exponent ↥C := Monoid.order_dvd_exponent _
      rwa [Subgroup.orderOf_mk] at hd
    · refine dvd_trans ?_ (Nat.dvd_lcm_left _ _)
      have hd : orderOf (⟨a, ha⟩ : ↥A₀) ∣ Monoid.exponent ↥A₀ := Monoid.order_dvd_exponent _
      rwa [Subgroup.orderOf_mk] at hd
  have hfac : (Monoid.exponent ↥E₂).factorization p ≤
      max ((Monoid.exponent ↥A₀).factorization p) ((Monoid.exponent ↥C).factorization p) := by
    have hle := (Finsupp.le_def.mp
      ((Nat.factorization_le_iff_dvd (hne E₂) (Nat.lcm_ne_zero (hne A₀) (hne C))).mpr hdvd)) p
    rwa [Nat.factorization_lcm (hne A₀) (hne C), Finsupp.sup_apply] at hle
  -- `ν_p(exp A₀) ≤ 1`.
  have hA₀fac : (Monoid.exponent ↥A₀).factorization p ≤ 1 := by
    have hdvdp : Monoid.exponent ↥A₀ ∣ p := hA₀card ▸ Group.exponent_dvd_nat_card
    have hp := (Finsupp.le_def.mp ((Nat.factorization_le_iff_dvd (hne A₀)
      (Fact.out : p.Prime).pos.ne').mpr hdvdp)) p
    rwa [Nat.Prime.factorization_self Fact.out] at hp
  -- `C` is a nontrivial `p`-group, so `1 ≤ ν_p(exp C)`.
  have hE₂card2 : Nat.card ↥E₂ = p ^ (Nat.card ↥E).factorization p := by
    rw [← hcard]; exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₂E).toEquiv).symm
  have hCdvd : Nat.card ↥C ∣ p ^ (Nat.card ↥E).factorization p :=
    hE₂card2 ▸ Subgroup.card_dvd_of_le hCE₂
  have hpdvdC : p ∣ Nat.card ↥C := by
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp hCdvd
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [pow_zero] at hj; exact absurd (Subgroup.card_eq_one.mp hj) hCne
    · rw [hj]; exact dvd_pow_self p hj0.ne'
  have hCfac : 1 ≤ (Monoid.exponent ↥C).factorization p := by
    obtain ⟨c₀, hc₀⟩ := exists_prime_orderOf_dvd_card' p hpdvdC
    have hpdvd : p ∣ Monoid.exponent ↥C := hc₀ ▸ Monoid.order_dvd_exponent c₀
    exact (Nat.Prime.dvd_iff_one_le_factorization Fact.out (hne C)).mp hpdvd
  -- assemble: `ν_p(exp E) ≤ ν_p(exp E₂) ≤ ν_p(exp C)`.
  have hfactA := factorization_exponent_le_of_sylow hE₂E hcard
  obtain ⟨c, hc⟩ := (Fact.out : p.Prime).exists_orderOf_eq_pow_factorization_exponent ↥C
  refine ⟨Subgroup.inclusion hCE₀ c, ?_⟩
  have hc_ord : orderOf (Subgroup.inclusion hCE₀ c) = p ^ (Monoid.exponent ↥C).factorization p := by
    rw [orderOf_injective (Subgroup.inclusion hCE₀) (Subgroup.inclusion_injective hCE₀) c, hc]
  rw [hc_ord]
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    Nat.Prime.factorization_self Fact.out, mul_one]
  omega

/-- **Theorem 12.12, case nonabelian Sylow `p`** (`τ₂(M) ≠ ∅`, `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)`,
Sylow `p`-subgroups of `G` nonabelian). The canonical line `A₀ = A ⊓ C(M_σ)` (Theorem 12.7)
has a complement `E₀` in `E`; `A₀` witnesses part (a) (`E ⊓ C(x) = A₀` for `x ∈ M_σ#`, by the
Dedekind decomposition `E = A₀ ⊔ E₀` and `E₀ ⊓ C(x) = 1`), and `E₀` witnesses part (b): it is
regular on `M_σ` (`π(E₀ ⊓ C(x)) ⊆ τ₁` by 12.7(e), killed by the `(τ₁∪τ₃)`-regularity), has the
same exponent as `E` (the `r`-parts transfer through the complement, the `p`-part through the
abelian Sylow `E₂`), so `M_σ E₀` is Frobenius. -/
theorem frobFact_of_nonabelianSylow [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    (hnonab : ∃ S : Sylow p G, ¬ IsMulCommutative (S : Subgroup G))
    (hreg : ∀ e ∈ E, e ≠ 1 → (∀ r ∈ (orderOf e).primeFactors, r ∈ tau1 M ∪ tau3 M) →
      S10.Msigma M ⊓ Subgroup.centralizer ({e} : Set G) = ⊥) :
    FrobFactConclusion M E := by
  classical
  have hAM : A ≤ M := hAE.trans h.E_le
  have hprime_eq : ∀ q : ℕ, q.Prime → q ∈ tau2 M → q = p :=
    fun q hq hq2 => tau2_prime_eq_of_nonabelianSylow hG h hp hA hAE hnonab hq hq2
  obtain ⟨A₀, hA₀eq, hA₀card, hA₀A, hMσC, hc, habs⟩ :=
    exists_canonical_line_of_nonabelianSylow hG h hp hA hAE hnonab
  have hMnorm : M ≤ Subgroup.normalizer (A₀ : Set G) :=
    (fitting_eq_sup_of_canonical_line hG h hp hA hAE hprime_eq hA₀eq hA₀card hMσC habs).1
  obtain ⟨E₀, hE₀E, hA₀E₀, hA₀E₀sup⟩ :=
    exists_complement_of_canonical_line hG h hp hA hAE hnonab hprime_eq hA₀A hA₀card hMσC hMnorm
  -- placement and abelianness of `A₀`.
  have hA₀E : A₀ ≤ E := hA₀A.trans hAE
  have hEN : E ≤ Subgroup.normalizer (A₀ : Set G) := h.E_le.trans hMnorm
  have hE₀N : E₀ ≤ Subgroup.normalizer (A₀ : Set G) := hE₀E.trans hEN
  have hA₀comm : IsMulCommutative ↥A₀ := isMulCommutative_of_le ⟨⟨hA.1.comm⟩⟩ hA₀A
  have hA₀norm : (A₀.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA₀E).mpr hEN
  -- regularity in the complement: `E₀ ⊓ C(x) = 1` for `x ∈ M_σ#`.
  have hreg₀ : ∀ x ∈ S10.Msigma M, x ≠ 1 →
      E₀ ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ := by
    intro x hx hx1
    rw [← Subgroup.card_eq_one]
    by_contra hcard1
    obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hcard1
    have : Fact r.Prime := ⟨hr_prime⟩
    have hrmem : r ∈ (Nat.card ↥(E₀ ⊓ Subgroup.centralizer ({x} : Set G) :
        Subgroup G)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hr_prime, hr_dvd, Nat.card_pos.ne'⟩
    have hrτ1 : r ∈ tau1 M :=
      primeFactors_centralizer_le_tau1_of_disjoint hG h hp hA hAE hprime_eq hc hE₀E hA₀E₀ hx hx1 r
        hrmem
    obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' r hr_dvd
    set y : G := ((y' : ↥(E₀ ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G)) : G) with hydef
    have hyord : orderOf y = r := by rw [hydef, Subgroup.orderOf_coe]; exact hy'
    have hyE₀ : y ∈ E₀ := (Subgroup.mem_inf.mp y'.2).1
    have hyCx : y ∈ Subgroup.centralizer ({x} : Set G) := (Subgroup.mem_inf.mp y'.2).2
    have hy1 : y ≠ 1 := by
      intro hcon; rw [hcon, orderOf_one] at hyord; exact hr_prime.one_lt.ne hyord
    have hregy : S10.Msigma M ⊓ Subgroup.centralizer ({y} : Set G) = ⊥ := by
      refine hreg y (hE₀E hyE₀) hy1 ?_
      intro s hs
      rw [hyord, Nat.Prime.primeFactors hr_prime, Finset.mem_singleton] at hs
      exact hs ▸ Set.mem_union_left _ hrτ1
    have hxCy : x ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm; rw [Set.mem_singleton_iff] at hm; subst hm
      exact (Subgroup.mem_centralizer_iff.mp hyCx x (Set.mem_singleton x)).symm
    have hxmem : x ∈ S10.Msigma M ⊓ Subgroup.centralizer ({y} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hx, hxCy⟩
    rw [hregy, Subgroup.mem_bot] at hxmem
    exact hx1 hxmem
  -- `E₀ ≠ 1` (else `E = A₀` has order `p`, but `A ≤ E` has order `p²`).
  have hE₀ne : E₀ ≠ ⊥ := by
    intro h0
    rw [h0, sup_bot_eq] at hA₀E₀sup
    have hdvd : Nat.card ↥A ∣ Nat.card ↥A₀ := Subgroup.card_dvd_of_le (hA₀E₀sup.symm ▸ hAE)
    rw [hA.2, hA₀card] at hdvd
    exact absurd (Nat.le_of_dvd (Fact.out : p.Prime).pos hdvd)
      (by nlinarith [(Fact.out : p.Prime).two_le])
  -- complement data inside `↥E`.
  have hcompl : (E₀.subgroupOf E).IsComplement' (A₀.subgroupOf E) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · have hinf : (E₀.subgroupOf E) ⊓ (A₀.subgroupOf E) = (E₀ ⊓ A₀).subgroupOf E := rfl
      rw [disjoint_iff, hinf, inf_comm, hA₀E₀, Subgroup.bot_subgroupOf]
    · rw [← Subgroup.mul_normal, ← Subgroup.subgroupOf_sup hE₀E hA₀E, sup_comm, hA₀E₀sup,
        Subgroup.subgroupOf_self, Subgroup.coe_top]
  -- the abelian Sylow `p`-subgroup `E₂`.
  have hAE₂ : A ≤ E₂ := elemAb_le_E2_of_prime_eq hG h hp hA hAE hprime_eq
  have hA₀E₂ : A₀ ≤ E₂ := hA₀A.trans hAE₂
  have hE₂ab : IsMulCommutative ↥E₂ := E2_isMulCommutative_of_prime_eq hG h hp hA hAM hprime_eq
  have hcardE₂ : Nat.card ↥(E₂.subgroupOf E) = p ^ (Nat.card ↥E).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv]
    exact card_E2_eq_pow h hp hprime_eq
  have hE₂sup : E₂ ≤ A₀ ⊔ E₀ := le_of_le_of_eq h.E₂_le hA₀E₀sup.symm
  have hCne : E₂ ⊓ E₀ ≠ ⊥ := by
    intro hC0
    have hmod : E₂ = A₀ ⊔ (E₂ ⊓ E₀) := eq_sup_inf_of_le_normalizer hE₀N hA₀E₂ hE₂sup
    rw [hC0, sup_bot_eq] at hmod
    have hdvd : Nat.card ↥A ∣ Nat.card ↥A₀ := Subgroup.card_dvd_of_le (hmod ▸ hAE₂)
    rw [hA.2, hA₀card] at hdvd
    exact absurd (Nat.le_of_dvd (Fact.out : p.Prime).pos hdvd)
      (by nlinarith [(Fact.out : p.Prime).two_le])
  -- same exponent for `E₀` and `E` (`r ≠ p` via the complement, `r = p` via the Sylow).
  have hattain : ∀ r : ℕ, r.Prime →
      ∃ g₀ : ↥E₀, (Monoid.exponent ↥E).factorization r ≤ (orderOf g₀).factorization r := by
    intro r hr
    have : Fact r.Prime := ⟨hr⟩
    by_cases hrp : r = p
    · subst hrp
      exact exists_factorization_le_at_prime hA₀E₂ h.E₂_le hE₀N hE₂ab hA₀card hE₂sup hA₀E₀
        hcardE₂ hCne
    · obtain ⟨g₀, hg₀⟩ := exists_orderOf_eq_rpow_in_complement hA₀E hE₀E hcompl hr
        (by rw [hA₀card]; exact (Nat.coprime_primes hr Fact.out).mpr hrp)
      refine ⟨g₀, le_of_eq ?_⟩
      rw [hg₀, Nat.factorization_pow]
      simp [Nat.Prime.factorization_self hr]
  have hexp : Monoid.exponent ↥E₀ = Monoid.exponent ↥E :=
    exponent_eq_of_forall_factorization_le hE₀E hattain
  have hreg₀' : ∀ a ∈ E₀, a ≠ 1 →
      S10.Msigma M ⊓ Subgroup.centralizer ({a} : Set G) = ⊥ :=
    inf_centralizer_bot_symm hreg₀
  -- assemble the two-part conclusion.
  refine ⟨⟨A₀, hA₀E, hA₀comm, hEN, ?_⟩,
    ⟨E₀, hE₀E, hexp, isFrobeniusGroup_of_regular hG h hE₀E hE₀ne hreg₀'⟩⟩
  intro x hx hx1
  have hA₀Cx : A₀ ≤ Subgroup.centralizer ({x} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro m hm; rw [Set.mem_singleton_iff] at hm; subst hm
    exact (Subgroup.mem_centralizer_iff.mp (hMσC hx) a ha).symm
  have hHinf : (E ⊓ Subgroup.centralizer ({x} : Set G)) ⊓ E₀ = ⊥ :=
    le_bot_iff.mp ((le_inf inf_le_right (inf_le_left.trans inf_le_right)).trans
      (hreg₀ x hx hx1).le)
  have hmod := eq_sup_inf_of_le_normalizer hE₀N (le_inf hA₀E hA₀Cx)
    (le_of_le_of_eq inf_le_left hA₀E₀sup.symm)
  rw [hHinf, sup_bot_eq] at hmod
  exact hmod.le

end OddOrder.BG.Ch3.S12


