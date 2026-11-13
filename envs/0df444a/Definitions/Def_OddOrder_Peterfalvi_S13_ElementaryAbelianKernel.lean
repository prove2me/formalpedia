-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
-- name    : OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:20:50.133228+00:00
-- url     : https://prove2.me/theorems/be0bd0af-917a-4d88-8ef9-3f7d3b63477a
-- title:
--   Peterfalvi (11.7): the chief-kernel triviality frame
-- statement:
--   Formalizes the frame for Peterfalvi (11.7) (Peterfalvi, *Character Theory for the Odd Order Theorem*, pp. 64-65): under Hypothesis (11.2), $H$ is elementary abelian of order $p^q$ with trivial chief kernel. The bundle consists of lemmas only.
--
--   The bundle also proves 14 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S13_ElementaryAbelianKernel.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S13_ElementaryAbelianKernel.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_WielandtSetup
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CliffordData
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CuS0
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CharacterCounts
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_Coherence911
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_SummandComplementKernel
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_ThetaCountAssembly
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassTwoSquareIndex
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Nilpotent

namespace OddOrder.Peterfalvi.S13

open OddOrder.Peterfalvi.S11

open scoped commutatorElement

section PGroupFrame

variable {K : Type*} [Group K]

/-- **`[K, N] < N` for a nontrivial normal subgroup of a nilpotent group**: if `[K, N] = N` the
lower central series could never swallow `N`. -/
theorem commutator_top_lt_of_normal_of_ne_bot [Group.IsNilpotent K]
    {N : Subgroup K} [hN : N.Normal] (hNne : N ≠ ⊥) :
    ⁅(⊤ : Subgroup K), N⁆ < N := by
  refine lt_of_le_of_ne (Subgroup.commutator_le_right ⊤ N) ?_
  intro heq
  apply hNne
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp ‹Group.IsNilpotent K›
  have hle : ∀ m, N ≤ (⊤ : Subgroup K).lowerCentralSeries m := by
    intro m
    induction m with
    | zero => exact le_top
    | succ m ih =>
        have hsucc : (⊤ : Subgroup K).lowerCentralSeries (m + 1)
            = ⁅(⊤ : Subgroup K).lowerCentralSeries m, ⊤⁆ := by
          rw [Subgroup.commutator_def, Subgroup.lowerCentralSeries_succ]
          rfl
        rw [hsucc]
        calc N = ⁅⊤, N⁆ := heq.symm
          _ = ⁅N, ⊤⁆ := Subgroup.commutator_comm _ _
          _ ≤ ⁅(⊤ : Subgroup K).lowerCentralSeries m, ⊤⁆ := Subgroup.commutator_mono ih le_rfl
  exact le_bot_iff.mp (hn ▸ hle n)

/-- **The index-`p` normal subgroup below a nontrivial normal subgroup of a `p`-group**
(Peterfalvi's citation of [BG] Lemma 1.22 in (11.7)): for `⊥ ≠ N ◁ K` with `K` a finite
`p`-group there is `Q ◁ K` with `[K, N] ≤ Q ≤ N` and `|N : Q| = p`.  Any subgroup between
`[K, N]` and `N` is automatically `K`-normal, so it suffices to take a hyperplane of the
nontrivial quotient `p`-group `N/[K, N]` (Sylow tower). -/
theorem exists_normal_subgroup_index_prime [Finite K] {p : ℕ}
    (hp : p.Prime) (hK : IsPGroup p K) {N : Subgroup K} [hNnorm : N.Normal] (hNne : N ≠ ⊥) :
    ∃ Q : Subgroup K, Q.Normal ∧ Q ≤ N ∧ ⁅(⊤ : Subgroup K), N⁆ ≤ Q ∧
      Nat.card ↥N = p * Nat.card ↥Q := by
  classical
  have := Fact.mk hp
  have : Group.IsNilpotent K := hK.isNilpotent
  have hRlt : ⁅(⊤ : Subgroup K), N⁆ < N := commutator_top_lt_of_normal_of_ne_bot hNne
  have hRnorm : (⁅(⊤ : Subgroup K), N⁆).Normal := Subgroup.commutator_normal ⊤ N
  set R' : Subgroup ↥N := (⁅(⊤ : Subgroup K), N⁆).subgroupOf N with hR'def
  have : R'.Normal := Subgroup.normal_subgroupOf
  -- the quotient `Ā = N/[K,N]` is a nontrivial finite `p`-group
  have hAbar_pgroup : IsPGroup p (↥N ⧸ R') := (hK.to_subgroup N).to_quotient R'
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hAbar_pgroup
  have hAbar_ne : Nat.card (↥N ⧸ R') ≠ 1 := by
    intro h1
    have hR'top : R' = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup R'
      rw [h1, one_mul] at hprod
      exact hprod.symm
    exact absurd (le_antisymm hRlt.le ((Subgroup.subgroupOf_eq_top).mp hR'top)) hRlt.ne
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h
    · rw [h0, pow_zero] at hm
      exact absurd hm hAbar_ne
    · exact h
  -- a hyperplane `Q̄ ≤ Ā` of order `p^(m-1)`
  obtain ⟨Qbar, hQbarcard, -⟩ := Sylow.exists_subgroup_card_pow_prime_le p
    (n := 0) (m := m - 1)
    (by rw [hm]; exact pow_dvd_pow p (by omega)) ⊥ (by simp) (by omega)
  -- pull back to `↥N`: index `p`
  set Q₀ : Subgroup ↥N := Qbar.comap (QuotientGroup.mk' R') with hQ₀def
  have hQ₀index : Q₀.index = p := by
    rw [hQ₀def, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective R')]
    have hprod := Subgroup.index_mul_card Qbar
    rw [hQbarcard, hm] at hprod
    have hpm : p ^ m = p * p ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hpm] at hprod
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) hprod
  -- `[K,N] ≤ Q₀.map N.subtype`
  have hRle : ⁅(⊤ : Subgroup K), N⁆ ≤ Q₀.map N.subtype := by
    intro r hr
    have hrN : r ∈ N := hRlt.le hr
    refine ⟨⟨r, hrN⟩, ?_, rfl⟩
    change (⟨r, hrN⟩ : ↥N) ∈ Q₀
    rw [hQ₀def, Subgroup.mem_comap]
    have : (⟨r, hrN⟩ : ↥N) ∈ R' := by
      rw [hR'def, Subgroup.mem_subgroupOf]
      exact hr
    rw [show (QuotientGroup.mk' R') ⟨r, hrN⟩ = 1 from (QuotientGroup.eq_one_iff _).mpr this]
    exact Qbar.one_mem
  have hQle : Q₀.map N.subtype ≤ N := Subgroup.map_subtype_le _
  refine ⟨Q₀.map N.subtype, ?_, hQle, hRle, ?_⟩
  · -- normality: `g q g⁻¹ = ⁅g, q⁆ * q` with `⁅g, q⁆ ∈ [K, N] ≤ Q`
    refine ⟨fun q hq g => ?_⟩
    have hcomm : ⁅g, q⁆ ∈ Q₀.map N.subtype :=
      hRle (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (hQle hq))
    have hgq : g * q * g⁻¹ = ⁅g, q⁆ * q := by
      rw [commutatorElement_def]
      group
    rw [hgq]
    exact Subgroup.mul_mem _ hcomm hq
  · -- the order relation `|N| = p * |Q|`
    have hcards : Nat.card ↥(Q₀.map N.subtype) = Nat.card ↥Q₀ :=
      (Nat.card_congr (Q₀.equivMapOfInjective N.subtype N.subtype_injective).toEquiv).symm
    rw [hcards, ← hQ₀index]
    exact (Subgroup.index_mul_card Q₀).symm

end PGroupFrame

section QuotientClassTwo

variable {K : Type*} [Group K]

/-- **The class-`2` structure of `Ĥ = K/Q`** (Peterfalvi (11.7), central-quotient step): for
`Q ◁ K` with `[K, N] ≤ Q ≤ N`, `|N : Q| = p`, and `N = K'`, in the quotient `Ĥ = K/Q` the image
`N̂ = N/Q`:

* has order `p`;
* equals the commutator `Ĥ' = K'Q/Q`;
* is *central* (directly from `[K, N] ≤ Q` — no `p`-group argument needed);

so `Ĥ` has nilpotency class `≤ 2` with `Ĥ' = N̂ ≤ Z(Ĥ)` of order `p`. -/
theorem quotient_classTwo_structure [Finite K] {p : ℕ} (_hp : p.Prime)
    {N Q : Subgroup K} [_hNnorm : N.Normal] (hQnorm : Q.Normal) (hQle : Q ≤ N)
    (hRQ : ⁅(⊤ : Subgroup K), N⁆ ≤ Q) (hcard : Nat.card ↥N = p * Nat.card ↥Q)
    (hNcomm : N = commutator K) :
    haveI := hQnorm
    Nat.card ↥(N.map (QuotientGroup.mk' Q)) = p ∧
      commutator (K ⧸ Q) = N.map (QuotientGroup.mk' Q) ∧
      N.map (QuotientGroup.mk' Q) ≤ Subgroup.center (K ⧸ Q) := by
  have := hQnorm
  refine ⟨?_, ?_, ?_⟩
  · -- `|N/Q| = p`: first isomorphism for `mk' Q` restricted to `N`
    set f : ↥N →* K ⧸ Q := (QuotientGroup.mk' Q).comp N.subtype with hf
    have hrange : f.range = N.map (QuotientGroup.mk' Q) := by
      rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    have hker : f.ker = Q.subgroupOf N := by
      rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      rfl
    have hiso := Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    have hkercard : Nat.card ↥f.ker = Nat.card ↥Q := by
      rw [hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv
    rw [hiso, hrange, hkercard, hcard] at hprod
    have hQpos : 0 < Nat.card ↥Q := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hQpos hprod.symm)
  · -- `Ĥ' = N̂`: commutators map onto commutators under the surjection
    have h1 : commutator (K ⧸ Q) = (commutator K).map (QuotientGroup.mk' Q) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Q)]
    rw [h1, hNcomm]
  · -- `N̂ ≤ Z(Ĥ)`: `[K, N] ≤ Q` kills every commutator against `N̂`
    rintro _ ⟨n, hnN, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro ghat
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q ghat
    have hcomm : ⁅g, n⁆ ∈ Q := hRQ
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) hnN)
    have h1 : (QuotientGroup.mk' Q) ⁅g, n⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hcomm
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1

end QuotientClassTwo

section ClassTwoCalculus

variable {Γ : Type*} [Group Γ]

/-- Central factors drop out of commutators (left argument). -/
theorem commutatorElement_mul_center_left {z : Γ} (hz : z ∈ Subgroup.center Γ) (a b : Γ) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have hzb : z * b = b * z := (Subgroup.mem_center_iff.mp hz b).symm
  rw [commutatorElement_def, commutatorElement_def]
  rw [show a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ by group, hzb]
  group

/-- The product expansion `⁅x·y, b⁆ = ⁅y, b⁆ · ⁅x, b⁆` when `⁅y, b⁆` is central
(the class-`2` "linearity" seed). -/
theorem commutatorElement_mul_left_of_center {y b : Γ}
    (hc : ⁅y, b⁆ ∈ Subgroup.center Γ) (x : Γ) :
    ⁅x * y, b⁆ = ⁅y, b⁆ * ⁅x, b⁆ := by
  have hexp : ⁅x * y, b⁆ = x * ⁅y, b⁆ * (b * x⁻¹ * b⁻¹) := by
    rw [commutatorElement_def, commutatorElement_def]
    group
  rw [hexp, show x * ⁅y, b⁆ * (b * x⁻¹ * b⁻¹) = x * (⁅y, b⁆ * (b * x⁻¹ * b⁻¹)) by group,
    ← Subgroup.mem_center_iff.mp hc (b * x⁻¹ * b⁻¹),
    show x * (b * x⁻¹ * b⁻¹ * ⁅y, b⁆) = (x * b * x⁻¹ * b⁻¹) * ⁅y, b⁆ by group,
    ← commutatorElement_def]
  exact Subgroup.mem_center_iff.mp hc ⁅x, b⁆

/-- **Class-`2` power bilinearity (left)**: `⁅a^k, b⁆ = ⁅a, b⁆^k` when `⁅a, b⁆` is central. -/
theorem commutatorElement_pow_left_of_center {a b : Γ}
    (hc : ⁅a, b⁆ ∈ Subgroup.center Γ) (k : ℕ) :
    ⁅a ^ k, b⁆ = ⁅a, b⁆ ^ k := by
  induction k with
  | zero => simp [commutatorElement_def]
  | succ k ih =>
      have hkc : ⁅a ^ k, b⁆ ∈ Subgroup.center Γ := by
        rw [ih]
        exact Subgroup.pow_mem _ hc k
      rw [pow_succ, show a ^ k * a = a * a ^ k by exact (Commute.pow_self a k).eq,
        commutatorElement_mul_left_of_center hkc a, ih, pow_succ]

end ClassTwoCalculus

section PrimeExponent

variable {Γ : Type*} [Group Γ]

/-- **An automorphism preserving a subgroup of prime order acts by exponentiation**: if
`|T| = p` and `e` maps `T` into itself, there is `k` (indivisible by `p`) with `e h = h^k` for
all `h ∈ T`. -/
theorem exists_pow_eq_of_mapsTo_of_card_prime {p : ℕ} (hp : p.Prime)
    {T : Subgroup Γ} (hT : Nat.card ↥T = p) (e : MulAut Γ)
    (hmem : ∀ h ∈ T, e h ∈ T) :
    ∃ k : ℕ, ¬ p ∣ k ∧ ∀ h ∈ T, e h = h ^ k := by
  classical
  have : Finite ↥T := Nat.finite_of_card_ne_zero (hT ▸ hp.pos.ne')
  have : Fact p.Prime := ⟨hp⟩
  have : IsCyclic ↥T := isCyclic_of_prime_card hT
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := ↥T)
  have htord : orderOf t = p := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ht, hT]
  have htfin : IsOfFinOrder t := isOfFinOrder_of_finite t
  -- `e t = t^k` for a natural `k`
  obtain ⟨k, hk⟩ := htfin.mem_powers_iff_mem_zpowers.mpr
    (ht (⟨e ↑t, hmem ↑t t.2⟩ : ↥T))
  have hek : e (↑t : Γ) = (↑t : Γ) ^ k := by
    have := congrArg (Subtype.val : ↥T → Γ) hk
    simpa using this.symm
  refine ⟨k, ?_, ?_⟩
  · -- `p ∤ k`: otherwise `e t = 1`, so `t = 1`, contradicting `|T| = p`
    intro hdvd
    have ht1 : t ^ k = 1 := orderOf_dvd_iff_pow_eq_one.mp (htord ▸ hdvd)
    have hcoe1 : (↑t : Γ) ^ k = 1 := by
      have := congrArg (Subtype.val : ↥T → Γ) ht1
      simpa using this
    have het1 : e (↑t : Γ) = 1 := by rw [hek, hcoe1]
    have ht1' : (↑t : Γ) = 1 := by
      have := congrArg e.symm het1
      simpa using this
    have : t = 1 := Subtype.ext (by simpa using ht1')
    rw [this, orderOf_one] at htord
    exact hp.one_lt.ne' htord.symm
  · -- every `h ∈ T` is a power of `t`, and `e` commutes with powers
    intro h hh
    obtain ⟨m, hm⟩ := htfin.mem_powers_iff_mem_zpowers.mpr (ht (⟨h, hh⟩ : ↥T))
    have hcoe : h = (↑t : Γ) ^ m := by
      have := congrArg (Subtype.val : ↥T → Γ) hm
      simpa using this.symm
    rw [hcoe, map_pow, hek, ← pow_mul, ← pow_mul, Nat.mul_comm]

end PrimeExponent

section CaseB

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

/-- **Peterfalvi (11.7), Galois case refuted**: if `H` is a `p`-group with `H₀ = N = H'` a
*nontrivial* chief kernel, `U` centralizes `N`, and `U` acts irreducibly on `H̄ = H/H₀`
(Clifford case (b) of (9.7)), then `q = |W₁|` odd is contradictory.

With `Q ◁ H`, `[H, N] ≤ Q ≤ N`, `|N : Q| = p` (`exists_normal_subgroup_index_prime`), the
quotient `Ĥ = H/Q` is class-`2` with `Ĥ' = N̂ ≤ Z(Ĥ)` of order `p`
(`quotient_classTwo_structure`).  The image of `Z(Ĥ)` in `H̄` is `U`-invariant (the `U`-action
descends past the `U`-pointwise-fixed `Q`, and centers are characteristic), so by irreducibility
it is `⊥` — giving `Z(Ĥ) = N̂` of order `p` and the parity contradiction
`even_of_card_eq_prime_pow_succ_of_class_two` (`|Ĥ| = p^(q+1)` forces `q` even) — or `⊤` —
making `Ĥ` abelian, contradicting `|Ĥ'| = p`. -/
theorem chiefKernel_caseB_false [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (hpK : IsPGroup chief.p ↥data.H)
    (hNcomm : chief.N = commutator ↥data.H)
    (hUcent : ∀ (u : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
      (n : ↥data.H), n ∈ chief.N → typeP_conjAction data.typeP ↑u n = n)
    (hqodd : Odd data.q)
    (hNne : chief.N ≠ ⊥)
    (hirr : ∀ J : Subgroup (↥data.H ⧸ chief.N),
      IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤) :
    False := by
  classical
  have := Fact.mk chief.p_prime
  -- the index-`p` normal subgroup `Q` and the class-`2` structure of `Ĥ = H/Q`
  obtain ⟨Q, hQnorm, hQle, hRQ, hcard⟩ :=
    exists_normal_subgroup_index_prime chief.p_prime hpK hNne
  have := hQnorm
  obtain ⟨hNhatCard, hcommHat, hNhatLe⟩ :=
    quotient_classTwo_structure chief.p_prime hQnorm hQle hRQ hcard hNcomm
  -- the projection `π : Ĥ → H̄`
  set π : (↥data.H ⧸ Q) →* (↥data.H ⧸ chief.N) :=
    QuotientGroup.map Q chief.N (MonoidHom.id ↥data.H) (by simpa using hQle) with hπdef
  have hπmk : ∀ x : ↥data.H, π ((QuotientGroup.mk' Q) x) = (QuotientGroup.mk' chief.N) x :=
    fun x => rfl
  have hπker : π.ker = chief.N.map (QuotientGroup.mk' Q) := by
    ext h
    constructor
    · intro hh
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q h
      rw [MonoidHom.mem_ker, hπmk] at hh
      exact ⟨x, (QuotientGroup.eq_one_iff _).mp hh, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      rw [MonoidHom.mem_ker, hπmk]
      exact (QuotientGroup.eq_one_iff _).mpr hn
  -- the `U`-action descends to `Ĥ` (as `U` fixes `Q ≤ N` pointwise)
  set φU : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) →* MulAut ↥data.H :=
    (typeP_conjAction data.typeP).comp
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype with hφUdef
  have hQinv : IsAInvariant φU Q := by
    intro u
    change Q.map (φU u).toMonoidHom = Q
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hfix : (φU u) x = x := hUcent u x (hQle hx)
      rw [show (φU u).toMonoidHom x = x from hfix]
      exact hx
    · intro x hx
      exact ⟨x, hx, hUcent u x (hQle hx)⟩
  -- the `π`-equivariance of the two descended `U`-actions
  have hπσ : ∀ (u : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
      (h : ↥data.H ⧸ Q),
      ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) u (π h) = π (quotientMulAutHom hQinv u h) := by
    intro u h
    refine QuotientGroup.induction_on h ?_
    intro x
    rfl
  -- centers are preserved by every automorphism
  have hZcen : ∀ (e : MulAut (↥data.H ⧸ Q)) (z : ↥data.H ⧸ Q),
      z ∈ Subgroup.center (↥data.H ⧸ Q) → e z ∈ Subgroup.center (↥data.H ⧸ Q) := by
    intro e z hz
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    calc g * e z = e (e.symm g * z) := by rw [map_mul, e.apply_symm_apply]
      _ = e (z * e.symm g) := by rw [hz (e.symm g)]
      _ = e z * g := by rw [map_mul, e.apply_symm_apply]
  -- the image of the center of `Ĥ` in `H̄` is `U`-invariant
  set J : Subgroup (↥data.H ⧸ chief.N) := (Subgroup.center (↥data.H ⧸ Q)).map π with hJdef
  have hJinv : IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
      chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
      chief.N_aInvariant).U.subtype) J := by
    intro u
    change J.map _ = J
    apply le_antisymm
    · rintro _ ⟨j, hj, rfl⟩
      rw [hJdef] at hj
      obtain ⟨z, hz, rfl⟩ := hj
      exact ⟨quotientMulAutHom hQinv u z, hZcen _ z hz, (hπσ u z).symm⟩
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨π ((quotientMulAutHom hQinv u).symm z),
        ⟨(quotientMulAutHom hQinv u).symm z, hZcen _ z hz, rfl⟩, ?_⟩
      exact (hπσ u _).trans (congrArg π ((quotientMulAutHom hQinv u).apply_symm_apply z))
  -- `|Ĥ| = p^(q+1)`
  have hHhatCard : Nat.card (↥data.H ⧸ Q) = chief.p ^ (data.q + 1) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Q
    have h2 : Nat.card ↥chief.H0 = Nat.card ↥chief.N := by
      rw [chief.H0_eq]
      exact (Nat.card_congr
        (chief.N.equivMapOfInjective data.H.subtype data.H.subtype_injective).toEquiv).symm
    have h3 := chief.quotient_order
    rw [h1, h2, hcard] at h3
    have hQpos : 0 < Nat.card ↥Q := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right hQpos ?_
    rw [h3, pow_succ]
    ring
  -- the dichotomy
  rcases hirr J hJinv with hJbot | hJtop
  · -- `J = ⊥`: `Z(Ĥ) = N̂` of order `p`, and the square-index parity forces `q` even
    have hZle : Subgroup.center (↥data.H ⧸ Q) ≤ chief.N.map (QuotientGroup.mk' Q) := by
      rw [← hπker]
      exact (Subgroup.map_eq_bot_iff _).mp hJbot
    have hZeq : Subgroup.center (↥data.H ⧸ Q) = chief.N.map (QuotientGroup.mk' Q) :=
      le_antisymm hZle hNhatLe
    have heven : Even data.q := by
      refine OddOrder.RepresentationTheory.even_of_card_eq_prime_pow_succ_of_class_two
        chief.p_prime (hpK.to_quotient Q) ?_ ?_ hHhatCard
      · rw [hZeq]
        exact hNhatCard
      · rw [hcommHat, ← hZeq]
    exact (Nat.not_even_iff_odd.mpr hqodd) heven
  · -- `J = ⊤`: `Ĥ` is abelian, contradicting `|Ĥ'| = p`
    have hZtop : Subgroup.center (↥data.H ⧸ Q) = ⊤ := by
      rw [eq_top_iff]
      intro h _
      have hmemJ : π h ∈ J := by
        rw [hJtop]
        exact Subgroup.mem_top _
      obtain ⟨z, hz, hzeq⟩ := hmemJ
      have hker : z⁻¹ * h ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hzeq, inv_mul_cancel]
      have hmem : z⁻¹ * h ∈ Subgroup.center (↥data.H ⧸ Q) :=
        hNhatLe (hπker ▸ hker)
      have hsplit : h = z * (z⁻¹ * h) := by group
      rw [hsplit]
      exact Subgroup.mul_mem _ hz hmem
    have hcommbot : commutator (↥data.H ⧸ Q) = ⊥ := by
      rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
      intro g _ h _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_center_iff.mp (hZtop ▸ Subgroup.mem_top h) g
    rw [hcommbot] at hcommHat
    have : Nat.card ↥(⊥ : Subgroup (↥data.H ⧸ Q)) = chief.p := hcommHat ▸ hNhatCard
    rw [Subgroup.card_bot] at this
    exact absurd this.symm chief.p_prime.one_lt.ne'

end CaseB

section CaseA

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

open scoped Pointwise

/-- **Case (a) endgame**: if `U` fixes the order-`p` factor `S₀ ≠ ⊥` pointwise, it fixes every
`U W₁`-translate pointwise (conjugating the acting element back into the normal kernel `U`),
hence all of `H̄ = ⨆ translates` — contradicting (9.4.b) (`U_noncentral_on_quotient`). -/
theorem caseA_fixed_contradiction [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    {S₀ : Subgroup (↥data.H ⧸ chief.N)} (hS₀ne : S₀ ≠ ⊥)
    (hfix : ∀ (v : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))),
      ∀ s ∈ S₀, quotientMulAutHom chief.N_aInvariant ↑v s = s) :
    False := by
  have hUnorm : (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer data.typeP.W1_normalizes_U)
  have hspan := iSup_smul_eq_top_of_irreducible
    (φ := quotientMulAutHom chief.N_aInvariant) chief.quotient_chiefFactor hS₀ne
  -- every translate is fixed pointwise by the `U`-part
  have hfixT : ∀ (a : ↥(data.typeP.U ⊔ data.typeP.W1)),
      (quotientMulAutHom chief.N_aInvariant a) • S₀ ≤
        OddOrder.GroupTheory.fixedSubgroup (quotientMulAutHom chief.N_aInvariant)
          (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) := by
    intro a h hh
    rw [Subgroup.mem_smul_pointwise_iff_exists] at hh
    obtain ⟨s, hs, rfl⟩ := hh
    rw [OddOrder.GroupTheory.mem_fixedSubgroup]
    intro l hl
    have hc : a⁻¹ * l * a ∈ data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1) := by
      simpa using hUnorm.conj_mem l hl a⁻¹
    have hkey := hfix ⟨a⁻¹ * l * a, hc⟩ s hs
    rw [MulAut.smul_def, ← MulAut.mul_apply, ← map_mul,
      show l * a = a * (a⁻¹ * l * a) by group, map_mul, MulAut.mul_apply, hkey]
  have htop : OddOrder.GroupTheory.fixedSubgroup (quotientMulAutHom chief.N_aInvariant)
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    exact iSup_le hfixT
  exact chief.U_noncentral_on_quotient htop

/-- **The odd-order exponent chain** (Peterfalvi (11.7), case (a) arithmetic): a multiplicative,
nowhere-zero `f : A → ZMod p` satisfying `f v · f (σ v) = 1` for an automorphism `σ` of odd
exponent on a group of odd order is identically `1`.

From the relation, `f ∘ σ` inverts `f`, so `f ∘ σ² = f`; as `σ = (σ²)^((m+1)/2)` for odd `m`
with `σ^m = 1`, also `f ∘ σ = f`, whence `f v² = 1`; and `f v` has odd multiplicative order
(`f v^(orderOf v) = 1` with `|A|` odd), so `f v = x = x^d = (x²)^k · x` forces `f v = 1`. -/
theorem chain_exponent_eq_one {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    (f : A → ZMod p) (hmul : ∀ u v, f (u * v) = f u * f v) (hne : ∀ u, f u ≠ 0)
    (hAodd : Odd (Nat.card A)) (σ : MulAut A) {m : ℕ} (hmodd : Odd m) (hσm : σ ^ m = 1)
    (hrel : ∀ v, f v * f (σ v) = 1) (v : A) : f v = 1 := by
  classical
  -- `f 1 = 1`
  have hf1 : f 1 = 1 := by
    have h := hmul 1 1
    rw [one_mul] at h
    have h2 : f 1 * f 1 = f 1 * 1 := by rw [mul_one, ← h]
    exact mul_left_cancel₀ (hne 1) h2
  -- `f` of powers
  have hpow : ∀ (w : A) (n : ℕ), f (w ^ n) = f w ^ n := by
    intro w n
    induction n with
    | zero => simpa using hf1
    | succ n ih => rw [pow_succ, pow_succ, hmul, ih]
  -- `f ∘ σ²` fixes `f`, hence so does `f ∘ σ` (odd exponent)
  have hστ : ∀ w, f (σ w) = (f w)⁻¹ := by
    intro w
    have h := congrArg (fun t => (f w)⁻¹ * t) (hrel w)
    simpa [← mul_assoc, inv_mul_cancel₀ (hne w)] using h
  have hσ2 : ∀ w, f ((σ ^ 2) w) = f w := by
    intro w
    have h1 : (σ ^ 2) w = σ (σ w) := by
      rw [sq]
      rfl
    rw [h1, hστ, hστ, inv_inv]
  have hσ2n : ∀ (n : ℕ) (w : A), f (((σ ^ 2) ^ n) w) = f w := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
        intro w
        rw [pow_succ, MulAut.mul_apply, ih, hσ2]
  have hσfix : ∀ w, f (σ w) = f w := by
    intro w
    obtain ⟨k, hk⟩ := hmodd
    have hσeq : σ = (σ ^ 2) ^ (k + 1) := by
      rw [← pow_mul]
      have : 2 * (k + 1) = m + 1 := by omega
      rw [this, pow_succ, hσm, one_mul]
    conv_lhs => rw [hσeq]
    exact hσ2n (k + 1) w
  -- `(f v)² = 1`
  have hsq : f v * f v = 1 := by
    have := hrel v
    rwa [hσfix] at this
  -- `f v` has odd order: `f v ^ orderOf v = 1`
  have hvord : f v ^ orderOf v = 1 := by
    rw [← hpow, pow_orderOf_eq_one, hf1]
  have hdodd : Odd (orderOf v) :=
    hAodd.of_dvd_nat (orderOf_dvd_natCard v)
  obtain ⟨k, hk⟩ := hdodd
  -- `f v = f v ^ (2k+1) = (f v²)^k · f v = f v` ... `1 = f v ^ d = f v`
  calc f v = (f v * f v) ^ k * f v := by rw [hsq, one_pow, one_mul]
    _ = f v ^ (2 * k + 1) := by ring
    _ = f v ^ orderOf v := by rw [hk]
    _ = 1 := hvord

/-- **Closure pullback along a surjection**: if `T` generates `Γ'` and contains `1`, its
preimage generates `Γ` (lifts of a product decomposition, kernel elements landing in the
preimage via `1 ∈ T`). -/
theorem closure_preimage_eq_top_of_closure_eq_top {Γ Γ' : Type*} [Group Γ] [Group Γ']
    (π : Γ →* Γ') (hsurj : Function.Surjective π) {T : Set Γ'}
    (h1T : (1 : Γ') ∈ T) (hT : Subgroup.closure T = ⊤) :
    Subgroup.closure (π ⁻¹' T) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : π g ∈ Subgroup.closure T := hT ▸ Subgroup.mem_top _
  refine Subgroup.closure_induction
    (p := fun t _ => ∀ g' : Γ, π g' = t → g' ∈ Subgroup.closure (π ⁻¹' T))
    ?_ ?_ ?_ ?_ hg g rfl
  · intro t ht g' hg'
    exact Subgroup.subset_closure (by simp only [Set.mem_preimage, hg']; exact ht)
  · intro g' hg'
    exact Subgroup.subset_closure (by simp only [Set.mem_preimage, hg']; exact h1T)
  · intro t₁ t₂ _ _ ih₁ ih₂ g' hg'
    obtain ⟨x, hx⟩ := hsurj t₁
    have h2 : π (x⁻¹ * g') = t₂ := by rw [map_mul, map_inv, hx, hg']; group
    have hmem := Subgroup.mul_mem _ (ih₁ x hx) (ih₂ _ h2)
    simpa using hmem
  · intro t _ ih g' hg'
    have h2 : π g'⁻¹ = t := by rw [map_inv, hg', inv_inv]
    have hmem := Subgroup.inv_mem _ (ih g'⁻¹ h2)
    simpa using hmem

/-- **The exponent function of an action on an order-`p` subgroup**: for a family
`φ : A →* MulAut Γ` of automorphisms each mapping `T` (of order `p`) into itself, there is
`e : A → ℕ` with `φ v s = s^(e v)` on `T`, no value divisible by `p`, *multiplicative mod `p`*,
and such that `e v ≡ 1` forces `φ v` to fix `T` pointwise. -/
theorem exists_exponent_fun_of_card_prime {Γ A : Type*} [Group Γ] [Group A] {p : ℕ}
    (hp : p.Prime) {T : Subgroup Γ} (hT : Nat.card ↥T = p)
    (φ : A →* MulAut Γ) (hmem : ∀ (v : A), ∀ s ∈ T, φ v s ∈ T) :
    ∃ e : A → ℕ,
      (∀ v, ¬ p ∣ e v) ∧
      (∀ v, ∀ s ∈ T, φ v s = s ^ e v) ∧
      (∀ u v, ((e (u * v) : ZMod p)) = (e u : ZMod p) * (e v : ZMod p)) ∧
      (∀ v, (e v : ZMod p) = 1 → ∀ s ∈ T, φ v s = s) := by
  classical
  choose e hep he using fun v : A =>
    exists_pow_eq_of_mapsTo_of_card_prime hp hT (φ v) (hmem v)
  have : Finite ↥T := Nat.finite_of_card_ne_zero (hT ▸ hp.pos.ne')
  have : Fact p.Prime := ⟨hp⟩
  have : IsCyclic ↥T := isCyclic_of_prime_card hT
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := ↥T)
  have htord : orderOf (↑t : Γ) = p := by
    have h := orderOf_injective T.subtype T.subtype_injective t
    rw [show T.subtype t = ↑t from rfl] at h
    rw [h, orderOf_eq_card_of_forall_mem_zpowers ht, hT]
  have htfin : IsOfFinOrder (↑t : Γ) := by
    rw [← orderOf_pos_iff, htord]
    exact hp.pos
  have hcong : ∀ k l : ℕ, (↑t : Γ) ^ k = (↑t : Γ) ^ l → (k : ZMod p) = l := by
    intro k l hkl
    have hmod := htfin.pow_eq_pow_iff_modEq.mp hkl
    rw [htord] at hmod
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  refine ⟨e, hep, he, ?_, ?_⟩
  · -- multiplicativity mod `p`, extracted at the generator
    intro u v
    have h2 := he (u * v) ↑t t.2
    rw [map_mul, MulAut.mul_apply, he v ↑t t.2, map_pow, he u ↑t t.2, ← pow_mul] at h2
    have h3 := hcong _ _ h2
    rw [Nat.cast_mul] at h3
    exact h3.symm
  · -- `e v ≡ 1` pointwise-fixes `T`
    intro v hv1 s hs
    rw [he v s hs]
    have hordfin : 0 < orderOf (⟨s, hs⟩ : ↥T) := by
      rw [orderOf_pos_iff]
      exact isOfFinOrder_of_finite _
    have hords : orderOf s = orderOf (⟨s, hs⟩ : ↥T) := by
      have h := orderOf_injective T.subtype T.subtype_injective (⟨s, hs⟩ : ↥T)
      rw [show T.subtype ⟨s, hs⟩ = s from rfl] at h
      exact h
    have horddvd : orderOf s ∣ p := by
      rw [hords, ← hT]
      exact orderOf_dvd_natCard _
    have hfin : IsOfFinOrder s := by
      rw [← orderOf_pos_iff, hords]
      exact hordfin
    have hmod : e v ≡ 1 [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ _).mp (by simpa using hv1)
    have hmods : e v ≡ 1 [MOD orderOf s] := Nat.ModEq.of_dvd horddvd hmod
    calc s ^ e v = s ^ 1 := hfin.pow_eq_pow_iff_modEq.mpr hmods
      _ = s := pow_one s

/-- **Case (a) exponent reduction** (Peterfalvi (11.7), the `phi = 1` step abstracted): if `U`
acts on the order-`p` subgroup `S₀ ≤ H̄` (`hmem`), `|U|` is odd, and there is an odd-order
automorphism `σ` of the acting `U`-group whose conjugate action *inverts* the `v`-action on `S₀`
— the chain relation `(φ v) ∘ (φ (σ v)) = id` on `S₀` — then `U` fixes `S₀` pointwise.

This wires the exponent morphism `e : U → ℤ/p` (`exists_exponent_fun_of_card_prime`) to
`chain_exponent_eq_one`: the chain relation gives `e(v)·e(σ v) ≡ 1 (mod p)` (both actions are
exponentiations, and `S₀` is cyclic of order `p`), so `e ≡ 1`, i.e. `φ v` fixes `S₀`.  The chain
relation is Peterfalvi's `phi_{w_1}(u)·phi_{w_2}(u) = 1`, the antisymmetry of the commutator form
`D`; supplying it (with `σ` the `W₁`-generator's inverse-conjugation action on `U`) discharges the
`hfix` obligation of `caseA_fixed_contradiction`. -/
theorem caseA_fixes_of_action_chain [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    {S₀ : Subgroup (↥data.H ⧸ chief.N)} (hcardS₀ : Nat.card ↥S₀ = chief.p)
    (hmem : ∀ (v : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))),
      ∀ s ∈ S₀, quotientMulAutHom chief.N_aInvariant ↑v s ∈ S₀)
    (hAodd : Odd (Nat.card ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))))
    (σ : MulAut ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
    {m : ℕ} (hmodd : Odd m) (hσm : σ ^ m = 1)
    (hchain : ∀ (v : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))),
      ∀ s ∈ S₀, quotientMulAutHom chief.N_aInvariant ↑v
        (quotientMulAutHom chief.N_aInvariant ↑(σ v) s) = s) :
    ∀ (v : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))),
      ∀ s ∈ S₀, quotientMulAutHom chief.N_aInvariant ↑v s = s := by
  classical
  have := Fact.mk chief.p_prime
  -- the `U`-action morphism `φ : A →* MulAut (H̄)`
  set φ : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) →*
      MulAut (↥data.H ⧸ chief.N) :=
    (quotientMulAutHom chief.N_aInvariant).comp
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype with hφ
  have hφv : ∀ v, φ v = quotientMulAutHom chief.N_aInvariant ↑v := fun _ => rfl
  obtain ⟨e, hep, he, hemul, hefix⟩ :=
    exists_exponent_fun_of_card_prime chief.p_prime hcardS₀ φ
      (fun v s hs => by rw [hφv]; exact hmem v s hs)
  set f : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) → ZMod chief.p :=
    fun v => (e v : ZMod chief.p) with hf
  have hne : ∀ v, f v ≠ 0 := fun v h =>
    hep v ((CharP.cast_eq_zero_iff (ZMod chief.p) chief.p (e v)).mp h)
  -- `S₀` is cyclic of order `p`; fix a generator `g`
  have hfin : Finite ↥S₀ := Nat.finite_of_card_ne_zero (hcardS₀ ▸ chief.p_prime.pos.ne')
  have : IsCyclic ↥S₀ := isCyclic_of_prime_card hcardS₀
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥S₀)
  have hgS : (g : ↥data.H ⧸ chief.N) ∈ S₀ := g.2
  have hordg : orderOf (g : ↥data.H ⧸ chief.N) = chief.p := by
    have h := orderOf_injective S₀.subtype S₀.subtype_injective g
    rw [show S₀.subtype g = (g : ↥data.H ⧸ chief.N) from rfl] at h
    rw [h, orderOf_eq_card_of_forall_mem_zpowers hg, hcardS₀]
  have hgfin : IsOfFinOrder (g : ↥data.H ⧸ chief.N) := by
    rw [← orderOf_pos_iff, hordg]; exact chief.p_prime.pos
  -- the chain relation `f v · f (σ v) = 1`
  have hrel : ∀ v, f v * f (σ v) = 1 := by
    intro v
    have hσvS := hmem (σ v) _ hgS
    have e1 : quotientMulAutHom chief.N_aInvariant ↑(σ v) (g : ↥data.H ⧸ chief.N)
        = (g : ↥data.H ⧸ chief.N) ^ e (σ v) := by rw [← hφv (σ v)]; exact he (σ v) _ hgS
    have hstep := hchain v (g : ↥data.H ⧸ chief.N) hgS
    rw [e1, ← hφv v, map_pow, he v _ hgS, ← pow_mul] at hstep
    have hmodp : e v * e (σ v) ≡ 1 [MOD chief.p] := by
      have hpow : (g : ↥data.H ⧸ chief.N) ^ (e v * e (σ v)) = (g : ↥data.H ⧸ chief.N) ^ 1 := by
        rw [pow_one]; exact hstep
      have h := hgfin.pow_eq_pow_iff_modEq.mp hpow
      rwa [hordg] at h
    have h1 : ((e v * e (σ v) : ℕ) : ZMod chief.p) = ((1 : ℕ) : ZMod chief.p) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmodp
    simpa [hf, Nat.cast_mul] using h1
  -- conclude
  intro v s hs
  have hf1 : f v = 1 := chain_exponent_eq_one f (fun u v => hemul u v) hne hAodd σ hmodd hσm hrel v
  rw [← hφv v]; exact hefix v hf1 s hs

/-- **Case (a), the commutator-form chain relation** (Peterfalvi (11.7), non-Galois case).  For the
order-`p` `U`-invariant `S₀ ≤ H̄` there is an automorphism `σ` of the acting `U`-group, of odd
order,
whose conjugate action inverts every `v`-action on `S₀` — the chain relation
`(φ v) ∘ (φ (σ v)) = id`.
Fed to `caseA_fixes_of_action_chain`, this forces `U` to fix `S₀` pointwise (whence the (11.7)
contradiction in `chief_H0_eq_bot`).

The `σ` is conjugation `MulAut.conjNormal w` by the *specific* element `w = b₀⁻¹ a₀ ∈ U W₁` at which
the commutator form `D(y,z) = ⁅ẑ, ŷ⁆` on `Ĥ = H/Q` (`Q` maximal in `H₀`) is nontrivial — **not** a
generic generator, so it is produced together with the chain relation (hence the existential).
Proof
(Coq `FTtype34_Fcore_kernel_trivial`, `PFsection11.v`:365-540, translated top-to-bottom):
* STEP 0 — `U` centralizes `N = H₀` (Wielandt (9.1) via `C_{H₀}(W₁) = 1`, Coq
`FTtype34_facts.cH0U`);
* STEP 1/2 — `Ĥ = H/Q` is class-`2` with `Ĥ' = H₀/Q = N̂` central of order `p`
  (`exists_normal_subgroup_index_prime`, `quotient_classTwo_structure`); `D` is antisymmetric
  (`⁅b,a⁆ = ⁅a,b⁆⁻¹`) and bilinear (`commutatorElement_*`, central commutators);
* STEP 3/4 — the `U`-action on `S₀` is exponentiation by `e : U → ℤ/p`
  (`exists_exponent_fun_of_card_prime`); the `L`-conjugates `Φ a • S₀` span `H̄`
  (`iSup_smul_eq_top_of_irreducible`), so `D` is nontrivial for some `xC a₀, xC b₀`
  (`hntrivD`, else `Ĥ' = 1`);
* STEP 5/6 — the action of `v ∈ U` on the second `D`-slot is `^{e(a⁻¹ v a)}` (`hDXn`), and applying
  it to both slots while `v` centralises the commutator `⁅xC b₀, xC a₀⁆ ∈ N` gives
  `e(b₀⁻¹ v b₀)·e(a₀⁻¹ v a₀) ≡ 1 (mod p)` (`hcore`, Coq `phi_w12`);
* STEP 7 — reparametrising yields `e(v)·e(w v w⁻¹) ≡ 1` for `w = b₀⁻¹ a₀`, whence
  `chain_exponent_eq_one`-style inversion; `σ = conjNormal w`, `m = orderOf w` odd (`|G|` odd).

The type-II disjunct of the general `TypesIIIIIIVSetup` is excluded here (it is needed only for
`|W₂| = chief.p`); Peterfalvi (11.7) is a type III/IV statement and the caller supplies the
restriction. -/
theorem caseA_commutator_chain [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (htype : OddOrder.GroupTheory.IsTypeIII M ∨ OddOrder.GroupTheory.IsTypeIV M)
    (hpK : IsPGroup chief.p ↥data.H) (hNcomm : chief.N = commutator ↥data.H)
    (hNne : chief.N ≠ ⊥)
    {S₀ : Subgroup (↥data.H ⧸ chief.N)} (hcardS₀ : Nat.card ↥S₀ = chief.p)
    (hmem : ∀ (v : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))),
      ∀ s ∈ S₀, quotientMulAutHom chief.N_aInvariant ↑v s ∈ S₀) :
    ∃ (σ : MulAut ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))) (m : ℕ),
      Odd m ∧ σ ^ m = 1 ∧
      ∀ (v : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))),
        ∀ s ∈ S₀, quotientMulAutHom chief.N_aInvariant ↑v
          (quotientMulAutHom chief.N_aInvariant ↑(σ v) s) = s := by
  classical
  have := Fact.mk chief.p_prime
  set L := data.typeP.U ⊔ data.typeP.W1 with hLdef
  set φ := OddOrder.Peterfalvi.S11.typeP_conjAction data.typeP with hφdef
  -- `U ◁ L` (the Frobenius kernel), so conjugation `σ = conjNormal w` acts on `U.subgroupOf L`.
  have hUnorm : (data.typeP.U.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer data.typeP.W1_normalizes_U)
  -- ###########################################################################
  -- STEP 0: `U` centralizes `N = H₀` (Peterfalvi (8.5.a) / (11.6), Wielandt (9.1)).
  -- This is the `cH0U` of Coq `FTtype34_facts`; it needs `|W₂| = chief.p` (types III/IV).
  -- ###########################################################################
  -- `H₀ = N.map H.subtype ≠ ⊥`.
  have hH0ne : chief.H0 ≠ ⊥ := by
    rw [chief.H0_eq]
    intro h
    exact hNne (Subgroup.map_injective (data.H).subtype_injective (by rw [h, Subgroup.map_bot]))
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  -- **`data` is of type III or IV** (`htype`, hypothesis).  Peterfalvi (11.7) (Hypothesis (11.2))
  -- is stated only for types III/IV; the `|W₂| = chief.p` identity below
  -- (`chief.typeIII_IV_p_eq_W2`),
  -- needed for the (9.6) fixed-point-free step `C_{H₀}(W₁) = 1` yielding `U ≤ C(H₀)` (Coq
  -- `FTtype34_facts.cH0U`), requires it. The commutator-form antisymmetry argument is
  -- type-agnostic.
  -- `|W₂| = chief.p` (types III/IV).
  have hW2p : Nat.card ↥data.typeP.W2 = chief.p := chief.typeIII_IV_p_eq_W2 htype
  -- The `W₂ ⊓ H₀ = ⊥` core (Peterfalvi (9.6), `chief_W2_inf_H0_eq_bot` replicated at chief level):
  -- `|C_{H̄}(W₁)| = p` (`coprimeFrobeniusChiefFactor_card`) shows `W̄₂ ≠ ⊥`, and `|W₂| = p` prime
  -- rules out `W₂ ⊆ H₀`.
  have hW2H0bot : data.typeP.W2 ⊓ chief.H0 = ⊥ := by
    have hHH : data.typeP.H = data.typeP.H := rfl
    have hH0le : chief.H0 ≤ data.typeP.H := chief.H0_lt_H.le
    set F : Subgroup ↥data.typeP.H :=
      OddOrder.GroupTheory.fixedSubgroup φ (data.typeP.W1.subgroupOf L) with hF
    have hFW2 : F.map data.typeP.H.subtype = data.typeP.W2 := by
      rw [hF, hφdef, OddOrder.Peterfalvi.S11.typeP_fixedSubgroup_map data.typeP le_sup_right,
        OddOrder.Peterfalvi.S11.typeP_H_inf_centralizer_W1]
    have hH0eq : chief.H0 = chief.N.map data.typeP.H.subtype := chief.H0_eq
    set act := OddOrder.Peterfalvi.S11.typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant
      with hact
    have hcopHW1 : Nat.Coprime
        (Nat.card ↥(data.typeP.W1.subgroupOf L)) (Nat.card ↥data.typeP.H) :=
      (OddOrder.Peterfalvi.S11.typeP_coprime_H_uW1 data.typeP hU).symm.coprime_dvd_left
        (Subgroup.card_subgroup_dvd_card _)
    have : Group.IsSolvable ↥data.typeP.H :=
      (OddOrder.Peterfalvi.S11.typeP_coprimeAction data.typeP hU).H_solvable
    have hmap : F.map (QuotientGroup.mk' chief.N) = act.fixedByE :=
      OddOrder.GroupTheory.map_fixedSubgroup_eq_fixedSubgroup_quotient chief.N_aInvariant hcopHW1
        (Or.inr inferInstance)
    have hUnormE : act.U.Normal :=
      (OddOrder.Peterfalvi.S11.typeP_uW1_frobenius data.typeP hU).isNormal
    have hEcyc : IsCyclic ↥act.fixedByE :=
      OddOrder.Peterfalvi.S11.typeP_quotient_fixedByE_cyclic data.typeP hU chief.N_aInvariant
    have hK1 : Nat.card (↥data.typeP.H ⧸ chief.N) ≠ 1 := by
      have hNtop : chief.N ≠ ⊤ := by
        intro htop
        have hH0H : chief.H0 = data.typeP.H := by
          rw [hH0eq, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
        exact absurd (hH0H ▸ chief.H0_lt_H) (lt_irrefl _)
      exact fun h => hNtop (Subgroup.index_eq_one.mp h)
    have hcardE : Nat.card ↥act.fixedByE = chief.p :=
      (OddOrder.Peterfalvi.S11.coprimeFrobeniusChiefFactor_card act hUnormE chief.p_prime
        chief.quotient_elementaryAbelian chief.quotient_chiefFactor
        chief.U_noncentral_on_quotient hEcyc hK1).2
    have hp := chief.p_prime
    have hdvd : Nat.card ↥(data.typeP.W2 ⊓ chief.H0 : Subgroup G) ∣ chief.p := by
      rw [← hW2p]; exact Subgroup.card_dvd_of_le inf_le_left
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hpp
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have hle : data.typeP.W2 ⊓ chief.H0 = data.typeP.W2 :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (hW2p.trans hpp.symm))
      have hW2H0 : data.typeP.W2 ≤ chief.H0 := hle ▸ inf_le_right
      have hFN : F ≤ chief.N := by
        have hmm : F.map data.typeP.H.subtype ≤ chief.N.map data.typeP.H.subtype := by
          rw [hFW2, ← hH0eq]; exact hW2H0
        exact (Subgroup.map_le_map_iff_of_injective data.typeP.H.subtype_injective).mp hmm
      have hFbot : act.fixedByE = ⊥ := by
        rw [← hmap]
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
        exact hFN
      rw [hFbot, Subgroup.card_bot] at hcardE
      exact chief.p_prime.one_lt.ne' hcardE.symm
  -- `U` centralizes `H₀` (Wielandt (9.1) via the fpf condition `C_{H₀}(W₁) = 1`).
  have hUcentH0 : data.typeP.U ≤ Subgroup.centralizer (chief.H0 : Set G) := by
    have hH0le : chief.H0 ≤ data.typeP.H := chief.H0_lt_H.le
    have hUM : data.typeP.U ≤ M := data.typeP.U_le.trans (Subgroup.map_subtype_le _)
    have hUEnorm : data.typeP.U ⊔ data.typeP.W1 ≤ Subgroup.normalizer (chief.H0 : Set G) :=
      sup_le (hUM.trans chief.H0_normalized_by_M)
        (data.typeP.W1_le.trans chief.H0_normalized_by_M)
    have : Group.IsNilpotent ↥data.typeP.H := by
      rw [data.typeP.H_eq]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent M
    have : Group.IsSolvable ↥data.typeP.H := IsNilpotent.to_isSolvable
    have hsolv : Group.IsSolvable ↥chief.H0 :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hH0le).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hH0le).symm.injective
    have hcop : Nat.Coprime (Nat.card ↥chief.H0)
        (Nat.card ↥(data.typeP.U ⊔ data.typeP.W1)) :=
      Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hH0le)
        (OddOrder.Peterfalvi.S11.typeP_coprime_H_uW1 data.typeP hU)
    -- fpf: any `H₀`-element centralized by `W₁` lies in `W₂ ⊓ H₀ = ⊥`.
    have hfpf : ∀ n ∈ chief.H0, (∀ w ∈ data.typeP.W1, w * n * w⁻¹ = n) → n = 1 := by
      intro n hn hcent
      have hnW2 : n ∈ data.typeP.W2 := by
        rw [← OddOrder.Peterfalvi.S11.typeP_H_inf_centralizer_W1 data.typeP]
        refine Subgroup.mem_inf.mpr ⟨hH0le hn, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        exact fun w hw => mul_inv_eq_iff_eq_mul.mp (hcent w hw)
      have hmem : n ∈ data.typeP.W2 ⊓ chief.H0 := ⟨hnW2, hn⟩
      rw [hW2H0bot] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact OddOrder.GroupTheory.frobenius_kernel_centralizes_of_complement_fpf hUEnorm
      (OddOrder.Peterfalvi.S11.typeP_uW1_frobenius data.typeP hU) hsolv hcop hfpf
  -- Translate to the `φ`-action form: `φ v` fixes every `N`-element pointwise, for `v ∈ U`.
  have hUcentN : ∀ (v : ↥L), (v : G) ∈ data.typeP.U → ∀ n : ↥data.typeP.H, n ∈ chief.N →
      φ v n = n := by
    intro v hvU n hnN
    have hnH0 : (n : G) ∈ chief.H0 := by rw [chief.H0_eq]; exact ⟨n, hnN, rfl⟩
    refine Subtype.ext ?_
    rw [hφdef, OddOrder.Peterfalvi.S11.typeP_conjAction_apply data.typeP v n]
    have hcent := Subgroup.mem_centralizer_iff.mp (hUcentH0 hvU) (n : G) hnH0
    rw [← hcent]; group
  -- ###########################################################################
  -- STEP 1: the class-`2` structure of `Ĥ = H/Q` (`Q` maximal in `H₀ = N`).
  -- ###########################################################################
  obtain ⟨Q, hQnorm, hQle, hRQ, hcardQ⟩ :=
    exists_normal_subgroup_index_prime chief.p_prime hpK hNne
  have := hQnorm
  obtain ⟨hNhatCard, hcommHat, hNhatLe⟩ :=
    quotient_classTwo_structure chief.p_prime hQnorm hQle hRQ hcardQ hNcomm
  -- `mk'Q : H → H/Q` and `π : H/Q → H/N`.
  set hat : ↥data.typeP.H →* (↥data.typeP.H ⧸ Q) := QuotientGroup.mk' Q with hhatdef
  set π : (↥data.typeP.H ⧸ Q) →* (↥data.typeP.H ⧸ chief.N) :=
    QuotientGroup.map Q chief.N (MonoidHom.id ↥data.typeP.H) (by simpa using hQle) with hπdef
  have hπmk : ∀ x : ↥data.typeP.H, π (hat x) = (QuotientGroup.mk' chief.N) x := fun x => rfl
  -- `N̂ = N.map hat` is central of order `p`, equal to `(H/Q)'`.
  set Nhat : Subgroup (↥data.typeP.H ⧸ Q) := chief.N.map hat with hNhatdef
  have hNhatCentral : Nhat ≤ Subgroup.center (↥data.typeP.H ⧸ Q) := hNhatLe
  -- ###########################################################################
  -- STEP 2: the commutator form `D y z = ⁅hat z, hat y⁆` on `Ĥ`.
  -- ###########################################################################
  -- Every commutator `⁅hat b, hat a⁆` lies in `N̂ = (H/Q)'`, hence is central.
  have hDmem : ∀ y z : ↥data.typeP.H, ⁅hat z, hat y⁆ ∈ Nhat := by
    intro y z
    have : ⁅hat z, hat y⁆ ∈ commutator (↥data.typeP.H ⧸ Q) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rwa [hcommHat] at this
  have hDcentral : ∀ y z : ↥data.typeP.H, ⁅hat z, hat y⁆ ∈ Subgroup.center (↥data.typeP.H ⧸ Q) :=
    fun y z => hNhatCentral (hDmem y z)
  -- `D y z = 1` when `z ∈ N` (image `hat z ∈ N̂` is central).
  have hD_N_1 : ∀ (y : ↥data.typeP.H) {z : ↥data.typeP.H}, z ∈ chief.N → ⁅hat z, hat y⁆ = 1 := by
    intro y z hz
    have hzc : hat z ∈ Subgroup.center (↥data.typeP.H ⧸ Q) :=
      hNhatCentral (Subgroup.mem_map_of_mem _ hz)
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hzc (hat y)).symm
  -- antisymmetry.
  have hDsym : ∀ y z : ↥data.typeP.H, (⁅hat z, hat y⁆)⁻¹ = ⁅hat y, hat z⁆ :=
    fun y z => commutatorElement_inv _ _
  -- morphism in `z` (class-`2` linearity, values central).
  have hDmul : ∀ (y z t : ↥data.typeP.H),
      ⁅hat (z * t), hat y⁆ = ⁅hat z, hat y⁆ * ⁅hat t, hat y⁆ := by
    intro y z t
    have hcomm : Commute (⁅hat t, hat y⁆) (⁅hat z, hat y⁆) :=
      (Subgroup.mem_center_iff.mp (hDcentral y z) _)
    rw [map_mul, commutatorElement_mul_left_of_center (hDcentral y t) (hat z), hcomm.eq]
  -- ###########################################################################
  -- STEP 3: the exponent function `e` of the `U`-action on `S₀ ≤ H̄`.
  -- ###########################################################################
  set L' := data.typeP.U.subgroupOf L with hL'def
  set Φ : ↥L' →* MulAut (↥data.typeP.H ⧸ chief.N) :=
    (quotientMulAutHom chief.N_aInvariant).comp L'.subtype with hΦdef
  have hΦv : ∀ v : ↥L', Φ v = quotientMulAutHom chief.N_aInvariant ↑v := fun _ => rfl
  obtain ⟨e, hep, he, hemul, _hefix⟩ :=
    exists_exponent_fun_of_card_prime chief.p_prime hcardS₀ Φ
      (fun v s hs => by rw [hΦv]; exact hmem v s hs)
  -- `S₀` is cyclic of order `p` with generator `g`.
  have hfin : Finite ↥S₀ := Nat.finite_of_card_ne_zero (hcardS₀ ▸ chief.p_prime.pos.ne')
  have : IsCyclic ↥S₀ := isCyclic_of_prime_card hcardS₀
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥S₀)
  have hgS : (g : ↥data.typeP.H ⧸ chief.N) ∈ S₀ := g.2
  have hordg : orderOf (g : ↥data.typeP.H ⧸ chief.N) = chief.p := by
    have h := orderOf_injective S₀.subtype S₀.subtype_injective g
    rw [show S₀.subtype g = (g : ↥data.typeP.H ⧸ chief.N) from rfl] at h
    rw [h, orderOf_eq_card_of_forall_mem_zpowers hg, hcardS₀]
  have hgfin : IsOfFinOrder (g : ↥data.typeP.H ⧸ chief.N) := by
    rw [← orderOf_pos_iff, hordg]; exact chief.p_prime.pos
  -- ###########################################################################
  -- STEP 7 (assembly): given a `W₁`-element `w` realising the antisymmetry
  -- `e(v)·e(w v w⁻¹) ≡ 1 (mod p)`, take `σ = conjNormal w` and `m = orderOf w`.
  -- ###########################################################################
  suffices hantisym : ∃ (w : ↥L),
      ∀ v : ↥L', (e v : ZMod chief.p) * (e (MulAut.conjNormal w v) : ZMod chief.p) = 1 by
    obtain ⟨w, hrel⟩ := hantisym
    have := hUnorm
    refine ⟨MulAut.conjNormal w, orderOf w, ?_, ?_, ?_⟩
    · -- `orderOf w` is odd (divides `|G|`).
      exact hG.odd.of_dvd_nat ((orderOf_dvd_natCard w).trans (Subgroup.card_subgroup_dvd_card L))
    · -- `σ^m = conjNormal (w^m) = conjNormal 1 = 1`.
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    · -- the chain relation on `S₀`, via the exponent identity `e(v)·e(σ v) ≡ 1`.
      intro v s hs
      rw [← hΦv v, ← hΦv (MulAut.conjNormal w v), he (MulAut.conjNormal w v) s hs,
        map_pow, he v _ hs, ← pow_mul]
      -- `s^{e(σv)·e(v)} = s` since `e(σv)·e(v) ≡ 1 (mod p)` and `s` has order dividing `p`.
      have hords : orderOf s ∣ chief.p := by
        have h := orderOf_injective S₀.subtype S₀.subtype_injective (⟨s, hs⟩ : ↥S₀)
        rw [show S₀.subtype ⟨s, hs⟩ = s from rfl] at h
        rw [h, ← hcardS₀]; exact orderOf_dvd_natCard _
      have hfin' : IsOfFinOrder s := by
        rw [← orderOf_pos_iff]
        rcases (Nat.eq_zero_or_pos (orderOf s)) with h0 | hpos
        · rw [h0] at hords
          exact absurd (Nat.eq_zero_of_zero_dvd hords) chief.p_prime.pos.ne'
        · exact hpos
      have hmodp : e v * e (MulAut.conjNormal w v) ≡ 1 [MOD chief.p] := by
        have h1 : ((e v * e (MulAut.conjNormal w v) : ℕ) : ZMod chief.p)
            = ((1 : ℕ) : ZMod chief.p) := by push_cast; rw [hrel v]
        exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h1
      have hmods : e v * e (MulAut.conjNormal w v) ≡ 1 [MOD orderOf s] :=
        Nat.ModEq.of_dvd hords hmodp
      calc s ^ (e v * e (MulAut.conjNormal w v))
          = s ^ 1 := hfin'.pow_eq_pow_iff_modEq.mpr hmods
        _ = s := pow_one s
  -- ###########################################################################
  -- STEP 4: the `W₁`-conjugation basis of `H̄` and the nontriviality of `D`.
  -- ###########################################################################
  -- Lift the generator `g` of `S₀` to `x ∈ H`.
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective chief.N (g : ↥data.typeP.H ⧸ chief.N)
  -- Conjugates `x_ a = φ a x ∈ H` (for `a ∈ L`); their images are the `Φ a`-translates of `g`.
  set xC : ↥L → ↥data.typeP.H := fun a => φ a x with hxCdef
  have hxCmk : ∀ a : ↥L, QuotientGroup.mk' chief.N (xC a) =
      quotientMulAutHom chief.N_aInvariant a (g : ↥data.typeP.H ⧸ chief.N) := by
    intro a
    rw [hxCdef]
    change QuotientGroup.mk' chief.N (φ a x) = _
    rw [← hx]
    rfl
  have hS₀ne : S₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardS₀
    exact chief.p_prime.one_lt.ne' hcardS₀.symm
  -- `⨆_{ŵ ∈ W1} Φ ŵ • S₀ = ⊤`: the `W₁`-conjugates of `S₀` span `H̄` (non-Galois structure).  Every
  -- `L`-conjugate `Φ a • S₀` reduces to a `W₁`-conjugate because `S₀` is `U`-invariant and
  -- `L = U W₁` is a Frobenius product.
  have hspanL : ⨆ (a : ↥L), quotientMulAutHom chief.N_aInvariant a • S₀ = ⊤ :=
    OddOrder.Peterfalvi.S11.iSup_smul_eq_top_of_irreducible
      (φ := quotientMulAutHom chief.N_aInvariant) chief.quotient_chiefFactor hS₀ne
  -- The images `mk'N (xC a) = Φ a • g` generate `H̄` (each generates `Φ a • S₀`, and these span).
  have hgenHbar : Subgroup.closure
      (Set.range (fun a : ↥L => QuotientGroup.mk' chief.N (xC a))) = ⊤ := by
    rw [eq_top_iff, ← hspanL]
    refine iSup_le fun a => ?_
    intro y hy
    rw [Subgroup.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    -- `s ∈ S₀ = <g>`, so `s = g^k`, and `Φ a • s = (Φ a • g)^k ∈ closure`.
    obtain ⟨k, hk⟩ := hg (⟨s, hs⟩ : ↥S₀)
    have hks : (g : ↥data.typeP.H ⧸ chief.N) ^ k = s := by
      have := congrArg (Subtype.val : ↥S₀ → _) hk
      simpa using this
    rw [MulAut.smul_def, ← hks, map_zpow, ← hxCmk a]
    exact (Subgroup.closure _).zpow_mem (Subgroup.subset_closure (Set.mem_range_self a)) k
  -- `Dx`: if `⁅hat (xC a), hat y⁆ = 1` for all `a`, then `⁅hat z, hat y⁆ = 1` for all `z`.
  -- The map `z ↦ ⁅hat z, hat y⁆` is a morphism (class-`2` linearity) killing `N`, and the
  -- `mk'N (xC a)`
  -- generate `H̄`, so it vanishes on all of `H`.
  have hDx : ∀ (y : ↥data.typeP.H), (∀ a : ↥L, ⁅hat (xC a), hat y⁆ = 1) →
      ∀ z : ↥data.typeP.H, ⁅hat z, hat y⁆ = 1 := by
    intro y hya z
    -- the morphism `ψ z = ⁅hat z, hat y⁆`.
    set ψ : ↥data.typeP.H →* (↥data.typeP.H ⧸ Q) :=
      MonoidHom.mk' (fun z => ⁅hat z, hat y⁆) (fun z t => hDmul y z t) with hψdef
    -- `ψ` kills `N` and factors through `H̄`, so `mk'N a = mk'N b → ψ a = ψ b`.
    have hψN : ∀ n : ↥data.typeP.H, n ∈ chief.N → ψ n = 1 := fun n hn => hD_N_1 y hn
    have hψeq : ∀ a b : ↥data.typeP.H,
        QuotientGroup.mk' chief.N a = QuotientGroup.mk' chief.N b → ψ a = ψ b := by
      intro a b hab
      have hmem : a * b⁻¹ ∈ chief.N := by
        have := QuotientGroup.eq_iff_div_mem.mp hab
        rwa [div_eq_mul_inv] at this
      have := hψN _ hmem
      rw [map_mul, map_inv, mul_inv_eq_one] at this
      exact this
    -- `ψ` vanishes on all of `H` since `mk'N (xC a)` generate `H̄` and `ψ (xC a) = 1`.
    have hker : ψ.ker = ⊤ := by
      rw [eq_top_iff]
      have hclos : Subgroup.closure ((QuotientGroup.mk' chief.N) ⁻¹'
          (insert 1 (Set.range (fun a : ↥L => QuotientGroup.mk' chief.N (xC a))))) = ⊤ :=
        closure_preimage_eq_top_of_closure_eq_top (QuotientGroup.mk' chief.N)
          (QuotientGroup.mk'_surjective _) (Set.mem_insert _ _)
          (by rw [eq_top_iff, ← hgenHbar]; exact Subgroup.closure_mono (Set.subset_insert _ _))
      rw [← hclos]
      refine (Subgroup.closure_le _).mpr fun w hw => ?_
      rw [Set.mem_preimage, Set.mem_insert_iff] at hw
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      rcases hw with h1 | ⟨a, ha⟩
      · have : ψ w = ψ 1 := hψeq w 1 (by rw [h1, map_one])
        rw [this, map_one]
      · rw [hψeq w (xC a) ha.symm]
        exact hya a
    have : z ∈ ψ.ker := hker ▸ Subgroup.mem_top z
    rwa [MonoidHom.mem_ker] at this
  -- `ntrivD`: some `⁅hat (xC a₀), hat (xC b₀)⁆ ≠ 1` (else `(H/Q)' = ⊥`, contradicting `|N̂| = p`).
  have hntrivD : ∃ a₀ b₀ : ↥L, ⁅hat (xC b₀), hat (xC a₀)⁆ ≠ 1 := by
    by_contra hall
    push Not at hall
    -- All `⁅hat (xC b), hat (xC a)⁆ = 1`, so `H/Q` is abelian.
    have hcommbot : commutator (↥data.typeP.H ⧸ Q) = ⊥ := by
      rw [commutator_eq_bot_iff_center_eq_top, eq_top_iff]
      intro w _
      -- `w = hat z` for some `z`; show `hat z` central.
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective Q w
      rw [Subgroup.mem_center_iff]
      intro w'
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Q w'
      -- `⁅hat y, hat z⁆ = 1`.
      have hzy : ⁅hat y, hat z⁆ = 1 := by
        refine hDx z (fun a => ?_) y
        -- `⁅hat (xC a), hat z⁆ = 1` from `⁅hat w', hat (xC a)⁆ = 1 ∀ w'` (via `hDx (xC a)`).
        have h1 : ∀ z' : ↥data.typeP.H, ⁅hat z', hat (xC a)⁆ = 1 :=
          hDx (xC a) (fun b => hall a b)
        rw [← hDsym (xC a) z]
        exact inv_eq_one.mpr (h1 z)
      exact commutatorElement_eq_one_iff_mul_comm.mp hzy
    rw [hcommHat] at hcommbot
    have hbot : Nat.card ↥(⊥ : Subgroup (↥data.typeP.H ⧸ Q)) = chief.p :=
      hcommbot ▸ hNhatCard
    rw [Subgroup.card_bot] at hbot
    exact chief.p_prime.one_lt.ne' hbot.symm
  -- ###########################################################################
  -- STEP 5: the action of `v ∈ U` on `xC a` is exponentiation by `e(a⁻¹ v a)`.
  -- ###########################################################################
  -- `L'` is normal in `L`, so `a⁻¹ v a ∈ L'` for `v ∈ L'`, `a ∈ L`.
  have hconjL' : ∀ (a : ↥L) (v : ↥L'), (a⁻¹ * (v : ↥L) * a) ∈ L' := by
    intro a v
    have := hUnorm
    have := hUnorm.conj_mem (v : ↥L) v.2 a⁻¹
    simpa [mul_assoc] using this
  -- the action `φ (v:↥L) (xC a)` agrees, mod `N`, with `(xC a)^{e(a⁻¹ v a)}`.
  have hactexp : ∀ (a : ↥L) (v : ↥L'),
      QuotientGroup.mk' chief.N (φ (v : ↥L) (xC a))
        = (QuotientGroup.mk' chief.N (xC a)) ^ e (MulAut.conjNormal (a⁻¹) v) := by
    intro a v
    -- `φ (v:↥L) (xC a) = φ ((v:↥L) * a) x = xC ((v:↥L) * a)`.
    have hcomp : φ (v : ↥L) (xC a) = xC ((v : ↥L) * a) := by
      change φ (v : ↥L) (φ a x) = φ ((v : ↥L) * a) x
      rw [map_mul, MulAut.mul_apply]
    rw [hcomp, hxCmk ((v : ↥L) * a)]
    -- `Φ ((v:↥L)*a) g = Φ a (Φ (a⁻¹ (v:↥L) a) g) = Φ a (g ^ e va) = (Φ a g)^{e va}`.
    set va : ↥L' := MulAut.conjNormal (a⁻¹) v with hva
    have hvaL : (va : ↥L) = a⁻¹ * (v : ↥L) * a := by
      rw [hva]
      have := MulAut.conjNormal_apply (a⁻¹ : ↥L) v
      rw [inv_inv] at this
      exact this
    have hsplit : (v : ↥L) * a = a * (va : ↥L) := by rw [hvaL]; group
    rw [hsplit, map_mul, MulAut.mul_apply]
    have hgexp : quotientMulAutHom chief.N_aInvariant (va : ↥L)
        (g : ↥data.typeP.H ⧸ chief.N) = (g : ↥data.typeP.H ⧸ chief.N) ^ e va := by
      have h := he va (g : ↥data.typeP.H ⧸ chief.N) hgS
      rw [hΦv va] at h
      exact h
    rw [hgexp, map_pow, ← hxCmk a]
  -- ###########################################################################
  -- STEP 6: `DXn` (action of `v` on the second `D`-slot) and the antisymmetry `phi_w12`.
  -- ###########################################################################
  -- `DXn`: `⁅hat (φ_v (xC a)), hat y⁆ = ⁅hat (xC a), hat y⁆ ^ e(a⁻¹ v a)`.
  have hDXn : ∀ (a : ↥L) (y : ↥data.typeP.H) (v : ↥L'),
      ⁅hat (φ (v : ↥L) (xC a)), hat y⁆
        = ⁅hat (xC a), hat y⁆ ^ e (MulAut.conjNormal (a⁻¹) v) := by
    intro a y v
    set k := e (MulAut.conjNormal (a⁻¹) v) with hk
    -- `φ_v (xC a)` and `(xC a)^k` differ by `n ∈ N`.
    have hNmem : φ (v : ↥L) (xC a) * ((xC a) ^ k)⁻¹ ∈ chief.N := by
      have heq : QuotientGroup.mk' chief.N (φ (v : ↥L) (xC a))
          = QuotientGroup.mk' chief.N ((xC a) ^ k) := by rw [map_pow]; exact hactexp a v
      have := QuotientGroup.eq_iff_div_mem.mp heq
      rwa [div_eq_mul_inv] at this
    set n : ↥data.typeP.H := φ (v : ↥L) (xC a) * ((xC a) ^ k)⁻¹ with hn
    have hsplit : φ (v : ↥L) (xC a) = n * (xC a) ^ k := by rw [hn]; group
    -- `hat n ∈ N̂` is central.
    have hnhat : hat n ∈ Subgroup.center (↥data.typeP.H ⧸ Q) :=
      hNhatCentral (Subgroup.mem_map_of_mem _ hNmem)
    have hcomm2 : hat n * hat ((xC a) ^ k) = hat ((xC a) ^ k) * hat n :=
      (Subgroup.mem_center_iff.mp hnhat _).symm
    rw [hsplit, map_mul, hcomm2, commutatorElement_mul_center_left hnhat, map_pow,
      commutatorElement_pow_left_of_center (hDcentral y (xC a))]
  -- Extract the nontrivial pair and the order-`p` commutator `D₀`.
  obtain ⟨a₀, b₀, hD₀ne⟩ := hntrivD
  set D₀ : ↥data.typeP.H ⧸ Q := ⁅hat (xC b₀), hat (xC a₀)⁆ with hD₀def
  -- `D₀` has order `p` (nonidentity element of `N̂` of prime order `p`).
  have hD₀ord : orderOf D₀ = chief.p := by
    have hmemN : D₀ ∈ Nhat := hDmem (xC a₀) (xC b₀)
    have hdvd : orderOf D₀ ∣ chief.p := by
      have h := orderOf_injective Nhat.subtype Nhat.subtype_injective (⟨D₀, hmemN⟩ : ↥Nhat)
      rw [show Nhat.subtype ⟨D₀, hmemN⟩ = D₀ from rfl] at h
      rw [h, ← hNhatCard]; exact orderOf_dvd_natCard _
    rcases (chief.p_prime.eq_one_or_self_of_dvd _ hdvd) with h1 | hp
    · exact absurd (orderOf_eq_one_iff.mp h1) hD₀ne
    · exact hp
  -- `phi_w12` core: `e(b₀⁻¹ v b₀)·e(a₀⁻¹ v a₀) ≡ 1 (mod p)` for all `v ∈ U`.
  have hcore : ∀ v : ↥L',
      (e (MulAut.conjNormal (b₀⁻¹) v) : ZMod chief.p)
        * (e (MulAut.conjNormal (a₀⁻¹) v) : ZMod chief.p) = 1 := by
    intro v
    -- `v` (as an element of `L`) lies in `U` and centralizes `N`.
    have hvU : ((v : ↥L) : G) ∈ data.typeP.U := Subgroup.mem_subgroupOf.mp v.2
    -- compute `E := ⁅hat (φ_v (xC b₀)), hat (φ_v (xC a₀))⁆` in two ways.
    -- Way 2 (centralizer): `E = D₀`.
    have hway2 : ⁅hat (φ (v : ↥L) (xC b₀)), hat (φ (v : ↥L) (xC a₀))⁆ = D₀ := by
      -- `⁅mk'Q p, mk'Q q⁆ = mk'Q ⁅p, q⁆` and `φ_v` preserves commutators.
      have hcomm_map : ⁅hat (φ (v : ↥L) (xC b₀)), hat (φ (v : ↥L) (xC a₀))⁆
          = hat ⁅φ (v : ↥L) (xC b₀), φ (v : ↥L) (xC a₀)⁆ := (map_commutatorElement hat _ _).symm
      have hphi_comm : ⁅φ (v : ↥L) (xC b₀), φ (v : ↥L) (xC a₀)⁆
          = φ (v : ↥L) ⁅xC b₀, xC a₀⁆ := (map_commutatorElement (φ (v : ↥L)).toMonoidHom _ _).symm
      have hcommN : ⁅xC b₀, xC a₀⁆ ∈ chief.N := by
        rw [hNcomm]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      have hfix : φ (v : ↥L) ⁅xC b₀, xC a₀⁆ = ⁅xC b₀, xC a₀⁆ :=
        hUcentN v hvU _ hcommN
      rw [hcomm_map, hphi_comm, hfix, hD₀def, map_commutatorElement]
    -- Way 1 (bilinearity via `hDXn`): `E = D₀ ^ (e(a₀⁻¹ v a₀) · e(b₀⁻¹ v b₀))`.
    have hway1 : ⁅hat (φ (v : ↥L) (xC b₀)), hat (φ (v : ↥L) (xC a₀))⁆
        = D₀ ^ (e (MulAut.conjNormal (a₀⁻¹) v) * e (MulAut.conjNormal (b₀⁻¹) v)) := by
      -- second slot first (via antisymmetry + `hDXn`).
      have hinner : ⁅hat (xC b₀), hat (φ (v : ↥L) (xC a₀))⁆
          = D₀ ^ e (MulAut.conjNormal (a₀⁻¹) v) := by
        rw [← hDsym (xC b₀) (φ (v : ↥L) (xC a₀)), hDXn a₀ (xC b₀) v, ← inv_pow]
        congr 1
        rw [hD₀def]; exact hDsym (xC b₀) (xC a₀)
      rw [hDXn b₀ (φ (v : ↥L) (xC a₀)) v, hinner, ← pow_mul]
    -- combine: `D₀ = D₀ ^ (…)`, so the exponent is `≡ 1 (mod p)`.
    have hDeq : D₀ = D₀ ^ (e (MulAut.conjNormal (a₀⁻¹) v) * e (MulAut.conjNormal (b₀⁻¹) v)) := by
      rw [← hway1, hway2]
    have hmod : e (MulAut.conjNormal (a₀⁻¹) v) * e (MulAut.conjNormal (b₀⁻¹) v) ≡ 1 [MOD chief.p] :=
        by
      have hpoweq : D₀ ^ (e (MulAut.conjNormal (a₀⁻¹) v) * e (MulAut.conjNormal (b₀⁻¹) v))
          = D₀ ^ 1 := by rw [pow_one]; exact hDeq.symm
      have hfinD : IsOfFinOrder D₀ := by
        rw [← orderOf_pos_iff, hD₀ord]; exact chief.p_prime.pos
      have h := hfinD.pow_eq_pow_iff_modEq.mp hpoweq
      rwa [hD₀ord] at h
    have h1 : ((e (MulAut.conjNormal (a₀⁻¹) v) * e (MulAut.conjNormal (b₀⁻¹) v) : ℕ)
        : ZMod chief.p) = ((1 : ℕ) : ZMod chief.p) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    push_cast at h1
    rw [mul_comm]; exact h1
  -- Assemble `hantisym` with `w = b₀⁻¹ a₀`: reparametrise `v = conjNormal a₀ v'`.
  refine ⟨b₀⁻¹ * a₀, fun v' => ?_⟩
  set v : ↥L' := MulAut.conjNormal a₀ v' with hvdef
  -- `conjNormal a₀⁻¹ v = v'` and `conjNormal b₀⁻¹ v = conjNormal (b₀⁻¹ a₀) v'`.
  have hva : MulAut.conjNormal (a₀⁻¹) v = v' := by
    rw [hvdef, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  have hvb : MulAut.conjNormal (b₀⁻¹) v = MulAut.conjNormal (b₀⁻¹ * a₀) v' := by
    rw [hvdef, ← MulAut.mul_apply, ← map_mul]
  have h := hcore v
  rw [hva, hvb] at h
  rw [mul_comm]; exact h

end CaseA

end OddOrder.Peterfalvi.S13


