-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04e_GorThm37
-- name    : OddOrder_BG_Ch1_Preliminary_S04e_GorThm37
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:53:19.631569+00:00
-- url     : https://prove2.me/theorems/381c56da-b3ba-42f5-9cef-d70f871510bf
-- title:
--   Gorenstein, *Finite Groups*, Theorem 3.7: minimal $\psi$-invariant subgroups have special structure
-- statement:
--   Gorenstein, *Finite Groups* (2nd ed.), Chapter 3, Theorem 3.7, referenced by Bender–Glauberman §4 (Lemma 4.13) via Theorems 3.8 and 3.10: let $A$ be a group of $p'$-automorphisms of a $p$-group $P$ ($\phi:A\to\mathrm{Aut}\,P$, coprime orders) and consider a minimal invariant subgroup on which an element acts nontrivially.
--
--   Main definition: `fixerSubgroup` (the operators fixing an $A$-invariant subgroup $N\le P$ pointwise, a normal subgroup of $A$), with `isAInvariant_actionCommutator_comp` for restricted actions.
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S04e_GorThm37.lean

/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S04e_GorThm37.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_OperatorMaschke
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_OperatorQuotientAction
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S01_Solvable
import Definitions.Def_OddOrder_GroupTheory_CoprimeAbelianPGroup
import Definitions.Def_OddOrder_GroupTheory_IsExtraspecial
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04_PGroupsSmallRank

open scoped Pointwise commutatorElement

namespace OddOrder.BG.Ch1.S04

open OddOrder.Isaacs.Ch03 (IsAInvariant)

open OddOrder.Isaacs.Ch04

open OddOrder.GroupTheory

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk' quotientMulAutHom_apply)

open OddOrder.BG.Ch1.S01 (coprime_actsTrivially_of_normal_and_quotient)

open OddOrder.BG.Ch1.OperatorQuotientAction (actionCommutator_restrict_self_map_subtype_eq)

open OddOrder.BG.Ch1_Preliminary (isAInvariant_comap_mk' isAInvariant_map_mk'
  pow_eq_one_of_mem_omega_one_of_comm exists_aInvariant_complement_in_omega1_quotient
  isAInvariant_map_subtype_of_restrict)

/-- **Gorenstein "Finite Groups" Lemma 3.9(ii).** In a group `G` of class `≤ 2` with `p` odd
such that every `p`-th power lies in `Z(G)` (e.g. `G/Z(G)` elementary abelian), the `p`-th
power map is multiplicative: `(x * y) ^ p = x ^ p * y ^ p`.

Proof: the class-`≤ 2` collection formula gives `(xy)^p = x^p y^p ⁅y,x⁆^(p(p-1)/2)`; since
`y^p ∈ Z` we get `⁅y,x⁆^p = ⁅y^p, x⁆ = 1`, and `p ∣ p(p-1)/2` for odd `p`, so the last factor
vanishes. -/
private theorem mul_pow_prime_of_class_le_two_of_pow_mem_center {G : Type*} [Group G] {p : ℕ}
    (hp_odd : Odd p) (hcl : _root_.commutator G ≤ Subgroup.center G)
    (hZ : ∀ g : G, g ^ p ∈ Subgroup.center G) (x y : G) :
    (x * y) ^ p = x ^ p * y ^ p := by
  have hcen : ⁅y, x⁆ ∈ Subgroup.center G :=
    hcl (Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top x))
  have hyp : ⁅y, x⁆ ^ p = 1 := by
    rw [← commutatorElement_pow_left_of_central hcen p, commutatorElement_eq_one_iff_commute]
    exact (Subgroup.mem_center_iff.mp (hZ y) x).symm
  have hdvd : p ∣ p * (p - 1) / 2 := by
    obtain ⟨k, rfl⟩ := hp_odd
    rw [show 2 * k + 1 - 1 = 2 * k by omega,
      Nat.mul_div_assoc _ (Dvd.intro k rfl : 2 ∣ 2 * k), Nat.mul_div_cancel_left k two_pos]
    exact Dvd.intro k rfl
  obtain ⟨m, hm⟩ := hdvd
  rw [mul_pow_of_class_le_two hcl, hm, pow_mul, hyp, one_pow, mul_one]

variable {A P : Type*} [Group A] [Group P] [Finite A] [Finite P] {p : ℕ} [Fact p.Prime]

/-- The set of operators `a : A` fixing an `A`-invariant subgroup `N ≤ P` pointwise is a
subgroup of `A` (the *pointwise stabilizer* of `N`). It is well-defined as a subgroup because
`N` is `φ`-invariant (needed for `inv_mem`). -/
private def fixerSubgroup (φ : A →* MulAut P) {N : Subgroup P} (hN : IsAInvariant φ N) :
    Subgroup A where
  carrier := {a : A | ∀ n ∈ N, (φ a) n = n}
  one_mem' := fun n _ => by rw [map_one]; rfl
  mul_mem' := fun {a b} ha hb n hn => by
    rw [map_mul, MulAut.mul_apply, hb n hn]; exact ha n hn
  inv_mem' := fun {a} ha n hn => by
    have h := ha ((φ a)⁻¹ n) (hN.inv_smul_mem a hn)
    rw [MulAut.apply_inv_self] at h
    rw [map_inv]; exact h.symm

omit [Finite A] [Finite P] in
@[simp] private theorem mem_fixerSubgroup {φ : A →* MulAut P} {N : Subgroup P}
    (hN : IsAInvariant φ N) {a : A} :
    a ∈ fixerSubgroup φ hN ↔ ∀ n ∈ N, (φ a) n = n := Iff.rfl

omit [Finite A] [Finite P] in
/-- The pointwise stabilizer of an `A`-invariant subgroup `N` is normal in `A`. -/
private theorem fixerSubgroup_normal (φ : A →* MulAut P) {N : Subgroup P}
    (hN : IsAInvariant φ N) : (fixerSubgroup φ hN).Normal where
  conj_mem := by
    intro x hx c n hn
    rw [map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply,
      hx ((φ c)⁻¹ n) (hN.inv_smul_mem c hn), MulAut.apply_inv_self]

omit [Finite A] [Finite P] in
/-- If `B ◁ A`, then the action commutator `[P, B]` of the restricted action `φ ∘ B.subtype`
is invariant under the full action of `A` (the generating set is `φ(A)`-stable because
`B` is normal). -/
private theorem isAInvariant_actionCommutator_comp (φ : A →* MulAut P) {B : Subgroup A}
    [hBN : B.Normal] : IsAInvariant φ (actionCommutator (φ.comp B.subtype)) := by
  apply IsAInvariant.closure_of_invariant_set
  -- A generator `g * φ(↑β) g⁻¹` is sent by `φ a` to `φ(a)g * φ(↑(aβa⁻¹)) (φ(a)g)⁻¹`.
  have key : ∀ (a : A) (g : P) (β : B), (φ a) (g * ((φ.comp B.subtype) β) g⁻¹) =
      (φ a) g * ((φ.comp B.subtype) (⟨a * ↑β * a⁻¹, hBN.conj_mem β β.2 a⟩ : B)) ((φ a) g)⁻¹ := by
    intro a g β
    change (φ a) (g * (φ ↑β) g⁻¹) = (φ a) g * (φ (a * ↑β * a⁻¹)) ((φ a) g)⁻¹
    rw [map_mul (φ a)]
    congr 1
    rw [show ((φ a) g)⁻¹ = (φ a) g⁻¹ from (map_inv (φ a) g).symm,
      show (φ (a * ↑β * a⁻¹)) = (φ a) * (φ ↑β) * (φ a)⁻¹ from by rw [map_mul, map_mul, map_inv],
      MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  -- the generating set is `φ(a)`-stable for every `a` (image ⊆); equality via `a⁻¹`.
  have hsub : ∀ a : A,
      (φ a) '' {x : P | ∃ g : P, ∃ β : B, x = g * ((φ.comp B.subtype) β) g⁻¹} ⊆
        {x : P | ∃ g : P, ∃ β : B, x = g * ((φ.comp B.subtype) β) g⁻¹} := by
    rintro a _ ⟨_, ⟨g, β, rfl⟩, rfl⟩
    exact ⟨(φ a) g, ⟨a * ↑β * a⁻¹, hBN.conj_mem β β.2 a⟩, key a g β⟩
  intro a
  refine Set.Subset.antisymm (hsub a) (fun s hs => ⟨(φ a⁻¹) s, hsub a⁻¹ ⟨s, hs, rfl⟩, ?_⟩)
  rw [show (φ a⁻¹) = (φ a)⁻¹ from map_inv φ a, MulAut.apply_inv_self]

/-- **Single-element stability** (Gorenstein Thm 3.2 for `⟨ψ⟩`). If `ψ` fixes an `A`-invariant
normal subgroup `N ≤ P` pointwise and acts trivially on `P/N`, then `ψ` acts trivially on `P`
(coprime action of the `p′`-element `ψ`). -/
theorem acts_trivially_of_trivial_on_normal_quotient
    (φ : A →* MulAut P) (hP : IsPGroup p P) (hCop : Nat.Coprime (Nat.card A) (Nat.card P))
    {ψ : A} {N : Subgroup P} [N.Normal] (hN : IsAInvariant φ N)
    (hfix : ∀ n ∈ N, (φ ψ) n = n) (hquot : ∀ g : P, (φ ψ) g * g⁻¹ ∈ N) :
    ∀ g : P, (φ ψ) g = g := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have : Group.IsSolvable P := inferInstance
  -- Act through the cyclic subgroup `C = ⟨ψ⟩ ≤ A`.
  set C : Subgroup A := Subgroup.zpowers ψ with hC_def
  set φC : C →* MulAut P := φ.comp C.subtype with hφC_def
  have hψC : ψ ∈ C := Subgroup.mem_zpowers ψ
  -- `N` is `C`-invariant.
  have hN_C : IsAInvariant φC N := fun c => hN (c : A)
  -- coprimality of `|C|` with `|P|`.
  have hCcop : Nat.Coprime (Nat.card C) (Nat.card P) :=
    hCop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card C)
  -- `ψ` fixes `N` pointwise ⇒ every `c ∈ C` does (`C ≤ fixerSubgroup`).
  have hC_fix : C ≤ fixerSubgroup φ hN := by
    rw [hC_def, Subgroup.zpowers_le]; exact hfix
  -- `ψ` acts trivially on `P/N` ⇒ `ψ ∈ ker φ̄` ⇒ every `c ∈ C` does.
  have hψ_ker : ψ ∈ (quotientMulAutHom hN).ker := by
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro q
    refine QuotientGroup.induction_on q ?_
    intro g
    rw [MulAut.one_apply, quotientMulAutHom_apply, QuotientGroup.eq_iff_div_mem,
      div_eq_mul_inv]
    exact hquot g
  have hC_ker : C ≤ (quotientMulAutHom hN).ker := by
    rw [hC_def, Subgroup.zpowers_le]; exact hψ_ker
  -- Apply the group stability lemma to `C`.
  have hconc : ∀ c : C, ∀ g : P, (φC c) g = g :=
    coprime_actsTrivially_of_normal_and_quotient hCcop (Or.inr ‹Group.IsSolvable P›) hN_C
      (fun c n hn => hC_fix c.2 n hn)
      (fun c g => by
        -- `c ∈ ker φ̄`, so `(φ c) g` and `g` agree mod `N`; take `x = g⁻¹ * (φ c) g ∈ N`.
        have hck := hC_ker c.2
        rw [MonoidHom.mem_ker] at hck
        have happ := congrArg (fun (f : MulAut (P ⧸ N)) => f (g : P ⧸ N)) hck
        simp only [quotientMulAutHom_apply, MulAut.one_apply] at happ
        refine ⟨g⁻¹ * (φ (c : A)) g, ?_, by change (φ (c : A)) g = g * (g⁻¹ * (φ (c : A)) g); group⟩
        rw [← QuotientGroup.eq]
        exact happ.symm)
  exact fun g => hconc ⟨ψ, hψC⟩ g

/-- **Gorenstein "Finite Groups" Theorem 3.7.** Let `A` be a `p′`-group of automorphisms of
the `p`-group `P` (`φ : A →* MulAut P`, coprime, `A` or `P` solvable). Suppose `ψ : A` acts
nontrivially on `P` but trivially on every proper `A`-invariant normal subgroup of `P`. Then:

* **(i)** `[P,P] ⊆ Z(P)`;
* **(ii)** `P/[P,P]` is elementary abelian, `A` acts irreducibly on it (every `A`-invariant
  subgroup `N` with `[P,P] ≤ N` is `[P,P]` or `⊤`), and `ψ` acts nontrivially on it;
* **(iii)** `P` is special (`IsSpecial p P`).

See `notes/bg/s04_precursor2_special_expP_design.md`. -/
theorem isSpecial_of_pprimeAction_trivialOnProper
    (φ : A →* MulAut P) (hP : IsPGroup p P)
    (hCop : Nat.Coprime (Nat.card A) (Nat.card P))
    {ψ : A}
    (hψ_ntriv : ¬ ∀ g : P, (φ ψ) g = g)
    (hψ_proper : ∀ N : Subgroup P, N.Normal → IsAInvariant φ N → N ≠ ⊤ →
        ∀ n ∈ N, (φ ψ) n = n) :
    commutator P ≤ Subgroup.center P ∧
    IsElementaryAbelian p (P ⧸ commutator P) ∧
    (∀ N : Subgroup P, IsAInvariant φ N → commutator P ≤ N →
        N = commutator P ∨ N = ⊤) ∧
    (∃ g : P, (φ ψ) g * g⁻¹ ∉ commutator P) ∧
    IsSpecial p P := by
  classical
  have : Group.IsNilpotent P := hP.isNilpotent
  have hPntriv : Nontrivial P := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hψ_ntriv fun g => Subsingleton.elim _ _
  -- `P' = commutator P` is `A`-invariant, normal, and proper (nilpotent ambient).
  have hP'_inv : IsAInvariant φ (commutator P) := IsAInvariant.commutator_self φ
  have hP'_ne_top : commutator P ≠ ⊤ :=
    (commutator_lt_self_of_isNilpotent_ambient (E := ⊤) (F := ⊤) bot_lt_top.ne').ne
  -- STEP 1: `ψ` acts trivially on `P'`.
  have hψP' : ∀ n ∈ commutator P, (φ ψ) n = n :=
    hψ_proper (commutator P) inferInstance hP'_inv hP'_ne_top
  -- STEP 2 (= conjunct ii.c): `ψ` acts nontrivially on `P/P'`.
  have hψ_ntriv_bar : ∃ g : P, (φ ψ) g * g⁻¹ ∉ commutator P := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hψ_ntriv (acts_trivially_of_trivial_on_normal_quotient φ hP hCop hP'_inv hψP' h)
  -- ## Quotient `P̄ = P/P'` setup.
  have hP'_normal : (commutator P).Normal := inferInstance
  have hPbar_comm : ∀ x y : P ⧸ commutator P, x * y = y * x :=
    isMulCommutative_iff.mp
      ((Subgroup.Normal.quotient_commutative_iff_commutator_le
        (N := commutator P)).mpr le_rfl)
  let hPbar_cg : CommGroup (P ⧸ commutator P) :=
    { (inferInstance : Group (P ⧸ commutator P)) with mul_comm := hPbar_comm }
  have hPbar_pgroup : IsPGroup p (P ⧸ commutator P) := hP.to_quotient _
  set φbar : A →* MulAut (P ⧸ commutator P) := quotientMulAutHom hP'_inv with hφbar_def
  -- `ψ` acts nontrivially on `P̄` (restatement of conjunct ii.c).
  have hψbar_ntriv : ¬ ∀ q : P ⧸ commutator P, (φbar ψ) q = q := by
    intro h
    obtain ⟨g, hg⟩ := hψ_ntriv_bar
    refine hg ?_
    have hgq := h (g : P ⧸ commutator P)
    rw [hφbar_def, quotientMulAutHom_apply] at hgq
    rwa [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv] at hgq
  -- `ψ` acts trivially on every proper `A`-invariant subgroup of `P̄` (correspondence).
  have hψ_triv_proper_bar : ∀ Y : Subgroup (P ⧸ commutator P), IsAInvariant φbar Y → Y ≠ ⊤ →
      ∀ q ∈ Y, (φbar ψ) q = q := by
    intro Y hY hYne q hq
    set Q := Y.comap (QuotientGroup.mk' (commutator P)) with hQ_def
    have hQinv : IsAInvariant φ Q := isAInvariant_comap_mk' hP'_inv hY
    have : Y.Normal := inferInstance
    have : Q.Normal := inferInstance
    have hsurj := QuotientGroup.mk'_surjective (commutator P)
    have hQne : Q ≠ ⊤ := by
      intro hQtop
      exact hYne (Subgroup.comap_injective hsurj (hQtop.trans (Subgroup.comap_top _).symm))
    have hψQ := hψ_proper Q ‹Q.Normal› hQinv hQne
    obtain ⟨g, rfl⟩ := hsurj q
    have hgQ : g ∈ Q := by rw [hQ_def, Subgroup.mem_comap]; exact hq
    rw [hφbar_def, quotientMulAutHom_apply_mk', hψQ g hgQ]
  have : Group.IsSolvable P := inferInstance
  -- conjuncts.
  -- STEP 4 (= conjunct ii.a): `P̄` is elementary abelian, via `Ω₁(P̄) = ⊤`.
  have hPbar_elemab : IsElementaryAbelian p (P ⧸ commutator P) := by
    have hOmega_top : Omega (P ⧸ commutator P) p 1 = ⊤ := by
      by_contra hne
      have hOmega_inv : IsAInvariant φbar (Omega (P ⧸ commutator P) p 1) :=
        IsAInvariant.of_characteristic φbar
      have hψ_triv_omega : ∀ q ∈ Omega (P ⧸ commutator P) p 1, (φbar ψ) q = q :=
        hψ_triv_proper_bar _ hOmega_inv hne
      -- Apply Theorem 2.4 to `C = ⟨ψ⟩ ≤ A` acting on `P̄`.
      set C : Subgroup A := Subgroup.zpowers ψ with hC_def
      set φbarC : C →* MulAut (P ⧸ commutator P) := φbar.comp C.subtype with hφbarC_def
      have hCcop : Nat.Coprime (Nat.card C) (Nat.card (P ⧸ commutator P)) :=
        (hCop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card C)).coprime_dvd_right
          (Subgroup.card_quotient_dvd_card _)
      have htriv : Omega (P ⧸ commutator P) p 1 ≤ Subgroup.fixedPointsOfMulAut φbarC := by
        have hC_fix : C ≤ fixerSubgroup φbar hOmega_inv := by
          rw [hC_def, Subgroup.zpowers_le]; exact hψ_triv_omega
        intro q hq
        rw [Subgroup.mem_fixedPointsOfMulAut]
        exact fun c => hC_fix c.2 q hq
      have hbot : actionCommutator φbarC = ⊥ :=
        actionCommutator_eq_bot_of_omega1_le_fixedPoints φbarC hCcop hPbar_pgroup htriv
      rw [actionCommutator_eq_bot_iff_acts_trivially] at hbot
      exact hψbar_ntriv fun q => hbot ⟨ψ, Subgroup.mem_zpowers ψ⟩ q
    refine ⟨hPbar_comm, fun x => ?_⟩
    apply pow_eq_one_of_mem_omega_one_of_comm hPbar_comm
    rw [hOmega_top]; exact Subgroup.mem_top x
  -- `Ω₁(P̄) = ⊤` (consequence of `P̄` elementary abelian), reused for Maschke.
  have hOmega_top : Omega (P ⧸ commutator P) p 1 = ⊤ := by
    rw [eq_top_iff]
    intro q _
    exact Omega.mem_of_pow_eq_one (by simpa using hPbar_elemab.pow_eq_one q)
  -- STEP 3: `A` acts indecomposably on `P̄` (internal direct products are trivial).
  have h_indecomp : ∀ W₁ W₂ : Subgroup (P ⧸ commutator P),
      IsAInvariant φbar W₁ → IsAInvariant φbar W₂ →
      W₁ ⊓ W₂ = ⊥ → W₁ ⊔ W₂ = ⊤ → W₁ = ⊥ ∨ W₂ = ⊥ := by
    intro W₁ W₂ h1 h2 hinf hsup
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hW1, hW2⟩ := hcon
    have hW1ne : W₁ ≠ ⊤ := fun ht => hW2 (by rw [ht, top_inf_eq] at hinf; exact hinf)
    have hW2ne : W₂ ≠ ⊤ := fun ht => hW1 (by rw [ht, inf_top_eq] at hinf; exact hinf)
    have ht1 := hψ_triv_proper_bar W₁ h1 hW1ne
    have ht2 := hψ_triv_proper_bar W₂ h2 hW2ne
    -- `ψ̄` trivial on `W₁` and `W₂`, which generate `P̄` ⇒ `ψ̄` trivial on `P̄`, contra ii.c.
    apply hψbar_ntriv
    intro q
    have hq : q ∈ W₁ ⊔ W₂ := hsup ▸ Subgroup.mem_top q
    rw [Subgroup.sup_eq_closure] at hq
    induction hq using Subgroup.closure_induction with
    | mem w hw => rcases hw with hw | hw
                  · exact ht1 w hw
                  · exact ht2 w hw
    | one => exact map_one (φbar ψ)
    | mul a b _ _ ha hb => rw [map_mul, ha, hb]
    | inv a _ ha => rw [map_inv, ha]
  -- STEP 5 (= conjunct ii.b): `A` acts irreducibly on `P̄`.
  have h_irred : ∀ N : Subgroup P, IsAInvariant φ N → commutator P ≤ N →
      N = commutator P ∨ N = ⊤ := by
    intro N hN_inv hP'_le_N
    have hpP : p ∣ Nat.card P := by
      rcases hP.card_eq_or_dvd with h1 | hd
      · exact absurd h1 (by simpa using (Finite.one_lt_card (α := P)).ne')
      · exact hd
    set Nbar := N.map (QuotientGroup.mk' (commutator P)) with hNbar_def
    have hNbar_inv : IsAInvariant φbar Nbar := isAInvariant_map_mk' hP'_inv hN_inv
    have hNΩ : Nbar ≤ Omega (P ⧸ commutator P) p 1 := by rw [hOmega_top]; exact le_top
    obtain ⟨X, _hP'X, hXinv, _hXΩ, hXinf, hXsup⟩ :=
      exists_aInvariant_complement_in_omega1_quotient hpP hCop hP'_inv hPbar_comm hN_inv hNΩ
    set Xbar := X.map (QuotientGroup.mk' (commutator P)) with hXbar_def
    have hXbar_inv : IsAInvariant φbar Xbar := isAInvariant_map_mk' hP'_inv hXinv
    have hinf : Nbar ⊓ Xbar = ⊥ := by rw [inf_comm]; exact hXinf
    have hsup : Nbar ⊔ Xbar = ⊤ := by rw [sup_comm, hXsup, hOmega_top]
    rcases h_indecomp Nbar Xbar hNbar_inv hXbar_inv hinf hsup with hNbot | hXbot
    · -- `Nbar = ⊥` ⇒ `N ≤ P'` ⇒ `N = P'`.
      left
      have hle : N ≤ commutator P := by
        rw [← QuotientGroup.ker_mk' (commutator P)]
        intro n hn
        rw [MonoidHom.mem_ker]
        have hmem : (QuotientGroup.mk' (commutator P)) n ∈ Nbar :=
          Subgroup.mem_map_of_mem _ hn
        rw [hNbot, Subgroup.mem_bot] at hmem
        exact hmem
      exact le_antisymm hle hP'_le_N
    · -- `Xbar = ⊥` ⇒ `Nbar = ⊤` ⇒ `N = ⊤`.
      right
      have hNbar_top : Nbar = ⊤ := by rw [← hsup, hXbot, sup_bot_eq]
      rw [eq_top_iff]
      intro g _
      have hg : (g : P ⧸ commutator P) ∈ Nbar := hNbar_top ▸ Subgroup.mem_top _
      obtain ⟨n, hnN, hn⟩ := hg
      have hng : n⁻¹ * g ∈ commutator P := by
        rw [← QuotientGroup.eq]; exact hn
      have hgeq : g = n * (n⁻¹ * g) := by group
      rw [hgeq]
      exact N.mul_mem hnN (hP'_le_N hng)
  -- STEP 6 (= conjunct i): `P' ⊆ Z(P)`.
  have h_i : commutator P ≤ Subgroup.center P := by
    -- `B` = pointwise stabilizer of `P'`: normal in `A`, contains `ψ`, centralizes `P'`.
    set B : Subgroup A := fixerSubgroup φ hP'_inv with hB_def
    have hB_normal : B.Normal := fixerSubgroup_normal φ hP'_inv
    have hψB : ψ ∈ B := hψP'
    set φB : B →* MulAut P := φ.comp B.subtype with hφB_def
    -- (6a) `[P, B] = ⊤`.
    have hPB_top : actionCommutator φB = ⊤ := by
      have hH_inv : IsAInvariant φ (actionCommutator φB) := isAInvariant_actionCommutator_comp φ
      have hH_normal : (actionCommutator φB).Normal := actionCommutator.normal φB
      by_contra hHne
      by_cases hHP' : actionCommutator φB ≤ commutator P
      · -- `H ⊆ P'`: `B` is trivial on `H`, so Thm 3.6 forces `H = ⊥`, i.e. `ψ` trivial — contra.
        have hBcop : Nat.Coprime (Nat.card B) (Nat.card P) :=
          hCop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card B)
        have hInner_bot :
            actionCommutator (IsAInvariant.actionCommutator φB).toMulAutHom = ⊥ := by
          rw [actionCommutator_eq_bot_iff_acts_trivially]
          intro b h
          apply Subtype.ext
          change (φ ↑b) (h : P) = (h : P)
          exact b.2 (h : P) (hHP' h.2)
        have hHbot : actionCommutator φB = ⊥ := by
          have h36 := actionCommutator_restrict_self_map_subtype_eq (φ := φB) hBcop
            (Or.inr ‹Group.IsSolvable P›)
          rw [hInner_bot, Subgroup.map_bot] at h36
          exact h36.symm
        rw [actionCommutator_eq_bot_iff_acts_trivially] at hHbot
        exact hψ_ntriv fun g => hHbot ⟨ψ, hψB⟩ g
      · -- `H ⊄ P'`: `N := H ⊔ P'` is `A`-invariant `⊇ P'`; irreducibility forces `N = P'` or `⊤`.
        set N := actionCommutator φB ⊔ commutator P with hN_def
        have hN_inv : IsAInvariant φ N := hH_inv.sup hP'_inv
        rcases h_irred N hN_inv le_sup_right with hNP' | hNtop
        · exact hHP' (le_trans le_sup_left hNP'.le)
        · have hψH : ∀ n ∈ actionCommutator φB, (φ ψ) n = n :=
            hψ_proper _ hH_normal hH_inv hHne
          apply hψ_ntriv
          intro g
          have hgN : g ∈ N := hNtop ▸ Subgroup.mem_top g
          rw [hN_def, Subgroup.sup_eq_closure] at hgN
          induction hgN using Subgroup.closure_induction with
          | mem w hw => rcases hw with hw | hw
                        · exact hψH w hw
                        · exact hψP' w hw
          | one => exact map_one (φ ψ)
          | mul a b _ _ ha hb => rw [map_mul, ha, hb]
          | inv a _ ha => rw [map_inv, ha]
    -- (6b) three-subgroup lemma in `Γ = P ⋊[φ] A`: `[P', P, B] = 1`, `[B, P', P] = 1`
    --       ⇒ `[P, B, P'] = 1`; with `[P, B] = P` this gives `[P, P'] = 1`.
    set H₁ : Subgroup (P ⋊[φ] A) := (SemidirectProduct.inl : P →* P ⋊[φ] A).range with hH₁_def
    set H₂ : Subgroup (P ⋊[φ] A) := B.map (SemidirectProduct.inr : A →* P ⋊[φ] A) with hH₂_def
    set H₃ : Subgroup (P ⋊[φ] A) :=
      (commutator P).map (SemidirectProduct.inl : P →* P ⋊[φ] A) with hH₃_def
    -- `[inr B, inl P'] = 1` (B centralizes P').
    have hbot23 : ⁅H₂, H₃⁆ ≤ ⊥ := by
      rw [Subgroup.commutator_le]
      rintro x hx y hy
      rw [hH₂_def, Subgroup.mem_map] at hx
      rw [hH₃_def, Subgroup.mem_map] at hy
      obtain ⟨a, haB, rfl⟩ := hx
      obtain ⟨z, hzP', rfl⟩ := hy
      rw [Subgroup.mem_bot]
      have hfix : (φ a) z⁻¹ = z⁻¹ := haB z⁻¹ ((commutator P).inv_mem hzP')
      have hcomm : ⁅(SemidirectProduct.inl z : P ⋊[φ] A), (SemidirectProduct.inr a : P ⋊[φ] A)⁆
          = 1 := by
        rw [SemidirectProduct.commutator_inl_inr, hfix, mul_inv_cancel, map_one]
      rw [← commutatorElement_inv, hcomm, inv_one]
    -- `[inl P', inl P] ⊆ inl P'` (P' normal).
    have hP'_comm_top : ⁅commutator P, (⊤ : Subgroup P)⁆ ≤ commutator P := by
      rw [Subgroup.commutator_le]
      intro x hx y _
      have : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
      rw [this]
      exact (commutator P).mul_mem hx
        (hP'_normal.conj_mem x⁻¹ ((commutator P).inv_mem hx) y)
    have h31_le : ⁅H₃, H₁⁆ ≤ H₃ := by
      rw [hH₃_def, hH₁_def, MonoidHom.range_eq_map, ← Subgroup.map_commutator]
      exact Subgroup.map_mono hP'_comm_top
    -- `[inl P, inr B] = inl P` (from `[P, B] = ⊤`).
    have hH1H2 : ⁅H₁, H₂⁆ = H₁ := by
      have h := actionCommutator_map_inl_comp φ B.subtype
      rw [hPB_top, ← MonoidHom.range_eq_map] at h
      rw [hH₁_def, hH₂_def, ← B.range_subtype, ← MonoidHom.range_comp]
      exact h.symm
    have h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ ⊥ :=
      le_trans (Subgroup.commutator_mono hbot23 le_rfl) (Subgroup.commutator_bot_left H₁).le
    have h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ ⊥ := by
      refine le_trans (Subgroup.commutator_mono h31_le le_rfl) ?_
      rw [Subgroup.commutator_comm]; exact hbot23
    have hrot := commutator_commutator_le_of_rotate (N := (⊥ : Subgroup (P ⋊[φ] A))) h1 h2
    rw [hH1H2] at hrot
    -- conclude `[g, z] = 1` for `g : P`, `z ∈ P'`.
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    have hmem : (⁅(SemidirectProduct.inl g : P ⋊[φ] A), SemidirectProduct.inl z⁆) ∈ ⁅H₁, H₃⁆ :=
      Subgroup.commutator_mem_commutator ⟨g, rfl⟩ (Subgroup.mem_map_of_mem _ hz)
    have hone : (⁅(SemidirectProduct.inl g : P ⋊[φ] A),
        (SemidirectProduct.inl z : P ⋊[φ] A)⁆) = 1 := by
      have h := hrot hmem; rwa [Subgroup.mem_bot] at h
    rw [← map_commutatorElement] at hone
    have hgz : ⁅g, z⁆ = 1 := SemidirectProduct.inl_injective (by rw [map_one]; exact hone)
    exact (commutatorElement_eq_one_iff_commute.mp hgz).eq
  -- STEP 7 (= conjunct iii): `P` is special.
  have h_special : IsSpecial p P := by
    refine ⟨hP, ?_⟩
    by_cases hPea : IsElementaryAbelian p P
    · exact Or.inl hPea
    · right
      -- (a) `[P,P] = Z(P)`.
      have ha : commutator P = Subgroup.center P := by
        refine le_antisymm h_i ?_
        rcases h_irred (Subgroup.center P ⊔ commutator P)
            ((IsAInvariant.center φ).sup hP'_inv) le_sup_right with hN | hN
        · exact le_trans le_sup_left hN.le
        · exfalso
          apply hPea
          have hctop : Subgroup.center P = ⊤ := by rw [← hN, sup_eq_left.mpr h_i]
          have hcomm_P : ∀ x y : P, x * y = y * x := fun x y =>
            (Subgroup.mem_center_iff.mp (hctop ▸ Subgroup.mem_top x) y).symm
          refine ⟨hcomm_P, fun x => ?_⟩
          have hcomm_bot : commutator P = ⊥ := by
            rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
            intro u _ v _
            rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
            exact hcomm_P u v
          have h := hPbar_elemab.pow_eq_one (QuotientGroup.mk' (commutator P) x)
          rw [← map_pow] at h
          have hxmem : x ^ p ∈ commutator P := (QuotientGroup.eq_one_iff _).mp h
          rw [hcomm_bot, Subgroup.mem_bot] at hxmem
          exact hxmem
      -- key: every commutator has `p`-th power `1`.
      have hkey : ∀ u v : P, ⁅u, v⁆ ^ p = 1 := by
        intro u v
        have hcen : ⁅u, v⁆ ∈ Subgroup.center P :=
          h_i (Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top v))
        have hvp : v ^ p ∈ commutator P := by
          have h := hPbar_elemab.pow_eq_one (QuotientGroup.mk' (commutator P) v)
          rw [← map_pow] at h
          exact (QuotientGroup.eq_one_iff _).mp h
        have h1 : ⁅u, v ^ p⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_commute]
          exact Subgroup.mem_center_iff.mp (h_i hvp) u
        rw [← commutatorElement_pow_right_of_central hcen p]; exact h1
      -- every element of `[P,P]` has `p`-th power `1` (abelian + generators are `p`-torsion).
      have hcomm_pow : ∀ z ∈ commutator P, z ^ p = 1 := by
        let S : Subgroup P :=
          { carrier := {w | w ∈ commutator P ∧ w ^ p = 1}
            one_mem' := ⟨one_mem _, one_pow p⟩
            mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
              have hcx : Commute x y := (Subgroup.mem_center_iff.mp (h_i hx.1) y).symm
              rw [hcx.mul_pow, hx.2, hy.2, mul_one]⟩
            inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
        have hsub : commutator P ≤ S := by
          rw [commutator_def, Subgroup.commutator_le]
          intro u _ v _
          exact ⟨Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top v),
            hkey u v⟩
        exact fun z hz => (hsub hz).2
      -- (b) `Φ(P) = Z(P)`.
      have hb : frattini P = Subgroup.center P := by
        have hfrat_ne_top : frattini P ≠ ⊤ := by
          obtain ⟨M, hM, _⟩ :=
            (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup P)).resolve_left bot_lt_top.ne
          exact fun htop => hM.1 (le_antisymm le_top (htop ▸ frattini_le_coatom hM))
        rcases h_irred (frattini P) (IsAInvariant.frattini φ)
            (commutator_le_frattini_of_pgroup hP) with hf | hf
        · rw [hf]; exact ha
        · exact absurd hf hfrat_ne_top
      -- (c) `Z(P)` is elementary abelian.
      have hc : (Subgroup.center P).IsElementaryAbelian p := by
        rw [← ha]
        refine ⟨fun x y => Subtype.ext (Subgroup.mem_center_iff.mp (h_i x.2) y.1).symm,
          fun x => Subtype.ext ?_⟩
        rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
        exact hcomm_pow x.1 x.2
      exact ⟨ha, hb, hc⟩
  exact ⟨h_i, hPbar_elemab, h_irred, hψ_ntriv_bar, h_special⟩

/-- **Gorenstein "Finite Groups" Theorem 3.8.** Let `A` be a `p′`-group of automorphisms of the
`p`-group `P` (`φ : A →* MulAut P`, coprime) and `ψ : A` acting nontrivially on `P`. Then `P`
has an `A`-invariant subgroup `Q`, **minimal** among `A`-invariant subgroups on which `ψ` acts
nontrivially, and `Q` is a **special** `p`-group.

(Gorenstein's full statement also records that `A` acts irreducibly on `Q/Φ(Q)`, `ψ`
nontrivially on `Q/Φ(Q)`, and trivially on `Φ(Q)`; for a special group `Φ(Q) = Q′`, so those are
exactly conjuncts (ii)/(i) of Theorem 3.7 applied to `Q` and are available on demand. The
payload needed downstream — precursor 2 of BG Lem 4.13 — is `IsSpecial p ↥Q` together with the
minimality, which drives the exponent-`p` argument via Theorem 3.10.)

Proof: choose `Q` minimal `A`-invariant with `ψ` nontrivial (finite lattice). By minimality `ψ`
acts trivially on every proper `A`-invariant (normal) subgroup of `Q`, so Theorem 3.7 applied to
the restricted action `φ|_Q` gives `Q` special. -/
theorem exists_minimal_aInvariant_isSpecial_of_pprimeAction
    (φ : A →* MulAut P) (hP : IsPGroup p P)
    (hCop : Nat.Coprime (Nat.card A) (Nat.card P))
    {ψ : A} (hψ_ntriv : ¬ ∀ g : P, (φ ψ) g = g) :
    ∃ Q : Subgroup P, IsAInvariant φ Q ∧ (∃ g ∈ Q, (φ ψ) g ≠ g) ∧ IsSpecial p ↥Q ∧
      ∀ N : Subgroup P, IsAInvariant φ N → N ≤ Q → (∃ g ∈ N, (φ ψ) g ≠ g) → N = Q := by
  classical
  -- Minimal `A`-invariant subgroup on which `ψ` acts nontrivially.
  set S : Set (Subgroup P) := {Q | IsAInvariant φ Q ∧ ∃ g ∈ Q, (φ ψ) g ≠ g} with hS_def
  have hS_ne : S.Nonempty := by
    obtain ⟨g, hg⟩ := not_forall.mp hψ_ntriv
    exact ⟨⊤, IsAInvariant.top φ, g, Subgroup.mem_top g, hg⟩
  obtain ⟨Q, ⟨hQ_inv, hψ_nt⟩, hQ_min⟩ := (Set.toFinite S).exists_minimal hS_ne
  have hmin : ∀ N : Subgroup P, IsAInvariant φ N → N ≤ Q → (∃ g ∈ N, (φ ψ) g ≠ g) → N = Q :=
    fun N hN_inv hN_le hN_nt => le_antisymm hN_le (hQ_min ⟨hN_inv, hN_nt⟩ hN_le)
  refine ⟨Q, hQ_inv, hψ_nt, ?_, hmin⟩
  -- Apply Theorem 3.7 to the restricted action `φ|_Q : A →* MulAut ↥Q`.
  have : Finite ↥Q := inferInstance
  have hQ_pgroup : IsPGroup p ↥Q := hP.to_subgroup Q
  have hQ_cop : Nat.Coprime (Nat.card A) (Nat.card ↥Q) :=
    hCop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card Q)
  -- hypothesis: `ψ` nontrivial on `↥Q`.
  have hψ_nt_Q : ¬ ∀ x : ↥Q, (hQ_inv.restrict ψ) x = x := by
    intro h
    obtain ⟨g, hgQ, hg⟩ := hψ_nt
    apply hg
    have hgg := h ⟨g, hgQ⟩
    rwa [Subtype.ext_iff, IsAInvariant.restrict_apply_val] at hgg
  -- hypothesis: `ψ` trivial on every proper `A`-invariant normal subgroup of `↥Q`.
  have hψ_proper_Q : ∀ N' : Subgroup ↥Q, N'.Normal → IsAInvariant hQ_inv.restrict N' → N' ≠ ⊤ →
      ∀ n ∈ N', (hQ_inv.restrict ψ) n = n := by
    intro N' _ hN'_inv hN'_ne n hn
    set N := N'.map Q.subtype with hN_def
    have hN_inv : IsAInvariant φ N := isAInvariant_map_subtype_of_restrict hQ_inv hN'_inv
    have hN_le : N ≤ Q := Subgroup.map_subtype_le N'
    have hN_ne : N ≠ Q := by
      intro hNQ
      apply hN'_ne
      have hQtop : Q = (⊤ : Subgroup ↥Q).map Q.subtype := by
        rw [← MonoidHom.range_eq_map, Q.range_subtype]
      exact Subgroup.map_injective Q.subtype_injective (hN_def ▸ hNQ.trans hQtop)
    have hψ_triv_N : ∀ m ∈ N, (φ ψ) m = m := by
      intro m hm
      by_contra hmne
      exact hN_ne (hmin N hN_inv hN_le ⟨m, hm, hmne⟩)
    apply Subtype.ext
    rw [IsAInvariant.restrict_apply_val]
    exact hψ_triv_N (n : P) (Subgroup.mem_map_of_mem _ hn)
  exact (isSpecial_of_pprimeAction_trivialOnProper hQ_inv.restrict hQ_pgroup hQ_cop
    hψ_nt_Q hψ_proper_Q).2.2.2.2

/-- **precursor 2 of BG Lemma 4.13** (= **G** Theorem 4.15(ii) input, with
minimality retained; Gorenstein Theorems 3.7/3.8/3.10 combined, `p` odd).
Let `A` be a `p′`-group of automorphisms of the `p`-group `P` (`φ`, coprime)
and `ψ : A` acting nontrivially on `P`. Then `P` has a minimal `A`-invariant
subgroup `Q` on which `ψ` acts nontrivially, and `Q` is **special of exponent `p`**.

The exponent-`p` half replaces the full induction of Gorenstein Theorem 3.10: as `Q` is already
special (Theorem 3.8) and minimal, `ψ` acts trivially on the proper `A`-invariant characteristic
subgroups `Q′` and `Ω₁(Q)`. With `Q′` this gives `[Q, ψ] ⊆ Ω₁(Q)` (via Lemma 3.9(ii) and
`q^p ∈ Q′`), and then `Ω₁(Q) = Q` follows from the stabilization theorem; `Ω₁(Q) = Q` plus class
`≤ 2` and `p` odd give exponent `p` (Lemma 3.9(i)). -/
theorem exists_minimal_aInvariant_isExpPSpecial_of_pprimeAction_with_minimality
    (hp_odd : Odd p)
    (φ : A →* MulAut P) (hP : IsPGroup p P)
    (hCop : Nat.Coprime (Nat.card A) (Nat.card P))
    {ψ : A} (hψ_ntriv : ¬ ∀ g : P, (φ ψ) g = g) :
    ∃ Q : Subgroup P, IsAInvariant φ Q ∧ (∃ g ∈ Q, (φ ψ) g ≠ g) ∧
      IsSpecial p ↥Q ∧ Monoid.exponent ↥Q = p ∧
        ∀ N : Subgroup P, IsAInvariant φ N → N ≤ Q →
          (∃ g ∈ N, (φ ψ) g ≠ g) → N = Q := by
  obtain ⟨Q, hQ_inv, hψ_nt, hQ_special, hmin⟩ :=
    exists_minimal_aInvariant_isSpecial_of_pprimeAction φ hP hCop hψ_ntriv
  refine ⟨Q, hQ_inv, hψ_nt, hQ_special, ?_, hmin⟩
  set φQ : A →* MulAut ↥Q := hQ_inv.restrict with hφQ_def
  have : Finite ↥Q := inferInstance
  have hQ_pgroup : IsPGroup p ↥Q := hP.to_subgroup Q
  have hQ_nilp : Group.IsNilpotent ↥Q := hQ_pgroup.isNilpotent
  have hQ_cop : Nat.Coprime (Nat.card A) (Nat.card ↥Q) :=
    hCop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card Q)
  have hQ_nt : Nontrivial ↥Q := by
    obtain ⟨g, hgQ, hg⟩ := hψ_nt
    have hg1 : g ≠ 1 := fun h => hg (by rw [h, map_one])
    exact ⟨⟨g, hgQ⟩, 1, fun h => hg1 (congrArg Subtype.val h)⟩
  -- `ψ` acts nontrivially on `↥Q`.
  have hψ_nt_Q : ¬ ∀ x : ↥Q, (φQ ψ) x = x := by
    intro h
    obtain ⟨g, hgQ, hg⟩ := hψ_nt
    apply hg
    have hgg := h ⟨g, hgQ⟩
    rwa [Subtype.ext_iff, IsAInvariant.restrict_apply_val] at hgg
  -- `ψ` acts trivially on every proper `A`-invariant subgroup of `↥Q` (minimality).
  have hψ_triv_proper : ∀ K : Subgroup ↥Q, IsAInvariant φQ K → K ≠ ⊤ →
      ∀ z ∈ K, (φQ ψ) z = z := by
    intro K hK_inv hK_ne z hz
    set N := K.map Q.subtype with hN_def
    have hN_inv : IsAInvariant φ N := isAInvariant_map_subtype_of_restrict hQ_inv hK_inv
    have hN_ne : N ≠ Q := by
      intro hNQ
      apply hK_ne
      have hQtop : Q = (⊤ : Subgroup ↥Q).map Q.subtype := by
        rw [← MonoidHom.range_eq_map, Q.range_subtype]
      exact Subgroup.map_injective Q.subtype_injective (hN_def ▸ hNQ.trans hQtop)
    have hψ_triv_N : ∀ m ∈ N, (φ ψ) m = m := fun m hm => by
      by_contra hmne
      exact hN_ne (hmin N hN_inv (Subgroup.map_subtype_le K) ⟨m, hm, hmne⟩)
    apply Subtype.ext
    rw [IsAInvariant.restrict_apply_val]
    exact hψ_triv_N (z : P) (Subgroup.mem_map_of_mem _ hz)
  -- `Q` special ⇒ class `≤ 2` and `p`-th powers lie in `Q′ ⊆ Z(Q)`.
  have hcl : _root_.commutator ↥Q ≤ Subgroup.center ↥Q := by
    rcases hQ_special.2 with hea | ⟨hcomm, _, _⟩
    · exact fun x _ => Subgroup.mem_center_iff.mpr fun g => hea.comm g x
    · exact le_of_eq hcomm
  have hZcomm : ∀ g : ↥Q, g ^ p ∈ _root_.commutator ↥Q := by
    intro g
    rcases hQ_special.2 with hea | ⟨hcomm, hfrat, _⟩
    · rw [hea.pow_eq_one g]; exact one_mem _
    · rw [hcomm, ← hfrat]; exact hQ_special.1.pow_mem_frattini g
  have hZ : ∀ g : ↥Q, g ^ p ∈ Subgroup.center ↥Q := fun g => hcl (hZcomm g)
  -- `ψ` trivial on `Q′ = [Q,Q]` (proper `A`-invariant).
  have hψ_triv_comm : ∀ z ∈ _root_.commutator ↥Q, (φQ ψ) z = z :=
    hψ_triv_proper _ (IsAInvariant.commutator_self φQ)
      (commutator_lt_self_of_isNilpotent_ambient (E := ⊤) (F := ⊤) bot_lt_top.ne').ne
  -- `[Q, ψ] ⊆ Ω₁(Q)`: `(φψ x · x⁻¹)^p = 1`.
  have hquot : ∀ x : ↥Q, (φQ ψ) x * x⁻¹ ∈ Omega ↥Q p 1 := by
    intro x
    refine Omega.mem_of_pow_eq_one (n := 1) ?_
    rw [pow_one, mul_pow_prime_of_class_le_two_of_pow_mem_center hp_odd hcl hZ,
      ← map_pow, inv_pow, hψ_triv_comm (x ^ p) (hZcomm x), mul_inv_cancel]
  -- `Ω₁(Q) = ⊤` (else stabilization forces `ψ` trivial on `Q`).
  have hOmega_top : Omega ↥Q p 1 = ⊤ := by
    by_contra hne
    have hOmega_inv : IsAInvariant φQ (Omega ↥Q p 1) := IsAInvariant.of_characteristic φQ
    have : (Omega ↥Q p 1).Normal := inferInstance
    exact hψ_nt_Q (acts_trivially_of_trivial_on_normal_quotient φQ hQ_pgroup hQ_cop
      hOmega_inv (hψ_triv_proper _ hOmega_inv hne) hquot)
  -- exponent `= p`.
  rw [Monoid.exponent_eq_prime_iff Fact.out]
  exact fun g hg => orderOf_eq_prime
    (Omega.pow_eq_one_of_class_le_two hp_odd hcl (hOmega_top ▸ Subgroup.mem_top g)) hg

end OddOrder.BG.Ch1.S04


