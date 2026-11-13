-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03g_Thm310Core
-- name    : OddOrder_BG_Ch1_Preliminary_S03g_Thm310Core
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:09:28.903796+00:00
-- url     : https://prove2.me/theorems/c504c4c1-fc30-4b80-a824-2a11f87378bc
-- title:
--   BG Theorem 3.10(a): module-level core
-- statement:
--   Builds the representation-theoretic core of Theorem 3.10(a) of Bender–Glauberman, *Local Analysis for the Odd Order Theorem* on top of the free block permutation keystone and the weight-space machinery of §3E. The spine is `prime_card_of_freeBlock_cond3`: a finite subgroup $R\le G$ acting on $V=\bigoplus_i W_i$ and permuting the blocks freely, with a primality condition, has prime order.
--
--   The main declaration: `mulActionSubgroupOfLe` (The restriction of a `↥R`-action on `ι` to a subgroup `↥S` (`S ≤ R`), via the inclusion `↥S →* ↥R`).
--
--   The bundle also proves 6 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S03g_Thm310Core.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S03g_Thm310Core.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_FreeBlockPermutation
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03e_Thm35

open Module LinearMap

namespace OddOrder.BG.Ch1.S03

variable {F : Type*} [Field F] {G : Type*} [Group G]

variable {V : Type*} [AddCommGroup V] [Module F V]

/-- The restriction of a `↥R`-action on `ι` to a subgroup `↥S` (`S ≤ R`), via the inclusion
`↥S →* ↥R`.  Used to apply the free block keystone to `R` and to `⟨x⟩ ≤ R` with the same blocks. -/
@[reducible]
noncomputable def mulActionSubgroupOfLe {R S : Subgroup G} (hSR : S ≤ R)
    {ι : Type*} [MulAction ↥R ι] : MulAction ↥S ι :=
  MulAction.compHom ι (Subgroup.inclusion hSR)

/-- **BG Theorem 3.10(a), block form.** Let a finite subgroup `R ≤ G` act via `ρ` on a
finite-dimensional nontrivial `V = ⨁ᵢ Wᵢ` (internal direct sum), permuting the blocks **freely**
(`ρ h` maps `Wᵢ` onto `W (h • i)`, and `h • i = i ⟹ h = 1`).  If for every `x ∈ R^#` the fixed
subspaces satisfy `finrank V^⟨x⟩ = finrank V^R` (the "prime action" condition (3)), then `|R|` is
prime.

This is the heart of Theorem 3.10(a) Case 2: the keystone `finrank V = |H|·finrank V^H` applied to
`H = R` and to `H = ⟨x⟩` for an `x` of prime order `p` yields `|R|·finrank V^R = p·finrank V^⟨x⟩`,
and the condition collapses this to `|R| = p`. -/
theorem prime_card_of_freeBlock_cond3
    [FiniteDimensional F V] [Nontrivial V] (ρ : Representation F G V)
    {R : Subgroup G} [Finite ↥R] (hRne : R ≠ ⊥)
    {ι : Type*} [Finite ι] [DecidableEq ι] [MulAction ↥R ι]
    {W : ι → Submodule F V} (hW : DirectSum.IsInternal W)
    (hfree : ∀ (h : ↥R) (i : ι), h • i = i → h = 1)
    (hperm : ∀ (h : ↥R) (i : ι), (W i).map (ρ (h : G)) = W (h • i))
    (hcond3 : ∀ x : G, x ∈ R → x ≠ 1 →
      finrank F (Representation.invariants (ρ.comp (Subgroup.zpowers x).subtype))
        = finrank F (Representation.invariants (ρ.comp R.subtype))) :
    ∃ p : ℕ, p.Prime ∧ Nat.card ↥R = p := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  -- Cauchy: pick `x ∈ R` of prime order `p`.
  obtain ⟨p, hp, hpdvd⟩ := (Nat.card ↥R).exists_prime_and_dvd
    (fun h1 => hRne (Subgroup.card_eq_one.mp h1))
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) p hpdvd
  have hxR : (x₀ : G) ∈ R := x₀.2
  have hxord : orderOf (x₀ : G) = p := by
    have h := orderOf_injective R.subtype R.subtype_injective x₀
    rw [hx₀] at h; exact h
  have hxne : (x₀ : G) ≠ 1 := by
    intro h; rw [h, orderOf_one] at hxord; exact hp.ne_one hxord.symm
  have hPR : Subgroup.zpowers (x₀ : G) ≤ R := Subgroup.zpowers_le.mpr hxR
  have hPcard : Nat.card ↥(Subgroup.zpowers (x₀ : G)) = p := by rw [Nat.card_zpowers, hxord]
  have : Finite ↥(Subgroup.zpowers (x₀ : G)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hPR)
  -- Keystone applied to `R`.
  have hR := ρ.finrank_eq_card_mul_finrank_invariants_of_freeBlock R hW hfree hperm
  -- Keystone applied to `⟨x⟩` (same blocks, restricted action).
  let : MulAction ↥(Subgroup.zpowers (x₀ : G)) ι := mulActionSubgroupOfLe hPR
  have hfreeP : ∀ (h : ↥(Subgroup.zpowers (x₀ : G))) (i : ι), h • i = i → h = 1 := by
    intro h i hi
    have hi' : (Subgroup.inclusion hPR h) • i = i := hi
    exact Subgroup.inclusion_injective hPR
      ((hfree (Subgroup.inclusion hPR h) i hi').trans (map_one (Subgroup.inclusion hPR)).symm)
  have hpermP : ∀ (h : ↥(Subgroup.zpowers (x₀ : G))) (i : ι),
      (W i).map (ρ (h : G)) = W (h • i) := by
    intro h i
    have h1 : ((h : G)) = ((Subgroup.inclusion hPR h : ↥R) : G) := by
      rw [Subgroup.coe_inclusion]
    rw [h1]
    exact hperm (Subgroup.inclusion hPR h) i
  have hP := ρ.finrank_eq_card_mul_finrank_invariants_of_freeBlock
    (Subgroup.zpowers (x₀ : G)) hW hfreeP hpermP
  rw [hPcard] at hP
  -- `finrank V^⟨x⟩ = finrank V^R` (the prime-action condition (3)).
  have hcond := hcond3 (x₀ : G) hxR hxne
  rw [hcond] at hP
  -- `finrank V ≥ 1`, hence `finrank V^R ≥ 1`.
  have hdRpos : 0 < finrank F (Representation.invariants (ρ.comp R.subtype)) := by
    rcases Nat.eq_zero_or_pos (finrank F (Representation.invariants (ρ.comp R.subtype)))
      with h0 | h
    · rw [h0, Nat.mul_zero] at hR
      exact absurd hR Module.finrank_pos.ne'
    · exact h
  refine ⟨p, hp, ?_⟩
  -- `|R| · dR = finrank V = p · dR`, cancel `dR`.
  exact Nat.eq_of_mul_eq_mul_right hdRpos (hR.symm.trans hP)

section WeightFreeness

open OddOrder.BG.Ch1.S03e OddOrder.RepresentationTheory

variable (ρ : Representation F G V) {K : Subgroup G}

/-- A nonzero weight space forces `χ k ≠ 0` (`ρ k` is invertible). -/
theorem weightChar_ne_zero {χ : ↥K → F} (hχ : weightSpace ρ K χ ≠ ⊥) (k : ↥K) : χ k ≠ 0 := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  rw [mem_weightSpace] at hv
  intro h0
  have hzero : ρ (k : G) v = 0 := by rw [hv k, h0, zero_smul]
  exact hv0 ((ρ.apply_bijective (k : G)).injective (hzero.trans (map_zero _).symm))

/-- A nonzero weight space forces `χ` to be multiplicative. -/
theorem weightChar_mul {χ : ↥K → F} (hχ : weightSpace ρ K χ ≠ ⊥) (k k' : ↥K) :
    χ (k * k') = χ k * χ k' := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  rw [mem_weightSpace] at hv
  have h1 : ρ ((k * k' : ↥K) : G) v = χ (k * k') • v := hv (k * k')
  have h2 : ρ ((k * k' : ↥K) : G) v = (χ k * χ k') • v := by
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hv k', map_smul, hv k, smul_smul,
      mul_comm (χ k') (χ k)]
  have heqv : χ (k * k') • v = (χ k * χ k') • v := h1.symm.trans h2
  have h3 : (χ (k * k') - χ k * χ k') • v = 0 := by rw [sub_smul, heqv, sub_self]
  rcases smul_eq_zero.mp h3 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hv0

/-- A nonzero weight space gives `χ 1 = 1`. -/
theorem weightChar_one {χ : ↥K → F} (hχ : weightSpace ρ K χ ≠ ⊥) : χ 1 = 1 := by
  have h := weightChar_mul ρ hχ 1 1
  rw [mul_one] at h
  exact (mul_left_cancel₀ (weightChar_ne_zero ρ hχ 1) (by rw [mul_one, ← h])).symm

/-- A nonzero weight space gives `χ a⁻¹ = (χ a)⁻¹`. -/
theorem weightChar_inv {χ : ↥K → F} (hχ : weightSpace ρ K χ ≠ ⊥) (a : ↥K) :
    χ a⁻¹ = (χ a)⁻¹ := by
  have h : χ a * χ a⁻¹ = 1 := by rw [← weightChar_mul ρ hχ, mul_inv_cancel, weightChar_one ρ hχ]
  exact (inv_eq_of_mul_eq_one_right h).symm

/-- **Freeness (L4).** If conjugation by `c⁻¹` is fixed-point-free on the abelian normal kernel `K`
(equivalently `C_K(c) = 1`), then a `conjChar c`-fixed character with nonzero weight space is
trivial.  The Frobenius hypothesis on the complement supplies the fixed-point-freeness. -/
theorem weightChar_eq_one_of_conjChar_fixed [Finite G] [K.Normal]
    {c : G} (hFPF : MonoidHom.FixedPointFree (conjNormalMulAut K c⁻¹))
    {χ : ↥K → F} (hχ : weightSpace ρ K χ ≠ ⊥) (heq : conjChar K c χ = χ) :
    χ = fun _ => 1 := by
  funext j
  obtain ⟨k, hk⟩ := hFPF.commutatorMap_surjective j
  rw [MonoidHom.commutatorMap_apply] at hk
  have hfix : χ (conjNormalMulAut K c⁻¹ k) = χ k := congrFun heq k
  calc χ j = χ (k / conjNormalMulAut K c⁻¹ k) := by rw [hk]
    _ = χ k * (χ (conjNormalMulAut K c⁻¹ k))⁻¹ := by
        rw [div_eq_mul_inv, weightChar_mul ρ hχ, weightChar_inv ρ hχ]
    _ = χ k * (χ k)⁻¹ := by rw [hfix]
    _ = 1 := mul_inv_cancel₀ (weightChar_ne_zero ρ hχ k)

end WeightFreeness

end OddOrder.BG.Ch1.S03


