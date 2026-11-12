-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassTwoSquareIndex
-- name    : OddOrder_GroupTheory_RepresentationTheory_ClassTwoSquareIndex
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:09:24.52672+00:00
-- url     : https://prove2.me/theorems/d53fb8ea-27a3-4fcf-9246-1c8d7791945f
-- title:
--   Faithful irreducibles of $p$-groups with center of order $p$ and the square-index theorem
-- statement:
--   Constructs a faithful irreducible complex representation of a finite $p$-group with $|Z(P)|=p$ and proves the associated square-index theorem.
--
--   The bundle also proves 6 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/ClassTwoSquareIndex.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/ClassTwoSquareIndex.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ExtraspecialFaithful
import Mathlib.GroupTheory.PGroup

namespace OddOrder.RepresentationTheory

open _root_.OddOrder.RepresentationTheory.Representation

variable {P : Type*} [Group P]

/-- **A nontrivial normal subgroup of a finite `p`-group meets the center nontrivially**
(existence form).  The conjugation action of `P` on `↥K` has fixed-point set `K ∩ Z(P)`; the
`p`-group fixed-point congruence `|K| ≡ |K ∩ Z(P)| (mod p)` and `p ∣ |K|` force a second fixed
point besides `1`. -/
theorem exists_mem_center_of_normal_of_isPGroup [Finite P] {p : ℕ} (hp : p.Prime)
    (hP : IsPGroup p P) {K : Subgroup P} (hK : K.Normal) (hKne : K ≠ ⊥) :
    ∃ w : P, w ∈ K ∧ w ∈ Subgroup.center P ∧ w ≠ 1 := by
  classical
  have := hK
  have := Fact.mk hp
  -- conjugation action of `P` on `↥K`
  let : MulDistribMulAction P ↥K :=
    MulDistribMulAction.compHom ↥K (MulAut.conjNormal (H := K))
  have hmod := hP.card_modEq_card_fixedPoints ↥K
  -- `p ∣ |K|`
  have hKnontriv : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
  obtain ⟨n, hn0, hncard⟩ := (hP.to_subgroup K).nontrivial_iff_card.mp hKnontriv
  have hpdvd : p ∣ Nat.card ↥K := hncard ▸ dvd_pow_self p hn0.ne'
  -- hence `p ∣ |fixedPoints|`
  have hpfix : p ∣ Nat.card (MulAction.fixedPoints P ↥K) :=
    (Nat.modEq_zero_iff_dvd.mp ((hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hpdvd))))
  -- `1` is a fixed point, and `|fixedPoints| ≥ p ≥ 2` gives a second one
  have h1fix : (1 : ↥K) ∈ MulAction.fixedPoints P ↥K := fun g => smul_one g
  have : Finite ↥(MulAction.fixedPoints P ↥K) := Subtype.finite
  have hpos : 0 < Nat.card ↥(MulAction.fixedPoints P ↥K) :=
    Nat.card_pos_iff.mpr ⟨⟨⟨1, h1fix⟩⟩, inferInstance⟩
  have hcard2 : 2 ≤ Nat.card ↥(MulAction.fixedPoints P ↥K) :=
    le_trans hp.two_le (Nat.le_of_dvd hpos hpfix)
  have hnontriv : Nontrivial ↥(MulAction.fixedPoints P ↥K) :=
    Finite.one_lt_card_iff_nontrivial.mp hcard2
  obtain ⟨w, hwne⟩ := exists_ne (⟨⟨1, K.one_mem⟩, h1fix⟩ : ↥(MulAction.fixedPoints P ↥K))
  -- unpack: `w` is a fixed point of the conjugation action, i.e. central
  refine ⟨(w : ↥K), (w : ↥K).2, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    have hfix := w.2 g
    have hcoe : ((g • (w : ↥K) : ↥K) : P) = g * (w : ↥K) * g⁻¹ := rfl
    have := congrArg (Subtype.val : ↥K → P) hfix
    rw [hcoe] at this
    calc g * (w : ↥K) = g * (w : ↥K) * g⁻¹ * g := by group
      _ = (w : ↥K) * g := by rw [this]
  · intro h1
    apply hwne
    apply Subtype.ext
    apply Subtype.ext
    exact h1

/-- **Some irreducible character separates a nontrivial element from `1`**: for `z ≠ 1` there is
`χ ∈ Irr P` with `χ(z) ≠ χ(1)`.  Otherwise the column relation at the non-conjugate pair `(z, 1)`
(`column_orthogonality_not_conjugate`) would read `∑ χ(1)² = 0`, contradicting the Burnside
degree-sum `∑ χ(1)² = |P| ≠ 0` (`sumIrreducibleDegreeSq`). -/
theorem exists_irreducibleCharacter_apply_ne [Finite P] {z : P} (hz : z ≠ 1) :
    ∃ χ : IrreducibleCharacter P,
      (χ : ClassFunction P ℂ) z ≠ (χ : ClassFunction P ℂ) 1 := by
  classical
  by_contra hall
  push Not at hall
  have hnc : ¬ IsConj z 1 := fun hc => hz (isConj_one_left.mp hc)
  have h0 := column_orthogonality_not_conjugate (g := z) (h := 1) hnc
  have hsq : ∀ χ : IrreducibleCharacter P,
      ((χ : ClassFunction P ℂ) z) * star ((χ : ClassFunction P ℂ) 1)
        = ((χ : ClassFunction P ℂ) 1) ^ 2 := by
    intro χ
    obtain ⟨d, -, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
    rw [hall χ, hd, star_natCast, sq]
  rw [Finset.sum_congr rfl (fun χ _ => hsq χ), sumIrreducibleDegreeSq] at h0
  exact Nat.cast_ne_zero.mpr Nat.card_pos.ne' h0

/-- **Existence of a faithful irreducible representation** for a finite `p`-group with center of
order `p`.  Pick `z ≠ 1` central and `χ ∈ Irr P` with `χ(z) ≠ χ(1)`
(`exists_irreducibleCharacter_apply_ne`); the kernel of the underlying representation is a normal
subgroup meeting the center trivially (the center is cyclic of prime order and `z` survives), so
it is trivial (`exists_mem_center_of_normal_of_isPGroup`). -/
theorem exists_faithful_irreducible_of_card_center_eq_prime [Finite P] {p : ℕ} (hp : p.Prime)
    (hP : IsPGroup p P) (hZ : Nat.card (Subgroup.center P) = p) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
      (ρ : Representation ℂ P V), ρ.IsIrreducible ∧ Function.Injective ρ := by
  classical
  -- a nontrivial central element
  have hZnt : Nontrivial ↥(Subgroup.center P) :=
    Finite.one_lt_card_iff_nontrivial.mp (hZ ▸ hp.one_lt)
  obtain ⟨z', hz'ne⟩ := exists_ne (1 : ↥(Subgroup.center P))
  have hzc : (z' : P) ∈ Subgroup.center P := z'.2
  have hzne : (z' : P) ≠ 1 := fun h => hz'ne (Subtype.ext h)
  obtain ⟨χ, hχ⟩ := exists_irreducibleCharacter_apply_ne hzne
  obtain ⟨V, _, _, _, ρ, hirr, hchar⟩ := χ.2
  have := hirr
  refine ⟨V, ‹_›, ‹_›, ‹_›, ρ, hirr, ?_⟩
  -- `ρ z ≠ 1`
  have hρz : ρ (z' : P) ≠ 1 := by
    intro he
    apply hχ
    rw [show ((χ : ClassFunction P ℂ) : P → ℂ) (z' : P) = ρ.character (z' : P)
        from congrFun hchar _,
      show ((χ : ClassFunction P ℂ) : P → ℂ) 1 = ρ.character 1 from congrFun hchar _,
      ρ.char_one]
    change LinearMap.trace ℂ V (ρ (z' : P)) = _
    rw [he]
    exact LinearMap.trace_one ℂ V
  -- the kernel subgroup of `ρ`
  let K : Subgroup P :=
    { carrier := {g | ρ g = 1}
      one_mem' := map_one ρ
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_mul, ha, hb, one_mul]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        have h := map_mul ρ a⁻¹ a
        rw [inv_mul_cancel, map_one, ha, mul_one] at h
        exact h.symm }
  have hmemK : ∀ g : P, g ∈ K ↔ ρ g = 1 := fun g => Iff.rfl
  have hKnorm : K.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hmemK] at hn ⊢
    rw [map_mul, map_mul, hn, mul_one, ← map_mul, mul_inv_cancel, map_one]
  -- the kernel is trivial: it meets the (prime-order) center trivially
  have hKbot : K = ⊥ := by
    by_contra hne
    obtain ⟨w, hwK, hwZ, hwne⟩ := exists_mem_center_of_normal_of_isPGroup hp hP hKnorm hne
    -- the center is cyclic of order `p`, so `w` generates it and `z ∈ ⟨w⟩ ≤ K`
    have hw'ne : (⟨w, hwZ⟩ : ↥(Subgroup.center P)) ≠ 1 := fun h =>
      hwne (by simpa using congrArg (Subtype.val : ↥(Subgroup.center P) → P) h)
    have hord : orderOf (⟨w, hwZ⟩ : ↥(Subgroup.center P)) = p := by
      have hdvd : orderOf (⟨w, hwZ⟩ : ↥(Subgroup.center P)) ∣ p := hZ ▸ orderOf_dvd_natCard _
      rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hself
      · exact absurd (orderOf_eq_one_iff.mp h1) hw'ne
      · exact hself
    have htop : Subgroup.zpowers (⟨w, hwZ⟩ : ↥(Subgroup.center P)) = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, hord, hZ]
    have hzmem : (⟨(z' : P), hzc⟩ : ↥(Subgroup.center P)) ∈
        Subgroup.zpowers (⟨w, hwZ⟩ : ↥(Subgroup.center P)) := htop ▸ Subgroup.mem_top _
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hzmem
    have hzw : w ^ n = (z' : P) := by
      have := congrArg (Subtype.val : ↥(Subgroup.center P) → P) hn
      simpa using this
    exact hρz ((hmemK _).mp (hzw ▸ K.zpow_mem hwK n))
  -- injectivity from the trivial kernel
  intro a b hab
  have hker : a⁻¹ * b ∈ K := by
    rw [hmemK, map_mul]
    have hinv : ρ a⁻¹ * ρ a = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rw [← hab]
    exact hinv
  have : a⁻¹ * b = 1 := by rwa [hKbot, Subgroup.mem_bot] at hker
  calc a = a * (a⁻¹ * b) := by rw [this, mul_one]
    _ = b := by group

/-- **Square-index theorem for class-`2` `p`-groups with center of prime order** (the
Gorenstein 5.5.5 mass formula, upgraded by faithful-existence): if `P` is a finite `p`-group with
`commutator P ≤ Z(P)` and `|Z(P)| = p`, then `|P : Z(P)|` is a perfect square. -/
theorem card_quotient_center_isSquare_of_class_two [Finite P] {p : ℕ} (hp : p.Prime)
    (hP : IsPGroup p P) (hZ : Nat.card (Subgroup.center P) = p)
    (hcl : commutator P ≤ Subgroup.center P) :
    IsSquare (Nat.card (P ⧸ Subgroup.center P)) := by
  obtain ⟨V, _, _, _, ρ, hirr, hinj⟩ :=
    exists_faithful_irreducible_of_card_center_eq_prime hp hP hZ
  have := hirr
  have : Invertible (Nat.card P : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact ⟨Module.finrank ℂ V, by
    rw [← sq_finrank_eq_card_quotient_center ρ hinj hcl, sq]⟩

/-- A prime power `p^n` is a perfect square only for even `n`. -/
theorem even_of_isSquare_prime_pow {p n : ℕ} (hp : p.Prime) (h : IsSquare (p ^ n)) :
    Even n := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨k, -, hmk⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro m hm.symm)
  subst hmk
  rw [← pow_add] at hm
  exact Nat.pow_right_injective hp.two_le hm ▸ ⟨k, rfl⟩

/-- **The (11.7) Galois-case parity kernel**: a finite class-`2` `p`-group with center of order
`p` and total order `p^(q+1)` forces `q` *even* (its central quotient has order `p^q`, a perfect
square by `card_quotient_center_isSquare_of_class_two`).  Applied with `q = |W₁|` an odd prime,
this refutes the `U`-irreducible (Galois) case of Peterfalvi (11.7). -/
theorem even_of_card_eq_prime_pow_succ_of_class_two [Finite P] {p q : ℕ} (hp : p.Prime)
    (hP : IsPGroup p P) (hZ : Nat.card (Subgroup.center P) = p)
    (hcl : commutator P ≤ Subgroup.center P)
    (hcard : Nat.card P = p ^ (q + 1)) : Even q := by
  have hsq := card_quotient_center_isSquare_of_class_two hp hP hZ hcl
  have hquot : Nat.card (P ⧸ Subgroup.center P) = p ^ q := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)
    rw [hcard, hZ, pow_succ] at h1
    exact (Nat.eq_of_mul_eq_mul_right hp.pos h1.symm)
  rw [hquot] at hsq
  exact even_of_isSquare_prime_pow hp hsq

end OddOrder.RepresentationTheory


