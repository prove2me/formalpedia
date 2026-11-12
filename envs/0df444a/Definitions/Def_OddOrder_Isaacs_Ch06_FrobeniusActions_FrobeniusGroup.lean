-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup
-- name    : OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:32:04.05055+00:00
-- url     : https://prove2.me/theorems/73da1772-c74a-4d7c-8534-f2a69d7b7a23
-- title:
--   Isaacs Ch. 6: abelian $Z$-groups, Lemma 6.16, Frobenius groups (Thm 6.4)
-- statement:
--   Part of the Isaacs, *Finite Group Theory*, Chapter 6 (Frobenius actions) formalization (pp. 184–193): finite abelian $Z$-groups, Lemma 6.16, and the Frobenius group Theorem 6.4.
--
--   Main definitions: `IsFrobeniusGroup` ($G$ has a nontrivial normal subgroup $N$, the Frobenius kernel, with the Frobenius complement acting appropriately), `conjugatesFinset`, and `frobeniusGroup` (the partition of §6B attached to a Frobenius group: the kernel together with the conjugates of the complement).
--
--   The bundle also proves 27 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusGroup.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusGroup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusActionTI
import Definitions.Def_OddOrder_Mathlib_Subgroup

namespace OddOrder.Isaacs.Ch06

open scoped IsMulCommutative

section

/-- A finite abelian group whose Sylow subgroups are all cyclic is cyclic. -/
theorem isCyclic_of_sylow_isCyclic
    {A : Type*} [Group A] [Finite A] [IsMulCommutative A]
    (hSylow : ∀ p : ℕ, p.Prime → ∀ P : Sylow p A, IsCyclic P) :
    IsCyclic A := by
  have : IsZGroup A := ⟨hSylow⟩
  exact inferInstance

end

section

open Int

/-- Helper for the `p = 2` branch of Lemma 6.16: if `2 ^ (e + 1) ∣ i ^ 2 - 1`, then
`2 ^ e` divides one of `i - 1` or `i + 1`. -/
private theorem two_pow_dvd_or_of_sq_sub_one {e : ℕ} {i : ℤ}
    (h : (2 : ℤ) ^ (e + 1) ∣ i ^ 2 - 1) :
    (2 : ℤ) ^ e ∣ i - 1 ∨ (2 : ℤ) ^ e ∣ i + 1 := by
  -- `i` must be odd, otherwise `i^2 - 1` is odd, contradicting even divisibility.
  have h_fact : (i ^ 2 - 1 : ℤ) = (i - 1) * (i + 1) := by ring
  rw [h_fact] at h
  have h_i_odd : Odd i := by
    rcases Int.even_or_odd i with ⟨k, rfl⟩ | hodd
    · -- `i = k + k`, so `(i - 1)(i + 1) = (k+k-1)(k+k+1)` is a product of two odd numbers; odd.
      exfalso
      have h2 : (2 : ℤ) ∣ (k + k - 1) * (k + k + 1) :=
        (dvd_pow_self 2 (Nat.succ_ne_zero _)).trans h
      rcases Int.prime_two.dvd_or_dvd h2 with h2' | h2'
      · -- `2 ∣ k + k - 1` is impossible mod 2.
        omega
      · omega
    · exact hodd
  obtain ⟨j, rfl⟩ := h_i_odd
  -- Now `i = 2 j + 1`. Factorization: `(i-1)(i+1) = (2j)(2j+2) = 4 · j · (j+1)`.
  have h_dvd' : (2 : ℤ) ^ (e + 1) ∣ 4 * (j * (j + 1)) := by
    have h_re : ((2 * j + 1) - 1) * ((2 * j + 1) + 1) = 4 * (j * (j + 1)) := by ring
    rwa [h_re] at h
  -- Case split on parity of `j` (then either `j` or `j + 1` contributes a 2-power).
  rcases Int.even_or_odd j with hjeven | hjodd
  · -- `j = 2k` (well, `j = k + k`). Then `i - 1 = 4k`.
    obtain ⟨k, rfl⟩ := hjeven
    -- Coprimality: `2k + 1` (i.e. `(k + k) + 1`) is odd.
    have h_coprime : IsCoprime ((2 : ℤ) ^ (e + 1)) ((k + k) + 1) := by
      apply IsCoprime.pow_left
      exact ⟨-k, 1, by ring⟩
    -- Rewrite `4 * ((k + k) * ((k + k) + 1))` as `(4 * (k + k)) * ((k + k) + 1)` to factor.
    have h_dvd'' : (2 : ℤ) ^ (e + 1) ∣ (4 * (k + k)) * ((k + k) + 1) := by
      convert h_dvd' using 1; ring
    have h_dvd_bulk : (2 : ℤ) ^ (e + 1) ∣ 4 * (k + k) :=
      h_coprime.dvd_of_dvd_mul_right h_dvd''
    -- `4 * (k + k) = 8 k = 2 · (4 k)`. Divide by 2: `2^e ∣ 4k = i - 1`.
    left
    rcases h_dvd_bulk with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h2pow : (2 : ℤ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
    have hm' : (4 : ℤ) * (k + k) = 2 * (2 ^ e * m) := by rw [hm, h2pow]; ring
    -- `((k + k) + 1) - 1 = k + k`, so `i - 1 = (2 j + 1) - 1` with `j = k + k`.
    linarith
  · -- `j = 2k + 1` for some `k`. Then `i + 1 = 2(2k+1) + 2 = 4(k+1)`.
    obtain ⟨k, rfl⟩ := hjodd
    right
    -- `2 k + 1` is odd.
    have h_coprime : IsCoprime ((2 : ℤ) ^ (e + 1)) (2 * k + 1) := by
      apply IsCoprime.pow_left
      exact ⟨-k, 1, by ring⟩
    -- `4 * ((2k+1) * ((2k+1) + 1)) = (4 * (2 * (k + 1))) * (2 k + 1)`.
    have h_dvd'' : (2 : ℤ) ^ (e + 1) ∣ (4 * (2 * (k + 1))) * (2 * k + 1) := by
      convert h_dvd' using 1; ring
    have h_dvd_bulk : (2 : ℤ) ^ (e + 1) ∣ 4 * (2 * (k + 1)) :=
      h_coprime.dvd_of_dvd_mul_right h_dvd''
    rcases h_dvd_bulk with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h2pow : (2 : ℤ) ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
    have hm' : (4 : ℤ) * (2 * (k + 1)) = 2 * (2 ^ e * m) := by rw [hm, h2pow]; ring
    -- `(2 * (2 k + 1) + 1) + 1 = 4 k + 4 = 4 (k + 1)`, so this is `i + 1`.
    linarith

/-- **Isaacs Lemma 6.16**. Let `p` be a prime and `e` a positive integer. If `i : ℤ` satisfies
`i ^ p ≡ 1 (mod p ^ e)`, then one of the following holds:
* `i ≡ 1 (mod p ^ (e - 1))`,
* `p = 2` and `i ≡ -1 (mod 2 ^ e)`,
* `p = 2` and `i ≡ 2 ^ (e - 1) - 1 (mod 2 ^ e)`. -/
theorem pow_prime_modEq_one_cases {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 0 < e) {i : ℤ}
    (h : i ^ p ≡ 1 [ZMOD ((p : ℤ) ^ e)]) :
    i ≡ 1 [ZMOD ((p : ℤ) ^ (e - 1))] ∨
    (p = 2 ∧ i ≡ -1 [ZMOD ((2 : ℤ) ^ e)]) ∨
    (p = 2 ∧ i ≡ ((2 : ℤ) ^ (e - 1) - 1) [ZMOD ((2 : ℤ) ^ e)]) := by
  -- Normalise `e = e' + 1` so `e - 1 = e'` is definitionally clean.
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, (Nat.sub_add_cancel he).symm⟩
  simp only [Nat.add_sub_cancel]
  -- Convert hypothesis to divisibility (`a ≡ b [ZMOD n]` gives `n ∣ b - a`).
  have h_dvd : ((p : ℤ) ^ (e' + 1)) ∣ i ^ p - 1 := h.symm.dvd
  rcases hp.eq_two_or_odd' with rfl | hp_odd
  · -- ##### Case p = 2 #####
    rcases two_pow_dvd_or_of_sq_sub_one h_dvd with h_left | h_right
    · -- (a) holds: `2 ^ e' ∣ i - 1` ⇒ `i ≡ 1 (mod 2^e')`.
      left
      refine Int.modEq_iff_dvd.mpr ?_
      have : (1 - i : ℤ) = -(i - 1) := by ring
      rw [this]
      exact dvd_neg.mpr h_left
    · -- `2 ^ e' ∣ i + 1`. Case-split on whether `2 ^ (e' + 1) ∣ i + 1`.
      by_cases h_b : (2 : ℤ) ^ (e' + 1) ∣ i + 1
      · -- (b): `2 ^ (e' + 1) ∣ i + 1`, i.e. `i ≡ -1 (mod 2 ^ (e' + 1))`.
        right; left
        refine ⟨rfl, Int.modEq_iff_dvd.mpr ?_⟩
        have : (-1 - i : ℤ) = -(i + 1) := by ring
        rw [this]
        exact dvd_neg.mpr h_b
      · -- (c): write `i + 1 = 2 ^ e' * a` with `a` odd (else (b) would hold).
        right; right
        refine ⟨rfl, Int.modEq_iff_dvd.mpr ?_⟩
        obtain ⟨a, ha⟩ := h_right
        have ha_odd : Odd a := by
          rcases Int.even_or_odd a with hev | hodd
          · -- `a = b + b`, so `i + 1 = 2 ^ e' * (b + b) = 2 * (2^e' * b)`, contradicting `h_b`.
            exfalso
            obtain ⟨b, rfl⟩ := hev
            apply h_b
            refine ⟨b, ?_⟩
            rw [ha, pow_succ]; ring
          · exact hodd
        obtain ⟨b, rfl⟩ := ha_odd
        -- `i + 1 = 2^e' * (2 b + 1)`, so `i = 2^e' * (2 b + 1) - 1 = (2^e' - 1) + 2^(e'+1) * b`.
        -- Goal: `2 ^ (e' + 1) ∣ (2 ^ e' - 1) - i`.
        refine ⟨-b, ?_⟩
        have hi : i = (2 : ℤ) ^ e' * (2 * b + 1) - 1 := by linarith
        rw [hi, pow_succ]; ring
  · -- ##### Case p odd ##### (LTE).
    left
    -- Step 1: `p ∣ i - 1` from Fermat + hypothesis reduced modulo `p`.
    have h_p_dvd_sub : (p : ℤ) ∣ i - 1 := by
      have h_fermat : i ^ p ≡ i [ZMOD (p : ℤ)] := Int.ModEq.pow_prime_eq_self hp i
      have h_mod_p : i ^ p ≡ 1 [ZMOD (p : ℤ)] :=
        h.of_dvd (dvd_pow_self _ (Nat.succ_ne_zero _))
      exact (h_fermat.symm.trans h_mod_p).symm.dvd
    -- Step 2: `p ∤ i` (else `p ∣ 1`).
    have h_p_not_dvd_i : ¬ (p : ℤ) ∣ i := by
      intro hpi
      have h1 : (p : ℤ) ∣ 1 := by
        have := dvd_sub hpi h_p_dvd_sub
        simpa using this
      have hp_eq : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h1
      have hp_eq' : p = 1 := by exact_mod_cast hp_eq
      exact hp.one_lt.ne' hp_eq'
    -- Step 3: LTE: `emultiplicity p (i^p - 1) = emultiplicity p (i - 1) + emultiplicity p p`.
    have h_LTE :=
      Int.emultiplicity_pow_sub_pow hp hp_odd (x := i) (y := 1) (by simpa using h_p_dvd_sub)
        h_p_not_dvd_i p
    rw [one_pow, hp.emultiplicity_self] at h_LTE
    -- Convert the hypothesis into an `emultiplicity` lower bound.
    have h_e_le : ((e' + 1 : ℕ) : ℕ∞) ≤ emultiplicity (p : ℤ) (i ^ p - 1) :=
      pow_dvd_iff_le_emultiplicity.mp h_dvd
    rw [h_LTE] at h_e_le
    -- `(e' + 1 : ℕ∞) ≤ m + 1 ⇒ (e' : ℕ∞) ≤ m`.
    have h_em : (e' : ℕ∞) ≤ emultiplicity (p : ℤ) (i - 1) := by
      have h_cast : ((e' + 1 : ℕ) : ℕ∞) = (e' : ℕ∞) + 1 := by push_cast; rfl
      rw [h_cast] at h_e_le
      exact (WithTop.add_le_add_iff_right WithTop.one_ne_top).mp h_e_le
    have h_pe'_dvd : (p : ℤ) ^ e' ∣ i - 1 := pow_dvd_iff_le_emultiplicity.mpr h_em
    refine Int.modEq_iff_dvd.mpr ?_
    have : (1 - i : ℤ) = -(i - 1) := by ring
    rw [this]
    exact dvd_neg.mpr h_pe'_dvd

end

section

/-- A **Frobenius group**: `G` has a nontrivial normal subgroup `N` (the *Frobenius kernel*)
complemented by a nontrivial subgroup `A` (the *Frobenius complement*), with the conjugation
action of `A` on `N` being Frobenius.

This is Isaacs's condition (1) of Thm 6.4; the other three equivalent conditions are proven
separately as `trivialIntersection` / `centralizer_complement_le` / `centralizer_kernel_le`,
with converse constructors `of_trivialIntersection` / `of_centralizer_complement_le` /
`of_centralizer_kernel_le`. -/
structure IsFrobeniusGroup (G : Type*) [Group G] (N A : Subgroup G) : Prop where
  /-- The kernel `N` is normal in `G`. -/
  isNormal : N.Normal
  /-- `N` and `A` are complements: `N ⊓ A = ⊥` and the product map `N × A → G` is a bijection. -/
  isComplement : Subgroup.IsComplement' N A
  /-- The kernel is nontrivial. -/
  ne_bot_kernel : N ≠ ⊥
  /-- The complement is nontrivial. -/
  ne_bot_complement : A ≠ ⊥
  /-- The conjugation action of `A` on `N` is Frobenius (Isaacs Thm 6.4 condition (1)). -/
  conj_frobenius : ∀ a ∈ A, a ≠ 1 → ∀ n ∈ N, n ≠ 1 → a * n * a⁻¹ ≠ n

namespace IsFrobeniusGroup

variable {G : Type*} [Group G] {N A : Subgroup G}

/-- A subgroup-pair Frobenius group gives a Frobenius action of the complement on the kernel by
conjugation. This is the bridge between the pair form of Isaacs Thm 6.4 and the action-based
definition used for Lemma 6.1. -/
theorem toFrobeniusAction (h : IsFrobeniusGroup G N A) :
    letI : N.Normal := h.isNormal
    @IsFrobeniusAction A N _ _
      (MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp A.subtype)) := by
  let : N.Normal := h.isNormal
  let : MulDistribMulAction A N :=
    MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp A.subtype)
  intro a ha n hn hfix
  have haG : (a : G) ≠ 1 := fun haG => ha (Subtype.ext haG)
  have hnG : (n : G) ≠ 1 := fun hnG => hn (Subtype.ext hnG)
  have hfixG : (a : G) * (n : G) * (a : G)⁻¹ = n := Subtype.ext_iff.mp hfix
  exact h.conj_frobenius (a : G) a.2 haG (n : G) n.2 hnG hfixG

/-- Subgroup-pair version of Isaacs Lemma 6.1: in a finite Frobenius group,
`|N| ≡ 1 (mod |A|)`. -/
theorem card_kernel_modEq_one [Finite G] (h : IsFrobeniusGroup G N A) :
    Nat.card N ≡ 1 [MOD Nat.card A] := by
  classical
  let : N.Normal := h.isNormal
  let : MulDistribMulAction A N :=
    MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp A.subtype)
  have : Fintype N := Fintype.ofFinite N
  have : Fintype A := Fintype.ofFinite A
  simpa only [Fintype.card_eq_nat_card] using
    IsFrobeniusAction.card_modEq_one (A := A) (N := N) h.toFrobeniusAction

/-- Subgroup-pair version of Isaacs Lemma 6.1: in a finite Frobenius group, the kernel and
complement have coprime orders. -/
theorem coprime_card_kernel_complement [Finite G] (h : IsFrobeniusGroup G N A) :
    Nat.Coprime (Nat.card N) (Nat.card A) := by
  classical
  let : N.Normal := h.isNormal
  let : MulDistribMulAction A N :=
    MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp A.subtype)
  have : Fintype N := Fintype.ofFinite N
  have : Fintype A := Fintype.ofFinite A
  simpa only [Fintype.card_eq_nat_card] using
    IsFrobeniusAction.coprime_card (A := A) (N := N) h.toFrobeniusAction

/-- **Frobenius-group image congruence.** In a finite Frobenius group `G = N ⋊ A`, for *any*
homomorphism `φ : G →* X`, the image `φ(N)` of the kernel satisfies `|φ(N)| ≡ 1 (mod |A|)`.

By Noether's first isomorphism theorem `φ(N) ≅ N / ker(φ|_N)`, and the Frobenius conjugation action
of `A` on `N` (`toFrobeniusAction`) descends — since `ker(φ|_N)` is `A`-invariant (`φ` is a
homomorphism on all of `G`, so it intertwines the conjugation) — to a Frobenius action of `A` on the
quotient `N / ker(φ|_N)` (Isaacs Cor 6.2, `IsFrobeniusAction.quotient`).  Isaacs Lemma 6.1
(`IsFrobeniusAction.card_modEq_one`) then gives `|N / ker(φ|_N)| ≡ 1 (mod |A|)`.

This is the mechanism behind Peterfalvi's `|Ū| ≡ 1 (mod q)` for the chief-factor image
`Ū = U/C_U(H̄)` in (11.8.1): take `φ` the `U W₁`-action on `H̄`, `N = U`, `A = W₁`, so that
`φ(U) = Ū` and `|A| = q`. -/
theorem card_range_comp_subtype_modEq_one [Finite G] (h : IsFrobeniusGroup G N A)
    {X : Type*} [Group X] (φ : G →* X) :
    Nat.card ↥((φ.comp N.subtype).range) ≡ 1 [MOD Nat.card A] := by
  classical
  let : N.Normal := h.isNormal
  let : MulDistribMulAction A N :=
    MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp A.subtype)
  have hFA : IsFrobeniusAction A N := h.toFrobeniusAction
  set ψ : N →* X := φ.comp N.subtype with hψ
  set K : Subgroup N := ψ.ker with hK
  have : K.Normal := by rw [hK]; infer_instance
  -- `K = ker(φ|_N)` is `A`-invariant: for `a ∈ A`, `m ∈ K`, the conjugate `a • m` has
  -- `φ(a·m·a⁻¹) = φ(a)·φ(m)·φ(a)⁻¹ = φ(a)·1·φ(a)⁻¹ = 1`, using `φ` a homomorphism on all of `G`.
  have hinv : ∀ a : A, ∀ m ∈ K, a • m ∈ K := by
    intro a m hm
    rw [hK, MonoidHom.mem_ker] at hm ⊢
    have hcoe : ((a • m : N) : G) = (a : G) * (m : G) * (a : G)⁻¹ := rfl
    have hψa : ψ (a • m) = φ ((a : G) * (m : G) * (a : G)⁻¹) := by
      rw [hψ]; exact congrArg φ hcoe
    have hφm : φ (m : G) = 1 := by rw [hψ] at hm; exact hm
    rw [hψa, map_mul, map_mul, map_inv, hφm, mul_one, mul_inv_cancel]
  -- descend the Frobenius conjugation action to `N ⧸ K`
  let : MulDistribMulAction A (N ⧸ K) :=
    IsFrobeniusAction.invariantQuotientMulDistribMulAction K hinv
  have hFAQ : IsFrobeniusAction A (N ⧸ K) := hFA.quotient K hinv
  have : Fintype A := Fintype.ofFinite A
  have : Fintype (N ⧸ K) := Fintype.ofFinite _
  have hcong : Nat.card (N ⧸ K) ≡ 1 [MOD Nat.card A] := by
    simpa only [Fintype.card_eq_nat_card] using IsFrobeniusAction.card_modEq_one hFAQ
  -- `N ⧸ K ≅ range ψ` (Noether I), so `|range ψ| = |N ⧸ K| ≡ 1 (mod |A|)`
  rwa [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv] at hcong

/-- Given `IsComplement' N A`, every `g : G` factors uniquely as `n * a` with `n ∈ N`, `a ∈ A`. -/
private theorem _root_.Subgroup.IsComplement'.factor
    (hC : Subgroup.IsComplement' N A) (g : G) :
    ∃ (n : G) (a : G), n ∈ N ∧ a ∈ A ∧ n * a = g := by
  obtain ⟨⟨n, a⟩, hna⟩ := (hC.existsUnique g).exists
  exact ⟨n, a, n.2, a.2, hna⟩

/-- **Isaacs Thm 6.4 (1) ⇒ (2)**: Frobenius group ⇒ trivial intersection.

If `g ∉ A`, then `A ⊓ A^g = ⊥`. (Here `A^g = g A g⁻¹ = (MulAut.conj g) '' A`.) -/
theorem trivialIntersection (h : IsFrobeniusGroup G N A) :
    ∀ g : G, g ∉ A → A ⊓ Subgroup.map (MulAut.conj g).toMonoidHom A = ⊥ := by
  intro g hg
  -- Outline: assume `A ⊓ A^g ≠ ⊥`, derive `g ∈ A`, contradiction.
  by_contra h_ne
  apply hg
  -- Factor `g = n * a` with `n ∈ N`, `a ∈ A` (from `IsComplement' N A`).
  obtain ⟨n, a, hnN, haA, hna⟩ := h.isComplement.factor g
  -- Get a nontrivial `x ∈ A ⊓ A^g`.
  have h_ne_bot : A ⊓ Subgroup.map (MulAut.conj g).toMonoidHom A ≠ ⊥ := h_ne
  obtain ⟨x, hxAg, hx_ne⟩ : ∃ x ∈ A ⊓ Subgroup.map (MulAut.conj g).toMonoidHom A, x ≠ 1 := by
    by_contra h_all
    apply h_ne_bot
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    by_contra hy_ne
    exact h_all ⟨y, hy, hy_ne⟩
  rw [Subgroup.mem_inf] at hxAg
  obtain ⟨hxA, hxAg⟩ := hxAg
  -- `x = g * b * g⁻¹` for some `b ∈ A`.
  rw [Subgroup.mem_map] at hxAg
  obtain ⟨b, hbA, hxeq⟩ := hxAg
  simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom] at hxeq
  -- Substitute `g = n * a`. Then `x = (n * a) * b * (n * a)⁻¹ = n * (a b a⁻¹) * n⁻¹`.
  have hxeq' : x = n * (a * b * a⁻¹) * n⁻¹ := by
    rw [← hxeq, ← hna]
    group
  -- Let `b' := a * b * a⁻¹ ∈ A`. Then `x = n * b' * n⁻¹` and `b' ∈ A`.
  set b' := a * b * a⁻¹ with hb'_def
  have hb'_mem : b' ∈ A := by
    rw [hb'_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ haA hbA) (Subgroup.inv_mem _ haA)
  have hx_eq2 : x = n * b' * n⁻¹ := hxeq'
  -- Consider `b'⁻¹ * x = b'⁻¹ * (n * b' * n⁻¹)`.
  -- This is in `A` (both `b'⁻¹` and `x` are in `A`).
  -- This is also in `N`: rewrite as `(b'⁻¹ * n * b') * n⁻¹`. The factor `b'⁻¹ * n * b' ∈ N`
  -- by normality of `N`, and `n⁻¹ ∈ N`, so the product is in `N`.
  have h_comm_elem : b'⁻¹ * (n * b' * n⁻¹) ∈ A := by
    apply Subgroup.mul_mem
    · exact Subgroup.inv_mem _ hb'_mem
    · rw [← hx_eq2]; exact hxA
  have h_comm_elem' : b'⁻¹ * (n * b' * n⁻¹) ∈ N := by
    -- Rewrite as `(b'⁻¹ * n * b') * n⁻¹`.
    have h_eq : b'⁻¹ * (n * b' * n⁻¹) = (b'⁻¹ * n * b') * n⁻¹ := by group
    rw [h_eq]
    apply Subgroup.mul_mem _ _ (Subgroup.inv_mem _ hnN)
    -- `b'⁻¹ * n * b' ∈ N` by normality.
    have := h.isNormal.conj_mem' n hnN b'
    exact this
  have hdisj : Disjoint N A := h.isComplement.disjoint
  -- So `b'⁻¹ * (n * b' * n⁻¹) = 1`, i.e., `n * b' * n⁻¹ = b'`, i.e., `b'` commutes with `n`.
  have h_one : b'⁻¹ * (n * b' * n⁻¹) = 1 := Subgroup.disjoint_def.mp hdisj h_comm_elem' h_comm_elem
  have h_conj_b' : n * b' * n⁻¹ = b' := by
    have := h_one
    -- `b'⁻¹ * Y = 1` ⇒ `Y = b'`.
    have h_mul := congrArg (b' * ·) this
    simp only [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at h_mul
    exact h_mul
  -- By Frobenius condition, if `b' ≠ 1` and `n ≠ 1`, then... wait, we have `b' * n * b'⁻¹ ≠ n`.
  -- Reformulate `h_conj_b'`: `n * b' * n⁻¹ = b'` ⇔ `n * b' = b' * n` ⇔ `b' * n * b'⁻¹ = n`.
  -- So if `b' ≠ 1` and `n ≠ 1`, Frobenius gives contradiction. Hence `b' = 1` or `n = 1`.
  have h_conj_n : b' * n * b'⁻¹ = n := by
    -- `n * b' * n⁻¹ = b'` ⇒ `n * b' = b' * n`.
    have h_nb' : n * b' = b' * n := by
      have := congrArg (· * n) h_conj_b'
      simpa using this
    -- `b' * n * b'⁻¹ = (b' * n) * b'⁻¹ = (n * b') * b'⁻¹ = n`.
    rw [← h_nb', mul_inv_cancel_right]
  -- Case analysis: either `b' = 1` or `n = 1`.
  by_cases h_n_one : n = 1
  · -- `n = 1` ⇒ `g = n * a = a ∈ A`.
    rw [← hna, h_n_one, one_mul]
    exact haA
  · -- `n ≠ 1`. By Frobenius, `b' = 1`. Then `x = n * 1 * n⁻¹ = 1`, contradiction.
    by_cases h_b'_one : b' = 1
    · exfalso
      have : x = 1 := by rw [hx_eq2, h_b'_one, mul_one, mul_inv_cancel]
      exact hx_ne this
    · exfalso
      exact h.conj_frobenius b' hb'_mem h_b'_one n hnN h_n_one h_conj_n

/-- **Isaacs Thm 6.4 (2) ⇒ (3)**: Frobenius group ⇒ centralizer of any nontrivial element of `A`
is contained in `A`. -/
theorem centralizer_complement_le (h : IsFrobeniusGroup G N A) :
    ∀ a ∈ A, a ≠ 1 → Subgroup.centralizer ({a} : Set G) ≤ A := by
  intro a haA ha x hx
  -- `x * a = a * x`, so `x * a * x⁻¹ = a`, so `a = (MulAut.conj x) a⁻¹⁻¹ ∈ A.map (MulAut.conj x)`.
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  -- Want: `x ∈ A`. Assume for contradiction `x ∉ A`.
  by_contra hxA
  -- By (2), `A ⊓ A^x = ⊥`.
  have h_ti := h.trivialIntersection x hxA
  -- `a ∈ A ⊓ A^x`: indeed `a ∈ A`, and `a = (MulAut.conj x) a` (from commutativity).
  have h_a_in_conj : a ∈ Subgroup.map (MulAut.conj x).toMonoidHom A := by
    rw [Subgroup.mem_map]
    refine ⟨a, haA, ?_⟩
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    -- `x * a * x⁻¹ = a` follows from `x * a = a * x`.
    have := hx
    calc x * a * x⁻¹ = (x * a) * x⁻¹ := by rfl
      _ = (a * x) * x⁻¹ := by rw [hx]
      _ = a := by rw [mul_inv_cancel_right]
  have h_a_in : a ∈ A ⊓ Subgroup.map (MulAut.conj x).toMonoidHom A :=
    Subgroup.mem_inf.mpr ⟨haA, h_a_in_conj⟩
  rw [h_ti, Subgroup.mem_bot] at h_a_in
  exact ha h_a_in

/-- **Isaacs Corollary 6.6**: In a Frobenius group `G` with kernel `N` and complement `A`, the
kernel `N` is exactly the set of elements **not** conjugate to any nonidentity element of `A`.

Proof: For `n ∈ N`, if `IsConj a n` with `a ∈ A`, write `g * a * g⁻¹ = n`. Then `a = g⁻¹ * n * g`
lies in `N` (by normality of `N`), so `a ∈ N ⊓ A = ⊥`, i.e., `a = 1`. Hence `N ⊆ notConjugateSet A`.
Equality follows by cardinality: `|N| = A.index = |notConjugateSet A|` (Lagrange + Lem 6.5). -/
theorem kernel_eq_notConjugateSet [Finite G] (h : IsFrobeniusGroup G N A) :
    (N : Set G) = notConjugateSet A := by
  classical
  -- Step 1: N ⊆ notConjugateSet A.
  have h_subset : (N : Set G) ⊆ notConjugateSet A := by
    intro n hnN a haA ha_ne h_conj
    rw [SetLike.mem_coe] at hnN
    rw [isConj_iff] at h_conj
    obtain ⟨g, hg⟩ := h_conj
    -- hg : g * a * g⁻¹ = n. Rearrange: a = g⁻¹ * n * g.
    have hag : a = g⁻¹ * n * g := by rw [← hg]; group
    -- g⁻¹ * n * g ∈ N (normality), so a ∈ N.
    have h_gng_in_N : g⁻¹ * n * g ∈ N := by
      have := h.isNormal.conj_mem n hnN g⁻¹
      simpa using this
    have ha_in_N : a ∈ N := hag ▸ h_gng_in_N
    have hdisj : Disjoint N A := h.isComplement.disjoint
    exact ha_ne (Subgroup.disjoint_def.mp hdisj ha_in_N haA)
  -- Step 2: Equal cardinalities + subset ⇒ equal.
  have h_ncard_N : (N : Set G).ncard = A.index := h.isComplement.ncard_left
  have h_ncard_X : (notConjugateSet A).ncard = A.index :=
    card_notConjugateSet_eq_index A fun g hg => h.trivialIntersection g hg
  have h_finite : (notConjugateSet A).Finite := Set.toFinite _
  exact Set.eq_of_subset_of_ncard_le h_subset (h_ncard_X.trans h_ncard_N.symm).le h_finite

/-- **Isaacs Thm 6.4 (1) ⇒ (4)**: Frobenius group ⇒ centralizer of any nontrivial element of `N`
is contained in `N`. Together with `of_centralizer_kernel_le` this completes the four-way
equivalence of Thm 6.4.

Proof uses Cor 6.6 (`kernel_eq_notConjugateSet`): suppose `c ∈ C_G(n) \ N`. Then `c` is conjugate
to some `1 ≠ a ∈ A`, say `c = g a g⁻¹`. Set `m := g⁻¹ n g ∈ N` (by normality, `m ≠ 1`). From
`c * n * c⁻¹ = n` we get `a * m * a⁻¹ = m`, contradicting the Frobenius condition. -/
theorem centralizer_kernel_le [Finite G] (h : IsFrobeniusGroup G N A) :
    ∀ n ∈ N, n ≠ 1 → Subgroup.centralizer ({n} : Set G) ≤ N := by
  intro n hnN hn_ne c hc
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  -- hc : c * n = n * c
  by_contra hcN
  -- c ∉ N. Use Cor 6.6: N = notConjugateSet A, so c ∉ notConjugateSet A.
  have hX_eq := h.kernel_eq_notConjugateSet
  have hcX : c ∉ notConjugateSet A := by
    intro h_mem
    apply hcN
    have h_in_N_set : c ∈ (N : Set G) := hX_eq ▸ h_mem
    exact h_in_N_set
  -- ¬ (∀ a ∈ A, a ≠ 1 → ¬ IsConj a c) ⇒ ∃ a ∈ A, a ≠ 1, IsConj a c.
  simp only [notConjugateSet, Set.mem_ofPred_eq, not_forall, not_not] at hcX
  obtain ⟨a, haA, ha_ne, h_conj⟩ := hcX
  rw [isConj_iff] at h_conj
  obtain ⟨g, hgac⟩ := h_conj
  -- hgac : g * a * g⁻¹ = c
  -- Set m := g⁻¹ * n * g; by normality m ∈ N, and m ≠ 1 since n ≠ 1.
  set m := g⁻¹ * n * g with hm_def
  have hmN : m ∈ N := by
    have := h.isNormal.conj_mem n hnN g⁻¹
    simpa using this
  have hm_ne : m ≠ 1 := by
    intro hm_one
    apply hn_ne
    have h_n_eq : n = g * m * g⁻¹ := by rw [hm_def]; group
    rw [h_n_eq, hm_one, mul_one, mul_inv_cancel]
  -- From c * n = n * c and c = g a g⁻¹, conjugating both sides by g⁻¹/g gives a * m = m * a.
  have h_am : a * m * a⁻¹ = m := by
    have h_eq : a * m = m * a := by
      have h_cn : c * n = n * c := hc
      have h_cong : g⁻¹ * (c * n) * g = g⁻¹ * (n * c) * g :=
        congrArg (fun x => g⁻¹ * x * g) h_cn
      have hLHS : g⁻¹ * (c * n) * g = a * m := by
        rw [← hgac, hm_def]; group
      have hRHS : g⁻¹ * (n * c) * g = m * a := by
        rw [← hgac, hm_def]; group
      rw [hLHS, hRHS] at h_cong
      exact h_cong
    -- a * m = m * a ⇒ a * m * a⁻¹ = m.
    calc a * m * a⁻¹ = (m * a) * a⁻¹ := by rw [h_eq]
      _ = m := mul_inv_cancel_right m a
  exact h.conj_frobenius a haA ha_ne m hmN hm_ne h_am

open scoped Pointwise

/-- In a Frobenius group, the kernel has trivial intersection with every conjugate of the
complement. This is the `N ∩ A^g = 1` part used in the partition construction of §6B. -/
theorem disjoint_kernel_conjugate_complement (h : IsFrobeniusGroup G N A) (g : G) :
    Disjoint N (MulAut.conj g • A : Subgroup G) := by
  rw [Subgroup.disjoint_def]
  intro x hxN hxAconj
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxAconj
  have haN : (MulAut.conj g)⁻¹ x ∈ N := by
    have hx_conj_N := h.isNormal.conj_mem x hxN g⁻¹
    change (MulAut.conj g).symm x ∈ N
    simpa [MulAut.conj_symm_apply] using hx_conj_N
  have hdisj : Disjoint N A := h.isComplement.disjoint
  have ha_one : (MulAut.conj g)⁻¹ x = 1 :=
    Subgroup.disjoint_def.mp hdisj haN hxAconj
  have hx_one : x = 1 := by
    have hraw : g⁻¹ * x * g = 1 := by
      simpa [MulAut.conj_symm_apply] using ha_one
    calc
      x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by
        rw [hraw]
        group
  exact hx_one

end IsFrobeniusGroup

namespace SubgroupPartition

open scoped Pointwise

variable {G : Type*} [Group G]

private theorem exists_ne_one_mem_of_ne_bot {H : Subgroup G} (hH : H ≠ ⊥) :
    ∃ x : G, x ∈ H ∧ x ≠ 1 := by
  by_contra hnone
  push Not at hnone
  apply hH
  exact (Subgroup.eq_bot_iff_forall H).mpr fun x hx => hnone x hx

private noncomputable def conjugatesFinset [Finite G] (A : Subgroup G) :
    Finset (Subgroup G) := by
  classical
  exact (Set.finite_range (fun g : G => MulAut.conj g • A)).toFinset

private theorem mem_conjugatesFinset [Finite G] {A B : Subgroup G} :
    B ∈ conjugatesFinset A ↔ ∃ g : G, B = MulAut.conj g • A := by
  classical
  unfold conjugatesFinset
  rw [Set.Finite.mem_toFinset, Set.mem_range]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, rfl⟩

private theorem conjugatesFinset_card_eq_index [Finite G] {A : Subgroup G}
    (hA_ne : A ≠ ⊥)
    (hTI : ∀ g : G, g ∉ A → A ⊓ (MulAut.conj g • A) = ⊥) :
    (conjugatesFinset A).card = A.index := by
  classical
  have hcard :=
    Set.ncard_eq_toFinset_card
      (Set.range (fun g : G => MulAut.conj g • A)) (Set.finite_range _)
  rw [conjugatesFinset, ← hcard]
  exact ncard_conjugates_eq_index_of_TI hA_ne hTI

/-- Isaacs §6B partition attached to a Frobenius group: the kernel together with all conjugates
of the complement. -/
noncomputable def frobeniusGroup [Finite G] {N A : Subgroup G}
    (h : IsFrobeniusGroup G N A) :
    SubgroupPartition G where
  parts := by
    classical
    exact insert N (conjugatesFinset A)
  nontrivial := by
    classical
    intro X hX hX_bot
    rcases Finset.mem_insert.mp hX with hXN | hX
    · apply h.ne_bot_kernel
      rw [← hXN]
      exact hX_bot
    · obtain ⟨g, rfl⟩ := mem_conjugatesFinset.mp hX
      obtain ⟨a, haA, ha_ne⟩ := exists_ne_one_mem_of_ne_bot h.ne_bot_complement
      apply ha_ne
      have hmem_conj : MulAut.conj g a ∈ (MulAut.conj g • A : Subgroup G) := by
        simpa using Subgroup.smul_mem_pointwise_smul a (MulAut.conj g) A haA
      have hmem : MulAut.conj g a ∈ (⊥ : Subgroup G) := by
        simpa [hX_bot] using hmem_conj
      rw [Subgroup.mem_bot] at hmem
      have ha_one : a = 1 := by
        have hraw : g⁻¹ * (g * a * g⁻¹) * g = 1 := by
          simpa [MulAut.conj_apply, MulAut.conj_symm_apply] using
            congrArg (MulAut.conj g).symm hmem
        calc
          a = g⁻¹ * (g * a * g⁻¹) * g := by group
          _ = 1 := hraw
      exact ha_one
  proper := by
    classical
    intro X hX hX_top
    rcases Finset.mem_insert.mp hX with hXN | hX
    · apply h.ne_bot_complement
      exact (Subgroup.eq_bot_iff_forall A).mpr fun a haA => by
        have haN : a ∈ N := by
          rw [← hXN, hX_top]
          exact Subgroup.mem_top a
        exact Subgroup.disjoint_def.mp h.isComplement.disjoint haN haA
    · obtain ⟨g, rfl⟩ := mem_conjugatesFinset.mp hX
      apply h.ne_bot_kernel
      exact (Subgroup.eq_bot_iff_forall N).mpr fun n hnN => by
        have hnAconj : n ∈ (MulAut.conj g • A : Subgroup G) := by
          rw [hX_top]
          exact Subgroup.mem_top n
        exact Subgroup.disjoint_def.mp (h.disjoint_kernel_conjugate_complement g) hnN hnAconj
  cover := by
    classical
    intro x
    by_cases hxN : x ∈ N
    · exact ⟨N, Finset.mem_insert_self _ _, hxN⟩
    · have hkernel := h.kernel_eq_notConjugateSet
      have hx_not : x ∉ notConjugateSet A := by
        intro hx
        have hxN' : x ∈ (N : Set G) := by
          rw [hkernel]
          exact hx
        exact hxN hxN'
      simp only [notConjugateSet, Set.mem_ofPred_eq, not_forall, not_not] at hx_not
      obtain ⟨a, haA, ha_ne, hconj⟩ := hx_not
      rw [isConj_iff] at hconj
      obtain ⟨g, hgax⟩ := hconj
      refine ⟨MulAut.conj g • A, ?_, ?_⟩
      · exact Finset.mem_insert.mpr (Or.inr (mem_conjugatesFinset.mpr ⟨g, rfl⟩))
      · rw [← hgax]
        simpa using Subgroup.smul_mem_pointwise_smul a (MulAut.conj g) A haA
  inf_eq_bot_of_ne := by
    classical
    intro X Y hX hY hXY
    rcases Finset.mem_insert.mp hX with hXN | hX
    · rcases Finset.mem_insert.mp hY with hYN | hY
      · exact False.elim (hXY (hXN.trans hYN.symm))
      · obtain ⟨g, rfl⟩ := mem_conjugatesFinset.mp hY
        rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_inf] at hx
        have hxN : x ∈ N := by
          rw [← hXN]
          exact hx.1
        exact Subgroup.disjoint_def.mp (h.disjoint_kernel_conjugate_complement g) hxN hx.2
    · obtain ⟨g, rfl⟩ := mem_conjugatesFinset.mp hX
      rcases Finset.mem_insert.mp hY with hYN | hY
      · rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_inf] at hx
        have hxN : x ∈ N := by
          rw [← hYN]
          exact hx.2
        exact Subgroup.disjoint_def.mp (h.disjoint_kernel_conjugate_complement g) hxN hx.1
      · obtain ⟨k, rfl⟩ := mem_conjugatesFinset.mp hY
        have hTI : ∀ g : G, g ∉ A → A ⊓ (MulAut.conj g • A) = ⊥ := by
          intro g hg
          exact h.trivialIntersection g hg
        exact TI_conjugate hTI g k hXY

/-- The Frobenius-group partition has cardinality `1 + |N|`, where `N` is the kernel. -/
theorem frobeniusGroup_parts_card [Finite G] {N A : Subgroup G}
    (h : IsFrobeniusGroup G N A) :
    (frobeniusGroup h).parts.card = Nat.card N + 1 := by
  classical
  have hTI : ∀ g : G, g ∉ A → A ⊓ (MulAut.conj g • A) = ⊥ := by
    intro g hg
    exact h.trivialIntersection g hg
  have hN_not_mem : N ∉ conjugatesFinset A := by
    intro hNmem
    obtain ⟨g, hNg⟩ := mem_conjugatesFinset.mp hNmem
    apply h.ne_bot_kernel
    exact (Subgroup.eq_bot_iff_forall N).mpr fun n hnN => by
      have hnAconj : n ∈ (MulAut.conj g • A : Subgroup G) := by
        rw [← hNg]
        exact hnN
      exact Subgroup.disjoint_def.mp (h.disjoint_kernel_conjugate_complement g) hnN hnAconj
  have hindex : A.index = Nat.card N := by
    have hn : Nat.card N = (N : Set G).ncard := by
      simpa using (Nat.card_coe_set_eq (N : Set G))
    rw [hn, h.isComplement.ncard_left]
  rw [frobeniusGroup, Finset.card_insert_of_notMem hN_not_mem,
    conjugatesFinset_card_eq_index h.ne_bot_complement hTI, hindex]

/-- Membership in the Frobenius partition: the parts are the kernel `N` and the conjugates of
the complement `A`. -/
theorem mem_frobeniusGroup_parts [Finite G] {N A : Subgroup G}
    (h : IsFrobeniusGroup G N A) {C : Subgroup G} :
    C ∈ (frobeniusGroup h).parts ↔ C = N ∨ ∃ g : G, C = MulAut.conj g • A := by
  classical
  rw [frobeniusGroup, Finset.mem_insert, mem_conjugatesFinset]

end SubgroupPartition

/-- **Isaacs Thm 6.9** reduction step: if a solvable subgroup `B` of the actor acts
Frobeniusly on a finite nontrivial target, then the target contains a nontrivial abelian
`B`-invariant subgroup.  This is the reusable form of the textbook move in L3495: choose an
invariant Sylow subgroup `R` by Isaacs Thm 3.23, then pass to `Z(R)`. -/
theorem exists_actorSubgroup_invariant_nontrivial_abelian_subgroup_of_isSolvable
    {A U : Type*} [Group A] [Group U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U] (hFrob : IsFrobeniusAction A U)
    (B : Subgroup A) [Finite B] [Group.IsSolvable B] :
    ∃ M : Subgroup U, Nontrivial M ∧ IsMulCommutative M ∧
      ∀ b : B, ∀ m ∈ M, (b : A) • m ∈ M := by
  classical
  let φ : B →* MulAut U := MulDistribMulAction.toMulAut B U
  have hFrobB : IsFrobeniusAction B U := IsFrobeniusAction.actorSubgroup hFrob B
  have hCop : Nat.Coprime (Nat.card B) (Nat.card U) := by
    have : Fintype B := Fintype.ofFinite B
    have : Fintype U := Fintype.ofFinite U
    simpa only [Nat.card_eq_fintype_card] using
      (IsFrobeniusAction.coprime_card (A := B) (N := U) hFrobB).symm
  have hU_gt_one : 1 < Nat.card U :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd hU_gt_one.ne'
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, hR_inv⟩ :=
    OddOrder.Isaacs.Ch04.exists_aInvariant_sylow (G := U) (A := B) (φ := φ)
      hCop (Or.inl (inferInstance : Group.IsSolvable B)) p
  let M : Subgroup U := (Subgroup.center R).map (R : Subgroup U).subtype
  have hM_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ M := by
    simpa [M] using
      (OddOrder.Isaacs.Ch03.IsAInvariant.map_subtype_of_characteristic
        (φ := φ) hR_inv (K := Subgroup.center R))
  have hR_ne_bot : (R : Subgroup U) ≠ ⊥ := R.ne_bot_of_dvd_card hp_dvd
  have hR_nontrivial : Nontrivial R :=
    (Subgroup.nontrivial_iff_ne_bot (R : Subgroup U)).mpr hR_ne_bot
  have hCenter_nontrivial : Nontrivial (Subgroup.center R) :=
    R.isPGroup'.center_nontrivial
  have hM_ne_bot : M ≠ ⊥ := by
    dsimp [M]
    rw [Subgroup.map_eq_bot_iff_of_injective
      (H := Subgroup.center R) (R : Subgroup U).subtype_injective]
    exact (Subgroup.nontrivial_iff_ne_bot (Subgroup.center R)).mp hCenter_nontrivial
  refine ⟨M, (Subgroup.nontrivial_iff_ne_bot M).mpr hM_ne_bot, ?_, ?_⟩
  · dsimp [M]
    infer_instance
  · intro b m hm
    simpa [φ, Subgroup.smul_def] using hM_inv.smul_mem b hm

/-- **Isaacs Thm 6.9** reduction hook for the elementary-abelian branch: if a subgroup `B` of
the Frobenius actor is elementary abelian of order `p^2` and the target contains a nontrivial
`B`-invariant abelian subgroup, then the action is impossible. -/
theorem false_of_invariant_abelian_target_actorSubgroup_isElementaryAbelian_card_prime_sq
    {A U : Type*} [Group A] [Group U] [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (B : Subgroup A) [Finite B]
    {p : ℕ} (hp : p.Prime)
    (hElem : OddOrder.GroupTheory.IsElementaryAbelian p B) (hCard : Nat.card B = p ^ 2)
    (M : Subgroup U) [Finite M] [Nontrivial M] [IsMulCommutative M]
    (hM : ∀ b : B, ∀ m ∈ M, (b : A) • m ∈ M) :
    False := by
  let : CommGroup M := inferInstance
  let : MulDistribMulAction B M := by
    letI : SMul B M := ⟨fun b m => ⟨(b : A) • (m : U), hM b m m.2⟩⟩
    exact Subtype.coe_injective.mulDistribMulAction M.subtype (fun _ _ => rfl)
  have hFrobM : IsFrobeniusAction B M := by
    intro b hb m hm hfix
    have hbA : (b : A) ≠ 1 := fun hbA => hb (Subtype.ext hbA)
    have hmU : (m : U) ≠ 1 := fun hmU => hm (Subtype.ext hmU)
    exact hFrob (b : A) hbA (m : U) hmU (Subtype.ext_iff.mp hfix)
  exact false_of_frobeniusAction_isElementaryAbelian_card_prime_sq hFrobM hp hElem hCard

/-- **Isaacs Thm 6.9** (elementary-abelian branch, finite target): a Frobenius actor cannot
contain an elementary abelian subgroup of order `p^2`.  The abelian-target partition argument is
applied after the invariant-Sylow-center reduction. -/
theorem false_of_frobeniusAction_actorSubgroup_isElementaryAbelian_card_prime_sq_of_finite_target
    {A U : Type*} [Group A] [Group U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (B : Subgroup A) [Finite B]
    {p : ℕ} (hp : p.Prime)
    (hElem : OddOrder.GroupTheory.IsElementaryAbelian p B) (hCard : Nat.card B = p ^ 2) :
    False := by
  have : IsMulCommutative B := ⟨⟨fun x y => hElem.comm x y⟩⟩
  let : CommGroup B := inferInstance
  have : Group.IsSolvable B := inferInstance
  obtain ⟨M, hM_nontrivial, hM_comm, hM_inv⟩ :=
    exists_actorSubgroup_invariant_nontrivial_abelian_subgroup_of_isSolvable hFrob B
  have : Nontrivial M := hM_nontrivial
  have : IsMulCommutative M := hM_comm
  exact
    false_of_invariant_abelian_target_actorSubgroup_isElementaryAbelian_card_prime_sq
      hFrob B hp hElem hCard M hM_inv

/-- **Isaacs Cor 6.10**: if `P` is a Sylow `p`-subgroup of a finite Frobenius
complement, then `P` contains at most one subgroup of order `p`. -/
theorem subgroups_card_prime_unique_of_frobeniusAction_sylow
    {A U : Type*} [Group A] [Finite A] [Group U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) {p : ℕ} [hp : Fact p.Prime] (P : Sylow p A) :
    ∀ K L : Subgroup P, Nat.card K = p → Nat.card L = p → K = L := by
  intro K L hK_card hL_card
  by_contra hKL_ne
  obtain ⟨E, hE_elem, hE_card⟩ :=
    P.isPGroup'.exists_isElementaryAbelian_card_prime_sq_of_subgroups_card_prime_ne
      hK_card hL_card hKL_ne
  exact
    false_of_frobeniusAction_actorSubgroup_isElementaryAbelian_card_prime_sq_of_finite_target
      (A := P) (U := U) (IsFrobeniusAction.actorSubgroup hFrob (P : Subgroup A))
      E hp.out hE_elem hE_card

/-- **Isaacs Thm 6.11 (abelian branch, in Frobenius-complement form)**: a commutative
Sylow `p`-subgroup of a finite Frobenius complement is cyclic.  Corollary 6.10 supplies the
unique order-`p` subgroup hypothesis, and the finite abelian p-group structure theorem turns it
into cyclicity. -/
theorem sylow_isCyclic_of_frobeniusAction_of_isMulCommutative
    {A U : Type*} [Group A] [Finite A] [Group U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) {p : ℕ} [Fact p.Prime]
    (P : Sylow p A) [IsMulCommutative P] :
    IsCyclic P :=
  P.isPGroup'.isCyclic_of_subgroups_card_prime_unique
    (subgroups_card_prime_unique_of_frobeniusAction_sylow hFrob P)

/-- **Isaacs Cor 6.17 observation (abelian complement branch)**: a finite abelian Frobenius
complement is cyclic.  This is the part needed later in Theorem 6.21 to rule out a noncyclic
abelian group acting Frobeniusly. -/
theorem isCyclic_of_frobeniusAction_of_isMulCommutative
    {A U : Type*} [Group A] [Finite A] [IsMulCommutative A]
    [Group U] [Finite U] [Nontrivial U] [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) :
    IsCyclic A := by
  exact isCyclic_of_sylow_isCyclic (A := A) fun p hp P => by
    have : Fact p.Prime := ⟨hp⟩
    have : IsMulCommutative P := ⟨⟨fun x y => by
      ext
      exact mul_comm (x : A) (y : A)⟩⟩
    exact sylow_isCyclic_of_frobeniusAction_of_isMulCommutative hFrob P

/-- The contradiction step in Isaacs Thm 6.21 after the induction hypothesis has shown that
every proper `A`-invariant subgroup of `N` lies in `K = ⟨C_N(a) | a ≠ 1⟩`. -/
theorem nontrivialActionFixedByClosure_eq_top_of_proper_invariant_le
    {A N : Type*} [Group A] [Finite A] [IsMulCommutative A]
    [Group N] [Finite N] [Nontrivial N] [MulDistribMulAction A N]
    (hCop : Nat.Coprime (Nat.card A) (Nat.card N)) (hNotCyclic : ¬ IsCyclic A)
    (hproper : ∀ P : Subgroup N,
      (∀ a : A, ∀ n ∈ P, a • n ∈ P) → P ≠ ⊤ →
        P ≤ nontrivialActionFixedByClosure (MulDistribMulAction.toMulAut A N)) :
    nontrivialActionFixedByClosure (MulDistribMulAction.toMulAut A N) = ⊤ := by
  classical
  let φ : A →* MulAut N := MulDistribMulAction.toMulAut A N
  let K : Subgroup N := nontrivialActionFixedByClosure φ
  change K = ⊤
  by_contra hK_ne_top
  have hidx_gt : 1 < K.index := Subgroup.one_lt_index_of_ne_top hK_ne_top
  obtain ⟨p, hp_prime, hp_dvd⟩ :=
    Nat.exists_prime_and_dvd (Nat.ne_of_gt hidx_gt)
  have : Fact p.Prime := ⟨hp_prime⟩
  have hSolvA : Group.IsSolvable A := Group.isSolvable_of_comm fun a b : A => mul_comm a b
  obtain ⟨P, _hP_inv, hP_top⟩ :=
    exists_aInvariant_sylow_eq_top_of_prime_dvd_index_of_proper_invariant_le
      (A := A) (N := N) (K := K) (p := p) hCop (Or.inl hSolvA) hp_dvd
      (by simpa [K, φ] using hproper)
  have hN_pgroup : IsPGroup p N := by
    have hP_pgroup : IsPGroup p (P : Subgroup N) := P.isPGroup'
    rw [hP_top] at hP_pgroup
    exact hP_pgroup.of_equiv Subgroup.topEquiv
  have hN_solv : Group.IsSolvable N := by
    have : Group.IsNilpotent N := hN_pgroup.isNilpotent
    exact IsNilpotent.to_isSolvable
  let : Group.IsSolvable N := hN_solv
  have hcomm : _root_.commutator N ≤ K :=
    commutator_le_of_proper_invariant_le_of_isSolvable (A := A) (N := N) (K := K)
      (by simpa [K, φ] using hproper)
  let : K.Normal := normal_of_commutator_le hcomm
  have hK_inv : ∀ a : A, ∀ n ∈ K, a • n ∈ K := by
    simpa [K, φ] using nontrivialActionFixedByClosure_invariant_of_commutative φ
  have hCopAK : Nat.Coprime (Nat.card A) (Nat.card K) :=
    hCop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card K)
  have hfixed : ∀ a : A, a ≠ 1 → actionFixedBy φ a ≤ K := by
    intro a ha
    exact actionFixedBy_le_nontrivialActionFixedByClosure (φ := φ) ha
  let : MulDistribMulAction A (N ⧸ K) :=
    IsFrobeniusAction.invariantQuotientMulDistribMulAction K hK_inv
  have : Nontrivial (N ⧸ K) := Subgroup.nontrivial_quotient_of_ne_top hK_ne_top
  have hFrobQuot : IsFrobeniusAction A (N ⧸ K) :=
    quotient_isFrobeniusAction_of_fixedBy_le (A := A) (N := N) (M := K)
      hK_inv hCopAK hfixed
  exact hNotCyclic (isCyclic_of_frobeniusAction_of_isMulCommutative hFrobQuot)

universe uA uN

/-- **Isaacs Thm 6.21** (nontrivial case): if a finite abelian noncyclic group `A` acts
coprimely on a finite nontrivial group `N`, then the subgroups `C_N(a)` for `a ≠ 1`
generate `N`. -/
theorem nontrivialActionFixedByClosure_eq_top_of_not_isCyclic_of_nontrivial
    {A : Type uA} {N : Type uN} [Group A] [Finite A] [IsMulCommutative A]
    [Group N] [Finite N] [Nontrivial N] [MulDistribMulAction A N]
    (hCop : Nat.Coprime (Nat.card A) (Nat.card N)) (hNotCyclic : ¬ IsCyclic A) :
    nontrivialActionFixedByClosure (MulDistribMulAction.toMulAut A N) = ⊤ := by
  classical
  let motive : ℕ → Prop := fun n =>
    ∀ (N : Type uN) [Group N] [Finite N] [Nontrivial N] [MulDistribMulAction A N],
      Nat.card N = n →
      Nat.Coprime (Nat.card A) (Nat.card N) →
      nontrivialActionFixedByClosure (MulDistribMulAction.toMulAut A N) = ⊤
  have hmain : motive (Nat.card N) := by
    refine Nat.strong_induction_on (Nat.card N) ?_
    intro n ih N _ _ _ _ hcard hCopN
    refine nontrivialActionFixedByClosure_eq_top_of_proper_invariant_le
      (A := A) (N := N) hCopN hNotCyclic ?_
    intro M hM hM_ne_top
    by_cases hM_nontriv : Nontrivial M
    · let : Nontrivial M := hM_nontriv
      let : MulDistribMulAction A M :=
        IsFrobeniusAction.invariantSubgroupMulDistribMulAction M hM
      have hM_card_lt_N : Nat.card M < Nat.card N := by
        have h_dvd : Nat.card M ∣ Nat.card N := Subgroup.card_subgroup_dvd_card M
        have h_le : Nat.card M ≤ Nat.card N := Nat.le_of_dvd Nat.card_pos h_dvd
        have h_ne : Nat.card M ≠ Nat.card N := fun heq =>
          hM_ne_top (Subgroup.eq_top_of_card_eq M heq)
        exact Nat.lt_of_le_of_ne h_le h_ne
      have hM_card_lt : Nat.card M < n := by
        simpa [hcard] using hM_card_lt_N
      have hCopM : Nat.Coprime (Nat.card A) (Nat.card M) :=
        hCopN.coprime_dvd_right (Subgroup.card_subgroup_dvd_card M)
      have hMtop :
          nontrivialActionFixedByClosure (MulDistribMulAction.toMulAut A M) = ⊤ :=
        (ih (Nat.card M) hM_card_lt) M rfl hCopM
      exact
        subgroup_le_nontrivialActionFixedByClosure_of_closure_eq_top
          (M := M) (by intro a m; rfl) hMtop
    · have : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM_nontriv
      intro n hn
      have hn_one : n = 1 := by
        have hsub : (⟨n, hn⟩ : M) = 1 := Subsingleton.elim _ _
        exact congrArg Subtype.val hsub
      rw [hn_one]
      exact Subgroup.one_mem _
  exact hmain N rfl hCop

/-- **Isaacs Thm 6.21**: if a finite abelian noncyclic group `A` acts coprimely on a finite
group `N`, then the subgroups `C_N(a)` for `a ≠ 1` generate `N`. -/
theorem nontrivialActionFixedByClosure_eq_top_of_not_isCyclic
    {A : Type uA} {N : Type uN} [Group A] [Finite A] [IsMulCommutative A]
    [Group N] [Finite N] [MulDistribMulAction A N]
    (hCop : Nat.Coprime (Nat.card A) (Nat.card N)) (hNotCyclic : ¬ IsCyclic A) :
    nontrivialActionFixedByClosure (MulDistribMulAction.toMulAut A N) = ⊤ := by
  by_cases hN_nontriv : Nontrivial N
  · let : Nontrivial N := hN_nontriv
    exact nontrivialActionFixedByClosure_eq_top_of_not_isCyclic_of_nontrivial
      hCop hNotCyclic
  · have : Subsingleton N := not_nontrivial_iff_subsingleton.mp hN_nontriv
    rw [eq_top_iff]
    intro n _hn
    have hn_one : n = 1 := Subsingleton.elim n 1
    rw [hn_one]
    exact Subgroup.one_mem _

end

end OddOrder.Isaacs.Ch06


