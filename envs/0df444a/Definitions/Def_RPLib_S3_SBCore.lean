-- Prove2me | Definitions.Def_RPLib_S3_SBCore
-- name    : RPLib_S3_SBCore
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:23:34.891282+00:00
-- url     : https://prove2.me/theorems/1c3d239f-c1b1-419b-99d6-3ef6ebab0f8e
-- title:
--   Weight-two Ramanujan-Petersson library: Stepanov-Bombieri, abstract core (twisted form)
-- statement:
--   Stepanov-Bombieri, abstract core (twisted form).
--
--   For abstract Riemann-Roch data `d : Data Fq F ι` (RR_A/RR_B), a ring endomorphism `τ` of `F`
--   moving the valuations along a permutation `π` of the places, a place `P0` with `deg P0 = ℓ(0)`
--   (rational over the constant field) and `Q0 = p ^ k` (`p` the characteristic of `F`): every
--   finite set `T` of places such that `τ f ≡ f ^ (Q0 ^ 2)` at `P` for every `P`-integral `f` satisfies
--   `Q0 * Σ_{P ∈ T, P ≠ P0} deg P ≤ ℓ(0) * (Q0 (Q0 - 1) + Q0 ^ 2 B)`
--   as soon as `ℓ(0) B ≥ ℓ(0) Q0 + 2g` and `(g + ℓ(0)) ^ 2 < ℓ(0) ^ 2 Q0`.
--
--   Proof (Bombieri): `f_a` (`a ∈ S`) elements of `L((Q0-1) P0)` with pairwise distinct pole orders
--   `a < Q0` at `P0`; the additive map `g ↦ Σ f_a ^ Q0 τ(g_a)` from `L(B P0) ^ S` to
--   `L(Q0 (Q0-1) P0 + B π(P0))` has a nonzero kernel element (counting); then
--   `H = Σ f_a ^ Q0 g_a ^ (Q0 ^ 2) = (Σ f_a g_a ^ Q0) ^ Q0` is nonzero (distinct valuations at `P0`),
--   has its poles at `P0` only and vanishes to order `≥ Q0` on `T`; `deg div H = 0` gives the bound.
--   No linearity of `τ` over `Fq` is used.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_RRB

/-!
# Stepanov-Bombieri, abstract core (twisted form)

For abstract Riemann-Roch data `d : Data Fq F ι` (RR_A/RR_B), a ring endomorphism `τ` of `F`
moving the valuations along a permutation `π` of the places, a place `P0` with `deg P0 = ℓ(0)`
(rational over the constant field) and `Q0 = p ^ k` (`p` the characteristic of `F`): every
finite set `T` of places such that `τ f ≡ f ^ (Q0 ^ 2)` at `P` for every `P`-integral `f` satisfies
`Q0 * Σ_{P ∈ T, P ≠ P0} deg P ≤ ℓ(0) * (Q0 (Q0 - 1) + Q0 ^ 2 B)`
as soon as `ℓ(0) B ≥ ℓ(0) Q0 + 2g` and `(g + ℓ(0)) ^ 2 < ℓ(0) ^ 2 Q0`.

Proof (Bombieri): `f_a` (`a ∈ S`) elements of `L((Q0-1) P0)` with pairwise distinct pole orders
`a < Q0` at `P0`; the additive map `g ↦ Σ f_a ^ Q0 τ(g_a)` from `L(B P0) ^ S` to
`L(Q0 (Q0-1) P0 + B π(P0))` has a nonzero kernel element (counting); then
`H = Σ f_a ^ Q0 g_a ^ (Q0 ^ 2) = (Σ f_a g_a ^ Q0) ^ Q0` is nonzero (distinct valuations at `P0`),
has its poles at `P0` only and vanishes to order `≥ Q0` on `T`; `deg div H = 0` gives the bound.
No linearity of `τ` over `Fq` is used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero

namespace RamanujanPetersson.ZetaSB

open RR

/-! ### Arithmetic in `ℤᵐ⁰` and `ℤ` -/

theorem lt_exp_iff_le_exp_sub_one {x : ℤᵐ⁰} {n : ℤ} : x < exp n ↔ x ≤ exp (n - 1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · obtain ⟨k, rfl⟩ : ∃ k : ℤ, x = exp k := ⟨log x, (exp_log hx).symm⟩
    rw [exp_lt_exp, exp_le_exp]; omega

theorem pow_le_exp_mul {x : ℤᵐ⁰} {n : ℤ} (h : x ≤ exp n) (k : ℕ) :
    x ^ k ≤ exp ((k : ℤ) * n) := by
  calc x ^ k ≤ (exp n) ^ k := pow_le_pow_left' h k
    _ = exp ((k : ℤ) * n) := by rw [← exp_nsmul, nsmul_eq_mul]

theorem lt_one_of_pow_lt_one {x : ℤᵐ⁰} {k : ℕ} (h : x ^ k < 1) : x < 1 := by
  by_contra hx
  push Not at hx
  exact absurd h (not_lt.2 (one_le_pow_of_one_le' hx k))

/-- `Q0 a + Q0 ^ 2 s = Q0 b + Q0 ^ 2 t` with `a, b < Q0` forces `a = b`. -/
theorem eq_of_mul_add_sq_eq {Q0 a b : ℕ} (hQ : 0 < Q0) (ha : a < Q0) (hb : b < Q0) {s t : ℤ}
    (h : (Q0 : ℤ) * a + (Q0 : ℤ) ^ 2 * s = (Q0 : ℤ) * b + (Q0 : ℤ) ^ 2 * t) : a = b := by
  have hQ' : (0 : ℤ) < Q0 := by exact_mod_cast hQ
  have h1 : (a : ℤ) - b = Q0 * (t - s) := by
    have : (Q0 : ℤ) * ((a : ℤ) - b) = Q0 * (Q0 * (t - s)) := by linear_combination h
    exact mul_left_cancel₀ hQ'.ne' this
  have h2 : (a : ℤ) - b = 0 :=
    Int.eq_zero_of_abs_lt_dvd ⟨t - s, h1⟩ (by rw [abs_lt]; constructor <;> omega)
  omega

/-! ### Divisor helpers -/

section Core

variable {Fq F ι : Type*} [Field Fq] [Fintype Fq] [Field F] [Algebra Fq F]

theorem degD_sum_single (d : Data Fq F ι) (s : Finset ι) (c : ℤ) :
    d.degD (∑ P ∈ s, Finsupp.single P c) = c * ∑ P ∈ s, (d.deg P : ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Data.degD]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, d.degD_add, ih, d.degD_single]; ring

theorem sum_single_apply [DecidableEq ι] (s : Finset ι) (c : ℤ) (i : ι) :
    (∑ P ∈ s, Finsupp.single P c) i = if i ∈ s then c else 0 := by
  rw [Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

theorem single_sub_one_le (P : ι) (n : ℤ) : Finsupp.single P (n - 1) ≤ Finsupp.single P n := by
  classical
  rw [Finsupp.le_def]
  intro i
  simp only [Finsupp.single_apply]
  split_ifs <;> omega

theorem v_le_one_of_mem_single {d : Data Fq F ι} {P0 P : ι} (hP : P ≠ P0) {c : ℤ} {f : F}
    (hf : f ∈ d.LD (Finsupp.single P0 c)) : d.v P f ≤ 1 := by
  classical
  have := (d.mem_LD.1 hf) P
  rwa [Finsupp.single_apply, if_neg (Ne.symm hP), exp_zero] at this

theorem v_le_exp_of_mem_single {d : Data Fq F ι} {P0 : ι} {c : ℤ} {f : F}
    (hf : f ∈ d.LD (Finsupp.single P0 c)) : d.v P0 f ≤ exp c := by
  have := (d.mem_LD.1 hf) P0
  rwa [Finsupp.single_eq_same] at this

/-! ### Elements with distinct pole orders at `P0` -/

open Classical in
/-- The pole orders `a < n` attained at `P0` by elements of `L(a P0)`. -/
noncomputable def ordSet (d : Data Fq F ι) (P0 : ι) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun a => ∃ f ∈ d.LD (Finsupp.single P0 (a : ℤ)), d.v P0 f = exp (a : ℤ)

open Classical in
/-- A chosen element of `L(a P0)` with pole order exactly `a` at `P0` (`0` if there is none). -/
noncomputable def ordFun (d : Data Fq F ι) (P0 : ι) (a : ℕ) : F :=
  if h : ∃ f ∈ d.LD (Finsupp.single P0 (a : ℤ)), d.v P0 f = exp (a : ℤ) then h.choose else 0

theorem mem_ordSet {d : Data Fq F ι} {P0 : ι} {n a : ℕ} :
    a ∈ ordSet d P0 n ↔ a < n ∧ ∃ f ∈ d.LD (Finsupp.single P0 (a : ℤ)), d.v P0 f = exp (a : ℤ) := by
  classical
  simp [ordSet]

theorem ordFun_spec {d : Data Fq F ι} {P0 : ι} {a : ℕ}
    (h : ∃ f ∈ d.LD (Finsupp.single P0 (a : ℤ)), d.v P0 f = exp (a : ℤ)) :
    ordFun d P0 a ∈ d.LD (Finsupp.single P0 (a : ℤ)) ∧ d.v P0 (ordFun d P0 a) = exp (a : ℤ) := by
  rw [ordFun, dif_pos h]
  exact h.choose_spec

/-- `ℓ((n-1) P0) ≤ deg P0 · #{pole orders a < n attained at P0}`. -/
theorem ell_single_le {d : Data Fq F ι} (hd : d.Axioms) (P0 : ι) (n : ℕ) :
    d.ell (Finsupp.single P0 ((n : ℤ) - 1)) ≤ d.deg P0 * (ordSet d P0 n).card := by
  classical
  induction n with
  | zero =>
    have h : d.degD (Finsupp.single P0 (((0 : ℕ) : ℤ) - 1)) < 0 := by
      rw [d.degD_single]
      have := hd.deg_pos P0
      push_cast
      have : (0 : ℤ) < d.deg P0 := by exact_mod_cast this
      linarith
    rw [Data.ell_eq_zero_of_degD_neg hd h]
    exact Nat.zero_le _
  | succ n ih =>
    have h2 : ((n + 1 : ℕ) : ℤ) - 1 = n := by push_cast; ring
    rw [h2]
    by_cases hn : ∃ f ∈ d.LD (Finsupp.single P0 (n : ℤ)), d.v P0 f = exp (n : ℤ)
    · have hS : ordSet d P0 (n + 1) = insert n (ordSet d P0 n) := by
        ext a
        simp only [mem_ordSet, Finset.mem_insert]
        constructor
        · rintro ⟨ha, hf⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
          · exact Or.inr ⟨ha, hf⟩
          · exact Or.inl rfl
        · rintro (rfl | ⟨ha, hf⟩)
          · exact ⟨Nat.lt_succ_self _, hn⟩
          · exact ⟨Nat.lt_succ_of_lt ha, hf⟩
      have hnot : n ∉ ordSet d P0 n := fun h => (lt_irrefl n) (mem_ordSet.1 h).1
      rw [hS, Finset.card_insert_of_notMem hnot]
      have h1 := (Data.ell_sub_le hd.toAxioms0 (single_sub_one_le P0 (n : ℤ))).1
      rw [d.degD_single, d.degD_single] at h1
      have ih' : (d.ell (Finsupp.single P0 ((n : ℤ) - 1)) : ℤ) ≤ d.deg P0 * (ordSet d P0 n).card := by
        exact_mod_cast ih
      have : (d.ell (Finsupp.single P0 (n : ℤ)) : ℤ) ≤ d.deg P0 * ((ordSet d P0 n).card + 1) := by
        linarith
      exact_mod_cast this
    · have hS : ordSet d P0 (n + 1) = ordSet d P0 n := by
        ext a
        simp only [mem_ordSet]
        constructor
        · rintro ⟨ha, hf⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
          · exact ⟨ha, hf⟩
          · exact absurd hf hn
        · rintro ⟨ha, hf⟩
          exact ⟨Nat.lt_succ_of_lt ha, hf⟩
      have hL : d.LD (Finsupp.single P0 (n : ℤ)) = d.LD (Finsupp.single P0 ((n : ℤ) - 1)) := by
        refine le_antisymm (fun f hf => ?_) (d.LD_mono (single_sub_one_le P0 n))
        rw [Data.mem_LD] at hf ⊢
        intro i
        by_cases hi : i = P0
        · rw [hi]
          have h1 := hf P0
          rw [Finsupp.single_eq_same] at h1 ⊢
          have h3 : d.v P0 f ≠ exp (n : ℤ) := fun h => hn ⟨f, d.mem_LD.2 hf, h⟩
          exact lt_exp_iff_le_exp_sub_one.1 (lt_of_le_of_ne h1 h3)
        · have h1 := hf i
          have hi' : P0 ≠ i := Ne.symm hi
          simp only [Finsupp.single_apply, hi', if_false] at h1 ⊢
          exact h1
      rw [hS]
      have : d.ell (Finsupp.single P0 (n : ℤ)) = d.ell (Finsupp.single P0 ((n : ℤ) - 1)) := by
        unfold Data.ell; rw [hL]
      rw [this]
      exact ih

/-! ### The twisted Stepanov-Bombieri bound -/

/-- **Twisted Stepanov-Bombieri bound (abstract).** -/
theorem twisted_stepanov [DecidableEq ι] {d : Data Fq F ι} (hd : d.Axioms) (p : ℕ) [Fact p.Prime] [CharP F p]
    (k Q0 : ℕ) (hQ0def : Q0 = p ^ k)
    (τ : F →+* F) (π : ι ≃ ι) (hτ : ∀ i f, d.v (π i) (τ f) = d.v i f)
    (hπ : ∀ i, d.deg (π i) = d.deg i)
    (P0 : ι) (hP0 : d.deg P0 = d.ell 0) (B : ℕ)
    (hB : d.ell 0 * Q0 + 2 * d.genus ≤ d.ell 0 * B)
    (hQ0 : (d.genus + d.ell 0) ^ 2 < d.ell 0 ^ 2 * Q0)
    (T : Finset ι)
    (hT : ∀ P ∈ T, P ≠ P0 → ∀ f : F, d.v P f ≤ 1 → d.v P (τ f - f ^ (Q0 ^ 2)) < 1) :
    Q0 * ∑ P ∈ T.erase P0, d.deg P ≤ d.ell 0 * (Q0 * (Q0 - 1) + Q0 ^ 2 * B) := by
  classical
  have hQ0pos : 0 < Q0 := hQ0def ▸ pow_pos (Fact.out : p.Prime).pos k
  have hQ1 : (1 : ℤ) ≤ Q0 := by exact_mod_cast hQ0pos
  have hrpos : 0 < d.ell 0 := hP0 ▸ hd.deg_pos P0
  -- elements with distinct pole orders
  obtain ⟨S, f, hSA, hfS, hSell⟩ : ∃ (S : Finset ℕ) (f : ℕ → F), (∀ a ∈ S, a < Q0) ∧
      (∀ a ∈ S, f a ∈ d.LD (Finsupp.single P0 (a : ℤ)) ∧ d.v P0 (f a) = exp (a : ℤ)) ∧
      d.ell (Finsupp.single P0 ((Q0 : ℤ) - 1)) ≤ d.deg P0 * S.card :=
    ⟨ordSet d P0 Q0, ordFun d P0, fun a ha => (mem_ordSet.1 ha).1,
      fun a ha => ordFun_spec (mem_ordSet.1 ha).2, ell_single_le hd P0 Q0⟩
  have hf0 : ∀ a ∈ S, f a ≠ 0 := fun a ha h => by
    have := (hfS a ha).2
    rw [h, map_zero] at this
    exact exp_ne_zero this.symm
  -- the target divisor of the twisted map
  obtain ⟨C, hC⟩ : ∃ C : ι →₀ ℤ, C = Finsupp.single P0 ((Q0 : ℤ) * ((Q0 : ℤ) - 1)) +
      Finsupp.single (π P0) (B : ℤ) := ⟨_, rfl⟩
  have hmem : ∀ g : S → d.LD (Finsupp.single P0 (B : ℤ)),
      ∑ a : S, f a ^ Q0 * τ (g a) ∈ d.LD C := by
    intro g
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [Data.mem_LD]
    intro i
    rw [map_mul, map_pow]
    have h1 : d.v i (f a) ^ Q0 ≤ exp (Finsupp.single P0 ((Q0 : ℤ) * ((Q0 : ℤ) - 1)) i) := by
      have h0 := (d.mem_LD.1 (hfS a a.2).1) i
      refine (pow_le_exp_mul h0 Q0).trans (exp_le_exp.2 ?_)
      simp only [Finsupp.single_apply]
      split_ifs
      · have := hSA a a.2
        have h5 : ((a : ℕ) : ℤ) ≤ (Q0 : ℤ) - 1 := by omega
        exact mul_le_mul_of_nonneg_left h5 (by positivity)
      · simp
    have h2 : d.v i (τ (g a)) ≤ exp (Finsupp.single (π P0) (B : ℤ) i) := by
      obtain ⟨j, rfl⟩ := π.surjective i
      rw [hτ, Finsupp.single_apply_left π.injective]
      exact (d.mem_LD.1 (g a).2) j
    calc d.v i (f a) ^ Q0 * d.v i (τ (g a))
        ≤ exp (Finsupp.single P0 ((Q0 : ℤ) * ((Q0 : ℤ) - 1)) i) *
          exp (Finsupp.single (π P0) (B : ℤ) i) := mul_le_mul' h1 h2
      _ = exp (C i) := by rw [← exp_add, hC, Finsupp.add_apply]
  -- the dimension count
  have hcount : d.ell C < S.card * d.ell (Finsupp.single P0 (B : ℤ)) := by
    have hr0 : (0 : ℤ) < d.ell 0 := by exact_mod_cast hrpos
    have hRA := Data.riemann_inequality hd (Finsupp.single P0 ((Q0 : ℤ) - 1))
    have hRB := Data.riemann_inequality hd (Finsupp.single P0 (B : ℤ))
    rw [d.degD_single, hP0] at hRA hRB
    have hdegC : d.degD C = (Q0 : ℤ) * ((Q0 : ℤ) - 1) * d.ell 0 + B * d.ell 0 := by
      rw [hC, d.degD_add, d.degD_single, d.degD_single, hπ, hP0]
    have hB' : (d.ell 0 : ℤ) * Q0 + 2 * d.genus ≤ d.ell 0 * B := by exact_mod_cast hB
    have hQ0' : ((d.genus : ℤ) + d.ell 0) ^ 2 < (d.ell 0 : ℤ) ^ 2 * Q0 := by exact_mod_cast hQ0
    have hG0 : (0 : ℤ) ≤ d.genus := by positivity
    have hlarge : 2 * (d.genus : ℤ) - 2 * d.ell 0 < d.degD C := by
      rw [hdegC]
      have : (0 : ℤ) ≤ (Q0 : ℤ) * ((Q0 : ℤ) - 1) * d.ell 0 :=
        mul_nonneg (mul_nonneg (by positivity) (by linarith)) hr0.le
      nlinarith
    have hEC := Data.ell_eq_of_large_degD hd hlarge
    rw [hdegC] at hEC
    have hSell' : (d.ell (Finsupp.single P0 ((Q0 : ℤ) - 1)) : ℤ) ≤ d.ell 0 * S.card := by
      rw [← hP0]; exact_mod_cast hSell
    have hbb0 : (0 : ℤ) ≤ d.ell (Finsupp.single P0 (B : ℤ)) := by positivity
    -- `G + r < r Q0`
    have h1 : (d.genus : ℤ) + d.ell 0 < d.ell 0 * Q0 := by
      by_contra hc
      push Not at hc
      have h5 : ((d.ell 0 : ℤ) * Q0) ^ 2 ≤ ((d.genus : ℤ) + d.ell 0) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hc 2
      have h6 : (0 : ℤ) ≤ (d.ell 0 : ℤ) ^ 2 * Q0 * (Q0 - 1) :=
        mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by linarith)
      nlinarith
    have hkey : ((d.ell 0 : ℤ) * Q0 - d.genus) * (d.ell 0 * B + d.ell 0 - d.genus) -
        d.ell 0 * d.ell C = (d.ell 0 : ℤ) ^ 2 * Q0 - ((d.genus : ℤ) + d.ell 0) ^ 2 +
        ((d.ell 0 : ℤ) * B - d.ell 0 * Q0 - 2 * d.genus) * (d.ell 0 * Q0 - d.genus - d.ell 0) := by
      rw [hEC]; ring
    have h7 : (0 : ℤ) ≤ ((d.ell 0 : ℤ) * B - d.ell 0 * Q0 - 2 * d.genus) *
        (d.ell 0 * Q0 - d.genus - d.ell 0) := mul_nonneg (by linarith) (by linarith)
    have h3 : ((d.ell 0 : ℤ) * Q0 - d.genus) * (d.ell 0 * B + d.ell 0 - d.genus) ≤
        ((d.ell 0 : ℤ) * Q0 - d.genus) * d.ell (Finsupp.single P0 (B : ℤ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h4 : ((d.ell 0 : ℤ) * Q0 - d.genus) * d.ell (Finsupp.single P0 (B : ℤ)) ≤
        (d.ell (Finsupp.single P0 ((Q0 : ℤ) - 1)) : ℤ) * d.ell (Finsupp.single P0 (B : ℤ)) :=
      mul_le_mul_of_nonneg_right (by linarith) hbb0
    have h5 : (d.ell (Finsupp.single P0 ((Q0 : ℤ) - 1)) : ℤ) * d.ell (Finsupp.single P0 (B : ℤ)) ≤
        (d.ell 0 * S.card : ℤ) * d.ell (Finsupp.single P0 (B : ℤ)) :=
      mul_le_mul_of_nonneg_right hSell' hbb0
    have h8 : (d.ell 0 : ℤ) * d.ell C < d.ell 0 * (S.card * d.ell (Finsupp.single P0 (B : ℤ))) := by
      nlinarith
    exact_mod_cast lt_of_mul_lt_mul_left h8 hr0.le
  -- a nonzero kernel element, by counting
  haveI : Finite (d.LD C) := Data.finite_LD hd.toAxioms0 C
  let Φ : (S → d.LD (Finsupp.single P0 (B : ℤ))) → d.LD C := fun g => ⟨_, hmem g⟩
  have hnotinj : ¬ Function.Injective Φ := by
    intro hinj
    have h1 := Nat.card_le_card_of_injective Φ hinj
    rw [Nat.card_fun, Data.card_LD hd.toAxioms0, Data.card_LD hd.toAxioms0, ← pow_mul,
      Nat.card_eq_finsetCard] at h1
    have h3 := Nat.pow_lt_pow_right (Data.one_lt_q (Fq := Fq))
      (show d.ell C < d.ell (Finsupp.single P0 (B : ℤ)) * S.card by rw [mul_comm]; exact hcount)
    exact absurd h1 (not_le.2 h3)
  obtain ⟨x, y, hxy, hΦ⟩ : ∃ x y, x ≠ y ∧ Φ x = Φ y := by
    by_contra h
    push Not at h
    exact hnotinj fun x y he => by_contra fun hne => h x y hne he
  obtain ⟨g, hg⟩ : ∃ g : S → F, g = fun a => ((x a : F) - (y a : F)) := ⟨_, rfl⟩
  have hgmem : ∀ a, g a ∈ d.LD (Finsupp.single P0 (B : ℤ)) := fun a => by
    rw [hg]; exact sub_mem (x a).2 (y a).2
  have hgne : ∃ a, g a ≠ 0 := by
    by_contra h
    push Not at h
    apply hxy
    funext a
    apply Subtype.ext
    have := h a
    rw [hg] at this
    exact sub_eq_zero.1 this
  have hker : ∑ a : S, f a ^ Q0 * τ (g a) = 0 := by
    have h1 : (Φ x : F) = Φ y := congrArg Subtype.val hΦ
    have h2 : ∑ a : S, f a ^ Q0 * τ (g a) = (Φ x : F) - Φ y := by
      simp only [Φ, hg, map_sub, mul_sub, Finset.sum_sub_distrib]
    rw [h2, h1, sub_self]
  -- the function `H`
  obtain ⟨H, hH⟩ : ∃ H : F, H = ∑ a : S, f a ^ Q0 * g a ^ (Q0 ^ 2) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : F, U = ∑ a : S, f a * g a ^ Q0 := ⟨_, rfl⟩
  have hHU : H = U ^ Q0 := by
    rw [hH, hU, hQ0def, sum_pow_char_pow]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_pow, ← pow_mul (g a), sq]
  -- `H ≠ 0`: the terms have distinct valuations at `P0`
  have hHne : H ≠ 0 := by
    obtain ⟨a0, ha0⟩ := hgne
    have hN : (Finset.univ.filter fun a : S => g a ≠ 0).Nonempty := ⟨a0, by simp [ha0]⟩
    obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image _
      (fun a : S => d.v P0 (f a ^ Q0 * g a ^ (Q0 ^ 2))) hN
    have hj' : g j ≠ 0 := (Finset.mem_filter.1 hj).2
    have htj : d.v P0 (f j ^ Q0 * g j ^ (Q0 ^ 2)) ≠ 0 :=
      (map_ne_zero _).2 (mul_ne_zero (pow_ne_zero _ (hf0 j j.2)) (pow_ne_zero _ hj'))
    have hval : ∀ a : S, g a ≠ 0 → ∃ s : ℤ,
        d.v P0 (f a ^ Q0 * g a ^ (Q0 ^ 2)) = exp ((Q0 : ℤ) * (a : ℕ) + (Q0 : ℤ) ^ 2 * s) := by
      intro a ha
      obtain ⟨s, hs⟩ : ∃ s : ℤ, d.v P0 (g a) = exp s :=
        ⟨_, (exp_log ((map_ne_zero _).2 ha)).symm⟩
      refine ⟨s, ?_⟩
      rw [map_mul, map_pow, map_pow, (hfS a a.2).2, hs, ← exp_nsmul, ← exp_nsmul, ← exp_add]
      congr 1
    have hlt : ∀ a ∈ (Finset.univ : Finset S) \ {j},
        d.v P0 (f a ^ Q0 * g a ^ (Q0 ^ 2)) < d.v P0 (f j ^ Q0 * g j ^ (Q0 ^ 2)) := by
      intro a ha
      have haj : a ≠ j := by simpa using ha
      by_cases hga : g a = 0
      · have h0 : f a ^ Q0 * g a ^ (Q0 ^ 2) = 0 := by
          rw [hga, zero_pow (pow_ne_zero 2 hQ0pos.ne'), mul_zero]
        rw [h0, map_zero]
        exact zero_lt_iff.2 htj
      · refine lt_of_le_of_ne (hjmax a (by simp [hga])) fun heq => haj ?_
        obtain ⟨s1, hs1⟩ := hval a hga
        obtain ⟨s2, hs2⟩ := hval j hj'
        rw [hs1, hs2] at heq
        have := le_antisymm (exp_le_exp.1 heq.le) (exp_le_exp.1 heq.ge)
        exact Subtype.ext (eq_of_mul_add_sq_eq hQ0pos (hSA a a.2) (hSA j j.2) this)
    have hv := Valuation.map_sum_eq_of_lt (d.v P0) (Finset.mem_univ j) hlt
    intro h0
    rw [← hH, h0, map_zero] at hv
    exact htj hv.symm
  -- `v_P H ≤ exp (-Q0)` on `T \ {P0}`
  have hHP : ∀ P ∈ T.erase P0, d.v P H ≤ exp (-(Q0 : ℤ)) := by
    intro P hP
    obtain ⟨hPne, hPT⟩ := Finset.mem_erase.1 hP
    have hH' : H = ∑ a : S, f a ^ Q0 * (g a ^ (Q0 ^ 2) - τ (g a)) := by
      simp only [mul_sub, Finset.sum_sub_distrib, hker, sub_zero, hH]
    have hlt1 : d.v P H < 1 := by
      rw [hH']
      refine Valuation.map_sum_lt _ one_ne_zero fun a _ => ?_
      rw [map_mul, map_pow]
      have h1 : d.v P (f a) ≤ 1 := v_le_one_of_mem_single hPne (hfS a a.2).1
      have h2 : d.v P (g a) ≤ 1 := v_le_one_of_mem_single hPne (hgmem a)
      have h3 : d.v P (g a ^ (Q0 ^ 2) - τ (g a)) < 1 := by
        rw [Valuation.map_sub_swap]; exact hT P hPT hPne (g a) h2
      calc d.v P (f a) ^ Q0 * d.v P (g a ^ (Q0 ^ 2) - τ (g a))
          ≤ 1 * d.v P (g a ^ (Q0 ^ 2) - τ (g a)) := mul_le_mul' (pow_le_one' h1 Q0) le_rfl
        _ < 1 := by rw [one_mul]; exact h3
    have hU1 : d.v P U < 1 := by
      rw [hHU, map_pow] at hlt1
      exact lt_one_of_pow_lt_one hlt1
    have hU2 : d.v P U ≤ exp (-1) := by
      have := lt_exp_iff_le_exp_sub_one.1 (show d.v P U < exp 0 by rwa [exp_zero])
      simpa using this
    rw [hHU, map_pow]
    have := pow_le_exp_mul hU2 Q0
    simpa using this
  -- `H ∈ L(D')`
  obtain ⟨D', hD'⟩ : ∃ D' : ι →₀ ℤ, D' = Finsupp.single P0 ((Q0 : ℤ) * ((Q0 : ℤ) - 1) +
      (Q0 : ℤ) ^ 2 * B) - ∑ P ∈ T.erase P0, Finsupp.single P (Q0 : ℤ) := ⟨_, rfl⟩
  have hHmem : H ∈ d.LD D' := by
    rw [Data.mem_LD]
    intro i
    rw [hD', Finsupp.sub_apply, sum_single_apply]
    by_cases hi0 : i = P0
    · rw [hi0, Finsupp.single_eq_same, if_neg (Finset.notMem_erase P0 T), sub_zero, hH]
      refine Valuation.map_sum_le _ fun a _ => ?_
      rw [map_mul, map_pow, map_pow, exp_add]
      have h1 := pow_le_exp_mul (v_le_exp_of_mem_single (hfS a a.2).1) Q0
      have h2 := pow_le_exp_mul (v_le_exp_of_mem_single (hgmem a)) (Q0 ^ 2)
      refine mul_le_mul' (h1.trans (exp_le_exp.2 ?_)) (h2.trans (le_of_eq (by push_cast; ring_nf)))
      have := hSA a a.2
      have h5 : ((a : ℕ) : ℤ) ≤ (Q0 : ℤ) - 1 := by omega
      exact mul_le_mul_of_nonneg_left h5 (by positivity)
    · have hs0 : Finsupp.single P0 ((Q0 : ℤ) * ((Q0 : ℤ) - 1) + (Q0 : ℤ) ^ 2 * B) i = 0 := by
        rw [Finsupp.single_apply, if_neg (Ne.symm hi0)]
      rw [hs0, zero_sub]
      by_cases hiT : i ∈ T.erase P0
      · rw [if_pos hiT]
        exact hHP i hiT
      · rw [if_neg hiT, neg_zero, exp_zero, hH]
        refine Valuation.map_sum_le _ fun a _ => ?_
        rw [map_mul, map_pow, map_pow]
        have h1 : d.v i (f a) ≤ 1 := v_le_one_of_mem_single hi0 (hfS a a.2).1
        have h2 : d.v i (g a) ≤ 1 := v_le_one_of_mem_single hi0 (hgmem a)
        calc d.v i (f a) ^ Q0 * d.v i (g a) ^ (Q0 ^ 2) ≤ 1 * 1 :=
              mul_le_mul' (pow_le_one' h1 Q0) (pow_le_one' h2 _)
          _ = 1 := one_mul 1
  -- `deg D' ≥ 0`
  have hdeg : 0 ≤ d.degD D' := by
    by_contra hneg
    push Not at hneg
    have := Data.LD_eq_bot_of_degD_neg hd hneg
    rw [this, Submodule.mem_bot] at hHmem
    exact hHne hHmem
  rw [hD', d.degD_sub, d.degD_single, degD_sum_single, hP0] at hdeg
  have key : (Q0 : ℤ) * ∑ P ∈ T.erase P0, (d.deg P : ℤ) ≤
      (d.ell 0 : ℤ) * ((Q0 : ℤ) * ((Q0 : ℤ) - 1) + (Q0 : ℤ) ^ 2 * B) := by
    linarith
  zify [(show 1 ≤ Q0 from hQ0pos)]
  push_cast
  linarith

end Core

end RamanujanPetersson.ZetaSB


