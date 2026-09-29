-- Prove2me | Definitions.Def_LocalNewvector_CharConductor
-- name    : LocalNewvector_CharConductor
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/f7101604-9798-5c18-96d4-a063aafee1ad
-- title:
--   Character conductor exponent and higher units of Qp×​
-- statement:
--   Fix a prime $p$. All notions here concern monoid homomorphisms $\mu : \mathbb{Q}_p^\times \to \mathbb{C}^\times$, with no continuity or finite-order requirement imposed.
--
--   `IsUnramified p μ` says that $\mu(u) = 1$ for every $u \in \mathbb{Q}_p^\times$ with $\|u\| = 1$. The filtration is given by `higherUnits p n`, a *set* (not a subgroup) of $\mathbb{Q}_p^\times$: for $n = 0$ it is $\{u : \|u\| = 1\}$, and for $n \ge 1$ it is $\{u : \|u\| = 1 \text{ and } \|u - 1\| \le p^{-n}\}$; the definition is phrased uniformly as $\|u\| = 1$ together with the disjunction ($n = 0$ or $\|u-1\| \le p^{-n}$). It contains $1$ and is antitone in $n$, so $n \mapsto$ `higherUnits p n` is a decreasing family.
--
--   `HasCharConductor p μ c` is a two-clause relation, not a function: $\mu$ is trivial on `higherUnits p c`, and for every $m < c$ there is some $u \in$ `higherUnits p m` with $\mu(u) \ne 1$. The minimality clause forces uniqueness of $c$ (`hasCharConductor_unique`), and at $c = 0$ the relation is equivalent to `IsUnramified p μ`; the trivial character has exponent $0$ and no positive exponent.
--
--   The unramified characters are produced explicitly: `unitValuation p` is the homomorphism $\mathbb{Q}_p^\times \to \mathrm{Multiplicative}\,\mathbb{Z}$ given by the $p$-adic valuation of a unit, and for $s \in \mathbb{C}^\times$, `valChar p s` is $u \mapsto s^{v(u)}$. Each `valChar p s` is unramified, hence has conductor exponent $0$; it is nontrivial as soon as $s \ne 1$ (evaluate at $p$, where $v(p) = 1$), giving a nontrivial unramified character, e.g. $u \mapsto 2^{v(u)}$.
--
--   **Relation to Mathlib.** Mathlib provides the $p$-adic norm and the valuation of a nonzero $p$-adic number (`Padic.valuation`, `Padic.norm_eq_zpow_neg_valuation`), on which `unitValuation` and the norm conditions rest; the higher unit sets, the unramifiedness predicate and the conductor-exponent relation are the project's own, with `higherUnits` carried as a set rather than as a subgroup.
--
--   **Where it is used.** This is the vocabulary in which the conductor exponent of a character of $\mathbb{Q}_p^\times$ is stated, as needed for the local newvector theory: the conductor of a principal series $B(\mu_1, \mu_2)$ is expressed in terms of exponents $n_1, n_2$ attached to $\mu_1, \mu_2$ by `HasCharConductor`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LocalNewvector_CharConductor.lean

import Definitions.Def_LocalLanglands_LocalHeckeInstance

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace LocalNewvector

variable (p : ℕ) [Fact p.Prime]

def IsUnramified (μ : ℚ_[p]ˣ →* ℂˣ) : Prop :=
  ∀ u : ℚ_[p]ˣ, ‖(u : ℚ_[p])‖ = 1 → μ u = 1

theorem isUnramified_one : IsUnramified p (1 : ℚ_[p]ˣ →* ℂˣ) := fun _ _ => rfl

def unitValuation : ℚ_[p]ˣ →* Multiplicative ℤ where
  toFun u := Multiplicative.ofAdd (u : ℚ_[p]).valuation
  map_one' := by simp [Padic.valuation_one]
  map_mul' u v := by
    simp only [Units.val_mul]
    rw [Padic.valuation_mul u.ne_zero v.ne_zero, ofAdd_add]

@[simp] theorem unitValuation_apply (u : ℚ_[p]ˣ) :
    Multiplicative.toAdd (unitValuation p u) = (u : ℚ_[p]).valuation := rfl

def valChar (s : ℂˣ) : ℚ_[p]ˣ →* ℂˣ :=
  (zpowersHom ℂˣ s).comp (unitValuation p)

@[simp] theorem valChar_apply (s : ℂˣ) (u : ℚ_[p]ˣ) :
    valChar p s u = s ^ (u : ℚ_[p]).valuation := rfl

theorem isUnramified_valChar (s : ℂˣ) : IsUnramified p (valChar p s) := by
  intro u hu
  rw [valChar_apply]
  have hv0 : (u : ℚ_[p]).valuation = 0 := by
    have hp_ne_one : (p : ℝ) ≠ 1 := mod_cast (Fact.out : p.Prime).ne_one
    have hp_pos : (0 : ℝ) < p := mod_cast (Fact.out : p.Prime).pos
    have := Padic.norm_eq_zpow_neg_valuation u.ne_zero
    rw [hu] at this
    have := (zpow_right_inj₀ hp_pos hp_ne_one).mp
      (this.symm.trans (zpow_zero (p : ℝ)).symm)
    omega
  rw [hv0, zpow_zero]

theorem valChar_ne_one {s : ℂˣ} (hs : s ≠ 1) : valChar p s ≠ 1 := by
  intro h
  have hpne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp1 : (p : ℚ_[p]).valuation = 1 := by
    have := Padic.valuation_p (p := p); exact_mod_cast this
  have := DFunLike.congr_fun h (Units.mk0 (p : ℚ_[p]) hpne)
  rw [valChar_apply, Units.val_mk0, hp1, zpow_one, MonoidHom.one_apply] at this
  exact hs this

theorem exists_isUnramified_ne_one : ∃ μ : ℚ_[p]ˣ →* ℂˣ, IsUnramified p μ ∧ μ ≠ 1 := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  refine ⟨valChar p (Units.mk0 2 h2), isUnramified_valChar p _, valChar_ne_one p ?_⟩
  intro h1
  have := Units.val_eq_one.mpr h1
  simp only [Units.val_mk0] at this
  exact (by norm_num : (2 : ℂ) ≠ 1) this

def higherUnits (n : ℕ) : Set ℚ_[p]ˣ :=
  {u | ‖(u : ℚ_[p])‖ = 1 ∧ (n = 0 ∨ ‖(u : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ)))}

theorem mem_higherUnits_iff {n : ℕ} {u : ℚ_[p]ˣ} :
    u ∈ higherUnits p n ↔ ‖(u : ℚ_[p])‖ = 1 ∧ (n = 0 ∨ ‖(u : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ))) :=
  Iff.rfl

theorem mem_higherUnits_zero_iff {u : ℚ_[p]ˣ} : u ∈ higherUnits p 0 ↔ ‖(u : ℚ_[p])‖ = 1 := by
  simp [mem_higherUnits_iff]

theorem one_mem_higherUnits (n : ℕ) : (1 : ℚ_[p]ˣ) ∈ higherUnits p n := by
  refine ⟨by simp, ?_⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · exact Or.inl h
  · right
    simp only [Units.val_one, sub_self, norm_zero]
    positivity

theorem higherUnits_antitone : Antitone (higherUnits p) := by
  intro m n hmn u hu
  obtain ⟨hnorm, hball⟩ := hu
  refine ⟨hnorm, ?_⟩
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exact Or.inl hm
  · right
    rcases hball with hn0 | hle
    · omega
    · have hp1 : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (Nat.Prime.one_lt (Fact.out (p := p.Prime))).le
      exact hle.trans (zpow_le_zpow_right₀ hp1 (by omega))

def HasCharConductor (μ : ℚ_[p]ˣ →* ℂˣ) (c : ℕ) : Prop :=
  (∀ u ∈ higherUnits p c, μ u = 1) ∧ ∀ m < c, ∃ u ∈ higherUnits p m, μ u ≠ 1

theorem hasCharConductor_zero_iff_isUnramified {μ : ℚ_[p]ˣ →* ℂˣ} :
    HasCharConductor p μ 0 ↔ IsUnramified p μ := by
  constructor
  · intro h u hu
    exact h.1 u ((mem_higherUnits_zero_iff p).mpr hu)
  · intro h
    exact ⟨fun u hu => h u ((mem_higherUnits_zero_iff p).mp hu), fun m hm => absurd hm (Nat.not_lt_zero m)⟩

theorem hasCharConductor_unique {μ : ℚ_[p]ˣ →* ℂˣ} {c c' : ℕ}
    (h : HasCharConductor p μ c) (h' : HasCharConductor p μ c') : c = c' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨u, hu, hne1⟩ := h'.2 c hlt
    exact hne1 (h.1 u hu)
  · obtain ⟨u, hu, hne1⟩ := h.2 c' hgt
    exact hne1 (h'.1 u hu)

theorem hasCharConductor_one_zero : HasCharConductor p (1 : ℚ_[p]ˣ →* ℂˣ) 0 :=
  (hasCharConductor_zero_iff_isUnramified p).mpr (isUnramified_one p)

theorem hasCharConductor_valChar_zero (s : ℂˣ) : HasCharConductor p (valChar p s) 0 :=
  (hasCharConductor_zero_iff_isUnramified p).mpr (isUnramified_valChar p s)

theorem not_hasCharConductor_one_succ (c : ℕ) : ¬ HasCharConductor p (1 : ℚ_[p]ˣ →* ℂˣ) (c + 1) := by
  rintro ⟨-, hmin⟩
  obtain ⟨u, -, hne⟩ := hmin c (Nat.lt_succ_self c)
  exact hne rfl

end LocalNewvector

end


