-- Prove2me | Definitions.Def_RPLib_S4_TameInertiaPole
-- name    : RPLib_S4_TameInertiaPole
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:02:10.474205+00:00
-- url     : https://prove2.me/theorems/024343bb-a527-4212-beec-19372dce5687
-- title:
--   A pole element of order $\equiv 1 \bmod N$
-- statement:
--   Let $A$ be a domain with fraction field $K$ and $v$ a height-one prime of a Dedekind domain $R_0$ with the same fraction field. If some $a \in A$ has a pole at $v$, then for every $N \ge 1$ some $f \in A$ has a pole of order exactly $$N n + 1, \qquad n > 0.$$ Proof: write a uniformiser as $b/c$ with $b, c \in A$; for $k$ large $f_1 = a^k b$ and $f_2 = a^k c$ have consecutive pole orders $n_0, n_0 + 1$, and $f_1^{N-1} f_2$ has pole order $N n_0 + 1$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Neukirch, Algebraic Number Theory, Grundlehren 322, Springer (1999), Chapter I, Section 11; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009), Chapter 1

import Mathlib

/-!
# Tame inertia, part Pole: a pole element of order `≡ 1 mod N` (S4-PD item (2), T4)

Let `A` be a domain with fraction field `K` and `v` a height-one prime of a Dedekind domain `R0` with the same
fraction field. If some `a ∈ A` has a pole at `v` (`1 < v(a)`), then for every `N = M + 1 ≥ 1` some `f ∈ A` has
a pole of order exactly `N n + 1` with `n > 0` (`exists_pole_mod`). Proof: write a uniformizer as `b / c`
with `b, c ∈ A`; for `k` large, `f₁ = a^k b` and `f₂ = a^k c` have consecutive pole orders `n₀, n₀ + 1`, and
`f₁^M f₂` has pole order `N n₀ + 1`.
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace TameInertia

open IsDedekindDomain

noncomputable section

section Pole

variable {A K R0 : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

theorem val_exp_of_ne_zero (v : HeightOneSpectrum R0) {x : K} (hx : x ≠ 0) :
    ∃ α : ℤ, v.valuation K x = WithZero.exp α :=
  ⟨WithZero.log (v.valuation K x), (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx)).symm⟩

/-- **T4.** From one pole at `v` in `A`, a pole of order exactly `(M + 1) n + 1` with `n > 0`. -/
theorem exists_pole_mod (v : HeightOneSpectrum R0) (M : ℕ) {a : A}
    (ha : 1 < v.valuation K (algebraMap A K a)) :
    ∃ (f : A) (n : ℕ), 0 < n ∧
      v.valuation K (algebraMap A K f) = WithZero.exp ((((M + 1) * n + 1 : ℕ)) : ℤ) := by
  have ha0 : algebraMap A K a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact not_lt_of_ge zero_le' ha
  obtain ⟨α, hα⟩ := val_exp_of_ne_zero v ha0
  have hα0 : 0 < α := by
    rw [hα, ← WithZero.exp_zero, WithZero.exp_lt_exp] at ha
    exact ha
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  obtain ⟨b, c, hc, hbc⟩ := IsFractionRing.div_surjective A π
  have hc0 : algebraMap A K c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc
  obtain ⟨γ, hγ⟩ := val_exp_of_ne_zero v hc0
  have hb : v.valuation K (algebraMap A K b) = WithZero.exp (γ - 1) := by
    have h : algebraMap A K b = π * algebraMap A K c := by
      rw [← hbc]
      field_simp
    rw [h, map_mul, hπ, hγ, ← WithZero.exp_add]
    congr 1
    ring
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = (2 - γ).toNat := ⟨_, rfl⟩
  have hk1 : 2 - γ ≤ (k : ℤ) := by rw [hk]; exact Int.self_le_toNat _
  obtain ⟨n0, hn0⟩ : ∃ n0 : ℤ, n0 = (k : ℤ) * α + (γ - 1) := ⟨_, rfl⟩
  have hn0pos : 0 < n0 := by
    have hk0 : (0 : ℤ) ≤ k := Int.natCast_nonneg k
    have : (k : ℤ) ≤ (k : ℤ) * α := by nlinarith
    omega
  refine ⟨(a ^ k * b) ^ M * (a ^ k * c), n0.toNat, by omega, ?_⟩
  simp only [map_mul, map_pow, hα, hb, hγ, ← WithZero.exp_nsmul, ← WithZero.exp_add]
  congr 1
  push_cast
  rw [Int.toNat_of_nonneg hn0pos.le, hn0]
  simp only [nsmul_eq_mul]
  ring

/-- The pole order `(M + 1) n + 1` is prime to `M + 1`. -/
theorem coprime_pole_order (M n : ℕ) : Nat.Coprime ((M + 1) * n + 1) (M + 1) := by
  exact (Nat.coprime_mul_left_add_left 1 (M + 1) n).2 (Nat.coprime_one_left _)

end Pole

end

end TameInertia
end RamanujanPetersson


