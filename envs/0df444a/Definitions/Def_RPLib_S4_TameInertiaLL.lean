-- Prove2me | Definitions.Def_RPLib_S4_TameInertiaLL
-- name    : RPLib_S4_TameInertiaLL
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:15:47.096219+00:00
-- url     : https://prove2.me/theorems/2f14a417-182e-4938-ada1-acbf6b1ba045
-- title:
--   Inertia fixes constants, and the local Kummer lemma
-- statement:
--   For a prime $Q$ of the pro-chart (integral closure of a boundary chart ring $R_0$ in $K_U$) the inertia group $I(Q)$ fixes every constant, so $I(Q) \le \pi_1^{geo}$. The local Kummer lemma: if $$\gamma^N = c^N b / s$$ with $\sigma \in I(Q)$ fixing $c, b, s$, with $b, s \notin Q$ and $N$ invertible, then $\sigma(\gamma) = \gamma$; that is, a Kummer radical whose $Q$-adic valuation is divisible by $N$ is not moved by inertia.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapter IV, Section 2; J. Neukirch, Algebraic Number Theory, Grundlehren 322, Springer (1999), Chapter I, Section 9

import Mathlib
import Definitions.Def_RPLib_S4_CurveCohCurve
import Definitions.Def_RPLib_S4_KummerUnrCore

/-!
# Tame inertia, part LL: inertia fixes constants and the local Kummer lemma (S4-PD item (2), T0 + T1)

* `inertia_le_pi1geo`: the inertia group of a prime of the pro-chart fixes every constant, so `I ≤ π₁^geo`.
* `fix_of_inertia_local`: if `γ^N = c^N b / s` with `σ` in the inertia of `Q` fixing `c, b, s` and `b, s ∉ Q`,
  then `σ γ = γ` (a Kummer radical whose `Q`-adic valuation is divisible by `N` is not moved by inertia).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
  (R0 : Type) [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)]
  [IsScalarTower R0 K (maxUnram A K)]

theorem coe_smul (σ : Pi1 A K) (x : proChart A K R0) :
    ((σ • x : proChart A K R0) : maxUnram A K) = σ (x : maxUnram A K) := rfl

/-- T0: inertia fixes the constants (the Artin-Schreier argument: `σ x - x` is a constant lying in `Q`). -/
theorem inertia_le_pi1geo (p : ℕ) [Fact p.Prime] [CharP K p] {e : ℕ} (he : 0 < e)
    (Q : Ideal (proChart A K R0)) [hQ : Q.IsPrime] :
    Q.inertia (Pi1 A K) ≤ pi1geo A K (p ^ e) := by
  intro σ hσ
  rw [mem_pi1geo]
  rintro x ⟨n, hn, hx⟩
  haveI : CharP (maxUnram A K) p :=
    charP_of_injective_algebraMap (algebraMap K (maxUnram A K)).injective p
  have hx' : x ^ p ^ (e * n) = x := by rw [pow_mul]; exact hx
  have hM1 : 1 < p ^ (e * n) :=
    Nat.one_lt_pow (Nat.mul_ne_zero he.ne' hn.ne') (Fact.out : p.Prime).one_lt
  haveI : Nontrivial R0 := (algebraMap R0 K).domain_nontrivial
  have hxint : IsIntegral R0 x := by
    refine ⟨Polynomial.X ^ (p ^ (e * n)) - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hM1)
    · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, hx', sub_self]
  let xI : proChart A K R0 := ⟨x, (mem_integralClosure_iff _ _).2 hxint⟩
  have hd : σ • xI - xI ∈ Q := AddSubgroup.mem_inertia.1 hσ xI
  have hdpow : (σ • xI - xI) ^ p ^ (e * n) = σ • xI - xI := by
    apply Subtype.ext
    show (σ x - x) ^ p ^ (e * n) = σ x - x
    rw [sub_pow_char_pow, ← map_pow, hx']
  have hd0 : σ • xI - xI = 0 := by
    by_contra hne
    have h1 : (σ • xI - xI) ^ (p ^ (e * n) - 1) * (σ • xI - xI) = 1 * (σ • xI - xI) := by
      rw [← pow_succ, Nat.sub_add_cancel hM1.le, hdpow, one_mul]
    have h2 := mul_right_cancel₀ hne h1
    have hu : IsUnit (σ • xI - xI) := IsUnit.of_pow_eq_one h2 (by omega)
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hd hu)
  have h3 : σ x - x = 0 := congrArg Subtype.val hd0
  exact sub_eq_zero.1 h3

/-- T1 (local Kummer lemma): `γ^N · s = c^N · b` with `b, s ∉ Q`, `σ ∈ I(Q)` fixing `c, b, s` ⇒ `σ γ = γ`. -/
theorem fix_of_inertia_local {Q : Ideal (proChart A K R0)} [hQ : Q.IsPrime] {N : ℕ}
    (hN : IsUnit (N : proChart A K R0)) {σ : Pi1 A K} (hσ : σ ∈ Q.inertia (Pi1 A K))
    {γ c : maxUnram A K} {b s : proChart A K R0} (hc : c ≠ 0) (hb : b ∉ Q) (hs : s ∉ Q)
    (hcf : σ c = c) (hbf : σ (b : maxUnram A K) = b) (hsf : σ (s : maxUnram A K) = s)
    (hγ : γ ^ N * (s : maxUnram A K) = c ^ N * (b : maxUnram A K)) : σ γ = γ := by
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hN
    · exact h
  have hb0 : (b : maxUnram A K) ≠ 0 := by
    intro h; apply hb
    have : b = 0 := Subtype.ext h
    rw [this]; exact Q.zero_mem
  have hs0 : (s : maxUnram A K) ≠ 0 := by
    intro h; apply hs
    have : s = 0 := Subtype.ext h
    rw [this]; exact Q.zero_mem
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [zero_pow hN0.ne', zero_mul] at hγ
    exact mul_ne_zero (pow_ne_zero _ hc) hb0 hγ.symm
  obtain ⟨g', hg'⟩ : ∃ g' : maxUnram A K, g' = (s : maxUnram A K) * γ / c := ⟨_, rfl⟩
  have hg'pow : g' ^ N = (s : maxUnram A K) ^ (N - 1) * b := by
    rw [hg', div_pow, mul_pow, div_eq_iff (pow_ne_zero _ hc)]
    have h4 : (s : maxUnram A K) ^ N = (s : maxUnram A K) ^ (N - 1) * s := by
      rw [← pow_succ]; congr 1; omega
    rw [h4, mul_assoc, mul_comm (s : maxUnram A K) (γ ^ N), hγ]
    ring
  have hg'int : IsIntegral R0 g' := by
    have h1 : IsIntegral R0 (g' ^ N) := by
      rw [hg'pow]
      exact (((mem_integralClosure_iff _ _).1 s.2).pow _).mul ((mem_integralClosure_iff _ _).1 b.2)
    exact IsIntegral.of_pow hN0 h1
  let gI : proChart A K R0 := ⟨g', (mem_integralClosure_iff _ _).2 hg'int⟩
  have hgQ : gI ∉ Q := by
    intro h
    have hpow : gI ^ N ∈ Q := Q.pow_mem_of_mem h N hN0
    have heq : gI ^ N = s ^ (N - 1) * b := by
      apply Subtype.ext
      show g' ^ N = (s : maxUnram A K) ^ (N - 1) * b
      exact hg'pow
    rw [heq] at hpow
    rcases hQ.mem_or_mem hpow with h1 | h1
    · exact hs (hQ.mem_of_pow_mem _ h1)
    · exact hb h1
  obtain ⟨z, hz⟩ : ∃ z : maxUnram A K, z = σ γ / γ := ⟨_, rfl⟩
  have hfix : σ (γ ^ N) = γ ^ N := by
    have h2 : γ ^ N = c ^ N * b / s := by rw [eq_div_iff hs0]; exact hγ
    rw [h2, map_div₀, map_mul, map_pow, hcf, hbf, hsf]
  have hzN : z ^ N = 1 := by
    rw [hz, div_pow, ← map_pow, hfix, div_self (pow_ne_zero _ hγ0)]
  have hzint : IsIntegral R0 z := IsIntegral.of_pow hN0 (by rw [hzN]; exact isIntegral_one)
  let zI : proChart A K R0 := ⟨z, (mem_integralClosure_iff _ _).2 hzint⟩
  have hmem : σ • gI - gI ∈ Q := AddSubgroup.mem_inertia.1 hσ gI
  have hfac : σ • gI - gI = (zI - 1) * gI := by
    apply Subtype.ext
    show σ g' - g' = (z - 1) * g'
    rw [hg', map_div₀, map_mul, hsf, hcf, hz]
    field_simp
  rw [hfac] at hmem
  have hz1 : zI - 1 ∈ Q := (hQ.mem_or_mem hmem).resolve_right hgQ
  have hzI : zI ^ N = 1 := by
    apply Subtype.ext
    show z ^ N = 1
    exact hzN
  have h5 : zI = 1 := Kummer.eq_one_of_sub_mem hN hzI hz1
  have hz' : z = 1 := congrArg Subtype.val h5
  rw [hz, div_eq_one_iff_eq hγ0] at hz'
  exact hz'

end TameInertia
end RamanujanPetersson


