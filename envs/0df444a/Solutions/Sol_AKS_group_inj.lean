-- Prove2me | solution 1 for AKS.group_inj
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:11:18.560989+00:00
-- url     : https://prove2.me/submissions/2e230d6b-9c8f-4c32-851e-0876d919c7dd

import Mathlib
import Definitions.Def_AKS_poly
import Definitions.Def_AKS_alg
open AKS

open Polynomial in
/-- If X^r - 1 divides f^m - f(X^m) then in AdjoinRoot h (h ∣ X^r - 1) f(ζ)^m = f(ζ^m). -/
theorem g71b_intro_eval {p r : ℕ} (h f : Polynomial (ZMod p))
    (hdiv : h ∣ (X ^ r - 1 : Polynomial (ZMod p))) {m : ℕ} (hm : introspective p r f m) :
    aeval (AdjoinRoot.root h) f ^ m = aeval (AdjoinRoot.root h ^ m) f := by
  have h1 : h ∣ f ^ m - f.comp (X ^ m) := dvd_trans hdiv hm
  have h2 : aeval (AdjoinRoot.root h) (f ^ m - f.comp (X ^ m)) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]; exact h1
  rw [map_sub, map_pow, aeval_comp, map_pow, aeval_X, sub_eq_zero] at h2
  exact h2

open Polynomial in
theorem g71b_root_pow_r {p r : ℕ} (h : Polynomial (ZMod p))
    (hdiv : h ∣ (X ^ r - 1 : Polynomial (ZMod p))) : AdjoinRoot.root h ^ r = 1 := by
  have h2 : aeval (AdjoinRoot.root h) (X ^ r - 1 : Polynomial (ZMod p)) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]; exact hdiv
  rw [map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at h2
  exact h2

theorem g71b_pow_mod {M : Type*} [Monoid M] (x : M) (r m : ℕ) (hx : x ^ r = 1) :
    x ^ m = x ^ (m % r) := by
  conv_lhs => rw [← Nat.mod_add_div m r, pow_add, pow_mul, hx, one_pow, mul_one]

theorem solution (n p r t ℓ : ℕ) [Fact (Nat.Prime p)]
    (h : Polynomial (ZMod p)) [Fact (Irreducible h)]
    (hdiv : h ∣ (Polynomial.X ^ r - 1 : Polynomial (ZMod p)))
    (hprim : ∀ k : ℕ, 0 < k → k < r →
      ¬ h ∣ (Polynomial.X ^ k - 1 : Polynomial (ZMod p)))
    (hintros : ∀ m, inI n p m → ∀ f, inP p ℓ f → introspective p r f m)
    (ht : t ≤ (Gfin n p r).card)
    (f g : Polynomial (ZMod p)) (hf : inP p ℓ f) (hg : inP p ℓ g)
    (hne : f ≠ g) (hft : Polynomial.natDegree f < t)
    (hgt : Polynomial.natDegree g < t) :
    Polynomial.aeval (AdjoinRoot.root h) f
      ≠ Polynomial.aeval (AdjoinRoot.root h) g := by
  intro hfg
  set ζ := AdjoinRoot.root h with hζ
  have hζr : ζ ^ r = 1 := g71b_root_pow_r h hdiv
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      have : Gfin n p r = ∅ := by
        rw [h0]; simp [Gfin]
      rw [this] at ht; simp at ht; omega
    · exact h0
  have hζ0 : ζ ≠ 0 := by
    intro h0; rw [h0, zero_pow hr.ne'] at hζr; exact zero_ne_one hζr
  have hζk : ∀ k, 0 < k → k < r → ζ ^ k ≠ 1 := by
    intro k hk hkr hk1
    apply hprim k hk hkr
    have h2 : Polynomial.aeval ζ (Polynomial.X ^ k - 1 : Polynomial (ZMod p)) = 0 := by
      rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hk1, sub_self]
    rwa [hζ, AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at h2
  have hinj : Set.InjOn (fun k : ℕ => ζ ^ k) ↑(Gfin n p r) := by
    have hlt : ∀ k ∈ Gfin n p r, k < r := by
      intro x hx
      simp only [Gfin, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i, -, j, -, rfl⟩ := hx
      exact Nat.mod_lt _ hr
    have key : ∀ k1 k2, k1 < k2 → k2 < r → ζ ^ k1 ≠ ζ ^ k2 := by
      intro k1 k2 h12 h2r heq
      have : ζ ^ k2 = ζ ^ k1 * ζ ^ (k2 - k1) := by rw [← pow_add]; congr 1; omega
      rw [this] at heq
      have h3 : ζ ^ (k2 - k1) = 1 :=
        mul_left_cancel₀ (pow_ne_zero k1 hζ0) (heq.symm.trans (mul_one _).symm)
      exact hζk (k2 - k1) (by omega) (by omega) h3
    intro k1 hk1 k2 hk2 heq
    simp only at heq
    have h1 := hlt k1 hk1
    have h2 := hlt k2 hk2
    rcases lt_trichotomy k1 k2 with hl | he | hl
    · exact absurd heq (key _ _ hl h2)
    · exact he
    · exact absurd heq.symm (key _ _ hl h1)
  set Q : Polynomial (AdjoinRoot h) := (f - g).map (algebraMap (ZMod p) (AdjoinRoot h)) with hQ
  have hQ0 : Q ≠ 0 := by
    rw [hQ, Polynomial.map_ne_zero_iff (algebraMap (ZMod p) (AdjoinRoot h)).injective]
    exact sub_ne_zero.2 hne
  have hQdeg : Q.natDegree < t := by
    calc Q.natDegree ≤ (f - g).natDegree := Polynomial.natDegree_map_le
      _ ≤ max f.natDegree g.natDegree := Polynomial.natDegree_sub_le f g
      _ < t := max_lt hft hgt
  have hsub : ((Gfin n p r).image (fun k : ℕ => ζ ^ k)).val ⊆ Q.roots := by
    intro x hx
    rw [Finset.mem_val, Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hk' := hk
    simp only [Gfin, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at hk'
    obtain ⟨i, -, j, -, hkij⟩ := hk'
    have hI : inI n p ((n / p) ^ i * p ^ j) := ⟨i, j, rfl⟩
    rw [Polynomial.mem_roots hQ0, Polynomial.IsRoot, hQ, Polynomial.eval_map_algebraMap,
      ← hkij, ← g71b_pow_mod ζ r _ hζr, map_sub,
      ← g71b_intro_eval h f hdiv (hintros _ hI f hf),
      ← g71b_intro_eval h g hdiv (hintros _ hI g hg), ← hζ, hfg, sub_self]
  have hc := Polynomial.card_le_degree_of_subset_roots hsub
  rw [Finset.card_image_of_injOn hinj] at hc
  omega
