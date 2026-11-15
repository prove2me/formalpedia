-- Prove2me | Definitions.Def_RPLib_S3_Wt2RPC
-- name    : RPLib_S3_Wt2RPC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:57:36.561311+00:00
-- url     : https://prove2.me/theorems/cea8e168-3051-4bc8-8bd4-e3617cb6d291
-- title:
--   Weight-two Ramanujan-Petersson library: `IdentityI' → PhiEigenBound 2`
-- statement:
--   `IdentityI' → PhiEigenBound 2`.
--
--   At weight 2, Identity (I') reads `Tr Φ^m + #Y₁(M)(F_{p^m}) - 1 - p^m = O(1 + m)`. The point count of `Y₁(M)` is
--   `Σ_i N_m(F_i) + O(1)` over a nonempty family of components (`X1Count`), and Hasse-Weil for an arbitrary constant
--   field (`hw_general`) gives `N_m(F_i) = [r_i ∣ m] r_i p^m + O(√p^m)`. With `[r ∣ m] r p^m = Σ_{j<r} (ζ_r^j p)^m`
--   the power sums of the multiset `roots(charpoly Φ) + (B - {p})`, `B = ⋃_i {ζ_{r_i}^j p}`, are `O(√p^m)`, so every
--   element, in particular every eigenvalue of `Φ`, has modulus at most `√p` (`ExpSum`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211

import Mathlib
import Definitions.Def_RPLib_S3_Wt2RPB
import Definitions.Def_RPLib_S3_Wt2RPCFC
import Definitions.Def_RPLib_S3_X1Count
import Definitions.Def_RPLib_S3_ExpSum
import Definitions.Def_RPLib_S1_FinDim

/-!
# S3-Wt2RP, O3 part C: `IdentityI' → PhiEigenBound 2`

At weight 2, Identity (I') reads `Tr Φ^m + #Y₁(M)(F_{p^m}) - 1 - p^m = O(1 + m)`. The point count of `Y₁(M)` is
`Σ_i N_m(F_i) + O(1)` over a nonempty family of components (`X1Count`), and Hasse-Weil for an arbitrary constant
field (`hw_general`) gives `N_m(F_i) = [r_i ∣ m] r_i p^m + O(√p^m)`. With `[r ∣ m] r p^m = Σ_{j<r} (ζ_r^j p)^m`
the power sums of the multiset `roots(charpoly Φ) + (B - {p})`, `B = ⋃_i {ζ_{r_i}^j p}`, are `O(√p^m)`, so every
element, in particular every eigenvalue of `Φ`, has modulus at most `√p` (`ExpSum`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open Polynomial Filter Asymptotics

namespace RamanujanPetersson.S3.Wt2

open RamanujanPetersson.Places RamanujanPetersson.Diamond

/-- The multiset `{ζ_r^j x : j < r}`. -/
noncomputable def rootsMul (r : ℕ) (x : ℂ) : Multiset ℂ := (Multiset.range r).map fun j => zeta r ^ j * x

theorem mem_rootsMul_self (r : ℕ) (hr : 1 ≤ r) (x : ℂ) : x ∈ rootsMul r x :=
  Multiset.mem_map.2 ⟨0, Multiset.mem_range.2 (by omega), by simp⟩

theorem one_isBigO (s : ℝ) (hs : 1 < s) : (fun _ : ℕ => (1 : ℝ)) =O[atTop] (fun m => s ^ m) := by
  simpa using (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 0 hs).isBigO

theorem one_add_isBigO (s : ℝ) (hs : 1 < s) : (fun m : ℕ => (1 : ℝ) + m) =O[atTop] (fun m => s ^ m) := by
  have h1 := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 1 hs).isBigO
  simp only [pow_one] at h1
  exact (one_isBigO s hs).add h1

/-- **Weight 2**: Identity (I') forces `|α| ≤ √p` for every eigenvalue of `Φ`. -/
theorem phiEigenBound_two_of (hI : IdentityI') : PhiEigenBound 2 := by
  intro M _ hM p _ hpM α hα
  classical
  haveI : FiniteDimensional ℂ (S1 M ((2 : ℕ) : ℤ)) := FinDim.finiteDimensional_cuspForm_Gamma1 M _
  have hp := (Fact.out : p.Prime)
  have hsp : 1 < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt zero_le_one (by exact_mod_cast hp.one_lt)
  set Φ := phiOp p hpM ((2 : ℕ) : ℤ) with hΦ
  obtain ⟨C1, hC1⟩ := hI M hM 2 le_rfl p hpM
  obtain ⟨ι, _, ⟨i0⟩, g, C2, hC2⟩ := X1Count.card_Y1_sub_numPoints_le p hM hpM
  choose r hr C3 hC3 using fun i => hw_general (ZMod p) (g i).FF
  set A := (LinearMap.charpoly Φ).roots with hA
  set B : Multiset ℂ := (Finset.univ : Finset ι).val.bind fun i => rootsMul (r i) p with hB
  have hpB : (p : ℂ) ∈ B := Multiset.mem_bind.2 ⟨i0, Finset.mem_univ _, mem_rootsMul_self _ (hr i0) _⟩
  -- the power sums
  have hpow : ∀ m : ℕ, 1 ≤ m → ((A + B.erase p).map (· ^ m)).sum =
      LinearMap.trace ℂ _ (Φ ^ m) + (((∑ i, (if r i ∣ m then (r i : ℝ) * (p : ℝ) ^ m else 0)) : ℝ) : ℂ) -
        (((p : ℝ) ^ m : ℝ) : ℂ) := by
    intro m hm
    have hBs : (B.map (· ^ m)).sum = ((B.erase p).map (· ^ m)).sum + (p : ℂ) ^ m := by
      conv_lhs => rw [← Multiset.cons_erase hpB]
      rw [Multiset.map_cons, Multiset.sum_cons, add_comm]
    have hBs' : (B.map (· ^ m)).sum = (((∑ i, (if r i ∣ m then (r i : ℝ) * (p : ℝ) ^ m else 0)) : ℝ) : ℂ) := by
      rw [hB, Multiset.map_bind, Multiset.sum_bind]
      change ∑ i, ((rootsMul (r i) p).map (· ^ m)).sum = _
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [rootsMul, powerSum_rootsMul (r i) (hr i) p m]
      split_ifs <;> push_cast <;> ring
    rw [Multiset.map_add, Multiset.sum_add, trace_pow_eq_sum_roots Φ m hm, ← hBs', hBs]
    push_cast
    ring
  -- the pointwise bound
  have hbd : ∀ m : ℕ, 1 ≤ m → ‖((A + B.erase p).map (· ^ m)).sum‖ ≤
      C1 * (1 + (m : ℝ)) + (C2 : ℝ) * 1 + (∑ i, C3 i) * Real.sqrt p ^ m + 1 := by
    intro m hm
    letI : Fintype (GaloisField p m) := Fintype.ofFinite _
    have hcard : Fintype.card (GaloisField p m) = p ^ m := by
      rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p m (by omega)
    have h1 := hC1 m hm (GaloisField p m) hcard
    have hY : pairSumU (GaloisField p m) M 2 (p ^ m) = (Nat.card (RPLib.TateNF.Y1 (GaloisField p m) M) : ℤ) := by
      rw [← hcard]; exact pairSumU_two_eq M
    rw [hY, if_pos rfl, Nat.sub_self, zero_mul, pow_zero, mul_one] at h1
    have h1x : ‖LinearMap.trace ℂ _ (Φ ^ m) + (((Nat.card (RPLib.TateNF.Y1 (GaloisField p m) M) : ℤ)) : ℂ) -
        (1 + ((((p : ℝ) ^ m : ℝ)) : ℂ))‖ ≤ C1 * (1 + (m : ℝ)) := by
      push_cast; exact h1
    have h2 : |(((Nat.card (RPLib.TateNF.Y1 (GaloisField p m) M) : ℤ)) : ℝ) -
        ∑ i, (numPoints (ZMod p) (g i).FF m : ℝ)| ≤ (C2 : ℝ) := by
      have := hC2 m hm
      exact_mod_cast this
    have h3 : ∀ i, |(numPoints (ZMod p) (g i).FF m : ℝ) - (if r i ∣ m then (r i : ℝ) * (p : ℝ) ^ m else 0)| ≤
        C3 i * Real.sqrt p ^ m := by
      intro i
      have := hC3 i (GaloisField p m)
      rwa [GaloisField.finrank p (by omega : m ≠ 0), ZMod.card p] at this
    have key := norm_combine (LinearMap.trace ℂ _ (Φ ^ m)) _ (fun i => numPoints (ZMod p) (g i).FF m)
      (fun i => if r i ∣ m then (r i : ℝ) * (p : ℝ) ^ m else 0) (fun i => C3 i * Real.sqrt p ^ m)
      ((p : ℝ) ^ m) _ _ h1x h2 h3
    rw [hpow m hm, mul_one, Finset.sum_mul]
    linarith
  -- the growth bound
  have hR : (fun m : ℕ => C1 * (1 + (m : ℝ)) + (C2 : ℝ) * 1 + (∑ i, C3 i) * Real.sqrt p ^ m + 1) =O[atTop]
      (fun m => Real.sqrt p ^ m) :=
    ((((one_add_isBigO _ hsp).const_mul_left C1).add ((one_isBigO _ hsp).const_mul_left (C2 : ℝ))).add
      ((isBigO_refl _ _).const_mul_left (∑ i, C3 i))).add (one_isBigO _ hsp)
  have hO : (fun m : ℕ => ((A + B.erase p).map (· ^ m)).sum) =O[atTop] (fun m => Real.sqrt p ^ m) := by
    refine IsBigO.trans ?_ hR
    refine IsBigO.of_bound 1 (eventually_atTop.2 ⟨1, fun m hm => ?_⟩)
    rw [one_mul, Real.norm_eq_abs]
    exact (hbd m hm).trans (le_abs_self _)
  have := ExpSum.multiset_norm_le_of_powerSum_isBigO (A + B.erase p) (Real.sqrt_nonneg _) hO α
    (Multiset.mem_add.2 (Or.inl (mem_roots_of_hasEigenvalue Φ α hα)))
  simpa using this

end RamanujanPetersson.S3.Wt2


