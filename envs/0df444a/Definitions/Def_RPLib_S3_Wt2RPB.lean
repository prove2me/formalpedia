-- Prove2me | Definitions.Def_RPLib_S3_Wt2RPB
-- name    : RPLib_S3_Wt2RPB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:39:56.632583+00:00
-- url     : https://prove2.me/theorems/682cb926-a175-47c7-b5c2-bb42dc7501aa
-- title:
--   Weight-two Ramanujan-Petersson library: the linear algebra and counting pieces of the weight-2 assembly
-- statement:
--   The linear algebra and counting pieces of the weight-2 assembly.
--
--   * `matrix_trace_pow_eq_sum_roots`, `trace_pow_eq_sum_roots`: `tr(f^m) = Σ_{α ∈ roots(charpoly f)} α^m` over `ℂ`.
--   * `mem_roots_of_hasEigenvalue`: an eigenvalue is a root of the characteristic polynomial.
--   * `sum_rootsOfUnity_pow`, `powerSum_rootsMul`: `Σ_{j<r} (ζ_r^j x)^m = [r ∣ m] · r · x^m`.
--   * `pairSumU_two_eq`: at weight 2, `pairSumU F M 2 q = #Y₁(M)(F)` (Hasse puts every trace in `[-2q, 2q]`).
--   * `norm_combine`: the triangle-inequality bookkeeping of the assembly.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211

import Mathlib
import Definitions.Def_RPLib_S3_MatchingF
import Definitions.Def_RPLib_S4_CP4aNewton

/-!
# S3-Wt2RP, O3 part B: the linear algebra and counting pieces of the weight-2 assembly

* `matrix_trace_pow_eq_sum_roots`, `trace_pow_eq_sum_roots`: `tr(f^m) = Σ_{α ∈ roots(charpoly f)} α^m` over `ℂ`.
* `mem_roots_of_hasEigenvalue`: an eigenvalue is a root of the characteristic polynomial.
* `sum_rootsOfUnity_pow`, `powerSum_rootsMul`: `Σ_{j<r} (ζ_r^j x)^m = [r ∣ m] · r · x^m`.
* `pairSumU_two_eq`: at weight 2, `pairSumU F M 2 q = #Y₁(M)(F)` (Hasse puts every trace in `[-2q, 2q]`).
* `norm_combine`: the triangle-inequality bookkeeping of the assembly.
-/

set_option autoImplicit false

open Polynomial Complex

namespace RamanujanPetersson.S3.Wt2

/-! ### Traces of powers -/

theorem multiset_prod_toList {β : Type*} (s : Multiset ℂ) (g : ℂ → β) [CommMonoid β] :
    (s.toList.map g).prod = (s.map g).prod := by
  conv_rhs => rw [← Multiset.coe_toList s]
  rw [Multiset.map_coe, Multiset.prod_coe]

theorem multiset_sum_toList (s : Multiset ℂ) (g : ℂ → ℂ) :
    (s.toList.map g).sum = (s.map g).sum := by
  conv_rhs => rw [← Multiset.coe_toList s]
  rw [Multiset.map_coe, Multiset.sum_coe]

theorem matrix_trace_pow_eq_sum_roots {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (m : ℕ)
    (hm : 1 ≤ m) : (A ^ m).trace = (A.charpoly.roots.map (· ^ m)).sum := by
  set l := A.charpoly.roots.toList with hl
  set D : Matrix (Fin l.length) (Fin l.length) ℂ := Matrix.diagonal fun i => l[i.1] with hD
  have hchar : A.charpoly = D.charpoly := by
    rw [hD, Matrix.charpoly_diagonal,
      show (∏ i : Fin l.length, (X - C (l[i.1]))) = (l.map fun a => X - C a).prod from
        Fin.prod_univ_fun_getElem l (fun a => X - C a), hl, multiset_prod_toList,
      prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic A) IsAlgClosed.card_roots_eq_natDegree]
  have hrev : A.charpolyRev = D.charpolyRev := by
    rw [← Matrix.reverse_charpoly, ← Matrix.reverse_charpoly, hchar]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [CP4a.trace_pow_eq_of_charpolyRev_eq A D hrev k, hD, Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp only [Pi.pow_apply]
  rw [show (∑ i : Fin l.length, l[i.1] ^ (k + 1)) = (l.map fun a => a ^ (k + 1)).sum from
    Fin.sum_univ_fun_getElem l (fun a => a ^ (k + 1)), hl, multiset_sum_toList]

theorem trace_pow_eq_sum_roots {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (m : ℕ) (hm : 1 ≤ m) :
    LinearMap.trace ℂ V (f ^ m) = ((LinearMap.charpoly f).roots.map (· ^ m)).sum := by
  classical
  let b := Module.Free.chooseBasis ℂ V
  rw [LinearMap.trace_eq_matrix_trace ℂ b, ← LinearMap.toMatrix_pow, matrix_trace_pow_eq_sum_roots _ m hm,
    LinearMap.charpoly_toMatrix]

theorem mem_roots_of_hasEigenvalue {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (α : ℂ) (h : f.HasEigenvalue α) : α ∈ (LinearMap.charpoly f).roots :=
  (Polynomial.mem_roots (LinearMap.charpoly_monic f).ne_zero).2
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly f α).1 h)

/-! ### Roots of unity -/

/-- `ζ_r = exp(2πi/r)`. -/
noncomputable def zeta (r : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / r)

theorem sum_rootsOfUnity_pow (r : ℕ) (hr : 1 ≤ r) (m : ℕ) :
    ∑ j ∈ Finset.range r, (zeta r ^ j) ^ m = if r ∣ m then (r : ℂ) else 0 := by
  have hζ : IsPrimitiveRoot (zeta r) r := Complex.isPrimitiveRoot_exp r (by omega)
  have hsw : ∀ j : ℕ, (zeta r ^ j) ^ m = (zeta r ^ m) ^ j := fun j => by
    rw [← pow_mul, ← pow_mul, mul_comm]
  simp_rw [hsw]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd m).2 h]
    simp
  · have hne : zeta r ^ m - 1 ≠ 0 := sub_ne_zero.2 fun h1 => h ((hζ.pow_eq_one_iff_dvd m).1 h1)
    have hpow : (zeta r ^ m) ^ r = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have := geom_sum_mul (zeta r ^ m) r
    rw [hpow, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right hne

theorem powerSum_rootsMul (r : ℕ) (hr : 1 ≤ r) (x : ℂ) (m : ℕ) :
    ((((Multiset.range r).map fun j => zeta r ^ j * x)).map (· ^ m)).sum =
      (if r ∣ m then (r : ℂ) else 0) * x ^ m := by
  rw [Multiset.map_map]
  change ∑ j ∈ Finset.range r, (zeta r ^ j * x) ^ m = _
  simp_rw [mul_pow]
  rw [← Finset.sum_mul, sum_rootsOfUnity_pow r hr m]

/-! ### Weight 2: the `U`-sum is the point count -/

theorem pairSumU_two_eq {F : Type} [Field F] [Fintype F] [DecidableEq F] (M : ℕ) :
    pairSumU F M 2 (Fintype.card F) = (Nat.card (RPLib.TateNF.Y1 F M) : ℤ) := by
  classical
  unfold pairSumU
  have hU : ∀ t q : ℤ, chebU (2 - 2) t q = 1 := fun _ _ => rfl
  rw [Finset.sum_congr rfl fun t _ => by rw [hU, mul_one]]
  rw [← Nat.cast_sum]
  congr 1
  unfold pairCount
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hq : (1 : ℤ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  symm
  refine (Finset.card_eq_sum_card_fiberwise (f := fun bc : F × F => RPLib.EllFq.trace (RPLib.TateNF.tate bc.1 bc.2))
    (t := Finset.Icc (-(2 * (Fintype.card F : ℤ))) (2 * Fintype.card F)) ?_).trans
    (Finset.sum_congr rfl fun t _ => ?_)
  · intro bc hbc
    rw [Finset.mem_coe, Finset.mem_filter] at hbc
    have h := Match.trace_tate_sq_le (F := F) hbc.2.1
    have h2 : RPLib.EllFq.trace (RPLib.TateNF.tate bc.1 bc.2) ^ 2 ≤ (2 * (Fintype.card F : ℤ)) ^ 2 := by nlinarith
    exact Finset.mem_Icc.2 (abs_le_of_sq_le_sq' h2 (by positivity))
  · rw [Finset.filter_filter]

/-! ### Bookkeeping -/

theorem norm_combine {ι : Type} [Fintype ι] (T : ℂ) (Y : ℤ) (N : ι → ℕ) (c e : ι → ℝ) (x a b : ℝ)
    (h1 : ‖T + (Y : ℂ) - (1 + (x : ℂ))‖ ≤ a) (h2 : |(Y : ℝ) - ∑ i, (N i : ℝ)| ≤ b)
    (h3 : ∀ i, |(N i : ℝ) - c i| ≤ e i) :
    ‖T + ((∑ i, c i : ℝ) : ℂ) - (x : ℂ)‖ ≤ a + b + ∑ i, e i + 1 := by
  have hid : T + ((∑ i, c i : ℝ) : ℂ) - (x : ℂ) = (T + (Y : ℂ) - (1 + (x : ℂ))) -
      ((((Y : ℝ) - ∑ i, (N i : ℝ)) : ℝ) : ℂ) - ((∑ i, ((N i : ℝ) - c i) : ℝ) : ℂ) + 1 := by
    rw [Finset.sum_sub_distrib]
    push_cast
    ring
  rw [hid]
  refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
    (add_le_add h1 ?_)) ?_)) (le_of_eq norm_one))
  · rw [Complex.norm_real, Real.norm_eq_abs]; exact h2
  · rw [Complex.norm_real, Real.norm_eq_abs]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => h3 i)

end RamanujanPetersson.S3.Wt2


