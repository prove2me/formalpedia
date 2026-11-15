-- Prove2me | Definitions.Def_RPLib_S3_X1CountA
-- name    : RPLib_S3_X1CountA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:19:54.232172+00:00
-- url     : https://prove2.me/theorems/980ea4ba-daa7-46ba-a810-3f28e36da0b4
-- title:
--   Weight-two Ramanujan-Petersson library: the polynomial description of `Y₁(M)` and existence of points
-- statement:
--   The polynomial description of `Y₁(M)` and existence of points.
--
--   * `polyG M = polyF M`, `polyH M = X₀ · Δ(X₀,X₁) · ∏_{j=2}^{M/2} polyN j` over `ℤ`;
--     `mem_Y1_iff_poly`: `(b,c) ∈ Y₁(M)(F) ↔ G(b,c) = 0 ∧ H(b,c) ≠ 0` (`M ≥ 4`, any field).
--   * `exists_mem_Y1`: for `p` prime, `n ≥ 4`, `p ∤ n`, `Y₁(n)` has a point over `AlgebraicClosure (ZMod p)`.
--   * `polyG_map_ne_zero`: `G_M mod p ≠ 0`; `exists_good_point`: a point with `G = 0`, `H ≠ 0` over a field of
--     characteristic `p` (so some irreducible factor of `G_M mod p` does not divide `H_M mod p`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S2_TateNFB
import Definitions.Def_RPLib_S2_Torsion

/-!
# X1Count part A: the polynomial description of `Y₁(M)` and existence of points (unit S3-X1Count)

* `polyG M = polyF M`, `polyH M = X₀ · Δ(X₀,X₁) · ∏_{j=2}^{M/2} polyN j` over `ℤ`;
  `mem_Y1_iff_poly`: `(b,c) ∈ Y₁(M)(F) ↔ G(b,c) = 0 ∧ H(b,c) ≠ 0` (`M ≥ 4`, any field).
* `exists_mem_Y1`: for `p` prime, `n ≥ 4`, `p ∤ n`, `Y₁(n)` has a point over `AlgebraicClosure (ZMod p)`.
* `polyG_map_ne_zero`: `G_M mod p ≠ 0`; `exists_good_point`: a point with `G = 0`, `H ≠ 0` over a field of
  characteristic `p` (so some irreducible factor of `G_M mod p` does not divide `H_M mod p`).
-/

set_option autoImplicit false

open MvPolynomial RPLib.TateNF RPLib.Torsion WeierstrassCurve

namespace RamanujanPetersson.X1Count

/-- The order polynomial `G_M = F_M(b,c)`. -/
noncomputable def polyG (M : ℕ) : MvPolynomial (Fin 2) ℤ := polyF M

/-- The discriminant `Δ(b,c)` as a polynomial. -/
noncomputable def polyDisc : MvPolynomial (Fin 2) ℤ := tateDisc (X 0) (X 1)

/-- The excluded locus `H_M = b · Δ(b,c) · ∏_{j=2}^{M/2} N_j(b,c)`. -/
noncomputable def polyH (M : ℕ) : MvPolynomial (Fin 2) ℤ :=
  X 0 * polyDisc * ∏ j ∈ Finset.Icc 2 (M / 2), polyN j

section Eval

variable {F : Type*} [Field F]

lemma aeval_polyDisc (b c : F) : aeval ![b, c] polyDisc = tateDisc b c := by
  simp [polyDisc, tateDisc]

lemma aeval_polyG (b c : F) (M : ℕ) : aeval ![b, c] (polyG M) = tateF b c M := aeval_polyF b c M

lemma aeval_polyH (b c : F) (M : ℕ) :
    aeval ![b, c] (polyH M) = b * tateDisc b c * ∏ j ∈ Finset.Icc 2 (M / 2), tateN b c j := by
  simp [polyH, aeval_polyDisc, aeval_polyN]

lemma aeval_polyH_ne_zero_iff (b c : F) (M : ℕ) :
    aeval ![b, c] (polyH M) ≠ 0 ↔
      tateDisc b c ≠ 0 ∧ ∀ j, 2 ≤ j → j ≤ M / 2 → tateN b c j ≠ 0 := by
  rw [aeval_polyH]
  constructor
  · intro h
    have h1 := left_ne_zero_of_mul h
    have h2 := right_ne_zero_of_mul h
    refine ⟨right_ne_zero_of_mul h1, fun j hj1 hj2 => ?_⟩
    exact (Finset.prod_ne_zero_iff.mp h2) j (Finset.mem_Icc.mpr ⟨hj1, hj2⟩)
  · rintro ⟨hD, hN⟩
    refine mul_ne_zero (mul_ne_zero (ne_zero_of_tateDisc_ne_zero hD) hD) ?_
    exact Finset.prod_ne_zero_iff.mpr fun j hj => hN j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2

variable [DecidableEq F]

/-- **Polynomial description of `Y₁(M)`.** -/
theorem mem_Y1_iff_poly {M : ℕ} (hM : 4 ≤ M) (b c : F) :
    (b, c) ∈ Y1 F M ↔ aeval ![b, c] (polyG M) = 0 ∧ aeval ![b, c] (polyH M) ≠ 0 := by
  rw [aeval_polyH_ne_zero_iff, aeval_polyG]
  show tateDisc b c ≠ 0 ∧ HasExactOrder M b c ↔ _
  rw [hasExactOrder_iff_tateF hM]
  constructor
  · rintro ⟨hD, -, hN, hF⟩; exact ⟨hF, hD, hN⟩
  · rintro ⟨hF, hD, hN⟩; exact ⟨hD, ne_zero_of_tateDisc_ne_zero hD, hN, hF⟩

end Eval

section Exists

variable {K : Type*} [Field K] [DecidableEq K] [IsSepClosed K]

/-- A Tate curve with nonzero discriminant over any field. -/
lemma exists_tate_ne (K : Type*) [Field K] : ∃ b : K, tateDisc b 0 ≠ 0 := by
  by_cases h17 : (17 : K) = 0
  · refine ⟨-1, ?_⟩
    have h2 : (2 : K) ≠ 0 := by
      intro h2
      apply one_ne_zero (α := K)
      linear_combination h17 - 8 * h2
    have : tateDisc (-1 : K) 0 = 2 := by
      simp only [tateDisc]; linear_combination -h17
    rw [this]; exact h2
  · refine ⟨1, ?_⟩
    have : tateDisc (1 : K) 0 = 17 := by simp only [tateDisc]; norm_num
    rw [this]; exact h17

/-- Over a separably closed field with `n ≠ 0`, `Y₁(n)` has a point (`n ≥ 4`). -/
theorem exists_mem_Y1_of_isSepClosed {n : ℕ} (hn : 4 ≤ n) (hnK : (n : K) ≠ 0) :
    ∃ bc : K × K, bc ∈ Y1 K n := by
  obtain ⟨b0, hb0⟩ := exists_tate_ne K
  set W : WeierstrassCurve K := tate b0 0
  have hΔ : W.Δ ≠ 0 := by rw [tate_Δ]; exact hb0
  have : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  obtain ⟨e⟩ := tors_equiv (W := W) n hnK
  set Q : tors W n := e.symm (1, 0)
  have hQ : addOrderOf (Q : W.toAffine.Point) = n := by
    rw [AddSubgroup.addOrderOf_coe, AddEquiv.addOrderOf_eq, Prod.addOrderOf, ZMod.addOrderOf_one,
      addOrderOf_zero, Nat.lcm_one_right]
  obtain ⟨⟨bc, hbc⟩, -⟩ := y1ToClass_surjective (F := K) hn
    (Quotient.mk (pairSetoid K n) ⟨⟨W, Q⟩, hΔ, hQ⟩)
  exact ⟨bc, hbc⟩

/-- `Y₁(n)` has a point over `AlgebraicClosure (ZMod p)` when `p ∤ n`, `n ≥ 4`. -/
theorem exists_mem_Y1 (p : ℕ) [Fact p.Prime] [DecidableEq (AlgebraicClosure (ZMod p))] {n : ℕ} (hn : 4 ≤ n) (hpn : ¬ p ∣ n) :
    ∃ bc : AlgebraicClosure (ZMod p) × AlgebraicClosure (ZMod p),
      bc ∈ Y1 (AlgebraicClosure (ZMod p)) n := by
  have hnK : (n : AlgebraicClosure (ZMod p)) ≠ 0 := by
    rw [← map_natCast (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))), Ne,
      map_eq_zero_iff _ (algebraMap (ZMod p) _).injective, ZMod.natCast_eq_zero_iff]
    exact hpn
  exact exists_mem_Y1_of_isSepClosed hn hnK

end Exists

section ModP

variable (p : ℕ) [Fact p.Prime]

/-- The reductions mod `p`. -/
noncomputable def polyGp (M : ℕ) : MvPolynomial (Fin 2) (ZMod p) := map (Int.castRingHom (ZMod p)) (polyG M)

noncomputable def polyHp (M : ℕ) : MvPolynomial (Fin 2) (ZMod p) := map (Int.castRingHom (ZMod p)) (polyH M)

lemma aeval_map_eq {L : Type*} [Field L] [Algebra (ZMod p) L] (P : MvPolynomial (Fin 2) ℤ) (v : Fin 2 → L) :
    aeval v (map (Int.castRingHom (ZMod p)) P) = aeval v P := by
  rw [← algebraMap_int_eq, aeval_map_algebraMap]

/-- Points of `Y₁(M)` over any `ZMod p`-algebra field are the points of `{G_p = 0, H_p ≠ 0}`. -/
theorem mem_Y1_iff_polyp {L : Type*} [Field L] [DecidableEq L] [Algebra (ZMod p) L] {M : ℕ} (hM : 4 ≤ M)
    (b c : L) :
    (b, c) ∈ Y1 L M ↔ aeval ![b, c] (polyGp p M) = 0 ∧ aeval ![b, c] (polyHp p M) ≠ 0 := by
  rw [polyGp, polyHp, aeval_map_eq, aeval_map_eq]; exact mem_Y1_iff_poly hM b c

/-- **`G_M mod p ≠ 0`** (`M ≥ 4`; uses a point of order `M + 1` or `M + 2`). -/
theorem polyGp_ne_zero {M : ℕ} (hM : 4 ≤ M) : polyGp p M ≠ 0 := by
  classical
  have hp := (Fact.out : p.Prime)
  obtain ⟨M', hM'1, hM'2, hpM'⟩ : ∃ M', M < M' ∧ M' ≤ M + 2 ∧ ¬ p ∣ M' := by
    by_cases h1 : p ∣ M + 1
    · refine ⟨M + 2, by omega, le_rfl, fun h2 => hp.one_lt.ne' ?_⟩
      have := (Nat.dvd_sub h2 h1)
      rw [show M + 2 - (M + 1) = 1 by omega] at this
      exact Nat.dvd_one.mp this
    · exact ⟨M + 1, by omega, by omega, h1⟩
  obtain ⟨⟨b, c⟩, hbc⟩ := exists_mem_Y1 p (n := M') (by omega) hpM'
  intro h0
  have hD : tateDisc b c ≠ 0 := hbc.1
  have hb : b ≠ 0 := ne_zero_of_tateDisc_ne_zero hD
  have hord : addOrderOf (tatePt b c) = M' := (hasExactOrder_iff (by omega) b c).mp hbc.2
  have hN : ∀ j, 2 ≤ j → j ≤ M / 2 → tateN b c j ≠ 0 :=
    (nsmul_ne_zero_iff_tateN hb (M / 2)).mp fun j hj1 hj2 =>
      nsmul_ne_zero_of_lt_addOrderOf (by omega) (by omega)
  have hG : aeval ![b, c] (polyGp p M) = 0 := by rw [h0, map_zero]
  have hH : aeval ![b, c] (polyHp p M) ≠ 0 := by
    rw [polyHp, aeval_map_eq]; exact (aeval_polyH_ne_zero_iff b c M).mpr ⟨hD, hN⟩
  have hY : (b, c) ∈ Y1 (AlgebraicClosure (ZMod p)) M := (mem_Y1_iff_polyp p hM b c).mpr ⟨hG, hH⟩
  have := (hasExactOrder_iff (by omega) b c).mp hY.2
  omega

/-- A point of `{G_p = 0, H_p ≠ 0}` over a field of characteristic `p` (`M ≥ 4`, `p ∤ M`). -/
theorem exists_good_point {M : ℕ} (hM : 4 ≤ M) (hpM : ¬ p ∣ M) :
    ∃ v : Fin 2 → AlgebraicClosure (ZMod p),
      aeval v (polyGp p M) = 0 ∧ aeval v (polyHp p M) ≠ 0 := by
  classical
  obtain ⟨⟨b, c⟩, hbc⟩ := exists_mem_Y1 p hM hpM
  exact ⟨![b, c], (mem_Y1_iff_polyp p hM b c).mp hbc⟩

end ModP

end RamanujanPetersson.X1Count


