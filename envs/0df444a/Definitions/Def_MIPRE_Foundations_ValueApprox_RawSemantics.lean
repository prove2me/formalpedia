-- Prove2me | Definitions.Def_MIPRE_Foundations_ValueApprox_RawSemantics
-- name    : MIPRE_Foundations_ValueApprox_RawSemantics
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:14:29.196709+00:00
-- url     : https://prove2.me/theorems/52cabd6b-edde-476b-87a1-8f0b909b06c7
-- title:
--   The certificate check is correct: raw candidates denote valid exact strategies with the claimed value
-- statement:
--   Two definitions and the correctness theorem of the exact check `Check g p q r` of raw candidates (bundle `MIPRE_Foundations_ValueApprox_RawStrategy`) against the semantics of exact strategies (bundle `MIPRE_Foundations_ValueApprox_Strategy`), for a game description `g : GameData` and naturals $p, q$.
--
--   **Denotations.** `MIPRE.ValueApprox.mat M d k` is the complex $d \times d$ matrix (`Matrix (Fin d) (Fin d) ℂ`) with entries $M_{ij}/k$, for a list matrix $M$ and a denominator $k$; `MIPRE.ValueApprox.vec dA dB v k` is the state on `Fin dA × Fin dB` with $(i,j) \mapsto v(i\,d_B + j)/k$.
--
--   The embedded lemmas read each clause of `Check` as the corresponding statement about the denotation, under $k \ne 0$: `isHermRaw_iff`, `isIdemRaw_iff`, `isSumRaw_iff`, `isPVMRaw_iff` (the `mat`s form an `IsPVM`); `vec_ne_zero_iff` (the state is nonzero iff some numerator at a row-major index below $d_A d_B$ is); `dotProduct_vec_self`, `re_dotProduct_vec_self` ($\mathrm{Re}\langle v, v\rangle = \mathrm{normRaw}/k^{2}$), `dotProduct_kronecker_vec`, `re_dotProduct_kronecker_vec` ($\mathrm{Re}\langle v,(\mathrm{mat}\,A \otimes \mathrm{mat}\,B)v\rangle = \mathrm{Re}\,\mathrm{quadRaw}/k^{4}$), `normRaw_pos`; `GameData.one_le_W`, `GameData.game_μ_eq` ($\mu = \mathrm{wt}/W$), `GameData.game_D_eq` ($D = \mathrm{Draw}$); `toInt_numer`, `interp_bornValue`, `interp_value` (the value of `interp r` is $\mathrm{numer}/(W\,k^{2}\,\mathrm{normRaw})$), `valueTest_iff`; and four auxiliary identities. The conclusion is `MIPRE.ValueApprox.check_iff_interp`:
--   $$\mathrm{Check}(g,p,q,r) \iff (r.\mathrm{interp}\ g.n_X\ g.n_A).\mathrm{IsValid}\ \wedge\ \frac{p}{q} < (r.\mathrm{interp}\ g.n_X\ g.n_A).\mathrm{value}(g.\mathrm{game}).$$
--   With the soundness and density of exact strategies this yields, in the next bundle, `exists_check_iff`: some raw candidate passes the check iff $p/q < \mathrm{val}^{*}(G_g)$, the semantic content of the semidecision procedure of `lem:value-lower-approx`.
--
--   **Formalization Note**. `interp r` unfolds to `mat` and `vec` on the numerator matrices and the state, so every lemma is stated about `mat` and `vec` and transferred; $p/q$ is real division with Lean's convention $p/0 = 0$, matched by the $q = 0$ clause of `ValueTest`; the hypothesis $k \ne 0$ of the clause lemmas is supplied by the clause $0 < k$ of `Check`, so `check_iff_interp` has no side condition. `mat` and `vec` are `noncomputable`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/ValueApprox/RawSemantics.lean; blueprint lem:value-lower-approx

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/ValueApprox/RawSemantics.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawInt
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_ValueApprox
import Definitions.Def_MIPRE_Foundations_ValueApprox_Cayley
import Definitions.Def_MIPRE_Foundations_ValueApprox_Projective
import Definitions.Def_MIPRE_Foundations_ValueApprox_Gaussian
import Definitions.Def_MIPRE_Foundations_ValueApprox_Norms
import Definitions.Def_MIPRE_Foundations_ValueApprox_Dense
import Definitions.Def_MIPRE_Foundations_ValueApprox_Strategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawStrategy

/-!
# The certificate check is correct

`MIPRE.ValueApprox.check_iff_interp`: `Check g p q r` holds iff the exact strategy `interp r`
denoted by the raw candidate is valid for the game `g.game` and has value greater than `p / q`.
Together with the soundness and density of exact strategies
(`MIPRE.Foundations.ValueApprox.Strategy`) this gives `exists_check_iff`: some raw candidate passes
the check iff `p / q < val*(G_g)` — the semantic content of the semidecision procedure of
`lem:value-lower-approx`.

The proof reads each clause of `Check` as the corresponding statement about `interp r`, with
`k ≠ 0`: the Hermitian, idempotence and completeness tests as the projective-measurement axioms of
`mat M d k = (M i j / k)`, the state test as `u ≠ 0`, and the value test as `p / q < value`, the
value being `numer / (W · k² · ⟨v, v⟩)`. The converse direction of `exists_check_iff` needs a raw
candidate denoting a given valid Gaussian-rational exact strategy, which
`exists_rawStrategy_interp_eq` builds from a common denominator of its entries.
-/

namespace MIPRE.ValueApprox

open HaltingGameValue (GameData)
open Matrix WithLp
open scoped Kronecker ComplexOrder

/-! ## Sums -/

theorem toC_gsum_fin (n : ℕ) (f : ℕ → GInt) : (gsum n f).toC = ∑ i : Fin n, (f i).toC := by
  rw [toC_gsum, Finset.sum_range]

theorem toInt_psum_fin (n : ℕ) (f : ℕ → PInt) : (psum n f).toInt = ∑ i : Fin n, (f i).toInt := by
  rw [toInt_psum, Finset.sum_range]

/-! ## Matrices -/

/-- The `d × d` complex matrix with entries `M i j / k`. -/
noncomputable def mat (M : GMat) (d k : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => (entry M i j).toC / k

variable {M : GMat} {d k : ℕ}

theorem isHermRaw_iff (hk : k ≠ 0) : IsHermRaw M d ↔ (mat M d k)ᴴ = mat M d k := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  constructor
  · intro h
    ext i j
    have := GInt.eq'_iff.mp (h i i.2 j j.2)
    rw [conjTranspose_apply, mat, Matrix.of_apply, Matrix.of_apply, star_div₀, star_natCast,
      this, GInt.toC_conj]
  · intro h i hi j hj
    have := congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩
    rw [conjTranspose_apply, mat, Matrix.of_apply, Matrix.of_apply, star_div₀, star_natCast,
      div_left_inj' hk'] at this
    rw [GInt.eq'_iff, GInt.toC_conj, this]

/-- `a / k² = e / k ↔ a = k e` for `k ≠ 0`. -/
theorem div_sq_eq_div_iff {a e k : ℂ} (hk : k ≠ 0) : a / k ^ 2 = e / k ↔ a = k * e := by
  rw [div_eq_iff (pow_ne_zero 2 hk)]
  constructor
  · intro h
    rw [h]
    field_simp
  · intro h
    rw [h]
    field_simp

theorem mat_mul_mat_apply (i j : Fin d) :
    (mat M d k * mat M d k) i j =
      (∑ l : Fin d, (entry M i l).toC * (entry M l j).toC) / (k : ℂ) ^ 2 := by
  simp only [Matrix.mul_apply, mat, Matrix.of_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem isIdemRaw_iff (hk : k ≠ 0) : IsIdemRaw M d k ↔ mat M d k * mat M d k = mat M d k := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have key : ∀ i j : Fin d,
      GInt.Eq' (gsum d fun l => GInt.mul (entry M i l) (entry M l j))
        (GInt.mul (GInt.ofNat k) (entry M i j)) ↔
      (mat M d k * mat M d k) i j = mat M d k i j := by
    intro i j
    rw [GInt.eq'_iff, toC_gsum_fin, GInt.toC_mul, GInt.toC_ofNat, mat_mul_mat_apply]
    simp only [GInt.toC_mul, mat, Matrix.of_apply]
    exact (div_sq_eq_div_iff hk').symm
  constructor
  · intro h
    ext i j
    exact (key i j).mp (h i i.2 j j.2)
  · intro h i hi j hj
    exact (key ⟨i, hi⟩ ⟨j, hj⟩).mpr (congrFun (congrFun h _) _)

theorem isSumRaw_iff {Ms : List GMat} {nA : ℕ} (hk : k ≠ 0) :
    IsSumRaw Ms nA d k ↔ ∑ a : Fin (nA + 1), mat (Ms.getD a []) d k = 1 := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have key : ∀ i j : Fin d,
      GInt.Eq' (gsum (nA + 1) fun a => entry (Ms.getD a []) i j)
        (if (i : ℕ) = j then GInt.ofNat k else GInt.zero) ↔
      (∑ a : Fin (nA + 1), mat (Ms.getD a []) d k) i j = (1 : Matrix (Fin d) (Fin d) ℂ) i j := by
    intro i j
    rw [GInt.eq'_iff, toC_gsum_fin, Matrix.sum_apply, Matrix.one_apply, apply_ite GInt.toC,
      GInt.toC_ofNat, GInt.toC_zero]
    simp only [mat, Matrix.of_apply, ← Finset.sum_div, Fin.ext_iff]
    rw [div_eq_iff hk']
    split_ifs <;> simp
  constructor
  · intro h
    ext i j
    exact (key i j).mp (h i i.2 j j.2)
  · intro h i hi j hj
    exact (key ⟨i, hi⟩ ⟨j, hj⟩).mpr (congrFun (congrFun h _) _)

theorem isPVMRaw_iff {Ms : List GMat} {nA : ℕ} (hk : k ≠ 0) :
    IsPVMRaw Ms nA d k ↔ IsPVM fun a : Fin (nA + 1) => mat (Ms.getD a []) d k := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun a => (isHermRaw_iff hk).mp (h₁ a a.2).1, fun a => (isIdemRaw_iff hk).mp (h₁ a a.2).2,
      (isSumRaw_iff hk).mp h₂⟩
  · intro h
    refine ⟨fun a ha => ⟨(isHermRaw_iff hk).mpr (h.conjTranspose_eq ⟨a, ha⟩),
      (isIdemRaw_iff hk).mpr (h.mul_self ⟨a, ha⟩)⟩, (isSumRaw_iff hk).mpr h.sum_eq_one⟩

/-! ## The state and the Born terms -/

section State

variable (dA dB : ℕ) (v : List GInt)

/-- The state denoted by `v`, `(i, j) ↦ v (i * dB + j) / k`. -/
noncomputable def vec (k : ℕ) : Fin dA × Fin dB → ℂ :=
  fun p => (vget v (p.1 * dB + p.2)).toC / k

theorem vec_ne_zero_iff (hk : k ≠ 0) :
    vec dA dB v k ≠ 0 ↔ ∃ i < dA, ∃ j < dB, ¬ GInt.Eq' (vget v (i * dB + j)) GInt.zero := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  simp only [GInt.eq'_iff, GInt.toC_zero, Ne, funext_iff, Pi.zero_apply, vec, div_eq_zero_iff, hk',
    or_false, Prod.forall, not_forall]
  constructor
  · rintro ⟨i, j, h⟩
    exact ⟨i, i.2, j, j.2, h⟩
  · rintro ⟨i, hi, j, hj, h⟩
    exact ⟨⟨i, hi⟩, ⟨j, hj⟩, h⟩

theorem dotProduct_vec_self (hk : k ≠ 0) :
    star (vec dA dB v k) ⬝ᵥ vec dA dB v k =
      ((gsum dA fun i => gsum dB fun j =>
        GInt.mul (GInt.conj (vget v (i * dB + j))) (vget v (i * dB + j))).toC) / (k : ℂ) ^ 2 := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, vec, toC_gsum_fin, GInt.toC_mul,
    GInt.toC_conj, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [star_div₀, star_natCast]
  field_simp

theorem re_dotProduct_vec_self (hk : k ≠ 0) :
    (star (vec dA dB v k) ⬝ᵥ vec dA dB v k).re = ((normRaw v dA dB).toInt : ℝ) / (k : ℝ) ^ 2 := by
  rw [dotProduct_vec_self dA dB v hk]
  have : ((k : ℂ) ^ 2) = (((k : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.div_ofReal_re, normRaw]
  congr 1
  rw [toInt_psum_fin, toC_gsum_fin, Complex.re_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [toInt_psum_fin, toC_gsum_fin, Complex.re_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [GInt.re_toC]

theorem dotProduct_kronecker_vec (A B : GMat) (hk : k ≠ 0) :
    star (vec dA dB v k) ⬝ᵥ ((mat A dA k ⊗ₖ mat B dB k) *ᵥ vec dA dB v k) =
      (quadRaw A B dA dB v).toC / (k : ℂ) ^ 4 := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  simp only [dotProduct, mulVec, kroneckerMap_apply, Fintype.sum_prod_type, Pi.star_apply, vec,
    mat, Matrix.of_apply, quadRaw, toC_gsum_fin, GInt.toC_mul, GInt.toC_conj, Finset.mul_sum,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun l _ => ?_
  rw [star_div₀, star_natCast]
  field_simp

theorem re_dotProduct_kronecker_vec (A B : GMat) (hk : k ≠ 0) :
    (star (vec dA dB v k) ⬝ᵥ ((mat A dA k ⊗ₖ mat B dB k) *ᵥ vec dA dB v k)).re =
      ((quadRaw A B dA dB v).1.toInt : ℝ) / (k : ℝ) ^ 4 := by
  rw [dotProduct_kronecker_vec dA dB v A B hk]
  have : ((k : ℂ) ^ 4) = (((k : ℝ) ^ 4 : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.div_ofReal_re, GInt.re_toC]

end State

/-! ## The interpretation -/

namespace RawStrategy

variable (nX nA : ℕ) (r : RawStrategy)

end RawStrategy

end MIPRE.ValueApprox

/-! ## The game -/

namespace HaltingGameValue.GameData

open MIPRE.ValueApprox

variable (g : GameData)

theorem one_le_W : 1 ≤ W g := by
  unfold W
  split_ifs with h
  · exact le_rfl
  · exact Nat.one_le_iff_ne_zero.mpr h

theorem game_μ_eq (x y : Fin (g.nX + 1)) : g.game.μ x y = (wt g x y : ℝ) / (W g : ℝ) := by
  rw [game_μ, wt, W]
  by_cases h : g.totalWeight = 0
  · have hx : x = 0 ↔ (x : ℕ) = 0 := by rw [Fin.ext_iff, Fin.val_zero]
    have hy : y = 0 ↔ (y : ℕ) = 0 := by rw [Fin.ext_iff, Fin.val_zero]
    simp only [h, if_true, hx, hy]
    split_ifs <;> simp
  · simp only [h, if_false]

theorem game_D_eq (x y : Fin (g.nX + 1)) (a b : Fin (g.nA + 1)) :
    g.game.D x y a b = Draw g x y a b := by
  rw [game_D, Draw]
  simp [Fin.ext_iff]

end HaltingGameValue.GameData

namespace MIPRE.ValueApprox

open HaltingGameValue (GameData)
open Matrix WithLp
open scoped Kronecker ComplexOrder

/-! ## The value -/

theorem toInt_numer (g : GameData) (r : RawStrategy) :
    ((numer g r).toInt : ℝ) = ∑ x : Fin (g.nX + 1), ∑ y : Fin (g.nX + 1), (wt g x y : ℝ) *
      ∑ a : Fin (g.nA + 1), ∑ b : Fin (g.nA + 1),
        (if Draw g x y a b then ((quadRaw (r.matA x a) (r.matB y b) r.dA r.dB r.v).1.toInt : ℝ)
          else 0) := by
  rw [numer, toInt_psum_fin, Int.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [toInt_psum_fin, Int.cast_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [PInt.toInt_mul, PInt.toInt_ofNat, Int.cast_mul, Int.cast_natCast, toInt_psum_fin,
    Int.cast_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [toInt_psum_fin, Int.cast_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

theorem interp_bornValue (g : GameData) (r : RawStrategy) (hk : r.k ≠ 0) :
    bornValue g.game (fun x a => mat (r.matA x a) r.dA r.k)
      (fun y b => mat (r.matB y b) r.dB r.k) (vec r.dA r.dB r.v r.k) =
      ((numer g r).toInt : ℝ) / ((W g : ℝ) * (r.k : ℝ) ^ 4) := by
  rw [bornValue, toInt_numer]
  simp only [re_dotProduct_kronecker_vec _ _ _ _ _ hk, g.game_μ_eq, g.game_D_eq]
  have hW : (W g : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp g.one_le_W)
  have hk' : (r.k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  rw [eq_div_iff (mul_ne_zero hW (pow_ne_zero 4 hk'))]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs
  · field_simp
  · simp

theorem interp_value (g : GameData) (r : RawStrategy) (hk : r.k ≠ 0) :
    (r.interp g.nX g.nA).value g.game =
      ((numer g r).toInt : ℝ) /
        ((W g : ℝ) * (r.k : ℝ) ^ 2 * ((normRaw r.v r.dA r.dB).toInt : ℝ)) := by
  have hk' : (r.k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  show bornValue g.game (fun x a => mat (r.matA x a) r.dA r.k)
      (fun y b => mat (r.matB y b) r.dB r.k) (vec r.dA r.dB r.v r.k) /
      (star (vec r.dA r.dB r.v r.k) ⬝ᵥ vec r.dA r.dB r.v r.k).re = _
  rw [interp_bornValue g r hk, re_dotProduct_vec_self _ _ _ hk, div_div_eq_mul_div,
    div_mul_eq_mul_div, div_div]
  have h : (W g : ℝ) * (r.k : ℝ) ^ 4 * ((normRaw r.v r.dA r.dB).toInt : ℝ) =
      (W g : ℝ) * (r.k : ℝ) ^ 2 * ((normRaw r.v r.dA r.dB).toInt : ℝ) * (r.k : ℝ) ^ 2 := by ring
  rw [h, mul_div_mul_right _ _ (pow_ne_zero 2 hk')]

theorem normRaw_pos {dA dB : ℕ} {v : List GInt} {k : ℕ} (hk : k ≠ 0) (hv : vec dA dB v k ≠ 0) :
    0 < (normRaw v dA dB).toInt := by
  have h := re_dotProduct_vec_self dA dB v hk
  have hpos : 0 < (star (vec dA dB v k) ⬝ᵥ vec dA dB v k).re := by
    have h1 : 0 ≤ star (vec dA dB v k) ⬝ᵥ vec dA dB v k := dotProduct_star_self_nonneg _
    have h2 : star (vec dA dB v k) ⬝ᵥ vec dA dB v k ≠ 0 := by
      rwa [Ne, dotProduct_star_self_eq_zero]
    rcases (Complex.nonneg_iff.mp h1) with ⟨hre, him⟩
    rcases hre.lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (Complex.ext heq.symm him.symm) h2
  rw [h] at hpos
  have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have := (div_pos_iff_of_pos_right hk2).mp hpos
  exact_mod_cast this

theorem valueTest_iff (g : GameData) (p q : ℕ) (r : RawStrategy) (hk : r.k ≠ 0)
    (hv : vec r.dA r.dB r.v r.k ≠ 0) :
    ValueTest g p q r ↔ (p : ℝ) / q < (r.interp g.nX g.nA).value g.game := by
  rw [interp_value g r hk]
  have hS := normRaw_pos hk hv
  have hS' : (0 : ℝ) < ((normRaw r.v r.dA r.dB).toInt : ℝ) := by exact_mod_cast hS
  have hW : (0 : ℝ) < (W g : ℝ) := by exact_mod_cast g.one_le_W
  have hk' : (0 : ℝ) < (r.k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hD : (0 : ℝ) < (W g : ℝ) * (r.k : ℝ) ^ 2 * ((normRaw r.v r.dA r.dB).toInt : ℝ) := by
    positivity
  rw [ValueTest]
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    simp only [true_and, ne_eq, not_true_eq_false, false_and, or_false, Nat.cast_zero, div_zero]
    rw [PInt.lt'_iff, PInt.toInt_zero, lt_div_iff₀ hD, zero_mul]
    exact_mod_cast Iff.rfl
  · have hq' : q ≠ 0 := hq.ne'
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    simp only [hq', false_and, ne_eq, not_false_eq_true, true_and, false_or]
    rw [PInt.lt'_iff, PInt.toInt_mul, PInt.toInt_mul, PInt.toInt_ofNat, PInt.toInt_ofNat,
      lt_div_iff₀ hD, div_mul_eq_mul_div, div_lt_iff₀ hqR]
    push_cast
    constructor
    · intro h
      have h' : ((p : ℝ) * (W g : ℝ) * ((r.k : ℝ) * (r.k : ℝ))) *
          ((normRaw r.v r.dA r.dB).toInt : ℝ) < (q : ℝ) * ((numer g r).toInt : ℝ) := by
        exact_mod_cast h
      linear_combination h'
    · intro h
      have h' : ((p : ℝ) * (W g : ℝ) * ((r.k : ℝ) * (r.k : ℝ))) *
          ((normRaw r.v r.dA r.dB).toInt : ℝ) < (q : ℝ) * ((numer g r).toInt : ℝ) := by
        linear_combination h
      exact_mod_cast h'

/-! ## The check is correct -/

theorem check_iff_interp (g : GameData) (p q : ℕ) (r : RawStrategy) :
    Check g p q r ↔
      (r.interp g.nX g.nA).IsValid ∧ (p : ℝ) / q < (r.interp g.nX g.nA).value g.game := by
  constructor
  · rintro ⟨hk, hA, hB, hv, hval⟩
    have hk' : r.k ≠ 0 := hk.ne'
    have hu : vec r.dA r.dB r.v r.k ≠ 0 := (vec_ne_zero_iff _ _ _ hk').mpr hv
    refine ⟨⟨fun x => (isPVMRaw_iff hk').mp (hA x x.2), fun y => (isPVMRaw_iff hk').mp (hB y y.2),
      hu⟩, (valueTest_iff g p q r hk' hu).mp hval⟩
  · rintro ⟨hval, hlt⟩
    have hk' : r.k ≠ 0 := by
      intro hk
      apply hval.u_ne_zero
      funext p
      simp [RawStrategy.interp, hk]
    have hu : vec r.dA r.dB r.v r.k ≠ 0 := hval.u_ne_zero
    exact ⟨Nat.pos_of_ne_zero hk', fun x hx => (isPVMRaw_iff hk').mpr (hval.isPVM_A ⟨x, hx⟩),
      fun y hy => (isPVMRaw_iff hk').mpr (hval.isPVM_B ⟨y, hy⟩), (vec_ne_zero_iff _ _ _ hk').mp hu,
      (valueTest_iff g p q r hk' hu).mpr hlt⟩

end MIPRE.ValueApprox


