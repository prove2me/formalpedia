-- Prove2me | Definitions.Def_MIPRE_Foundations_ValueApprox_RawComplete
-- name    : MIPRE_Foundations_ValueApprox_RawComplete
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:15:44.768277+00:00
-- url     : https://prove2.me/theorems/d94bd069-ecbf-4ad7-bfdc-02099d76df3b
-- title:
--   Every Gaussian-rational exact strategy is a raw candidate, and the semidecision criterion for the quantum value
-- statement:
--   This bundle contributes no definitions and five theorems, closing the semantic analysis of the raw-candidate check for `lem:value-lower-approx`.
--
--   `natCast_mul_ratCast_den`: $\mathrm{den}(a)\cdot a = \mathrm{num}(a)$ in $\mathbb{C}$ for a rational $a$. `exists_common_den`: finitely many Gaussian rationals (a `Finset ℂ` whose elements lie in `GaussianRat`) have a common denominator, some natural $k > 0$ such that for each of them $k z$ is the complex number of a Gaussian integer (`GInt.toC w` for some $w$). `getD_ofFn`: `(List.ofFn f).getD i d = f i` for $i$ in range. `exists_rawStrategy_interp_eq`: every exact strategy `c : ExactStrategy (Fin (nX + 1)) (Fin (nX + 1)) (Fin (nA + 1)) (Fin (nA + 1))` with `c.EntriesIn GaussianRat` is `r.interp nX nA` for some raw candidate $r$. Finally `MIPRE.ValueApprox.exists_check_iff`, for a game description `g : GameData` and naturals $p, q$:
--   $$\bigl(\exists\, r : \mathrm{RawStrategy},\ \mathrm{Check}(g,p,q,r)\bigr) \iff \frac{p}{q} < \mathrm{val}^{*}(g.\mathrm{game}).$$
--
--   As the module docstring records, the forward direction is the correctness of the check (`check_iff_interp`) with the soundness of exact strategies, and the converse is the density of Gaussian-rational exact strategies (`lt_quantumValue_iff`) with `exists_rawStrategy_interp_eq`. The left-hand side is a search over a `Primcodable` type for a decidable predicate, so this is the semantic content of the semidecision procedure for $\mathrm{val}^{*}(G) > p/q$.
--
--   **Formalization Note**. $p/q$ is real division, $p/0 = 0$ by Lean's convention, so the case $q = 0$ asks whether $\mathrm{val}^{*} > 0$; $\mathrm{val}^{*}$ is `MIPRE.quantumValue` of `g.game`, the reading of the description as a `MIPRE.Game` (bundle `MIPRE_Foundations_GameDescription`); the alphabets `Fin (nX + 1)` and `Fin (nA + 1)` are never empty, which is what `lt_quantumValue_iff` needs. The common denominator is a natural number $k > 0$, so the numerators are Gaussian integers represented in `GInt`, and `exists_rawStrategy_interp_eq` is an equality of `ExactStrategy` structures, dimensions included.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/ValueApprox/RawComplete.lean; blueprint lem:value-lower-approx

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/ValueApprox/RawComplete.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Data.List.GetD
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
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawSemantics

/-!
# Every Gaussian-rational exact strategy is a raw candidate

`MIPRE.ValueApprox.exists_rawStrategy_interp_eq`: an exact strategy whose entries lie in `ℚ(i)`
is `interp r` for some raw candidate `r` — clear a common denominator `k` of the finitely many
entries (`exists_common_den`) and list the numerators. With the correctness of the check
(`check_iff_interp`) and the density and soundness of exact strategies (`lt_quantumValue_iff`),
this gives `exists_check_iff`: some raw candidate passes `Check g p q` iff `p / q < val*(G_g)`.
-/

namespace MIPRE.ValueApprox

open HaltingGameValue (GameData)
open Matrix

/-! ## A common denominator -/

theorem natCast_mul_ratCast_den (a : ℚ) : ((a.den : ℕ) : ℂ) * (a : ℂ) = (a.num : ℂ) := by
  have h := congrArg (Rat.cast : ℚ → ℂ) (Rat.mul_den_eq_num a)
  push_cast at h
  rw [mul_comm]
  exact h

/-- Finitely many Gaussian rationals have a common denominator: some `k ≥ 1` with `k z ∈ ℤ[i]`
for all of them. -/
theorem exists_common_den (s : Finset ℂ) (hs : ∀ z ∈ s, z ∈ GaussianRat) :
    ∃ k : ℕ, 0 < k ∧ ∀ z ∈ s, ∃ w : GInt, (k : ℂ) * z = w.toC := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun z hz => absurd hz (Finset.notMem_empty z)⟩
  | insert z s hz ih =>
    obtain ⟨k₀, hk₀, hw⟩ := ih fun z' hz' => hs z' (Finset.mem_insert_of_mem hz')
    obtain ⟨a, b, rfl⟩ := GaussianRat.mem_iff_exists_eq.mp (hs z (Finset.mem_insert_self z s))
    refine ⟨k₀ * (a.den * b.den), by positivity, fun z' hz' => ?_⟩
    rcases Finset.mem_insert.mp hz' with rfl | hz'
    · refine ⟨GInt.ofInt (k₀ * b.den * a.num) (k₀ * a.den * b.num), ?_⟩
      rw [GInt.toC_ofInt]
      have ha := natCast_mul_ratCast_den a
      have hb := natCast_mul_ratCast_den b
      push_cast
      linear_combination ((k₀ : ℂ) * b.den) * ha + ((k₀ : ℂ) * a.den) * Complex.I * hb
    · obtain ⟨w, hw'⟩ := hw z' hz'
      refine ⟨GInt.mul (GInt.ofNat (a.den * b.den)) w, ?_⟩
      rw [GInt.toC_mul, GInt.toC_ofNat, ← hw']
      push_cast
      ring

/-! ## Reading off numerators -/

/-- `(List.ofFn f).getD i d = f i` for `i : Fin n`. -/
theorem getD_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    (List.ofFn f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simp [i.2]), List.getElem_ofFn]

section Construction

variable {nX nA : ℕ}

/-- Every exact strategy with Gaussian-rational entries is denoted by a raw candidate. -/
theorem exists_rawStrategy_interp_eq
    (c : ExactStrategy (Fin (nX + 1)) (Fin (nX + 1)) (Fin (nA + 1)) (Fin (nA + 1)))
    (hc : c.EntriesIn GaussianRat) : ∃ r : RawStrategy, r.interp nX nA = c := by
  classical
  obtain ⟨dA, dB, PA, PB, u⟩ := c
  obtain ⟨hPA, hPB, hu⟩ := hc
  -- the finite set of entries
  set s : Finset ℂ :=
    (Finset.univ.image fun q : Fin (nX + 1) × Fin (nA + 1) × Fin dA × Fin dA =>
        PA q.1 q.2.1 q.2.2.1 q.2.2.2) ∪
      (Finset.univ.image fun q : Fin (nX + 1) × Fin (nA + 1) × Fin dB × Fin dB =>
        PB q.1 q.2.1 q.2.2.1 q.2.2.2) ∪
      Finset.univ.image u with hs_def
  have hs : ∀ z ∈ s, z ∈ GaussianRat := by
    intro z hz
    simp only [hs_def, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hz
    rcases hz with (⟨q, rfl⟩ | ⟨q, rfl⟩) | ⟨p, rfl⟩
    · exact hPA _ _ _ _
    · exact hPB _ _ _ _
    · exact hu p
  obtain ⟨k, hk, hw⟩ := exists_common_den s hs
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  -- the numerator of an entry
  let num : ℂ → GInt := fun z =>
    if h : ∃ w : GInt, (k : ℂ) * z = w.toC then Classical.choose h else GInt.zero
  have hnum : ∀ z ∈ s, (num z).toC = k * z := by
    intro z hz
    have h := hw z hz
    simp only [num, dif_pos h]
    exact (Classical.choose_spec h).symm
  have hnum' : ∀ z ∈ s, (num z).toC / k = z := fun z hz => by
    rw [hnum z hz, mul_div_cancel_left₀ _ hk']
  -- the raw candidate
  let r : RawStrategy :=
    { k := k
      dA := dA
      dB := dB
      QA := List.ofFn fun x => List.ofFn fun a => List.ofFn fun i => List.ofFn fun j =>
        num (PA x a i j)
      QB := List.ofFn fun y => List.ofFn fun b => List.ofFn fun i => List.ofFn fun j =>
        num (PB y b i j)
      v := List.ofFn fun idx : Fin (dA * dB) => num (u (finProdFinEquiv.symm idx)) }
  refine ⟨r, ?_⟩
  have hmatA : ∀ (x : Fin (nX + 1)) (a : Fin (nA + 1)) (i j : Fin dA),
      entry (r.matA x a) i j = num (PA x a i j) := by
    intro x a i j
    simp only [r, RawStrategy.matA, entry, getD_ofFn]
  have hmatB : ∀ (y : Fin (nX + 1)) (b : Fin (nA + 1)) (i j : Fin dB),
      entry (r.matB y b) i j = num (PB y b i j) := by
    intro y b i j
    simp only [r, RawStrategy.matB, entry, getD_ofFn]
  have hvec : ∀ p : Fin dA × Fin dB, vget r.v (p.1 * dB + p.2) = num (u p) := by
    intro p
    have hidx : (p.1 : ℕ) * dB + p.2 = (finProdFinEquiv p : ℕ) := by
      simp only [finProdFinEquiv_apply_val]
      ring
    simp only [r, vget, hidx]
    rw [getD_ofFn _ (finProdFinEquiv p), Equiv.symm_apply_apply]
  have memA : ∀ (x : Fin (nX + 1)) (a : Fin (nA + 1)) (i j : Fin dA), PA x a i j ∈ s := by
    intro x a i j
    simp only [hs_def, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inl ⟨(x, a, i, j), rfl⟩)
  have memB : ∀ (y : Fin (nX + 1)) (b : Fin (nA + 1)) (i j : Fin dB), PB y b i j ∈ s := by
    intro y b i j
    simp only [hs_def, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl (Or.inr ⟨(y, b, i, j), rfl⟩)
  have memu : ∀ p : Fin dA × Fin dB, u p ∈ s := by
    intro p
    simp only [hs_def, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr ⟨p, rfl⟩
  -- the structures agree field by field
  show (⟨dA, dB, fun x a => Matrix.of fun i j => (entry (r.matA x a) i j).toC / k,
    fun y b => Matrix.of fun i j => (entry (r.matB y b) i j).toC / k,
    fun p => (vget r.v (p.1 * dB + p.2)).toC / k⟩ :
      ExactStrategy (Fin (nX + 1)) (Fin (nX + 1)) (Fin (nA + 1)) (Fin (nA + 1))) =
    ⟨dA, dB, PA, PB, u⟩
  congr 1
  · funext x a
    ext i j
    rw [Matrix.of_apply, hmatA, hnum' _ (memA x a i j)]
  · funext y b
    ext i j
    rw [Matrix.of_apply, hmatB, hnum' _ (memB y b i j)]
  · funext p
    rw [hvec, hnum' _ (memu p)]

end Construction

/-! ## The semidecision procedure is correct -/

/-- Some raw candidate passes the check iff the quantum value of the described game exceeds
`p / q`. -/
theorem exists_check_iff (g : GameData) (p q : ℕ) :
    (∃ r : RawStrategy, Check g p q r) ↔ (p : ℝ) / q < quantumValue g.game := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨hval, hlt⟩ := (check_iff_interp g p q r).mp hr
    exact hlt.trans_le (ExactStrategy.value_le_quantumValue _ g.game hval)
  · intro h
    obtain ⟨c, hc, hcK, hlt⟩ := (lt_quantumValue_iff g.game _).mp h
    obtain ⟨r, hr⟩ := exists_rawStrategy_interp_eq c hcK
    refine ⟨r, (check_iff_interp g p q r).mpr ?_⟩
    rw [hr]
    exact ⟨hc, hlt⟩

end MIPRE.ValueApprox


