-- Prove2me | Definitions.Def_OAIE3v2B008
-- name    : OAIE3v2B008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:57:40.743494+00:00
-- url     : https://prove2.me/theorems/6412aa72-525a-4fcd-8223-b2de18da4eea
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 9 of 311
-- statement:
--   Definitions bundle 9 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Estimates/PairedDiagonalApproximation.lean`, `Estimates/RowShiftTopSymbol.lean`, `Estimates/SymmetricIntervalDilation.lean`, `Geometry/BoxCornerMean.lean`, `Geometry/MultilinearCoordinateExpansion.lean`, `Geometry/UnconditionedSpatialWidthBudget.lean`, `Lattices/MultilinearAffineExpansion.lean`, `Lattices/SelectedResidueApproximation.lean`, `Lattices/ShortIntegerDifference.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymmetricIntervalDilation
namespace OAI

section

namespace Erdos3

theorem symmetricInterval_card (N : ℕ) :
    (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
  rw [Int.card_Icc]
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ShortIntegerDifference
namespace OAI

section

namespace Erdos3

theorem exists_short_integer_difference (D : Finset ℤ) {H Q : ℕ} (hQ : 0 < Q)
    (hD : ∀ h ∈ D, |h| ≤ (H : ℤ)) (hcard : 2 * H / Q + 1 < D.card) :
    ∃ x ∈ D, ∃ y ∈ D, x < y ∧ y - x < (Q : ℤ) := by
  let f : ℤ → ℤ := fun h => (h + (H : ℤ)) / (Q : ℤ)
  let B := Finset.Icc (0 : ℤ) ((2 * H / Q : ℕ) : ℤ)
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hmap : ∀ h ∈ D, f h ∈ B := by
    intro h hh
    have hd := abs_le.mp (hD h hh)
    simp only [B, f, Finset.mem_Icc]
    constructor
    · exact Int.ediv_nonneg (by omega) hQ'.le
    · have hl : h + (H : ℤ) ≤ ((2 * H : ℕ) : ℤ) := by omega
      exact_mod_cast Int.ediv_le_ediv hQ' hl
  have hB : B.card = 2 * H / Q + 1 := by
    simp only [B, Int.card_Icc, sub_zero]
    norm_cast
  obtain ⟨x, hx, y, hy, hxy, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (by rwa [hB] : B.card < D.card) hmap
  have hdif : |x - y| < (Q : ℤ) := by
    have hxrem := Int.emod_nonneg (x + (H : ℤ)) (by omega : (Q : ℤ) ≠ 0)
    have hyrem := Int.emod_nonneg (y + (H : ℤ)) (by omega : (Q : ℤ) ≠ 0)
    have hxlt := Int.emod_lt_of_pos (x + (H : ℤ)) hQ'
    have hylt := Int.emod_lt_of_pos (y + (H : ℤ)) hQ'
    have hxdiv := Int.emod_add_ediv_mul (x + (H : ℤ)) (Q : ℤ)
    have hydiv := Int.emod_add_ediv_mul (y + (H : ℤ)) (Q : ℤ)
    change (x + (H : ℤ)) / Q = (y + (H : ℤ)) / Q at heq
    rw [heq] at hxdiv
    rw [abs_lt]
    constructor <;> omega
  rcases lt_or_gt_of_ne hxy with hxy | hxy
  · exact ⟨x, hx, y, hy, hxy, by have := abs_lt.mp hdif; omega⟩
  · exact ⟨y, hy, x, hx, hxy, by have := abs_lt.mp hdif; omega⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MultilinearAffineExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem multilinear_affine_expansion {H R M : Type*} [Fintype H] [DecidableEq H] [CommRing R]
    [AddCommGroup M] [Module R M] (F : MultilinearMap R (fun _ : H => M) R)
    (b w : H → M) (x : H → R) :
    F (fun i => b i + x i • w i) =
      ∑ S : Finset H, F (S.piecewise w b) * ∏ i ∈ S, x i := by
  have he : (fun i => b i + x i • w i) = (fun i => x i • w i) + b := by
    funext i
    exact add_comm _ _
  rw [he, F.map_add_univ]
  apply Finset.sum_congr rfl
  intro S _
  have hs : S.piecewise (fun i => x i • w i) b =
      (fun i => (if i ∈ S then x i else 1) • S.piecewise w b i) := by
    funext i
    by_cases hi : i ∈ S <;> simp [Finset.piecewise, hi]
  rw [hs, F.map_smul_univ, Finset.prod_ite_mem_eq, smul_eq_mul, mul_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxCornerMean
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def boxTestCorrelation {n : ℕ} {X : Type*} [Fintype X]
    (F : (Fin n → X) → ℂ) (U : Fin n → (Fin n → X) → ℂ) : ℂ :=
  𝔼 x, F x * ∏ i, U i x

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def assignedBoxTest {n : ℕ} {S X : Type*} [Fintype S]
    (assignment : S → Fin n) (U : S → (Fin n → X) → ℂ)
    (i : Fin n) (x : Fin n → X) : ℂ :=
  ∏ s, if assignment s = i then U s x else 1

theorem assignedBoxTest_prod {n : ℕ} {S X : Type*} [Fintype S]
    (assignment : S → Fin n) (U : S → (Fin n → X) → ℂ) (x : Fin n → X) :
    (∏ i, assignedBoxTest assignment U i x) = ∏ s, U s x := by
  unfold assignedBoxTest
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro s _
  simp

theorem assignedBoxTest_norm {n : ℕ} {S X : Type*} [Fintype S]
    (assignment : S → Fin n) (U : S → (Fin n → X) → ℂ)
    (hU : ∀ s x, ‖U s x‖ ≤ 1) (i : Fin n) (x : Fin n → X) :
    ‖assignedBoxTest assignment U i x‖ ≤ 1 := by
  rw [assignedBoxTest, norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro s _
  split_ifs
  · exact hU s x
  · simp only [norm_one, le_refl]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RowShiftTopSymbol
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def rowShiftedTuple {h : ℕ} {K X V : Type*} [AddCommGroup V]
    (base : K → V) (rows : Fin h → K → ℤ) (shift : X → V)
    (x : Fin h → X) (k : K) : V := base k + ∑ i, rows i k • shift (x i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MultilinearCoordinateExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem multilinear_coordinate_expansion {H I R : Type*} [Fintype H] [Fintype I]
    [DecidableEq H] [DecidableEq I] [CommRing R]
    (F : MultilinearMap R (fun _ : H => I → R) R) (u : H → I → R) :
    F u = ∑ j : H → I, F (fun i => Pi.single (j i) (1 : R)) * ∏ i, u i (j i) := by
  have hu : u = fun h => ∑ i, u h i • Pi.single i (1 : R) := by
    funext h i
    simp [Pi.single_apply]
  calc
    F u = F (fun h => ∑ i, u h i • Pi.single i (1 : R)) := congrArg F hu
    _ = ∑ j : H → I, F (fun h => u h (j h) • Pi.single (j h) (1 : R)) :=
      F.map_sum (fun h i => u h i • Pi.single i (1 : R))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [F.map_smul_univ, smul_eq_mul, mul_comm]

theorem multilinear_diagonal_expansion {H I R : Type*} [Fintype H] [Fintype I]
    [DecidableEq H] [DecidableEq I] [CommRing R]
    (F : MultilinearMap R (fun _ : H => I → R) R) (w : I → R) :
    F (fun _ => w) = ∑ j : H → I, F (fun i => Pi.single (j i) (1 : R)) * ∏ i, w (j i) :=
  multilinear_coordinate_expansion F (fun _ => w)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PairedDiagonalApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem tensor_product_scale_le {I : Type*} {h : ℕ} (T H : I → ℝ)
    (hH : ∀ i, 0 ≤ H i) {A : ℝ} (hscale : ∀ i, H i ≤ A * T i)
    (j : Fin h → I) :
    (∏ i, H (j i)) ≤ A ^ h * ∏ i, T (j i) := by
  calc
    (∏ i, H (j i)) ≤ ∏ i, (A * T (j i)) :=
      Finset.prod_le_prod (fun i _ => hH (j i)) (fun i _ => hscale (j i))
    _ = _ := by simp [Finset.prod_mul_distrib]

theorem tensor_entry_bound_rescale {I : Type*} {h : ℕ}
    (f : (Fin h → I) → ℝ) (T H : I → ℝ)
    (hT : ∀ i, 0 < T i) (hH : ∀ i, 0 < H i) {A B : ℝ}
    (hscale : ∀ i, H i ≤ A * T i) (hB : 0 ≤ B)
    (hf : ∀ j, |f j| ≤ B / ∏ i, T (j i)) :
    ∀ j, |f j| ≤ (A ^ h * B) / ∏ i, H (j i) := by
  intro j
  apply (hf j).trans
  apply (div_le_div_iff₀ (Finset.prod_pos (fun i _ => hT (j i)))
    (Finset.prod_pos (fun i _ => hH (j i)))).mpr
  calc
    B * ∏ i, H (j i) ≤ B * (A ^ h * ∏ i, T (j i)) :=
      mul_le_mul_of_nonneg_left (tensor_product_scale_le T H (fun i => (hH i).le) hscale j) hB
    _ = (A ^ h * B) * ∏ i, T (j i) := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerRowShift {K I : Type*} {h : ℕ} {N : I → ℕ}
    (rows : Fin h → K → ℤ) (s : I → ℕ) (x : Fin h → ∀ j, Fin (N j)) : K × I → ℤ :=
  fun z => ∑ i, rows i z.1 * ((s z.2 : ℤ) * (x i z.2).val)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def residueProfileCenter {K I : Type*}
    (residue : K × I → ℤ) (modulus : I → ℕ) : K × I → ℝ :=
  fun z => -(residue z : ℝ) / modulus z.2

noncomputable def residueProfileWidth {K I : Type*}
    (modulus : I → ℕ) (V : K × I → ℝ) : K × I → ℝ := fun z => V z / modulus z.2

theorem residueProfileWidth_pos {K I : Type*} (modulus : I → ℕ) (V : K × I → ℝ)
    (hmodulus : ∀ j, 0 < modulus j) (hV : ∀ z, 0 < V z) (z : K × I) :
    0 < residueProfileWidth modulus V z :=
  div_pos (hV z) (by exact_mod_cast hmodulus z.2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def spatialSamplingBudget (P : ℝ) : ℝ := 4*P+128

end Erdos3

end

end OAI
end


