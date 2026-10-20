-- Prove2me | Definitions.Def_Hairer_GridWeight
-- name    : Hairer_GridWeight
-- status  : Definition
-- author  : @jmmaloney4
-- created : 2026-09-23T21:24:21.216988+00:00
-- url     : https://prove2.me/theorems/4d2d79d3-2701-4d67-96aa-bd546a8159e1
-- title:
--   Smooth anisotropic grid weight for reconstruction approximants
-- statement:
--   Auxiliary smooth weight for the grid / multiresolution approximants used in the reconstruction theorem.
--
--   Following the smooth-partition formalization of Hairer's Theorem 3.10 (cf. the inlined weight in the Proved lemma `Hairer.uniform_grid_model_comparison`, and Hairer arXiv:1303.5113 §3.1 / proof of Thm 3.10), we record:
--
--   - `gridWeight` — the tensor product of one-dimensional bumps `σ(t+1)-σ(t)` built from Mathlib's smooth transition;
--   - `gridCentre` — the anisotropic lattice point `δ^{s_i} j_i`;
--   - `dyadicScale` — the dyadic scale `2^{-n}`.
--
--   These are published as a Definition so theorem statements can import them instead of placing `def`s in a preamble (which breaks `/verify` type matching when the statement mentions those names).
-- source:
--   M. Hairer, A theory of regularity structures, Invent. Math. 198 (2014), arXiv:1303.5113 (v4), §3.1 and proof of Theorem 3.10; matches the weight inlined in Prove2Me lemma Hairer.uniform_grid_model_comparison

import Definitions.Def_Hairer_TestFunctions

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Hairer

/-- Smooth box weight built from Mathlib's `smoothTransition`, matching the
`W` inlined in `Hairer.uniform_grid_model_comparison`. -/
def gridWeight {d : ℕ} (z : Pt d) : ℝ :=
  ∏ i, (Real.smoothTransition (z i + 1) - Real.smoothTransition (z i))

/-- Grid centre at anisotropic scale `δ`. -/
def gridCentre {d : ℕ} (s : Fin d → ℕ) (δ : ℝ) (j : Fin d → ℤ) : Pt d :=
  fun i ↦ δ ^ s i * (j i : ℝ)

/-- Dyadic scale `2⁻ⁿ`. -/
def dyadicScale (n : ℕ) : ℝ := (2 : ℝ) ^ (-(n : ℝ))

end Hairer


