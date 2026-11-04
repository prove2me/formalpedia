-- Prove2me | Definitions.Def_OAIQ098E001
-- name    : OAIQ098E001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T04:53:23.868616+00:00
-- url     : https://prove2.me/theorems/9df081a3-6640-4fe7-a5c2-0dd70f32b1e7
-- title:
--   Definitions bundle OAIQ098E001 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 17 declarations of OpenAI's Lean: 16 definitions and 1 inductive type or structure. The definitions and types are `OAI.SharpPlanar.B`, `OAI.SharpPlanar.CardinalData`, `OAI.SharpPlanar.D`, `OAI.SharpPlanar.K`, `OAI.SharpPlanar.Pcoeff`, `OAI.SharpPlanar.Q`, `OAI.SharpPlanar.Scoords`, `OAI.SharpPlanar.X`, `OAI.SharpPlanar.b`, `OAI.SharpPlanar.density`, `OAI.SharpPlanar.h`, `OAI.SharpPlanar.kernelMoment`, `OAI.SharpPlanar.lambda`, `OAI.SharpPlanar.positiveData`, `OAI.SharpPlanar.u`, `OAI.SharpPlanar.v`, `OAI.SharpPlanar.z`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_Cardinal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean).
--
--   **Imports.** It imports the bundle `OAIQ098E000` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098E002`, `OAIQ098E003`, `OAIQ098E014`, `OAIQ098E016`, `OAIQ098E018`, `OAIQ098E136`, `OAIQ098E233` and `OAIQ098E234`; the statements `OAI.SharpPlanar.D_0_e`, `OAI.SharpPlanar.D_1_e`, `OAI.SharpPlanar.D_3_e`, `OAI.SharpPlanar.D_4_e`, `OAI.SharpPlanar.D_7_e`, `OAI.SharpPlanar.D_9_e`, `OAI.SharpPlanar.Q_0_e`, `OAI.SharpPlanar.Q_1_e`, `OAI.SharpPlanar.Q_3_e`, `OAI.SharpPlanar.Q_4_e`, `OAI.SharpPlanar.Q_7_e`, `OAI.SharpPlanar.Q_9_e`, `OAI.SharpPlanar.Scoords_add_e`, `OAI.SharpPlanar.Scoords_mem_e`, `OAI.SharpPlanar.Scoords_smul_e`, `OAI.SharpPlanar.X_norm_e`, `OAI.SharpPlanar.X_summable_coord_e`, `OAI.SharpPlanar.X_summable_e`, `OAI.SharpPlanar.X_summable_pairs_e`, `OAI.SharpPlanar.b_pos_e`, `OAI.SharpPlanar.b_sq_e`, `OAI.SharpPlanar.continuousOn_density_e`, `OAI.SharpPlanar.h_pos_e`, `OAI.SharpPlanar.lambda_sq_antitone_e`, `OAI.SharpPlanar.lambda_sq_e`, `OAI.SharpPlanar.positive_coeff_mass_e`, `OAI.SharpPlanar.positive_coeff_mass_le_e`, `OAI.SharpPlanar.tailScalar_summable_e`, `OAI.SharpPlanar.u_bound_e`, `OAI.SharpPlanar.v_bound_e`, `OAI.SharpPlanar.z_sq_antitone_e` and `OAI.SharpPlanar.z_sq_e`; the proofs of `OAI.SharpPlanar.Scoords_smul_e`, `OAI.SharpPlanar.X_norm_e`, `OAI.SharpPlanar.X_summable_coord_e`, `OAI.SharpPlanar.X_summable_e`, `OAI.SharpPlanar.X_summable_pairs_e`, `OAI.SharpPlanar.b_pos_e`, `OAI.SharpPlanar.b_sq_e`, `OAI.SharpPlanar.h_pos_e`, `OAI.SharpPlanar.lambda_sq_antitone_e`, `OAI.SharpPlanar.lambda_sq_e`, `OAI.SharpPlanar.positive_coeff_mass_le_e`, `OAI.SharpPlanar.tailScalar_summable_e`, `OAI.SharpPlanar.u_bound_e`, `OAI.SharpPlanar.v_bound_e`, `OAI.SharpPlanar.z_sq_antitone_e` and `OAI.SharpPlanar.z_sq_e`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ098E000

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

noncomputable def b : ℝ := Real.sqrt 3 / 2
noncomputable def h : ℝ := 2 / 5
noncomputable def B : ℝ := 4 / 3


abbrev X := lp (fun _ : Node × Bool => ℝ) 1

noncomputable def Pcoeff : ℕ → ℂ
  | 0 => 5
  | 1 => -1 + 2 * Complex.I * b
  | 2 => 1 + 2 * Complex.I * b
  | 3 => -2
  | 4 => -(1 / 2) + Complex.I * b
  | 5 => -1 - 2 * Complex.I * b
  | 6 => 1
  | _ => 0

noncomputable def Q (n : ℕ) : ℝ :=
  (Real.pi / 6) ^ 2 * ∏ a ∈ residues.erase (n % 12),
    (2 * Real.sin (Real.pi * (((n % 12 : ℕ) : ℝ) - (a : ℝ)) / 12)) ^ 2

noncomputable def D (n : ℕ) : ℝ :=
  (Real.pi / 6) * ∑ a ∈ residues.erase (n % 12),
    (Real.cos (Real.pi * (((n % 12 : ℕ) : ℝ) - (a : ℝ)) / 12) /
      Real.sin (Real.pi * (((n % 12 : ℕ) : ℝ) - (a : ℝ)) / 12))

noncomputable def lambda (t : ℝ) : ℂ :=
  Complex.I / ((b : ℂ) * ((t : ℂ) + Complex.I * (h : ℂ)))
noncomputable def z (t : ℝ) : ℂ :=
  -(B : ℂ) / ((t : ℂ) + Complex.I * (h : ℂ)) - Complex.I * (h : ℂ)


noncomputable def u (n j : ℕ) (t : ℝ) : ℂ :=
  -2 * (Real.pi : ℂ) ^ 2 * Complex.exp (-Complex.I * Real.pi * t * n) *
    ∑ l ∈ Finset.Icc (j+1) 6,
      ((l : ℂ) / 6 - t) * Pcoeff l * Complex.exp (Complex.I * Real.pi * (l : ℂ) / 6 * n)

noncomputable def v (n j : ℕ) (t : ℝ) : ℂ :=
  2 * Complex.I * Real.pi * Complex.exp (-Complex.I * Real.pi * t * n) *
    ∑ l ∈ Finset.Icc (j+1) 6,
      Pcoeff l * Complex.exp (Complex.I * Real.pi * (l : ℂ) / 6 * n)

structure CardinalData where
  C : ℝ
  c₀ : ℝ
  d₀ : ℝ
  x : X

noncomputable def density (p : CardinalData) (j : ℕ) (t : ℝ) : ℂ :=
  (p.c₀ : ℂ) * u 0 j t + (p.d₀ : ℂ) * v 0 j t +
    ∑' n : Node, ((p.x (n, false) : ℂ) * u n.val j t +
      (p.x (n, true) : ℂ) * v n.val j t)


noncomputable def kernelMoment (ell : ℕ) (s t : ℝ) : ℂ :=
  lambda t * (Complex.I * Real.pi * z t) ^ ell *
    Complex.exp (Complex.I * Real.pi * z t * s)


noncomputable def K (p : CardinalData) (ell : ℕ) (s : ℝ) : ℝ :=
  ((p.C : ℂ) * (Pcoeff 0 * kernelMoment ell s 0 +
    ∑ j ∈ Finset.Icc 1 6, 2 * Pcoeff j * kernelMoment ell s ((j : ℝ) / 6)) +
    ∑ j ∈ Finset.range 6,
      ∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
        density p j t * kernelMoment ell s t).re

noncomputable def positiveData (x : X) : CardinalData := ⟨0, 0, 0, x⟩


noncomputable def Scoords (x : X) (ni : Node × Bool) : ℝ :=
  if ni.2 then
    (D ni.1.val * K (positiveData x) 0 ni.1.val - K (positiveData x) 1 ni.1.val) /
      Q ni.1.val
  else -K (positiveData x) 0 ni.1.val / Q ni.1.val

end SharpPlanar

end OAI
end


