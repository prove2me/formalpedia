-- Prove2me | Definitions.Def_Eden_KaplanYorke
-- name    : Eden_KaplanYorke
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:45:18.373798+00:00
-- url     : https://prove2.me/theorems/323a0a5b-b0d6-52fc-85f0-94312231f869
-- title:
--   Kaplan Yorke
-- statement:
--   Definitions and structural lemmas for Kaplan Yorke, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/KaplanYorke.lean

import Definitions.Def_Eden_LyapunovExponents
import Mathlib.Data.Finset.Max
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time


set_option autoImplicit true
noncomputable section
namespace Eden
def spectrumEntry (a : Fin 5 → ℝ) (i : ℕ) : ℝ :=
  if h : i < 5 then a ⟨i, h⟩ else 0
def spectrumPartialSum (a : Fin 5 → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, spectrumEntry a i
@[simp] theorem spectrumPartialSum_zero (a : Fin 5 → ℝ) :
    spectrumPartialSum a 0 = 0 := by simp [spectrumPartialSum]
def nonnegativeSumIndices (a : Fin 5 → ℝ) : Finset ℕ :=
  (Finset.range 6).filter (fun k => 0 ≤ spectrumPartialSum a k)
theorem nonnegativeSumIndices_nonempty (a : Fin 5 → ℝ) :
    (nonnegativeSumIndices a).Nonempty := by
  refine ⟨0, ?_⟩
  simp [nonnegativeSumIndices]
def kaplanYorkeIndex (a : Fin 5 → ℝ) : ℕ :=
  (nonnegativeSumIndices a).max' (nonnegativeSumIndices_nonempty a)
def kaplanYorkeDimension (a : Fin 5 → ℝ) : ℝ :=
  if kaplanYorkeIndex a = 0 then 0
  else if kaplanYorkeIndex a = 5 then 5
  else (kaplanYorkeIndex a : ℝ) +
    spectrumPartialSum a (kaplanYorkeIndex a) / |spectrumEntry a (kaplanYorkeIndex a)|
def asymptoticDimension (c : ℝ) (p : PhaseSpace) : ℝ :=
  kaplanYorkeDimension (lyapunovExponent c p)
end Eden


