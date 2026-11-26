-- Prove2me | Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
-- name    : LeanNct_Auto_Reduction_VariationSeminorms
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:37:53.098799+00:00
-- url     : https://prove2.me/theorems/901ec4fe-d128-4ce6-9f11-92801f579562
-- title:
--   Variation Seminorms
-- statement:
--   Definitions and structural lemmas for Variation Seminorms, from Floris van Doorn, Polona Durcik, Joris Roos, Lenka Slavíková, Christoph Thiele (roos-j/lean-nct; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Norm-variation of multiple ergodic averages for commuting transformations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable def finiteVariationSeminorm {B : Type*} [SeminormedAddCommGroup B]
    {I : Set ℝ} (a : I → B) (r : ℝ) (J : ℕ) : ℝ≥0∞ :=
  ⨆ (t : {u : Fin (J + 1) → I // Monotone u}),
    (∑ j : Fin J,
      (‖a (t.1 j.succ) - a (t.1 j.castSucc)‖₊ : ℝ≥0∞) ^ r) ^ r⁻¹
noncomputable def aux_dyadicInterval (k : ℤ) : Set ℝ :=
  Set.Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
noncomputable def aux_logarithmicMeasure (α β : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Icc α β)).withDensity fun t ↦ ENNReal.ofReal t⁻¹
noncomputable def aux_logarithmicL2 (α β : ℝ) (f : ℝ → ℝ) : ℝ≥0∞ :=
  eLpNorm f 2 (aux_logarithmicMeasure α β)
theorem aux_dyadicLower_le_upper (k : ℤ) :
    (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) :=
  zpow_le_zpow_right₀ (by norm_num) (by omega)
noncomputable def aux_dyadicLowerPoint (k : ℤ) : aux_dyadicInterval k :=
  ⟨(2 : ℝ) ^ k, ⟨le_rfl, aux_dyadicLower_le_upper k⟩⟩
noncomputable def aux_dyadicLocalChain (J : ℕ) (k : ℤ)
    (t : Fin (J + 1) → ℝ) : Fin (J + 1) → aux_dyadicInterval k :=
  fun j ↦ Set.projIcc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
    (aux_dyadicLower_le_upper k) (t j)
noncomputable def aux_dyadicPairChain (J : ℕ) (k : ℤ)
    (x : aux_dyadicInterval k) : Fin (J + 1) → aux_dyadicInterval k :=
  Fin.cases (aux_dyadicLowerPoint k) (fun _ ↦ x)
noncomputable def aux_dyadicIndex (x : ℝ) : ℤ :=
  if hx : 0 < x then
    (exists_mem_Ico_zpow hx (by norm_num : (1 : ℝ) < 2)).choose
  else 0
noncomputable def aux_dyadicSet {J : ℕ} (t : Fin (J + 1) → ℝ) : Finset ℤ :=
  Finset.univ.image (fun j ↦ aux_dyadicIndex (t j))
def aux_crossIndices {J : ℕ} (b : Fin (J + 1) → ℤ) : Finset (Fin J) :=
  Finset.univ.filter fun j ↦ b j.castSucc < b j.succ
end Auto


