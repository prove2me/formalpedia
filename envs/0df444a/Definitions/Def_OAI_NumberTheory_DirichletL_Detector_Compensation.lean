-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Compensation
-- name    : OAI_NumberTheory_DirichletL_Detector_Compensation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:40:48.84155+00:00
-- url     : https://prove2.me/theorems/dee321cd-af81-4d64-a63d-9786de93a2ef
-- title:
--   Compensation
-- statement:
--   Definitions and structural lemmas for Compensation, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/Compensation.lean

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeCompensation
def tupleOperation {α : Type*} [CommMonoid α] {K : ℕ}
    (p : Fin K → α) (q : α → ℝ) (η : α → ℂ)
    (F : α → ℝ → ℝ → ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  ∑ J ∈ (Finset.univ : Finset (Fin K)).powerset,
    (-1 : ℂ) ^ J.card * ((q (∏ i ∈ J, p i) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
      star (η (∏ i ∈ Finset.univ \ J, p i)) *
      F (∏ i ∈ Finset.univ \ J, p i)
        (X / q (∏ i ∈ J, p i)) (Y / q (∏ i ∈ J, p i))
        (Z * q (∏ i ∈ Finset.univ \ J, p i))
end SevenEighths.ProbeCompensation
end
end OAI


