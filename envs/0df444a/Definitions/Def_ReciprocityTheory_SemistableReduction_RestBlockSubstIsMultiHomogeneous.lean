-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
-- name    : ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:28.724783+00:00
-- url     : https://prove2.me/theorems/9d2b681e-ebc2-4a22-b55b-3f9c42f8543b
-- title:
--   Rest Block Subst Is Multi Homogeneous
-- statement:
--   Definitions and structural lemmas for Rest Block Subst Is Multi Homogeneous, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory MvPolynomial
def lh0First {B n : ℕ} (y : BlockSphere B n) : Fin (B + 1) × Fin n → MvPolynomial (Fin n) ℂ :=
  fun p => (Fin.cons (fun j => X j) (fun b j => C (blockPoint y (b, j))) :
    Fin (B + 1) → Fin n → MvPolynomial (Fin n) ℂ) p.1 p.2
def lh0Rest {B n : ℕ} (x : Fin n → ℂ) : Fin (B + 1) × Fin n → MvPolynomial (Fin B × Fin n) ℂ :=
  fun p => (Fin.cons (fun j => C (x j)) (fun b j => X (b, j)) :
    Fin (B + 1) → Fin n → MvPolynomial (Fin B × Fin n) ℂ) p.1 p.2
abbrev lh0Split (B n : ℕ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (B + 1) => UnitSphereC n) 0
end ReciprocityTheory.MultiplicativeHeights


