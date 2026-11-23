-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegF
-- name    : ReciprocityTheory_SemistableReduction_SemiDegF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:07.941423+00:00
-- url     : https://prove2.me/theorems/bf42f834-0b86-4744-bab5-0fba022ed5cb
-- title:
--   Semi Deg F
-- statement:
--   Definitions and structural lemmas for Semi Deg F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegF.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
def wPart (r m : ℕ) (i : Fin r) : Fin r :=
  if (i : ℕ) < m ∨ r ≤ (i : ℕ) + m then Fin.rev i else i
def wVal {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (i : Fin r) : K :=
  if (i : ℕ) < m ∨ r ≤ (i : ℕ) + m then 1 else g i
def adMet {K : Type} [Field K] [NumberField K] (r m : ℕ) (g : Fin r → K) (dd : Fin r → ℝ) :
    (K →+* ℂ) → Fin r → ℝ :=
  fun σ i => if (i : ℕ) < m then dd i else if r ≤ (i : ℕ) + m then (dd (Fin.rev i))⁻¹
    else ‖σ (g i)‖
end ReciprocityTheory.MultiplicativeHeights.SemiPt


