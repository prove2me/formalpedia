-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousMemSpanLinearRoots
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousMemSpanLinearRoots
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:51.450252+00:00
-- url     : https://prove2.me/theorems/ae55335d-8b5b-49d3-8547-765c63d02911
-- title:
--   Homogeneous Mem Span Linear Roots
-- statement:
--   Definitions and structural lemmas for Homogeneous Mem Span Linear Roots, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomogeneousMemSpanLinearRoots.lean

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
namespace GlobalTheory
namespace PowLinSpan
variable {σ : Type} [Fintype σ] [DecidableEq σ]
noncomputable def polOf (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) : MvPolynomial σ ℝ :=
  ∑ k ∈ Finset.piAntidiag Finset.univ d,
    monomial (Finsupp.equivFunOnFinite.symm k)
      ((Nat.multinomial Finset.univ k : ℝ) * φ (monomial (Finsupp.equivFunOnFinite.symm k) 1))
end PowLinSpan
end GlobalTheory


