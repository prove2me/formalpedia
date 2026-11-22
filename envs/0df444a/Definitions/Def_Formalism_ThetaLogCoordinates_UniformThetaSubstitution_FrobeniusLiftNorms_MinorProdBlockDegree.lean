-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MinorProdBlockDegree
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MinorProdBlockDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:50:46.08939+00:00
-- url     : https://prove2.me/theorems/e822a613-22de-4886-babd-0933bbae18c3
-- title:
--   Minor Prod Block Degree
-- statement:
--   Definitions and structural lemmas for Minor Prod Block Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/MinorProdBlockDegree.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.G7
section BiLe
variable {K ι κ : Type} [Field K]
def BiLe (n0 : ι →₀ ℕ) (W : MvPolynomial κ (MvPolynomial ι K)) : Prop :=
  ∀ β : κ →₀ ℕ, ∀ n ∈ (MvPolynomial.coeff β W).support, n ≤ n0 ∧ n.degree + β.degree = n0.degree
end BiLe
section PosDeg
variable {K σ : Type} [Field K] [DecidableEq σ] {r0 r1 : ℕ}
def posWt (r0 r1 : ℕ) (s : σ) : σ × Fin r0 × Fin r1 → ℕ := fun x => if x.1 = s then 1 else 0
end PosDeg
end Formalism.InvariantFactorPaths.G7


