-- Prove2me | Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
-- name    : Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:04:34.782313+00:00
-- url     : https://prove2.me/theorems/a85b5ecc-c674-41d6-8d1b-410afe42161e
-- title:
--   Branch Scale
-- statement:
--   Definitions and structural lemmas for Branch Scale, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchScale.lean

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
open Formalism.REAL
noncomputable section
namespace Formalism.BranchingDeterminantCap
structure BsForm {n : ℕ} (sg : Fin n → ℕ)
    (D : MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ → ℂ) : Prop where
  addl : ∀ p p' q, D (p + p') q = D p q + D p' q
  smull : ∀ (c : ℂ) p q, D (c • p) q = c * D p q
  addr : ∀ p q q', D p (q + q') = D p q + D p q'
  smulr : ∀ (c : ℂ) p q, D p (c • q) = star c * D p q
  adj : ∀ (g : Matrix (Fin n) (Fin n) ℂ), ∀ p ∈ dualWeyl ℂ n n sg, ∀ q ∈ dualWeyl ℂ n n sg,
    D (rowAct ℂ g p) q = D p (rowAct ℂ g.conjTranspose q)
namespace BsForm
variable {n : ℕ} {sg : Fin n → ℕ}
  {D : MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ → ℂ}
end BsForm
end Formalism.BranchingDeterminantCap


