-- Prove2me | Definitions.Def_actuarial_crMixWeights
-- name    : actuarial_crMixWeights
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T11:28:52.633189+00:00
-- url     : https://prove2.me/theorems/f8b41eca-e822-472b-ad67-9a423e04975f
-- title:
--   Actual finite loss distributions and scenario ambiguity: crMixWeights
-- statement:
--   Convex mixture of two candidate actuarial scenario probability distributions at ambiguity weight λ.
--
--   Mathematical relation:
--
--   $$
--   λ*p i + (1-λ)*q i
--   $$
--   This is an original derived actuarial definition with explicit cashflow timing and mathematical domain.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def crMixWeights {n : ℕ} (p q : Fin n→ℝ) (mix : ℝ) (i : Fin n) : ℝ := mix*p i + (1-mix)*q i

end ActuarialValuation


