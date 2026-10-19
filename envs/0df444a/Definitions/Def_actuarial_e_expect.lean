-- Prove2me | Definitions.Def_actuarial_e_expect
-- name    : actuarial_e_expect
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T11:04:46.713804+00:00
-- url     : https://prove2.me/theorems/32403b35-b3c8-4084-8112-96b8e19d8424
-- title:
--   Expectation over dependent mortality states
-- statement:
--   Expectation over dependent mortality states. A single probability space supports member deaths, dependent deaths and every payable stream.
--
--   The contractual and mortality relation is:
--
--   $$
--   \mathbb{E}_p[F]=\sum_{i=0}^{h}\sum_{j=0}^{h}p_{ij}F(i,j)
--   $$
--
--   The object is defined at its stated payment dates. Amounts are per instalment or in pounds as appropriate; probabilities are dimensionless and discounts are to valuation.
-- source:
--   Reused published Prove2Me Definition via a local symbol-preserving alias: ActuarialJointD.expect, UUID 92475f9c-9714-4b2a-8935-d9e934c513bf, from CII module Definitions.Def_actuarial_d_expect. Verified in a pinned private Prove2Me import compilation. Independent actuarial context: Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, p. 359, https://doi.org/10.1017/9781108784184

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive

namespace ActuarialDeathE
noncomputable def expect (h : ℕ) (p : ℕ → ℕ → ℝ) (f : ℕ → ℕ → ℝ) : ℝ := ActuarialJointD.expect h p f
end ActuarialDeathE


