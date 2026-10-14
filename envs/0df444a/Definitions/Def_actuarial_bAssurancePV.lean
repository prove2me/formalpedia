-- Prove2me | Definitions.Def_actuarial_bAssurancePV
-- name    : actuarial_bAssurancePV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:24:29.331155+00:00
-- url     : https://prove2.me/theorems/3a8a8d4c-f8a2-4963-95a1-4098d07f02ad
-- title:
--   Death-in-year assurance paid at the next anniversary with terminal censoring preserved.
-- statement:
--   Death-in-year assurance paid at the next anniversary with terminal censoring preserved. It uses valuation at time zero and GBP per actual instalment.
--
--   Mathematical relation:
--
--   $$
--   A^{(h)}=\sum_{k<h}p_kv^{k+1}
--   $$
--
--   Exact domain restrictions and boundary instants are fixed in the declaration.
--
--   Units: Present value in GBP per unit nominal pension, with individual instalments in GBP, payment time in anniversaries and survival as dimensionless probability.
-- source:
--   Original derived finite annuity result. Contextual source page 110, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. Death-in-year assurance paid at the next anniversary with terminal censoring preserved.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialAnnuities

noncomputable def bAssurancePV (h : ℕ) (v : ℝ) (p : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range h, p k * v^(k+1)

end ActuarialAnnuities


