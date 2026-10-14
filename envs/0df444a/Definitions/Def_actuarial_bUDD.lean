-- Prove2me | Definitions.Def_actuarial_bUDD
-- name    : actuarial_bUDD
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:21:54.920379+00:00
-- url     : https://prove2.me/theorems/6877ac23-85f3-405c-a8af-e04ceef3b52e
-- title:
--   Within-year uniform-deaths absolute survival
-- statement:
--   Within-year uniform-deaths absolute survival.
--
--   Mathematical relation:
--
--   $$
--   S(u+f)=(1-f)S(u)+fS(u+1)
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 165, UDD approximation (Chapter 5, section 5.11.2). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialAnnuities

noncomputable def bUDD (s0 s1 f : ℝ) : ℝ := s0*(1-f)+s1*f

end ActuarialAnnuities


