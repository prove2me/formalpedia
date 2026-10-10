-- Prove2me | Definitions.Def_actuarial_commLifeValueBalance
-- name    : actuarial_commLifeValueBalance
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T23:16:15.798171+00:00
-- url     : https://prove2.me/theorems/d0beba5a-aa73-4b61-9bfd-540d2179f60b
-- title:
--   Assurance and annuity monetary values: commLifeValueBalance
-- statement:
--   Sum of term assurance, effective-discount-weighted annuity due and pure endowment. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   Q=A_{x:n}+d\ddot a_{x:n}+E_{x:n}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 50. Institute of Actuaries, International Actuarial Notation, Commutation Functions, https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Chapter 5, Annuities, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/annuities/6E4AF10872F5D04E3437447F025ECA97. Parent topic: Discounted survivor and death functions, term annuities, term assurances, endowment and finite-life present value decomposition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuaries.org.uk/system/files/documents/pdf/0042-0071.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commEffectiveDiscount
import Definitions.Def_actuarial_commTemporaryAnnuity
import Definitions.Def_actuarial_commTermAssurance
import Definitions.Def_actuarial_commPureEndowment

namespace ActuarialValuation

noncomputable def commLifeValueBalance (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) : ℝ := commTermAssurance l v x n + commEffectiveDiscount v * commTemporaryAnnuity l v x n + commPureEndowment l v x n

end ActuarialValuation


