-- Prove2me | Definitions.Def_actuarial_msTransitionBenefit
-- name    : actuarial_msTransitionBenefit
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T13:51:39.890052+00:00
-- url     : https://prove2.me/theorems/2674af0d-704e-4cbe-b2f0-5fb48306c9c9
-- title:
--   Transition benefits, annual reserve values and profit: msTransitionBenefit
-- statement:
--   Present value of end-year state-transition benefits, explicitly differentiated by both origin and destination. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   EPV=vΣ_iΣ_j p_iT_ij B_ij
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 305. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0; Buchardt, Møller and Schmidt, Cash flows and policyholder behaviour in the semi-Markov life insurance setup (2015), https://www.tandfonline.com/doi/full/10.1080/03461238.2013.879919. Parent topic: Finite discrete-time nonstationary and duration-dependent multi-state actuarial benefits, transition probabilities, reserve recursion, disability and surrender cashflows. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def msTransitionBenefit (p : Fin 3 → ℝ) (T : Fin 3 → Fin 3 → ℝ) (B : Fin 3 → Fin 3 → ℝ) (discount : ℝ) : ℝ := discount * ∑ i : Fin 3, ∑ j : Fin 3, p i*T i j*B i j

end ActuarialValuation


