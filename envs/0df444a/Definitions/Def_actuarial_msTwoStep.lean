-- Prove2me | Definitions.Def_actuarial_msTwoStep
-- name    : actuarial_msTwoStep
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T13:51:11.284215+00:00
-- url     : https://prove2.me/theorems/0592717e-ba10-4531-9196-7bee619e5381
-- title:
--   Finite-state transition and probability conservation: msTwoStep
-- statement:
--   Two-period Chapman-Kolmogorov conditional transition probability across all possible intermediate statuses. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   (TU)_{ik}=Σ_jT_{ij}U_{jk}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 305. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0; Buchardt, Møller and Schmidt, Cash flows and policyholder behaviour in the semi-Markov life insurance setup (2015), https://www.tandfonline.com/doi/full/10.1080/03461238.2013.879919. Parent topic: Finite discrete-time nonstationary and duration-dependent multi-state actuarial benefits, transition probabilities, reserve recursion, disability and surrender cashflows. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def msTwoStep (T U : Fin 3 → Fin 3 → ℝ) (i k : Fin 3) : ℝ := ∑ j : Fin 3, T i j * U j k

end ActuarialValuation


