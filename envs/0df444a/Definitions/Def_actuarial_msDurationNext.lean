-- Prove2me | Definitions.Def_actuarial_msDurationNext
-- name    : actuarial_msDurationNext
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T13:52:44.339988+00:00
-- url     : https://prove2.me/theorems/41d0cae9-67e3-451d-822f-bcf2b0556582
-- title:
--   Duration-dependent semi-Markov disability and exit valuations: msDurationNext
-- statement:
--   Exact elapsed-time reset at a genuine change of disability/active/exit state. Sojourn duration increments only if status is unchanged. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   d'=(d+1) if stay, otherwise 0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 305. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8, https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0; Buchardt, Møller and Schmidt, Cash flows and policyholder behaviour in the semi-Markov life insurance setup (2015), https://www.tandfonline.com/doi/full/10.1080/03461238.2013.879919. Parent topic: Finite discrete-time nonstationary and duration-dependent multi-state actuarial benefits, transition probabilities, reserve recursion, disability and surrender cashflows. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/multiple-state-models/BFEB2CD04A3EA012FCB1C7E3A326E9A0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

def msDurationNext (i j : Fin 3) (duration : ℕ) : ℕ := if i=j then duration+1 else 0

end ActuarialValuation


