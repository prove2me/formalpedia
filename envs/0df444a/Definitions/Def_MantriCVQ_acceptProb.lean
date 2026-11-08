-- Prove2me | Definitions.Def_MantriCVQ_acceptProb
-- name    : MantriCVQ_acceptProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:25.306473+00:00
-- url     : https://prove2.me/theorems/07e40a1b-7ca1-4e7c-a61c-cb0718057b05
-- title:
--   Acceptance probability of a public-coin proof
-- statement:
--   The acceptance probability of verifier $V$ on input $w$ against a strategy $\sigma$ is defined by recursion over the slots. At a prover slot it is the expectation under $\sigma$, at a verifier slot it is the uniform average over strings of the slot's length, and after the last slot it is the indicator that $V$ accepts the transcript.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_MantriCVQ_PCVerifier
import Definitions.Def_MantriCVQ_Strategy

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ

open Classical in
/-- The probability of acceptance from the transcript `tr` with `r` slots remaining: at a prover slot
the expectation under the strategy, at a verifier slot the uniform average over strings of the slot's
length, and at the end the indicator of the decision. -/
noncomputable def acceptFrom (O : Oracle) (V : PCVerifier) (σ : Strategy) (w : Str) :
    ℕ → List Str → ℝ
  | 0, tr => if V.decides O w tr then 1 else 0
  | r + 1, tr =>
    if V.proverSlot w tr.length = true then
      ∑ b : Bits (V.len w tr.length), (σ w tr _ b).toReal *
        acceptFrom O V σ w r (tr ++ [List.ofFn b])
    else
      ∑ b : Bits (V.len w tr.length), ((2 : ℝ) ^ V.len w tr.length)⁻¹ *
        acceptFrom O V σ w r (tr ++ [List.ofFn b])

/-- The probability that the verifier `V` accepts `w` when the prover plays `σ` (Mantri,
arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16)). -/
noncomputable def acceptProb (O : Oracle) (V : PCVerifier) (σ : Strategy) (w : Str) : ℝ :=
  acceptFrom O V σ w (V.S w) []

end MantriCVQ


