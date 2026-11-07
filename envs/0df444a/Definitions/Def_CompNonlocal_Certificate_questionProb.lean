-- Prove2me | Definitions.Def_CompNonlocal_Certificate_questionProb
-- name    : CompNonlocal_Certificate_questionProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:10.782166+00:00
-- url     : https://prove2.me/theorems/96eec998-97a7-47a9-b610-85f633dff4d3
-- title:
--   The question probability $\Pr[X=x]$
-- statement:
--   The probability that the verifier's question generation sends Alice the question $x$ (in the ASP of §8.1, that the sender's message is $x$).
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §6.3, p.30 and §8.1, p.35

import Mathlib
import Definitions.Def_CompNonlocal_Certificate

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The probability `Pr[X = x]` that the verifier's question generation sends Alice the question
`x`. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*,
manuscript (STOC 2027 submission, sha256 e245edd7…), §6.3, p.30 ("ω_{S|x} denote[s] its state
conditioned on X = x") and §8.1, p.35 (`ASP.Sen` runs `(x, y, td) ← Q(1^κ)` and sends `msg_S := x`).
It is the total trace of the verifier's register over the question outcomes `o` with
`o.take (lx κ) = x`. -/
noncomputable def Certificate.questionProb (c : Certificate) (κ : ℕ) (x : Str) : ℝ :=
  ∑ o : Bits (c.Qg κ).outC.length,
    if (List.ofFn o).take (c.lx κ) = x then (c.td κ (List.ofFn o)).trace.re else 0

end CompNonlocal


