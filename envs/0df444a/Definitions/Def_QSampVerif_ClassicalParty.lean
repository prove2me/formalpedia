-- Prove2me | Definitions.Def_QSampVerif_ClassicalParty
-- name    : QSampVerif_ClassicalParty
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:35:00.394605+00:00
-- url     : https://prove2.me/theorems/fb093981-4657-4d68-ab23-557234223147
-- title:
--   Interaction semantics between a classical party and a quantum prover
-- statement:
--   A **classical party** is given by three functions of the transcript $\mathrm{tr}$ (the list of pairs (classical message, prover reply) so far): the number of fresh uniform coins it draws in the next round, the message it sends as a function of those coins, and its final output (an accepted string or $\bot$).
--
--   The **interaction semantics** runs $R$ rounds. In each round the classical party speaks first; then the prover runs its step for that round (load, apply, measure), the reply is appended to the transcript, and the core is replaced by the projected, unnormalized post-measurement vector. The probability of a complete run is the squared norm of the final vector (the product of the Born probabilities of all replies) times the probabilities of the party's coins, and the output distribution is
--
--   $$\Pr[\text{output}=z]=\sum_{\text{runs}}\Pr[\text{run}]\cdot\mathbf 1[\mathrm{out}(\mathrm{tr}_{\mathrm{final}})=z].$$
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Protocol 14.1, pp.182–183 (PDF 183–184); Definition 3.20 item 2, p.24 (PDF 25); paper.md decision 7

import Definitions.Def_QSampVerif_Prover

set_option autoImplicit false

namespace QSampVerif

open QAlgorithms QAlgorithms.Complexity

/-- A classical party of an interaction with a quantum prover (the verifier of Protocol 14.1,
or the IND-CPA challenger of Definition 3.20). The transcript is the list of
(classical message, prover reply) pairs so far. In each round the party draws `coins tr` fresh
uniform bits `r` and sends `msg tr r`; at the end it outputs `out tr` (`none` is `⊥`). -/
structure ClassicalParty where
  /-- Number of fresh coins drawn in the round after transcript `tr`. -/
  coins : List (Str × Str) → ℕ
  /-- The message sent after transcript `tr` with fresh coins `r`. -/
  msg : (tr : List (Str × Str)) → Qubits (coins tr) → Str
  /-- The output on the final transcript. -/
  out : List (Str × Str) → Option Str

/-- The interaction semantics (paper.md decision 7): the probability that the classical party
`A` outputs `z` when `k` rounds remain, the next round is round `i`, the transcript is `tr`, and
the prover's core holds the unnormalized vector `ψ` (the branch so far has weight `‖ψ‖²`).

In each round the party speaks first, then the prover runs step `i`: the message is loaded by
`X` flips, the circuit is applied, the reply wires are measured, and the projected vector is
carried on. The Born weight of a complete run is the squared norm of the final vector. -/
noncomputable def runFrom (A : ClassicalParty) (P : Prover) (z : Option Str) :
    ℕ → ℕ → List (Str × Str) → QState P.n → ℝ
  | _, 0, tr, ψ => (∑ y, ‖ψ y‖ ^ 2) * (if A.out tr = z then 1 else 0)
  | i, k + 1, tr, ψ =>
      ((2 : ℝ) ^ A.coins tr)⁻¹ * ∑ r : Qubits (A.coins tr),
        match P.steps[i]? with
        | none => runFrom A P z (i + 1) k (tr ++ [(A.msg tr r, [])]) ψ
        | some s => ∑ a : Qubits s.outW.length,
            runFrom A P z (i + 1) k (tr ++ [(A.msg tr r, List.ofFn a)])
              (project s.outW a (runLayered s.circ (loadX s.inW (padEnc (A.msg tr r)) ψ)))

/-- The output distribution of `R` rounds between the classical party `A` and the prover `P`,
started with the empty transcript and the core in `|0…0⟩`. -/
noncomputable def runParty (A : ClassicalParty) (P : Prover) (R : ℕ) (z : Option Str) : ℝ :=
  runFrom A P z 0 R [] (zeroState P.n)

end QSampVerif


