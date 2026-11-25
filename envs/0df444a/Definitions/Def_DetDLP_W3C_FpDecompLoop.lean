-- Prove2me | Definitions.Def_DetDLP_W3C_FpDecompLoop
-- name    : DetDLP_W3C_FpDecompLoop
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T04:34:34.235804+00:00
-- url     : https://prove2.me/theorems/b1d6f934-7a7c-5fc2-9d7a-556cf322b0fb
-- title:
--   Finite-field decomposition loop composition
-- statement:
--   Inductively composes certified bounded coordinate cycles into a LoopRuns trace and transports predicates to a supplied endpoint.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_W3C_FpDecompOne

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.W3C.FpDecompLoop

open FpStep FpTraceStep NineOracleLoop

/-- A finite chain of certified coordinate cycles, ending at the root probe. -/
inductive Chain (R : List Bool → List Bool → Prop) (cap : ℕ) :
    ℕ → FpState → List Bool → FpState → List Bool → Prop where
  | done {s : FpState} {a : List Bool} : Chain R cap 0 s a s a
  | step {n : ℕ} {s next endState : FpState} {a final endAnswer : List Bool}
      (one : FpDecompOne.Cycle R cap s next a final)
      (tail : Chain R cap n next final endState endAnswer) :
      Chain R cap (n + 1) s a endState endAnswer

/-- Compose the cycle traces by induction. The endpoint and word-cap certificate
    are supplied in each `Cycle`; no global large-trace assumptions are hidden. -/
theorem chain_trace {R : List Bool → List Bool → Prop} {cap n rounds : ℕ}
    {s endState : FpState} {a endAnswer output : List Bool}
    (chain : Chain R cap n s a endState endAnswer)
    (tail : LoopRuns (step resume) R rounds (packState endState) endAnswer output cap) :
    LoopRuns (step resume) R (rounds + 2 * n) (packState s) a output cap := by
  induction chain generalizing rounds output with
  | done => simpa using tail
  | @step n s next endState a final endAnswer one rest ih =>
      have htail := ih tail
      have h := FpDecompOne.cycle_trace one htail
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_succ] using h

/-- If every certified coordinate cycle preserves a state predicate, the chain
    transports that predicate to its endpoint. -/
theorem chain_preserves {R : List Bool → List Bool → Prop} {cap n : ℕ}
    {s endState : FpState} {a endAnswer : List Bool}
    (P : FpState → Prop) (chain : Chain R cap n s a endState endAnswer)
    (preserves : ∀ {s next : FpState} {a final : List Bool},
      FpDecompOne.Cycle R cap s next a final → P s → P next) :
    P s → P endState := by
  intro h
  induction chain with
  | done => exact h
  | @step n s next endState a final endAnswer one tail ih =>
      exact ih (preserves one h)

/-- The advertised terminal endpoint has phase 6 and root index zero. -/
theorem rootEndpoint (s : FpState) (hphase : s.phase = 6) (hidx : s.idx = 0) :
    s.phase = 6 ∧ s.idx = 0 := ⟨hphase, hidx⟩

end DetDLP.W3C.FpDecompLoop


