-- Prove2me | Definitions.Def_GapAgnosticGS_OracleAlg
-- name    : GapAgnosticGS_OracleAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:29:35.258311+00:00
-- url     : https://prove2.me/theorems/2d8183a2-29f5-4b74-802c-69d10c9c39fd
-- title:
--   Adaptive quantum oracle algorithm (mid-run measurements, growing workspace, controlled $U$/$U^\dagger$ queries)
-- statement:
--   An **adaptive quantum oracle algorithm** with oracle register $Q$, output register $Y$ and classical output type $O$ is given by data fixed before the oracle:
--
--   1. a workspace dimension $w(h)$ for every classical history $h$ (finite list of outcomes, newest first);
--   2. an initial unit vector on $Q\otimes Y\otimes\mathbb C^2\otimes\mathbb C^{w([])}$ (oracle register, output register, query-control qubit, workspace);
--   3. for every history, a step (isometry, query, measurement or halt with output), with the isometry $V_h$ satisfying $V_h^\dagger V_h=I$, and for measurements a map assigning each workspace basis state to an outcome;
--   4. queries and measurements keep the workspace dimension.
--
--   The oracle $U$ enters only through query steps, which apply $|0\rangle\langle0|\otimes I+|1\rangle\langle1|\otimes U$ (or $U^\dagger$) to the control qubit and the oracle register. The model allows adaptivity with quantum memory, workspaces that grow with the history, and runs of unbounded length; an algorithm need not halt on every branch.
--
--   **Formalization Note** The paper never defines "algorithm", "queries" or "expected queries". This structure is the reading used for every algorithmic statement of the mission (Theorem 1.1 in both directions, Lemma 3.7, Theorems 3.8 and 3.10).
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 1.1, p.2 (PDF p.3); §1, p.1 (PDF p.2) (access model); Problem 3.2, p.9 (PDF p.10)

import Definitions.Def_GapAgnosticGS_OracleAlg_Step

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 1.1, p.2 (PDF p.3); §1, p.1 (PDF p.2), the access model; Problem 3.2, p.9
(PDF p.10): "The query complexity of an algorithm is the number of controlled queries to E and
E†". An **adaptive quantum oracle algorithm** with oracle register `Q`, output register `Y` and
classical output type `O`. The paper does not define its algorithm model; this is the standard
adaptive model, fixed before the oracle.

The state space after the classical history `h` (the list of measurement outcomes and step
markers, newest first) is `Q × Y × Bool × Fin (w h)`: the oracle register, the output register,
the query-control qubit and a workspace whose dimension `w h` may depend on the history.

* `init`: the (oracle-independent) initial unit vector;
* `step h`: what the algorithm does after history `h` (an isometry, a query, a measurement or a
  halt, with classical output);
* `V h`: the isometry used at an `iso` step, from the current space into the space with workspace
  `Fin (w (0 :: h))` (`V_isometry`: `V† V = 1`);
* `meas h`: the outcome map of a `measure` step: the workspace basis state `k` belongs to outcome
  `meas h k`; outcome `z` leads to history `z :: h` (a projective measurement diagonal in the
  computational basis, so part of the workspace can be measured and the rest kept coherent);
* `w_query`, `w_measure`: queries and measurements do not change the workspace dimension.

**Formalization Note.** Every ingredient (dimensions, isometries, measurements, branching,
outputs) is data fixed before the oracle `U`, which enters only through `query` steps (see
`OracleAlg.child`). There is no bound on the length of histories, and an algorithm need not halt
on every branch. -/
structure OracleAlg (Q Y O : Type) [Fintype Q] [DecidableEq Q] [Fintype Y] [DecidableEq Y] where
  w : List ℕ → ℕ
  init : EuclideanSpace ℂ (Q × Y × Bool × Fin (w []))
  init_norm : ‖init‖ = 1
  step : List ℕ → OracleAlg.Step O
  V : (h : List ℕ) → Matrix (Q × Y × Bool × Fin (w (0 :: h))) (Q × Y × Bool × Fin (w h)) ℂ
  V_isometry : ∀ h, step h = .iso → (V h).conjTranspose * V h = 1
  meas : (h : List ℕ) → Fin (w h) → ℕ
  w_query : ∀ h b, step h = .query b → w (0 :: h) = w h
  w_measure : ∀ h z, step h = .measure → w (z :: h) = w h

end GapAgnosticGS


