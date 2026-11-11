-- Prove2me | Definitions.Def_GapAgnosticGS_OracleAlg_child
-- name    : GapAgnosticGS_OracleAlg_child
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:30:54.396202+00:00
-- url     : https://prove2.me/theorems/45e27bae-48af-4bcb-bc3d-822c7854ea05
-- title:
--   One step of an adaptive oracle algorithm on its branch vector
-- statement:
--   Let $\psi_h$ be the unnormalized branch vector of a run of an adaptive oracle algorithm with oracle $U$ after history $h$. The branch vector after history $z::h$ is
--
--   1. $V_h\psi_h$ if the step is an isometry and $z=0$;
--   2. $\big(|0\rangle\langle0|\otimes I+|1\rangle\langle1|\otimes U^{(\dagger)}\big)\psi_h$ if the step is a query and $z=0$;
--   3. the projection of $\psi_h$ onto the workspace basis states with measurement outcome $z$ if the step is a measurement;
--   4. $0$ otherwise (after a halt, or for an outcome the step cannot produce).
--
--   Squared norms of branch vectors are the probabilities of the histories. This is the only place where the oracle enters the model.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §1, p.1 (PDF p.2) (controlled queries to W_H and W_H†)

import Definitions.Def_GapAgnosticGS_OracleAlg

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §1, p.1 (PDF p.2) (controlled queries to `W_H` and `W_H†`). One step of an
`OracleAlg` with oracle `U`: from the unnormalized branch vector `v` after history `h`, the branch
vector after history `z :: h`.

* `iso`: `z = 0` gives `V h v`;
* `query adj`: `z = 0` gives `(|0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ U^{(†)}) v`, the controlled (adjoint)
  oracle on the control qubit and the oracle register `Q`;
* `measure`: outcome `z` keeps the workspace basis states `k` with `meas h k = z`;
* `halt`, and any `z` the step does not produce: the zero vector.

**Formalization Note.** For `query` and `measure` the workspace dimension is unchanged
(`w_query`, `w_measure`); the guard `k < w h` only re-indexes `Fin (w (z :: h))` as `Fin (w h)`.
Unnormalized branch vectors carry the probabilities: the probability of reaching a history is the
squared norm of its branch vector. -/
noncomputable def OracleAlg.child {Q Y O : Type} [Fintype Q] [DecidableEq Q] [Fintype Y]
    [DecidableEq Y] (A : OracleAlg Q Y O) (U : Matrix Q Q ℂ) (h : List ℕ) (z : ℕ)
    (v : EuclideanSpace ℂ (Q × Y × Bool × Fin (A.w h))) :
    EuclideanSpace ℂ (Q × Y × Bool × Fin (A.w (z :: h))) :=
  match A.step h, z with
  | .iso, 0 => WithLp.toLp 2 ((A.V h).mulVec (WithLp.ofLp v))
  | .query b, 0 => WithLp.toLp 2 fun x =>
      if hk : (x.2.2.2 : ℕ) < A.w h then
        if x.2.2.1 then
          ∑ q : Q, (if b then U.conjTranspose else U) x.1 q * v (q, x.2.1, true, ⟨x.2.2.2, hk⟩)
        else v (x.1, x.2.1, false, ⟨x.2.2.2, hk⟩)
      else 0
  | .measure, z => WithLp.toLp 2 fun x =>
      if hk : (x.2.2.2 : ℕ) < A.w h then
        if A.meas h ⟨x.2.2.2, hk⟩ = z then v (x.1, x.2.1, x.2.2.1, ⟨x.2.2.2, hk⟩) else 0
      else 0
  | _, _ => 0

end GapAgnosticGS


