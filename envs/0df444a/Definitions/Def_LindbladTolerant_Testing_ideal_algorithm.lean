-- Prove2me | Definitions.Def_LindbladTolerant_Testing_ideal_algorithm
-- name    : LindbladTolerant_Testing_ideal_algorithm
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:54:49.835803+00:00
-- url     : https://prove2.me/theorems/17d42d7b-30bd-4bca-832a-f3db8afb304b
-- title:
--   Ideal flagged-output law for Algorithm 1
-- statement:
--   This definition records the output law obtained by running the fixed decision routine of Algorithm 1 on the ideal flagged preparations
--   $$\Omega_t^{\mathrm{ideal}}=(1-\Gamma t)\lvert\mathrm{fail}\rangle\langle\mathrm{fail}\rvert\oplus tC.$$
--   Each of the $M$ attempts succeeds independently with probability $\Gamma t$. Conditional on success, the retained output is the jump state $\sigma=C/\Gamma$ when $\Gamma>0$; at $\Gamma=0$ every attempt fails, so the dummy zero conditional operator has zero sampling mass. The sum over Boolean flag sequences uses exactly the same rate cutoffs, stored-copy estimator, and midpoint comparison as the physical algorithm.
--
--   This isolates Eqs.(95) and (98)–(105) from the finite-time experiment, so that the ideal success analysis and the physical–ideal comparison can be proved independently.
--
--   **Formalization Note** The ideal probability is a finite real weighted sum, using `rate g * attemptTime k bound eps1 eps2` for $\Gamma t$ and `idealConditional g` for the conditional jump state. No ideal-state property is asserted by the definition itself.
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf, Eq.(95), p.26, and Algorithm 1 with the ideal experiment analyzed on pp.26–27, Eqs.(96)–(105)

import Definitions.Def_LindbladTolerant_Testing_algorithm

set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
open scoped BigOperators Matrix

namespace LindbladTolerant.Testing
attribute [local instance] Classical.propDecidable Classical.decEq

variable {n : ℕ}

/-- In the ideal experiment (95), a successful preparation has unnormalized
block tC. Conditional on success its normalized state is C/Gamma when Gamma>0.
At zero rate there are no successes, so the dummy zero is never sampled. -/
def idealConditional (g : Super (Qubits n) (Qubits n)) :
    Op (Qubits n × Qubits n) :=
  if hp : 0 < rate g then jumpState g hp else 0

/-- Output law of Algorithm 1 applied to the ideal flagged preparations (95).
All M attempts have independent success probability Gamma*t. -/
def idealAlgorithmProbability (k : ℕ) (bound eps1 eps2 : ℝ)
    (g : Super (Qubits n) (Qubits n)) (yes : Bool) : ℝ :=
  let t := attemptTime k bound eps1 eps2
  ∑ f : Fin (attemptCount k bound eps1 eps2) → Bool,
    flagsWeight (rate g * t) f *
      flagDecisionProbability k eps1 eps2 (idealConditional g) f yes

end LindbladTolerant.Testing


