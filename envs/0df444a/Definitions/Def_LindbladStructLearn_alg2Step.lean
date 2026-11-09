-- Prove2me | Definitions.Def_LindbladStructLearn_alg2Step
-- name    : LindbladStructLearn_alg2Step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:02:00.033812+00:00
-- url     : https://prove2.me/theorems/50abfe42-9a8e-4691-9997-fa3e05ba4d11
-- title:
--   One round of Algorithm 2
-- statement:
--   One round of Algorithm 2 on the state $(c^{(r)}, Q^{(r)}, A^{(r)})$. Let $W_r = \sum_{j\in A^{(r)}} w_j$. If $W_r = 0$ or $c^{(r)} = 0$ the algorithm returns $0$. Otherwise it samples a site $i$ with probability $w_i/W_r$ ($i \in A^{(r)}$), then a term $b$ with $i \in S_b$ and $x_b \ne 0$ with probability $|x_b|/w_i$, and moves to
--
--   $$\Big(c^{(r)}\,\frac{W_r}{|A^{(r)}\cap S_b|}\,\frac{x_b}{|x_b|}\,c'_r,\ \ Q^{(r+1)},\ \ A^{(r)}\cup S_b\Big),\qquad \mathcal L_b^\dagger(Q^{(r)}) = c'_rQ^{(r+1)}.$$
--
--   **Formalization Note** "Return $0$" is the absorbing state with $c = 0$, whose final output $c\,\overline{\mathrm{tr}}(QR)$ is $0$.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Algorithm 2, lines 4–13, p.30

import Mathlib
import Definitions.Def_LindbladStructLearn_alg2Weight
import Definitions.Def_LindbladStructLearn_adjTermPauli
import Definitions.Def_LindbladStructLearn_adjTermCoeff
import Definitions.Def_LindbladStructLearn_FinDist

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- One round of Algorithm 2 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), lines 4–13, p.30), on the state `(c^(r), Q^(r), A^(r))`:
with `W_r = Σ_(j ∈ A^(r)) w_j`, if `W_r = 0` or `c^(r) = 0` the algorithm returns `0`; otherwise it
samples `i` with probability `w_i/W_r` (`i ∈ A^(r)`), then `b` with probability `|x_b|/w_i` among
the terms with `i ∈ S_b` (and `x_b ≠ 0`, line 6), and moves to
`(c^(r) · W_r/|A^(r) ∩ S_b| · (x_b/|x_b|) · c'_r, Q^(r+1), A^(r) ∪ S_b)` (Eq. (4.65)).

**Formalization Note** "Return 0" is the absorbing state `c = 0` (its output `c · tr̄(Q R)` is `0`,
and every later round keeps it). -/
def alg2Step {n k : ℕ} (x : Idx n k → ℂ) (s : ℂ × Pauli n × Finset (Fin n)) :
    FinDist (ℂ × Pauli n × Finset (Fin n)) :=
  let c := s.1
  let Q := s.2.1
  let A := s.2.2
  let W : ℝ := ∑ j ∈ A, alg2Weight x j
  by classical exact
  if W = 0 ∨ c = 0 then [(1, (0, Q, A))]
  else
    ((A ×ˢ (Finset.univ : Finset (Idx n k))).filter
      (fun ib => ib.1 ∈ pairSupport ib.2.1 ∧ x ib.2 ≠ 0)).toList.map fun ib =>
      (alg2Weight x ib.1 / W * (‖x ib.2‖ / alg2Weight x ib.1),
        (c * ((W : ℂ) / ((A ∩ pairSupport ib.2.1).card : ℂ)) * (x ib.2 / (‖x ib.2‖ : ℂ)) *
            adjTermCoeff ib.2.1 Q,
          adjTermPauli ib.2.1 Q, A ∪ pairSupport ib.2.1))

end LindbladStructLearn


