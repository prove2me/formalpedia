-- Prove2me | Definitions.Def_PartPredAlloc_alg1
-- name    : PartPredAlloc_alg1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:40.488984+00:00
-- url     : https://prove2.me/theorems/839cfdac-6d59-4ebf-8fe5-027f404cae99
-- title:
--   Algorithm 1 ($ALG_1$): the non-adaptive evolving/fixed threshold algorithm and its revenue
-- statement:
--   Algorithm 1 keeps three counters, $q_1$ (accepted type-1 customers), $q_{2,e}$ (type-2 customers accepted by the evolving threshold) and $q_{2,f}$ (type-2 customers accepted by the fixed threshold), all starting at $0$, and sets $\theta=\frac{1-p}{2-a}$. At each time $\lambda=1/n,\dots,1$ it accepts the arriving customer if there is remaining inventory ($q_1+q_{2,e}+q_{2,f}<b$) and one of the following holds:
--
--   1. the customer is type-1; then $q_1\leftarrow q_1+1$;
--   2. **evolving threshold rule**: the customer is type-2 and $q_1+q_{2,e}<\lfloor\lambda pb\rfloor$; then $q_{2,e}\leftarrow q_{2,e}+1$;
--   3. **fixed threshold rule**: the customer is type-2 and $q_{2,f}<\lfloor\theta b\rfloor$; then $q_{2,f}\leftarrow q_{2,f}+1$.
--
--   The evolving rule has priority when both type-2 rules apply. With $q_\cdot(1)$ the final counters, the revenue on the realized sequence $\vec v$ is
--
--   $$
--   ALG_1(\vec v)=q_1(1)+a\,(q_{2,e}(1)+q_{2,f}(1)).
--   $$
--
--   **Formalization Note** The algorithm is a left fold over slots $t=1,\dots,n$ with $\lambda=t/n$; $\lfloor\cdot\rfloor$ is the integer floor of a real number, compared with the counters in $\mathbb Z$.
-- source:
--   Hwang, Jaillet, Manshadi, Online Resource Allocation under Partially Predictable Demand, arXiv:1810.00447v1, Algorithm 1, p.15

import Mathlib
import Definitions.Def_PartPredAlloc_Cust
import Definitions.Def_PartPredAlloc_alphaL1

namespace PartPredAlloc

/-- The counters of Algorithm 1 (arXiv:1810.00447v1, p.15): `q1` accepted type-1 customers, `q2e`
type-2 customers accepted by the evolving threshold rule, `q2f` type-2 customers accepted by the
fixed threshold rule. -/
structure AlgState where
  /-- accepted type-1 customers `q₁` -/
  q1 : ℕ
  /-- type-2 customers accepted by the evolving threshold rule `q₂,ₑ` -/
  q2e : ℕ
  /-- type-2 customers accepted by the fixed threshold rule `q₂,f` -/
  q2f : ℕ

/-- One step of Algorithm 1 (arXiv:1810.00447v1, p.15) at time `λ = t/n` (slot `t ∈ {1, …, n}`)
with arriving value `c`, for `b` units, type-2 revenue `a` and probability `p`. If there is
remaining inventory (`q₁ + q₂,ₑ + q₂,f < b`):
(a) a type-1 customer is accepted (`q₁ ← q₁ + 1`);
(b) evolving threshold rule: a type-2 customer with `q₁ + q₂,ₑ < ⌊λpb⌋` is accepted
(`q₂,ₑ ← q₂,ₑ + 1`);
(c) fixed threshold rule: otherwise a type-2 customer with `q₂,f < ⌊θb⌋`, `θ = (1 − p)/(2 − a)`,
is accepted (`q₂,f ← q₂,f + 1`).
The evolving rule has priority. Everything else is rejected.

**Formalization Note.** `⌊·⌋` is `Int.floor` of a real number; the counters are compared with it in
`ℤ`. -/
noncomputable def algStep (n b : ℕ) (a p : ℝ) (s : AlgState) (t : ℕ) (c : Cust) : AlgState :=
  if s.q1 + s.q2e + s.q2f < b then
    match c with
    | Cust.high => { s with q1 := s.q1 + 1 }
    | Cust.low =>
      if ((s.q1 + s.q2e : ℕ) : ℤ) < ⌊(t : ℝ) / n * p * b⌋ then { s with q2e := s.q2e + 1 }
      else if ((s.q2f : ℕ) : ℤ) < ⌊theta a p * b⌋ then { s with q2f := s.q2f + 1 }
      else s
    | Cust.empty => s
  else s

/-- The counters of Algorithm 1 after the slots `1, …, m` of the realized sequence `v` have been
processed (arXiv:1810.00447v1, p.15), starting from `q₁ = q₂,ₑ = q₂,f = 0`. Slot `k + 1` is
`v ⟨k, _⟩` and is processed at time `λ = (k + 1)/n`. -/
noncomputable def algRun (n b : ℕ) (a p : ℝ) (v : Fin n → Cust) : ℕ → AlgState
  | 0 => ⟨0, 0, 0⟩
  | k + 1 =>
    if h : k < n then algStep n b a p (algRun n b a p v k) (k + 1) (v ⟨k, h⟩)
    else algRun n b a p v k

/-- `q₁(1)`: accepted type-1 customers at the end of the horizon (arXiv:1810.00447v1, p.16). -/
noncomputable def q1F (n b : ℕ) (a p : ℝ) (v : Fin n → Cust) : ℕ := (algRun n b a p v n).q1

/-- `q₂,ₑ(1)`: type-2 customers accepted by the evolving threshold rule at the end of the horizon
(arXiv:1810.00447v1, p.16). -/
noncomputable def q2eF (n b : ℕ) (a p : ℝ) (v : Fin n → Cust) : ℕ := (algRun n b a p v n).q2e

/-- `q₂,f(1)`: type-2 customers accepted by the fixed threshold rule at the end of the horizon
(arXiv:1810.00447v1, p.16). -/
noncomputable def q2fF (n b : ℕ) (a p : ℝ) (v : Fin n → Cust) : ℕ := (algRun n b a p v n).q2f

/-- `ALG₁(v)`: the revenue of Algorithm 1 (arXiv:1810.00447v1, p.15) on the realized arrival
sequence `v`, i.e. `q₁(1) + a (q₂,ₑ(1) + q₂,f(1))`. -/
noncomputable def alg1 (n b : ℕ) (a p : ℝ) (v : Fin n → Cust) : ℝ :=
  (q1F n b a p v : ℝ) + a * ((q2eF n b a p v : ℝ) + q2fF n b a p v)

end PartPredAlloc


