-- Prove2me | Definitions.Def_TwoAgentSched_Shops_Construction
-- name    : TwoAgentSched_Shops_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:18.550194+00:00
-- url     : https://prove2.me/theorems/e600682d-3a61-4c4e-bc63-10e564383ea2
-- title:
--   Proofs of Theorems 10.1 and 10.2: the flow shop and open shop instances built from PARTITION
-- statement:
--   The two instances built from a PARTITION instance in §10 of Agnetis, Mirchandani, Pacciarelli and Pacifici. Let $p_1,\dots,p_k$ be nonnegative integers, $P=\sum_{i=1}^k p_i$ and $\varepsilon = 1/(k+1)$.
--
--   **Flow shop (proof of Theorem 10.1, p. 238).** Agent A has $n_A=k$ jobs and agent B has $n_B=1$ job, with
--   $$p^A_{i1}=\varepsilon,\quad p^A_{i2}=p_i\ (i=1,\dots,k),\qquad p^B_{11}=\tfrac P2-(k-1)\varepsilon,\quad p^B_{12}=\tfrac P2,$$
--   and thresholds
--   $$Q_A=\tfrac{3P}{2}+\varepsilon,\qquad Q_B=P+\varepsilon.$$
--
--   **Open shop (proof of Theorem 10.2, p. 239).** Agent A has $n_A=k$ jobs and agent B has $n_B=1$ job, with
--   $$p^A_{i1}=p^A_{i2}=p_i\ (i=1,\dots,k),\qquad p^B_{11}=p^B_{12}=\tfrac P2,$$
--   and thresholds
--   $$Q_A=\tfrac{3P}{2},\qquad Q_B=P.$$
--
--   These are the instances on which the equivalences of the two NP-hardness proofs are stated.
--
--   **Formalization Note** The PARTITION integers are a list `p : List ℕ`, $k$ its length (0-based: $p_{i+1}$ is `p.get i`). The data are real numbers, since $\varepsilon$ and $P/2$ need not be integers; $k-1$ is computed in $\mathbb R$. For $P=0$ and $k\ge 2$ the printed $p^B_{11}$ is negative; the construction is kept as printed and the milestone that uses it excludes that case.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 238, proof of Theorem 10.1; p. 239, proof of Theorem 10.2

import Mathlib
import Definitions.Def_TwoAgentSched_Shops_Model

namespace TwoAgentSched.Shops

/-- `P = ∑_{i=1}^k p_i`, the total of the PARTITION integers `p = [p_1, …, p_k]`, as a real
number (proofs of Theorems 10.1 and 10.2, pp. 238–239). -/
def partSum (p : List ℕ) : ℝ := (p.sum : ℝ)

/-- `ε = 1/(k + 1)` with `k` the number of PARTITION integers (proof of Theorem 10.1, p. 238). -/
noncomputable def eps (p : List ℕ) : ℝ := 1 / ((p.length : ℝ) + 1)

/-- The flow shop instance built from the PARTITION integers `p = [p_1, …, p_k]` in the proof of
Theorem 10.1 (p. 238): `n_A = k`, `n_B = 1`, `p^A_{i1} = ε`, `p^A_{i2} = p_i`,
`p^B_{11} = P/2 − (k − 1)ε`, `p^B_{12} = P/2`. (`k − 1` is computed in `ℝ`.) -/
noncomputable def flowInst (p : List ℕ) : Instance where
  nA := p.length
  nB := 1
  pA1 := fun _ => eps p
  pA2 := fun i => (p.get i : ℝ)
  pB1 := fun _ => partSum p / 2 - ((p.length : ℝ) - 1) * eps p
  pB2 := fun _ => partSum p / 2

/-- `Q_A = 3P/2 + ε` (proof of Theorem 10.1, p. 238). -/
noncomputable def flowQA (p : List ℕ) : ℝ := 3 * partSum p / 2 + eps p

/-- `Q_B = P + ε` (proof of Theorem 10.1, p. 238). -/
noncomputable def flowQB (p : List ℕ) : ℝ := partSum p + eps p

/-- The A-job `J^A_{i+1}` of the flow shop instance (processing times `ε` and `p_{i+1}`). -/
noncomputable def flowA (p : List ℕ) (i : Fin p.length) :
    Fin ((flowInst p).nA + (flowInst p).nB) :=
  (flowInst p).aJob i

/-- The single B-job `J^B_1` of the flow shop instance. -/
noncomputable def flowB (p : List ℕ) : Fin ((flowInst p).nA + (flowInst p).nB) :=
  (flowInst p).bJob ⟨0, Nat.one_pos⟩

/-- The open shop instance built from the PARTITION integers `p = [p_1, …, p_k]` in the proof of
Theorem 10.2 (p. 239): `n_A = k`, `n_B = 1`, `p^A_{i1} = p^A_{i2} = p_i`,
`p^B_{11} = p^B_{12} = P/2`. -/
noncomputable def openInst (p : List ℕ) : Instance where
  nA := p.length
  nB := 1
  pA1 := fun i => (p.get i : ℝ)
  pA2 := fun i => (p.get i : ℝ)
  pB1 := fun _ => partSum p / 2
  pB2 := fun _ => partSum p / 2

/-- `Q_A = 3P/2` (proof of Theorem 10.2, p. 239). -/
noncomputable def openQA (p : List ℕ) : ℝ := 3 * partSum p / 2

/-- `Q_B = P` (proof of Theorem 10.2, p. 239). -/
noncomputable def openQB (p : List ℕ) : ℝ := partSum p

/-- The single B-job `J^B_1` of the open shop instance. -/
noncomputable def openB (p : List ℕ) : Fin ((openInst p).nA + (openInst p).nB) :=
  (openInst p).bJob ⟨0, Nat.one_pos⟩

end TwoAgentSched.Shops


