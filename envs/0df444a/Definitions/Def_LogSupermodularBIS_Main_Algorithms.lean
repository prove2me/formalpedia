-- Prove2me | Definitions.Def_LogSupermodularBIS_Main_Algorithms
-- name    : LogSupermodularBIS_Main_Algorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:37.811204+00:00
-- url     : https://prove2.me/theorems/e337ea10-4ada-4367-870d-ca7be1c1e326
-- title:
--   Input layouts, the estimator assumption (2.3), residual samplers and bipartite independent sets
-- statement:
--   The algorithms are programs of the costed machine. They receive $d$ and $B$ in pointer registers $0,1$; a node $v$ as its depth in pointer register $2$ and its bits in integer cells $0,\dots,|v|-1$; the accuracy parameters in real cells $0,1,\dots$, followed by a list of further real construction parameters. The weight is accessed only through the evaluator $\langle d,W,T_W\rangle$; $T_W$ is not an input.
--
--   **Standing assumptions** (Theorem 1.2, §2.1): $d\ge2$, $B\ge1$, $W$ positive with every value of bit length at most $B$.
--
--   **Estimator assumption (2.3).** A program $E$ satisfies it with additive error bound $b$ and cost $C_0(1+d+\log(1/\delta_{est}))^{a_0}$ if, for every node $v$ and every $0<\delta_{est}\le1/2$, every execution halts within that cost and returns a real $A_v\ge0$, equal to $0$ at leaves, and
--   $$\Pr\bigl[\log Z_{\Phi_v}-b\le A_v\le\log Z_{\Phi_v}\bigr]\ge1-\delta_{est}.$$
--   **Residual sampler.** A program $S$ samples every residual at cost $C_s(1+d+\log(1/\eta))^{a_0}$ if, for every node $v$ and $0<\eta\le1/2$, every execution halts within that cost and outputs a configuration of the free coordinates whose law is within total variation $\eta$ of $W_v/Z_v$.
--
--   **Bipartite independent sets.** A configuration $x\in\{0,1\}^n$ is an independent set of a simple graph $G$ on the labeled vertex set $\{0,\dots,n-1\}$ if no two vertices with $x_i=x_j=1$ are adjacent. $Z(G)=|I(G)|$ counts them (the empty set included), and $U_G$ is the uniform law on $I(G)$. A graph algorithm receives $n$ in pointer register $0$, the adjacency matrix row by row in integer memory, and its accuracy parameters in real memory; no bipartition is supplied.
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 3 (PDF 4), Theorem 1.2 assumptions; p. 10 (PDF 11), (2.3); p. 39 (PDF 40), Proposition A.2; p. 2 (PDF 3), Theorem 1.1 notation

import Mathlib
import Definitions.Def_LogSupermodularBIS_Main_Machine
import Definitions.Def_LogSupermodularBIS_Main_Weight

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-!
# Input layouts, estimator/sampler specifications and bipartite independent sets

All algorithms are programs of the machine in `Def_LogSupermodularBIS_Main_Machine`. They
receive the dimension `d` and the value-length bound `B` in pointer registers `0, 1`; a node `v`
of the self-reduction tree as its depth in pointer register `2` and its bits (`0`/`1`) in integer
memory cells `0, …, |v|-1`; real accuracy parameters in real memory cells `0, 1, …`, followed by
a list `par` of further real construction parameters. The weight is accessed only through the
evaluator `⟨d, W, T_W⟩`. The evaluation time `T_W` is not an input.
-/

/-- The evaluator of `W`, charged `T_W` operations per evaluation. -/
def evaluator {d : ℕ} (W : (Fin d → Bool) → ℚ) (TW : ℕ) : WeightOracle := ⟨d, W, TW⟩

/-- The bits of a prefix, as integers `0`/`1`. -/
def prefixCells (v : List Bool) : List ℤ := v.map fun b => if b then 1 else 0

/-- Input of an estimator or residual sampler at node `v`: `d, B, |v|`; the bits of `v`; the
accuracy parameter `r` (`δ_est` or `η`) followed by `par`. -/
noncomputable def nodeInput (d B : ℕ) (v : List Bool) (r : ℝ) (par : List ℝ) : State :=
  initState [(d : ℤ), (B : ℤ), (v.length : ℤ)] (prefixCells v) (r :: par)

/-- Input of a counter: `d, B`; real cells `ε, δ` followed by `par`. -/
noncomputable def counterInput (d B : ℕ) (ε δ : ℝ) (par : List ℝ) : State :=
  initState [(d : ℤ), (B : ℤ)] [] (ε :: δ :: par)

/-- The normalized residual log-partition function `log Z_{Φ_v}`. -/
noncomputable def residualLogPartition {d : ℕ} (W : (Fin d → Bool) → ℚ) (v : List Bool) : ℝ :=
  Real.log (potentialPartition (residualPotential W v))

/-- The estimator assumption (2.3) with additive error bound `b`, cost `C_0 (1+d+log(1/δ_est))^{a_0}`
on every execution, at every node `v` and failure parameter `0 < δ_est ≤ 1/2`: it returns a real
`A_v ≥ 0`, exactly `0` at leaves, with `Pr[log Z_{Φ_v} − b ≤ A_v ≤ log Z_{Φ_v}] ≥ 1 − δ_est`. -/
def IsResidualEstimator (E : Program) {d : ℕ} (W : (Fin d → Bool) → ℚ) (TW B : ℕ) (par : List ℝ)
    (b C0 : ℝ) (a0 : ℕ) : Prop :=
  ∀ v : List Bool, v.length ≤ d → ∀ δ ∈ Set.Ioc (0 : ℝ) (1 / 2),
    (∀ ω, ValidTape ω →
      HaltsWithin E (evaluator W TW) ω (nodeInput d B v δ par)
          (C0 * (1 + d + Real.log (1 / δ)) ^ a0) ∧
        0 ≤ outReal E (evaluator W TW) ω (nodeInput d B v δ par) ∧
        (v.length = d → outReal E (evaluator W TW) ω (nodeInput d B v δ par) = 0)) ∧
    ENNReal.ofReal (1 - δ) ≤ tapeLaw {ω |
      residualLogPartition W v - b ≤ outReal E (evaluator W TW) ω (nodeInput d B v δ par) ∧
      outReal E (evaluator W TW) ω (nodeInput d B v δ par) ≤ residualLogPartition W v}

/-- A sampler for the residual law of every node: for every node `v` and `0 < η ≤ 1/2`, every
execution halts within `C_s (1+d+log(1/η))^{a_0}` operations and returns a configuration of the
free coordinates, whose law is within total variation `η` of `W_v / Z_v`. -/
def IsResidualSampler (S : Program) {d : ℕ} (W : (Fin d → Bool) → ℚ) (TW B : ℕ) (par : List ℝ)
    (Cs : ℝ) (a0 : ℕ) : Prop :=
  ∀ v : List Bool, v.length ≤ d → ∀ η ∈ Set.Ioc (0 : ℝ) (1 / 2),
    SamplesWithin S (evaluator W TW) (nodeInput d B v η par) (d - v.length) (residualLaw W v) η
      (Cs * (1 + d + Real.log (1 / η)) ^ a0)

/-- The standing representation assumptions of Theorem 1.2 (p. 3) and §2.1 (p. 9):
`W : {0,1}^d → ℚ_{>0}` with `d ≥ 2`, and every value of bit length at most `B ≥ 1`.
(Log-supermodularity and the evaluator time `T_W ≥ 1` are stated separately.) -/
def StandingWeight {d : ℕ} (W : (Fin d → Bool) → ℚ) (B : ℕ) : Prop :=
  2 ≤ d ∧ 1 ≤ B ∧ PositiveWeight W ∧ ValueLengthBound W B

/-! ## Bipartite independent sets -/

/-- `x ∈ {0,1}^n` is (the indicator of) an independent set of `G`. -/
def IsIndependentConfig {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∀ i j, x i = true → x j = true → ¬ G.Adj i j

open Classical in
/-- `Z(G) = |I(G)|`, the number of independent sets (the empty set included). -/
noncomputable def numIndependentSets {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Bool => IsIndependentConfig G x).card

open Classical in
/-- The uniform law `U_G` on the independent sets of `G`. -/
noncomputable def uniformIndependent {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : ℝ :=
  if IsIndependentConfig G x then 1 / (numIndependentSets G : ℝ) else 0

open Classical in
/-- The adjacency matrix in row-major order: cell `i n + j` holds `1` if `i ~ j`, else `0`. -/
noncomputable def adjacencyCells {n : ℕ} (G : SimpleGraph (Fin n)) : List ℤ :=
  List.ofFn fun k : Fin (n * n) =>
    if G.Adj (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 then 1 else 0

/-- Input of a graph algorithm: `n` in pointer register `0`; the adjacency matrix in integer
memory; the accuracy parameters in real memory cells `0, 1, …`. No bipartition is supplied. -/
noncomputable def graphInput {n : ℕ} (G : SimpleGraph (Fin n)) (reals : List ℝ) : State :=
  initState [(n : ℤ)] (adjacencyCells G) reals

end LogSupermodularBIS.Main


