-- Prove2me | Definitions.Def_LinearOptimization_MstRelaxations
-- name    : LinearOptimization_MstRelaxations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-09T15:59:45.071598+00:00
-- url     : https://prove2.me/theorems/60941af6-8e4f-44aa-b46d-6658692863b2
-- title:
--   Subtour-elimination and cutset LP relaxations $P_{sub}, P_{cut}$ of the minimum spanning tree formulations
-- statement:
--   The LP relaxations of the two minimum spanning tree formulations of Bertsimas & Tsitsiklis, §10.3 (pp. 466–467), on a finite undirected graph with $n$ nodes given as an indexed edge family:
--
--   - $P_{sub}$ requires $\sum_e x_e = n-1$, $\sum_{e \in E(S)} x_e \le |S|-1$ for every proper nonempty $S$, and $0 \le x_e \le 1$;
--   - $P_{cut}$ requires $\sum_e x_e = n-1$, $\sum_{e \in \delta(S)} x_e \ge 1$ for every proper nonempty $S$, and $0 \le x_e \le 1$.
--
--   Here $E(S)$ is the set of edges with both endpoints in $S$ and $\delta(S)$ the set of edges with exactly one endpoint in $S$. Consumed by Theorem 10.1 (formulation strength).
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, §10.3, pp. 466–467

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
LP relaxations of the minimum spanning tree formulations.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, §10.3 pp. 466–467: for an undirected graph
`G = (𝒩, ℰ)` with `|𝒩| = n`, `E(S)` the set of edges with both endpoints
in `S`, and `δ(S)` the set of edges with exactly one endpoint in `S`, the
*subtour elimination* formulation's LP relaxation `P_sub` is
`∑_{e ∈ ℰ} x_e = n − 1`, `∑_{e ∈ E(S)} x_e ≤ |S| − 1` for every proper
nonempty `S ⊂ 𝒩`, `0 ≤ x_e ≤ 1`; the *cutset* formulation's LP relaxation
`P_cut` is `∑_{e ∈ ℰ} x_e = n − 1`, `∑_{e ∈ δ(S)} x_e ≥ 1` for every
proper nonempty `S ⊂ 𝒩`, `0 ≤ x_e ≤ 1`.

Encoding: a finite undirected graph is an indexed edge family
`ends : Fin k → Fin n × Fin n` (the series' indexed-family pattern); each
`ends e` is an ORDERED representative of an unordered pair, and both
`E(S)` and `δ(S)` are orientation-symmetric, so the choice of
representative is immaterial. Used by Bertsimas & Tsitsiklis, Theorem 10.1
(`LinearOptimization.integer_program_formulation_strength`, Mission XIII).
-/

namespace LinearOptimization

/-- The subtour-elimination LP relaxation `P_sub` of the minimum spanning
tree formulation on the edge family `ends` (Bertsimas & Tsitsiklis, p. 466):
`∑ x_e = n − 1`, `∑_{e ∈ E(S)} x_e ≤ |S| − 1` for proper nonempty
`S ⊆ 𝒩`, `0 ≤ x_e ≤ 1`. -/
def mstSubtourRelaxation {n k : ℕ} (ends : Fin k → Fin n × Fin n) :
    Set (Fin k → ℝ) :=
  {x | (∑ e, x e) = (n : ℝ) - 1 ∧
    (∀ S : Finset (Fin n), S ≠ ∅ → S ≠ Finset.univ →
      ∑ e ∈ Finset.univ.filter
          (fun e => (ends e).1 ∈ S ∧ (ends e).2 ∈ S), x e ≤
        (S.card : ℝ) - 1) ∧
    ∀ e, 0 ≤ x e ∧ x e ≤ 1}

/-- The cutset LP relaxation `P_cut` of the minimum spanning tree
formulation on the edge family `ends` (Bertsimas & Tsitsiklis, pp. 466–467): `∑ x_e = n − 1`,
`∑_{e ∈ δ(S)} x_e ≥ 1` for proper nonempty `S ⊆ 𝒩`, `0 ≤ x_e ≤ 1`. -/
def mstCutsetRelaxation {n k : ℕ} (ends : Fin k → Fin n × Fin n) :
    Set (Fin k → ℝ) :=
  {x | (∑ e, x e) = (n : ℝ) - 1 ∧
    (∀ S : Finset (Fin n), S ≠ ∅ → S ≠ Finset.univ →
      1 ≤ ∑ e ∈ Finset.univ.filter
          (fun e => ((ends e).1 ∈ S ∧ (ends e).2 ∉ S) ∨
            ((ends e).1 ∉ S ∧ (ends e).2 ∈ S)), x e) ∧
    ∀ e, 0 ≤ x e ∧ x e ≤ 1}

end LinearOptimization


