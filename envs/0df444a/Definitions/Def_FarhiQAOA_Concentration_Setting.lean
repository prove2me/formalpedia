-- Prove2me | Definitions.Def_FarhiQAOA_Concentration_Setting
-- name    : FarhiQAOA_Concentration_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:30.230441+00:00
-- url     : https://prove2.me/theorems/a68dd5b1-1553-48dd-a5ef-02b102f80d82
-- title:
--   §I–III, eqs. (1)–(17), (27)–(28), pp. 2–7 — MaxCut objective, QAOA state |γ,β⟩, F_p, edge covariances, light cones g(j,k)
-- statement:
--   This file fixes the objects of the MaxCut instance of the Quantum Approximate Optimization Algorithm (QAOA) of Farhi, Goldstone and Gutmann.
--
--   Let $G$ be a simple graph on the vertex set $\{0,\dots,n-1\}$; its vertices are the $n$ qubits, and a computational basis state is a bit string $z = z_0 z_1 \cdots z_{n-1} \in \{0,1\}^n$. The edge set $\{\langle jk\rangle\}$ lists every edge once (as the pair $j<k$); its size is $m$.
--
--   1. **Clause operators.** For qubits $j,k$ the operator $C_{\langle jk\rangle} = \tfrac12(-\sigma^z_j\sigma^z_k + 1)$ of eq. (12) is diagonal in the computational basis, with eigenvalue
--   $$C_{\langle jk\rangle}(z) = \begin{cases} 1 & z_j \ne z_k,\\ 0 & z_j = z_k.\end{cases}$$
--   2. **Objective.** $C(z) = \sum_{\langle jk\rangle} C_{\langle jk\rangle}(z)$ (eq. (11)) is the number of edges cut by $z$; as an operator it is the diagonal matrix $\sum_z C(z)\,|z\rangle\langle z|$.
--   3. **QAOA state.** For $p \ge 0$ and angles $\boldsymbol\gamma = (\gamma_1,\dots,\gamma_p)$, $\boldsymbol\beta = (\beta_1,\dots,\beta_p) \in \mathbb R^p$,
--   $$|\boldsymbol\gamma,\boldsymbol\beta\rangle = U(B,\beta_p)\,U(C,\gamma_p)\cdots U(B,\beta_1)\,U(C,\gamma_1)\,|s\rangle,$$
--   where $U(C,\gamma) = e^{-i\gamma C}$, $U(B,\beta) = e^{-i\beta B}$ with $B = \sum_j \sigma^x_j$, and $|s\rangle = 2^{-n/2}\sum_z |z\rangle$ (eqs. (2)–(6)).
--   4. **Expectations.** With $P(z) = |\langle z|\boldsymbol\gamma,\boldsymbol\beta\rangle|^2$ the probability of measuring $z$,
--   $$F_p(\boldsymbol\gamma,\boldsymbol\beta) = \sum_z P(z)\,C(z), \qquad \langle C_{\langle jk\rangle}\rangle = \sum_z P(z)\,C_{\langle jk\rangle}(z),$$
--   $$\operatorname{Var}(C) = \sum_z P(z)\,C(z)^2 - F_p(\boldsymbol\gamma,\boldsymbol\beta)^2 \quad\text{(eq. (27))},$$
--   and for two edges the summand of eq. (28),
--   $$\operatorname{Cov}(\langle jk\rangle,\langle j'k'\rangle) = \sum_z P(z)\,C_{\langle jk\rangle}(z)\,C_{\langle j'k'\rangle}(z) - \langle C_{\langle jk\rangle}\rangle\,\langle C_{\langle j'k'\rangle}\rangle .$$
--   5. **Light cone.** The qubit set of the subgraph $g(j,k)$ is
--   $$g(j,k) = \{\, u : d_G(u,j) \le p \text{ or } d_G(u,k) \le p \,\},$$
--   where $d_G$ is the graph distance ($+\infty$ between different connected components).
--
--   These are the objects of the concentration estimate of Section III: the variance of the cut value in the QAOA state and its decomposition into edge covariances.
--
--   **Formalization Note** The clause indicator, objective, QAOA state, mean and edge term (`edgeCut`, `cutValue`, `qaoaState`, `expectCut`, `edgeTerm`) are taken from the shared setting `FarhiQAOA.Cubic.Setting`; this file adds `edgePairs`, `cutVariance`, `edgePairTerm`, `edgeCov` and `lightCone`. The published `QAlgorithms` layer supplies `Qubits n` (bit strings `Fin n → Bool`, with `true` the bit 1), `prob`, `uniformState`, `problemHamiltonian` and `qaoaUnitary`. `qaoaUnitary f p β θ` takes the mixer angles first and the phase angles second, so $|\boldsymbol\gamma,\boldsymbol\beta\rangle$ is `act (qaoaUnitary (cutValue G) p β γ) (uniformState (Qubits n))`; layer `k : Fin p` is the paper's layer $k+1$. Because $C$ and $C_{\langle jk\rangle}$ are diagonal, $\langle\boldsymbol\gamma,\boldsymbol\beta|C|\boldsymbol\gamma,\boldsymbol\beta\rangle = \sum_z P(z)C(z)$ exactly, and likewise for $C^2$ and $C_{\langle jk\rangle}C_{\langle j'k'\rangle}$; these sums are used as the definitions. Edges are the ordered pairs $(j,k)$ with $j<k$ and $G$-adjacent, so each edge is counted once. The distance is Mathlib's extended distance `SimpleGraph.edist`, not `SimpleGraph.dist` (which is 0 between components).
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm, arXiv:1411.4028v1, pp. 2–7, Sections I–III, (1)–(8), (11)–(17), (27)–(28)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_FarhiQAOA_Cubic_Setting

namespace FarhiQAOA.Concentration

open QAlgorithms

/-- The edge set `{⟨jk⟩}` of the instance graph, each edge listed once as the ordered pair
`(j, k)` with `j < k`. Its cardinality is the paper's `m`. -/
def edgePairs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun e => e.1 < e.2 ∧ G.Adj e.1 e.2

/-- p. 7, (27): the variance `⟨γ, β| C² |γ, β⟩ − ⟨γ, β| C |γ, β⟩²` of `C` in the state `|γ, β⟩`,
written as `Σ_z |⟨z|γ, β⟩|² C(z)² − (Σ_z |⟨z|γ, β⟩|² C(z))²` (both terms in the same state). -/
noncomputable def cutVariance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : ℕ)
    (γ β : Fin p → ℝ) : ℝ :=
  ∑ z, prob (FarhiQAOA.Cubic.qaoaState G p γ β) z * FarhiQAOA.Cubic.cutValue G z ^ 2 - FarhiQAOA.Cubic.expectCut G p γ β ^ 2

/-- p. 7, (28), first term of the summand: `⟨γ, β| C_⟨jk⟩ C_⟨j′k′⟩ |γ, β⟩`. -/
noncomputable def edgePairTerm {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : ℕ)
    (γ β : Fin p → ℝ) (j k j' k' : Fin n) : ℝ :=
  ∑ z, prob (FarhiQAOA.Cubic.qaoaState G p γ β) z * (FarhiQAOA.Cubic.edgeCut j k z * FarhiQAOA.Cubic.edgeCut j' k' z)

/-- p. 7, (28): the summand
`⟨γ, β| C_⟨jk⟩ C_⟨j′k′⟩ |γ, β⟩ − ⟨γ, β| C_⟨jk⟩ |γ, β⟩ · ⟨γ, β| C_⟨j′k′⟩ |γ, β⟩`. -/
noncomputable def edgeCov {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : ℕ)
    (γ β : Fin p → ℝ) (j k j' k' : Fin n) : ℝ :=
  edgePairTerm G p γ β j k j' k' - FarhiQAOA.Cubic.edgeTerm G p γ β j k * FarhiQAOA.Cubic.edgeTerm G p γ β j' k'

/-- pp. 4–5, after (14) and (17): the qubits of the subgraph `g(j, k)`, i.e. `j`, `k` and every
qubit whose graph distance from `j` or from `k` is at most `p`. The distance is the extended
distance `G.edist` (`⊤` between different components). -/
noncomputable def lightCone {n : ℕ} (G : SimpleGraph (Fin n)) (p : ℕ) (j k : Fin n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun u => G.edist u j ≤ (p : ℕ∞) ∨ G.edist u k ≤ (p : ℕ∞)

end FarhiQAOA.Concentration


