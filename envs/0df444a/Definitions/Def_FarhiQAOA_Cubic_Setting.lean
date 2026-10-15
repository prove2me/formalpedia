-- Prove2me | Definitions.Def_FarhiQAOA_Cubic_Setting
-- name    : FarhiQAOA_Cubic_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:16.533979+00:00
-- url     : https://prove2.me/theorems/cd22e81d-33a9-477d-aede-97b4ba913640
-- title:
--   §I–II, eqs. (1)–(13), pp. 2–4 — MaxCut objective, QAOA state |γ,β⟩, F_p and edge terms
-- statement:
--   This file sets up the quantum approximate optimization algorithm (QAOA) for MaxCut, following §I–II of Farhi, Goldstone and Gutmann.
--
--   Let $G$ be a simple graph on the vertex set $\{0,\dots,n-1\}$. Each vertex $j$ carries one qubit, and a computational basis state is a bit string $z = z_0 z_1 \cdots z_{n-1}$ with $z_j \in \{0,1\}$.
--
--   1. **Edge clause.** For vertices $j,k$, the clause operator $C_{\langle jk\rangle} = \tfrac12(-\sigma^z_j\sigma^z_k + 1)$ of (12) is diagonal in the computational basis, with value
--   $$C_{\langle jk\rangle}(z) = \begin{cases} 1 & z_j \neq z_k,\\ 0 & z_j = z_k.\end{cases}$$
--   2. **Cut objective.** $C(z) = \sum_{\langle jk\rangle} C_{\langle jk\rangle}(z)$, the sum over the edges of $G$ (each edge once), as in (11): the number of edges cut by the bipartition that $z$ defines.
--   3. **QAOA state.** For $p \ge 1$ and angles $\boldsymbol\gamma = (\gamma_1,\dots,\gamma_p)$, $\boldsymbol\beta = (\beta_1,\dots,\beta_p)$,
--   $$|\boldsymbol\gamma,\boldsymbol\beta\rangle = U(B,\beta_p)\,U(C,\gamma_p)\cdots U(B,\beta_1)\,U(C,\gamma_1)\,|s\rangle,$$
--   where $U(C,\gamma) = e^{-i\gamma C}$ with $C$ viewed as a diagonal operator, $U(B,\beta) = e^{-i\beta B}$ with $B = \sum_j \sigma^x_j$, and $|s\rangle = 2^{-n/2}\sum_z |z\rangle$ is the uniform superposition ((2)–(6)).
--   4. **Expected cut.** $F_p(\boldsymbol\gamma,\boldsymbol\beta) = \langle\boldsymbol\gamma,\boldsymbol\beta|\,C\,|\boldsymbol\gamma,\boldsymbol\beta\rangle = \sum_z |\langle z|\boldsymbol\gamma,\boldsymbol\beta\rangle|^2\, C(z)$, as in (7).
--   5. **Edge terms.** $\langle\boldsymbol\gamma,\boldsymbol\beta|\,C_{\langle jk\rangle}\,|\boldsymbol\gamma,\boldsymbol\beta\rangle = \sum_z |\langle z|\boldsymbol\gamma,\boldsymbol\beta\rangle|^2\, C_{\langle jk\rangle}(z)$, the summands of the edge sum (13).
--   6. **The case $p = 1$.** $F_1(\gamma,\beta)$ and the corresponding edge terms, with single angles $\gamma = \gamma_1$ and $\beta = \beta_1$.
--
--   These are the objects about which every statement of this mission is made.
--
--   **Formalization Note** Bit strings are `Qubits n = Fin n → Bool`, with `true` the bit $1$. The cut counts each edge once, as an ordered pair $u < v$. Because $C$ and $C_{\langle jk\rangle}$ are diagonal, the expectation (7) equals the measurement average $\sum_z \Pr[z]\,C(z)$, which is how $F_p$ and the edge terms are defined. The state reuses the published `QAlgorithms.qaoaUnitary f p β θ`, which takes the mixer angles $\boldsymbol\beta$ first and the phase angles $\boldsymbol\theta = \boldsymbol\gamma$ second; layer $k$ in Lean is the paper's layer $k+1$.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm, arXiv:1411.4028v1, pp. 2–4, Sections I–II, (1)–(13)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Adiabatic

namespace FarhiQAOA.Cubic

open QAlgorithms

/-- Farhi–Goldstone–Gutmann p. 4, (12): the clause operator `C_⟨jk⟩ = ½(−σᶻ_j σᶻ_k + 1)` evaluated
on the computational basis state `|z⟩`. It is `1` when the bits `z_j, z_k` differ (the edge is cut)
and `0` when they agree. Since `C_⟨jk⟩` is diagonal, this is the operator itself, not an
approximation. -/
def edgeCut {n : ℕ} (j k : Fin n) (z : Qubits n) : ℝ :=
  if z j = z k then 0 else 1

/-- Farhi–Goldstone–Gutmann p. 4, (11): the MaxCut objective `C(z) = Σ_⟨jk⟩ C_⟨jk⟩(z)`, the number of
edges of `G` whose endpoints receive different bits. Each edge `⟨jk⟩` is counted once (as the
ordered pair `u < v`). Vertex `j` of the graph is qubit `j`; `z j = true` is the bit `z_j = 1`. -/
def cutValue {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (z : Qubits n) : ℝ :=
  ∑ u : Fin n, ∑ v : Fin n, if u < v ∧ G.Adj u v then edgeCut u v z else 0

/-- Farhi–Goldstone–Gutmann p. 3, (6): the angle-dependent state
`|γ, β⟩ = U(B, β_p) U(C, γ_p) ⋯ U(B, β₁) U(C, γ₁) |s⟩`, with `C` the cut objective of `G` as a
diagonal operator, `B = Σ_j σˣ_j`, and `|s⟩` the uniform superposition (5). Layer `k : Fin p` is the
paper's layer `k + 1`. The published `qaoaUnitary f p β θ` takes the mixer angles `β` first and the
phase angles `θ = γ` second. -/
noncomputable def qaoaState {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : ℕ)
    (γ β : Fin p → ℝ) : EuclideanSpace ℂ (Qubits n) :=
  act (qaoaUnitary (cutValue G) p β γ) (uniformState (Qubits n))

/-- Farhi–Goldstone–Gutmann p. 3, (7): `F_p(γ, β) = ⟨γ, β| C |γ, β⟩`. Because `C` is diagonal in the
computational basis this equals `Σ_z |⟨z|γ, β⟩|² C(z)`, the mean of `C(z)` over the outcomes of a
computational-basis measurement of `|γ, β⟩`. -/
noncomputable def expectCut {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : ℕ)
    (γ β : Fin p → ℝ) : ℝ :=
  ∑ z : Qubits n, prob (qaoaState G p γ β) z * cutValue G z

/-- Farhi–Goldstone–Gutmann p. 4, (13): the summand of the edge sum,
`⟨γ, β| C_⟨jk⟩ |γ, β⟩ = Σ_z |⟨z|γ, β⟩|² C_⟨jk⟩(z)`. -/
noncomputable def edgeTerm {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p : ℕ)
    (γ β : Fin p → ℝ) (j k : Fin n) : ℝ :=
  ∑ z : Qubits n, prob (qaoaState G p γ β) z * edgeCut j k z

/-- `F₁(γ, β)`: the case `p = 1` of `expectCut`, with the single angles `γ = γ₁`, `β = β₁`. -/
noncomputable def F1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (γ β : ℝ) : ℝ :=
  expectCut G 1 (fun _ => γ) (fun _ => β)

/-- The case `p = 1` of `edgeTerm`, with the single angles `γ = γ₁`, `β = β₁`. -/
noncomputable def edgeTerm1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (γ β : ℝ)
    (j k : Fin n) : ℝ :=
  edgeTerm G 1 (fun _ => γ) (fun _ => β) j k

end FarhiQAOA.Cubic


