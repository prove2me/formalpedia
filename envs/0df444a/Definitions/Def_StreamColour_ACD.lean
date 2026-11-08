-- Prove2me | Definitions.Def_StreamColour_ACD
-- name    : StreamColour_ACD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:51.341184+00:00
-- url     : https://prove2.me/theorems/e2287d29-5373-44de-b940-651e336031bd
-- title:
--   Definition 5.1 — the $(\eta,\varepsilon)$-almost-clique decomposition
-- statement:
--   For positive constants $\eta,\varepsilon$, an $(\eta,\varepsilon)$-almost-clique decomposition of $G$ relative to the degree bound $\Delta$ is a partition $V(G)=S_0\sqcup C_1\sqcup\dots\sqcup C_t$ with:
--
--   1. every $v\in S_0$ satisfies $\zeta_G(v)\ge\eta\varepsilon^2\Delta$, where $\zeta_G(v)=\bigl(\binom\Delta2-e(G[N(v)])\bigr)/\Delta$;
--   2. each $C_i$ has size $(1-\varepsilon/2)\Delta\le|C_i|\le(1+\varepsilon/2)\Delta$;
--   3. every $v\in C_i$ satisfies $a_{C_i}(v)\le\varepsilon\Delta$ and $e_{C_i}(v)\le\varepsilon\Delta$;
--   4. every $x\notin C_i$ satisfies $|C_i\setminus N(x)|\ge\varepsilon\Delta$.
--
--   **Formalization Note** A partition is a labelling $\pi:V\to\mathbb N$, with $S_0=\pi^{-1}(0)$ and $C_j=\pi^{-1}(j)$. Labels need not be consecutive, and conditions on $C_j$ are required of nonempty pieces. $\zeta_G$ is the published `DynBrooks.sparsity`, normalized by the supplied $\Delta$.
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), Definition 5.1, pp.49–50 (PDF 51–52), eq. (6), p.49

import Mathlib
import Definitions.Def_DynBrooks_Sparsity
import Definitions.Def_StreamColour_GraphQuantities

namespace StreamColour

/-! # The almost-clique decomposition

Chakraborty, Chatterjee, Kundu, Mishra (STOC 2027 submission, sha256 31a813b3…), Definition 5.1, pp.49–50
(PDF 51–52), with `ζ_G` of equation (6), p.49, which is `DynBrooks.sparsity Δ G v`: normalized by the supplied
`Δ`, so a low-degree vertex has large `ζ`.

**Formalization Note.** A partition `V = S₀ ⊔ C₁ ⊔ … ⊔ C_t` is a labelling `π : V → ℕ`, with `S₀ = π⁻¹(0)` and
`C_j = π⁻¹(j)`. Labels need not be consecutive, and a label `j ≥ 1` with empty `π⁻¹(j)` names no piece: every
condition on `C_j` is required of nonempty pieces only. The size bounds and `≤ ε Δ` are real inequalities. -/

variable {V : Type} [Fintype V]

open Classical in
/-- The set `π⁻¹(j)`: `S₀` for `j = 0`, and the piece `C_j` for `j ≥ 1`. -/
noncomputable def piece (π : V → ℕ) (j : ℕ) : Finset V := Finset.univ.filter fun v => π v = j

/-- Definition 5.1: `π` is an `(η, ε)`-almost-clique decomposition of `G` relative to `Δ`. -/
structure IsACD (η ε : ℝ) (Δ : ℕ) (G : SimpleGraph V) (π : V → ℕ) : Prop where
  /-- (i) Every `v ∈ S₀` satisfies `ζ_G(v) ≥ η ε² Δ`. -/
  sparse : ∀ v, π v = 0 → η * ε ^ 2 * (Δ : ℝ) ≤ DynBrooks.sparsity Δ G v
  /-- (ii) Each `C_i` has size `(1 − ε/2)Δ ≤ |C_i| ≤ (1 + ε/2)Δ`. -/
  size : ∀ j, 1 ≤ j → (piece π j).Nonempty →
    (1 - ε / 2) * (Δ : ℝ) ≤ ((piece π j).card : ℝ) ∧ ((piece π j).card : ℝ) ≤ (1 + ε / 2) * (Δ : ℝ)
  /-- (iii) Every `v ∈ C_i` satisfies `a_{C_i}(v) ≤ ε Δ` and `e_{C_i}(v) ≤ ε Δ`. -/
  internal : ∀ j, 1 ≤ j → ∀ v ∈ piece π j,
    (antiDeg G (piece π j) v : ℝ) ≤ ε * (Δ : ℝ) ∧ (extDeg G (piece π j) v : ℝ) ≤ ε * (Δ : ℝ)
  /-- (iv) Every `x ∉ C_i` satisfies `|C_i \ N(x)| ≥ ε Δ`. -/
  outsider : ∀ j, 1 ≤ j → (piece π j).Nonempty → ∀ x, x ∉ piece π j →
    ε * (Δ : ℝ) ≤ (missing G (piece π j) x : ℝ)

end StreamColour


