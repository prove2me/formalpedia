-- Prove2me | Definitions.Def_IsingLTL_BeliefProp_BPIteration
-- name    : IsingLTL_BeliefProp_BPIteration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:16.35595+00:00
-- url     : https://prove2.me/theorems/430cc904-2610-460f-8b09-86bff55c9b67
-- title:
--   Belief propagation messages, positive initial conditions, and the BP iteration (2.10)
-- statement:
--   Let $G=(V,E)$ be a finite graph. A **message family** associates to each directed edge $i\to j$ (with $(i,j)\in E$) a distribution $\nu_{i\to j}(x_i)$ over $x_i\in\{+1,-1\}$. It is **positive** if $\nu_{i\to j}(+1)\ge\nu_{i\to j}(-1)$ for every directed edge.
--
--   For $\beta\in\mathbb R$ and a constant field $B\in\mathbb R$, the **belief propagation (BP) iteration** updates the messages by
--   $$\nu^{(t+1)}_{i\to j}(x_i)=\frac1{z^{(t)}_{i\to j}}\,e^{Bx_i}\prod_{l\in\partial i\setminus j}\ \sum_{x_l}e^{\beta x_ix_l}\,\nu^{(t)}_{l\to i}(x_l),$$
--   where $\partial i$ is the set of neighbours of $i$, an empty product equals $1$, and $z^{(t)}_{i\to j}$ makes the right-hand side a distribution on $\{+1,-1\}$. The iterates are $\nu^{(t)}=\mathrm{BP}^t(\nu^{(0)})$, and a **fixed point** is a message family $\nu^*$ with $\mathrm{BP}(\nu^*)=\nu^*$.
--
--   These are the objects of Theorem 2.6 (exponential convergence of BP) and Theorem 2.7 (BP approximation of local marginals).
--
--   **Formalization Note** Messages are stored as $\nu\,i\,j:\{+1,-1\}\to\mathbb R$ for all pairs; only directed edges matter, and one BP step outputs $0$ on non-adjacent pairs. When the incoming messages are distributions, $z>0$.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, §2.3, p. 7, eq. (2.10) and the definition of a positive initial condition

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_IsingModel

namespace IsingLTL.BeliefProp

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A **message family** on the finite graph `G` (Dembo–Montanari, arXiv:0804.4726v3, §2.3,
p. 7): to each directed edge `i → j` (`G.Adj i j`) a distribution `ν_{i→j}` on `x_i ∈ {+1, −1}`.
Messages are stored as `ν i j : Bool → ℝ` (`true` = `+1`); the values on non-adjacent pairs are
not constrained and play no role. -/
def IsMsgFamily (G : SimpleGraph V) (ν : V → V → Bool → ℝ) : Prop :=
  ∀ i j, G.Adj i j → IsDistribution (ν i j)

/-- A message family is **positive** (arXiv:0804.4726v3, p. 7) if
`ν_{i→j}(+1) ≥ ν_{i→j}(−1)` for every directed edge `i → j`. -/
def IsPositiveMsg (G : SimpleGraph V) (ν : V → V → Bool → ℝ) : Prop :=
  ∀ i j, G.Adj i j → ν i j false ≤ ν i j true

/-- The unnormalized right-hand side of the BP update (2.10) (arXiv:0804.4726v3, p. 7):
`e^{B x_i} ∏_{l ∈ ∂i \ j} ∑_{x_l} e^{β x_i x_l} ν_{l→i}(x_l)` (an empty product is `1`). -/
noncomputable def bpUnnorm (G : SimpleGraph V) [DecidableRel G.Adj] (β B : ℝ)
    (ν : V → V → Bool → ℝ) (i j : V) (xi : Bool) : ℝ :=
  Real.exp (B * spin xi) *
    ∏ l ∈ (G.neighborFinset i).erase j,
      ∑ xl : Bool, Real.exp (β * spin xi * spin xl) * ν l i xl

/-- One step of the **belief propagation iteration** (2.10) with constant field `B`
(arXiv:0804.4726v3, p. 7):
`ν^{(t+1)}_{i→j}(x_i) = (1/z^{(t)}_{i→j}) e^{B x_i} ∏_{l∈∂i\j} ∑_{x_l} e^{β x_i x_l} ν^{(t)}_{l→i}(x_l)`,
`z^{(t)}_{i→j}` being the normalization making the right side a distribution on `{+1, −1}`.
On non-adjacent pairs the output is `0`.

Formalization Note: when the incoming messages are distributions, `z > 0`, so the division is
never by zero along the iteration. -/
noncomputable def bp (G : SimpleGraph V) [DecidableRel G.Adj] (β B : ℝ)
    (ν : V → V → Bool → ℝ) : V → V → Bool → ℝ :=
  fun i j xi =>
    if G.Adj i j then
      bpUnnorm G β B ν i j xi / (bpUnnorm G β B ν i j true + bpUnnorm G β B ν i j false)
    else 0

/-- The BP iterates `ν^{(t)} = bp^t ν^{(0)}` (arXiv:0804.4726v3, (2.10), p. 7). -/
noncomputable def bpIter (G : SimpleGraph V) [DecidableRel G.Adj] (β B : ℝ) (t : ℕ)
    (ν0 : V → V → Bool → ℝ) : V → V → Bool → ℝ :=
  (bp G β B)^[t] ν0

end IsingLTL.BeliefProp


