-- Prove2me | Definitions.Def_QCollLB_OneRound
-- name    : QCollLB_OneRound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:12:23.669323+00:00
-- url     : https://prove2.me/theorems/1ec721b2-00be-4e76-a7c1-3a52c39febcc
-- title:
--   §2.5, §3.1 — one-round $t$-query algorithms with a shared phase oracle, and their success probability for $k$-collision finding
-- statement:
--   Let $[n]=\{1,\dots,n\}$ and $\mathbb Z_q=\{0,\dots,q-1\}$ with addition mod $q$, and write $\omega_q=e^{2\pi\imath/q}$. An input is a string $x\in\mathbb Z_q^n$.
--
--   **Shared parallel phase oracle.** The phase oracle is $O_x|i,c\rangle=\omega_q^{c x_i}|i,c\rangle$ for $i\in[n]$, $c\in\mathbb Z_q$. A layer of $t$ parallel queries applies $O_x^{\otimes t}$ to $t$ index registers and $t$ answer registers, **all with the same input $x$**:
--   $$
--   O_x^{\otimes t}\,|i_1,\dots,i_t,c_1,\dots,c_t\rangle=\prod_{j=1}^t\omega_q^{c_j x_{i_j}}\,|i_1,\dots,i_t,c_1,\dots,c_t\rangle .
--   $$
--
--   **One-round algorithms.** A one-round $t$-query algorithm with workspace $W=\mathbb C^b$ consists of an input-independent unit start state and input-independent unitaries $U_0,U_1$ on $A=I^{\otimes t}\otimes C^{\otimes t}\otimes W$; its final state on input $x$ is
--   $$
--   \psi'_{x,1}=U_1\,(O_x^{\otimes t}\otimes I_W)\,U_0\,|0\rangle_A .
--   $$
--   The algorithm then measures $A$ and outputs an ordered $k$-tuple of positions.
--
--   **Success.** A $k$-collision of $x$ is a set of $k$ distinct indices on which $x$ is constant. The success probability of the algorithm on $x$ is the probability that its output tuple has distinct entries and a common value of $x$.
--
--   **Formalization Note** Positions are `Fin n` (0-based) and $\mathbb Z_q$ is `ZMod q`. The algorithm is the published `QAlgorithms.QueryAlg` with one oracle layer and query register `(Fin t → Fin n) × (Fin t → ZMod q)`; $\omega_q^a$ is the published `SelectiveDPT.rootPow`. The final measurement is a computational-basis measurement of the whole register followed by an arbitrary output map; with arbitrary $U_1$ and workspace this is the same class as an arbitrary projective measurement. The success event is the published `MultiCollQ.collisionRel k 1`. `IsKCollision` is the set form of a $k$-collision (used in Claim 6.5).
-- source:
--   Peng–Wu, Quantum Lower Bounds for Collision Problems, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), §2.5 p.14, Definition 2.2 p.15, Eqs. (5)–(6) p.15, Eq. (9) p.16

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_SelectiveDPT_phaseOracle
import Definitions.Def_MultiCollQ_HasExactType
import Definitions.Def_MultiCollQ_collisionRel

namespace QCollLB

open QAlgorithms

/-- The `t`-fold phase oracle `O_x^{⊗t}` on **one shared input** `x ∈ Z_q^n` (Peng–Wu, *Quantum
Lower Bounds for Collision Problems*, arXiv:2611.01767 (PDF sha256 4e5aba34…d9fc), Eq. (5) and
Eq. (6), p.15; Eq. (9), p.16: "All `t` query pairs share this single input register"). On the basis
query record `|i_1, …, i_t, c_1, …, c_t⟩` it multiplies by `∏_j ω_q^{c_j x_{i_j}}`.

**Formalization Note.** `[n]` is `Fin n` (0-based) and `Z_q` is `ZMod q`; `ω_q^a` is
`SelectiveDPT.rootPow q a = exp(2πi·a.val/q)`. The `t` index registers and the `t` answer registers
are collected as the query register `(Fin t → Fin n) × (Fin t → ZMod q)` of
`QAlgorithms.QueryAlg`. -/
noncomputable def parPhaseOracle {n q t : ℕ} (x : Fin n → ZMod q) :
    Matrix ((Fin t → Fin n) × (Fin t → ZMod q)) ((Fin t → Fin n) × (Fin t → ZMod q)) ℂ :=
  Matrix.diagonal fun p => ∏ j, SelectiveDPT.rootPow q (p.2 j * x (p.1 j))

/-- A one-round (non-adaptive) quantum algorithm with `t` parallel queries and workspace
`W = ℂ^b`: an input-independent unit start state, input-independent unitaries `U_0, U_1`, and one
oracle layer `U_1 (O_x^{⊗t} ⊗ I_W) U_0` (arXiv:2611.01767, Eq. (6), p.15).

**Formalization Note.** This is `QAlgorithms.QueryAlg … 1` (one oracle layer) with query register
`(Fin t → Fin n) × (Fin t → ZMod q)`, run with `parPhaseOracle x`. The paper's fixed initial state
`|0⟩_A` followed by `U_0` and the platform's arbitrary unit `start` followed by `U_0` give the same
class. -/
abbrev OneRoundAlg (n q t b : ℕ) [NeZero q] :=
  QueryAlg (Fin t → Fin n) (Fin t → ZMod q) (Fin b) 1

/-- The probability that the one-round algorithm `A`, run on input `x`, outputs a `k`-collision of
`x` (arXiv:2611.01767, §2.5, p.14: "a set `S = {i_1, …, i_k} ⊆ [n]` of `k` distinct indices with
`x_{i_1} = ⋯ = x_{i_k}`"; Definition 2.2, p.15; the response probability `‖Π_ρ ψ'_{x,1}‖²`, p.15).

**Formalization Note.** The final measurement is a computational-basis measurement of the whole
register `A = I^{⊗t} ⊗ C^{⊗t} ⊗ W` followed by an arbitrary output map `out`; with arbitrary `U_1`
and workspace this is the same class as an arbitrary PVM `{Π_ρ}` (every PVM is diagonal in some
orthonormal basis, which `U_1` can rotate to the computational one). The output is an ordered
`k`-tuple `out z 0 : Fin k → Fin n`; `MultiCollQ.collisionRel k 1` requires its entries to be
distinct with a common value (the third conjunct is vacuous for one group), i.e. its underlying set
is a `k`-collision. `out` does not see `x`. -/
noncomputable def oneRoundSuccess {n q t b k : ℕ} [NeZero q] (A : OneRoundAlg n q t b)
    (out : ((Fin t → Fin n) × (Fin t → ZMod q)) × Fin b → (Fin 1 → Fin k → Fin n))
    (x : Fin n → ZMod q) : ℝ := by
  classical
  exact probEvent (A.finalState (parPhaseOracle x)) fun z => MultiCollQ.collisionRel k 1 x (out z)

/-- `ρ ⊆ [n]` is a `k`-collision of `x`: `|ρ| = k` and `x` is constant on `ρ` (arXiv:2611.01767,
§2.5, p.14), the valid outputs of Promised `k`-to-one Finding (Definition 2.2, p.15). -/
def IsKCollision {n q : ℕ} (k : ℕ) (x : Fin n → ZMod q) (ρ : Finset (Fin n)) : Prop :=
  ρ.card = k ∧ ∀ i ∈ ρ, ∀ j ∈ ρ, x i = x j

end QCollLB


