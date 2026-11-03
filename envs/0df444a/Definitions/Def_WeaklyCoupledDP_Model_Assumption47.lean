-- Prove2me | Definitions.Def_WeaklyCoupledDP_Model_Assumption47
-- name    : WeaklyCoupledDP_Model_Assumption47
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:53.295207+00:00
-- url     : https://prove2.me/theorems/ebd5ba58-5376-420b-9a42-b46710c74f3b
-- title:
--   Assumption 4.7 — state-independent linking constraints with a totally unimodular system (12)
-- statement:
--   **Assumption 4.7.** For all periods $t$ and exogenous states $e_t$:
--
--   1. the linking vectors are independent of the subproblem states: $\ell_{t,i}(s_{t,i},e_t,a_{t,i}) = \ell_{t,i}(e_t,a_{t,i})$ for all $i$, $s_{t,i}$ and $a_{t,i}$;
--   2. $b_t(e_t)$ is integral, and the constraint matrix of the system
--   $$
--   \sum_{i=1}^N \sum_{a_{t,i} \in \bar A_{t,i}(e_t)} \ell_{t,i}(e_t,a_{t,i})\, x_{t,i}(e_t,a_{t,i}) \le b_t(e_t), \qquad (12a)
--   $$
--   $$
--   \sum_{a_{t,i} \in \bar A_{t,i}(e_t)} x_{t,i}(e_t,a_{t,i}) = 1 \quad \forall i = 1,\dots,N, \qquad (12b)
--   $$
--   in the variables $x_{t,i}(e_t,a_{t,i}) \in \{0,1\}$ is totally unimodular, where $\bar A_{t,i}(e_t) = \bigcup_{s_{t,i} \in S_{t,i}} A_{t,i}(s_{t,i},e_t)$.
--
--   The constraint matrix has one column per pair $(i, a)$ with $a \in \bar A_{t,i}(e_t)$, the $L_t$ rows of (12a) with entries $\ell_{t,i}(e_t,a)$, and the $N$ rows of (12b) with entry $1$ in the columns of subproblem $i$ and $0$ elsewhere. Action sets may still depend on the subproblem state.
--
--   **Formalization Note** The common vector $\ell_{t,i}(e_t,\cdot)$ is an existentially quantified function $\bar\ell$; clause 1 binds it only at pairs $(s,a)$ with $a$ available at $s$, because values of $\ell$ at unavailable actions are not part of the model. Total unimodularity is Mathlib's `Matrix.IsTotallyUnimodular` (every square submatrix has determinant in $\{-1,0,1\}$). The assumption is imposed for $1 \le t \le T$.
-- source:
--   Brown & Zhang, On the Strength of Relaxations of Weakly Coupled Stochastic Dynamic Programs, SSRN 3849573 (Feb. 6, 2022), Assumption 4.7, pp.15–16 (PDF pp.16–17), system (12a)–(12b)

import Mathlib
import Definitions.Def_WeaklyCoupledDP_Model

open Finset

namespace WeaklyCoupledDP

namespace Model

variable {N : ℕ} {S : ℕ → Fin N → Type*} {E : Type*} {Act : ℕ → Fin N → Type*} {L : ℕ → ℕ}
  [∀ t i, Fintype (S t i)] [Fintype E] (M : Model N S E Act L)

open Classical in
/-- `Āₜ,ᵢ(eₜ) = ⋃_{sₜ,ᵢ ∈ Sₜ,ᵢ} Aₜ,ᵢ(sₜ,ᵢ, eₜ)` (Assumption 4.7, p.16). -/
noncomputable def actionUnion (t : ℕ) (i : Fin N) (e : E) : Finset (Act t i) :=
  univ.biUnion fun s => M.A t i s e

/-- The constraint matrix of the system (12), pp.15–16, in the variables
`xₜ,ᵢ(eₜ, aₜ,ᵢ)`, `aₜ,ᵢ ∈ Āₜ,ᵢ(eₜ)`: one column per pair `(i, a)`, the `Lₜ` rows of (12a) with entries
`ℓₜ,ᵢ(eₜ, a)`, and the `N` rows of (12b) with entry `1` in the columns of subproblem `i`. -/
def constraintMatrix (t : ℕ) (e : E) (lbar : ∀ i, Act t i → Fin (L t) → ℝ) :
    Matrix (Fin (L t) ⊕ Fin N) (Σ i, {a // a ∈ M.actionUnion t i e}) ℝ :=
  Matrix.of fun r c =>
    match r with
    | Sum.inl l => lbar c.1 c.2 l
    | Sum.inr j => if j = c.1 then 1 else 0

/-- **Assumption 4.7, pp.15–16.** For all `t` and `eₜ`:
(i) the vectors `ℓₜ,ᵢ(sₜ,ᵢ, eₜ, aₜ,ᵢ) = ℓₜ,ᵢ(eₜ, aₜ,ᵢ)` are independent of `sₜ,ᵢ`; and
(ii) `bₜ(eₜ)` is integral and the constraint matrix of the system (12) is totally unimodular.

**Formalization Note.** `lbar` is the common vector `ℓₜ,ᵢ(eₜ, ·)`. Clause (i) binds it only at pairs
`(s, a)` with `a` available at `s`: the values of `ℓ` at unavailable actions are not part of the
model. Action sets may depend on `sₜ,ᵢ`. -/
def Assumption47 : Prop :=
  ∀ t, 1 ≤ t → t ≤ M.T → ∀ e : E, ∃ lbar : ∀ i, Act t i → Fin (L t) → ℝ,
    (∀ i s a, a ∈ M.A t i s e → M.ℓ t i s e a = lbar i a) ∧
    (∀ l, ∃ z : ℤ, M.b t e l = z) ∧
    (M.constraintMatrix t e lbar).IsTotallyUnimodular

end Model

end WeaklyCoupledDP


