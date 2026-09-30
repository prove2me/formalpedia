-- Prove2me | Definitions.Def_JewellMRP_GainRate_PolicyIteration
-- name    : JewellMRP_GainRate_PolicyIteration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:24:50.115345+00:00
-- url     : https://prove2.me/theorems/bce8ecda-18f3-477a-8732-60acc4724c8f
-- title:
--   Value determination (13), the test quantities (D 1)-(D 2) and a run of the policy-iteration algorithm of Fig. 2
-- statement:
--   Fix a Markov-renewal program with states $1, \dots, N$, transition probabilities $p^z_{ij}$, mean sojourn times $\nu^z_i > 0$ and expected rewards $\rho^z_i$.
--
--   1. **Value determination (13).** A pair $(g, v)$, $g \in \mathbb R$, $v \in \mathbb R^N$, solves the value-determination equations of the stationary policy $z$ if $v_N = 0$ and
--   $$v_i + g\,\nu^{z(i)}_i = \rho^{z(i)}_i + \sum_{j=1}^{N} p^{z(i)}_{ij}\, v_j \qquad (i = 1, \dots, N).$$
--   2. **Test quantity (D 2)** of alternative $z$ in state $i$ with relative values $v$:
--   $$\frac{1}{\nu^z_i}\Big\{\rho^z_i + \sum_{j=1}^{N} p^z_{ij} v_j - v_i\Big\}.$$
--   3. **Schweitzer's test quantity (D 1)** with relative values $v$ and gain rate $g$:
--   $$\rho^z_i + \sum_{j=1}^{N} p^z_{ij} v_j - g\,\nu^z_i.$$
--   4. **Improvement step (Fig. 2).** A policy $z'$ is an improvement step of $z$ with respect to $v$ if, in every state $i$, $z'(i)$ maximizes the test quantity (D 2) over all alternatives, and $z'(i) = z(i)$ whenever $z(i)$ already attains that maximum ("if there is no improvement in the test quantity from the last cycle, retain the same alternative"). No particular maximizer is chosen.
--   5. **Run of the algorithm.** Sequences $z_k$ of policies, $g_k \in \mathbb R$ and $v_k \in \mathbb R^N$ ($k = 0, 1, 2, \dots$) such that $(g_k, v_k)$ solves (13) for $z_k$ and $z_{k+1}$ is an improvement step of $z_k$ with respect to $v_k$, for every $k$.
--
--   These are the ingredients of the flow chart of Fig. 2, whose claim is that every run stops at a policy of maximal gain rate.
--
--   **Formalization Note** The paper writes (13) as $v_i + g\nu_i = \rho_i + \sum_{j=1}^{N-1} p_{ij} v_j$ together with $v_N = 0$; because $v_N = 0$ the sum over $j \le N-1$ equals the sum over all $j$, which is the form used here. The last state $N$ is `lastState N`, index $N-1$ of `Fin N`, which requires $N \ge 1$ (`NeZero N`). A run starts from an arbitrary initial policy $z_0$ (the "Guess an initial policy" entry of Fig. 2; the "Guess an initial set of returns" entry is a run from $z_1$) and continues constantly after termination, since the retain-on-tie rule reproduces the terminal policy.
-- source:
--   Jewell, Markov-Renewal Programming. II: Infinite Return Models, Example, Oper. Res. 11 (1963), p. 955 Eq. (13), p. 956 Fig. 2, pp. 969-970 Eqs. (D 1), (D 2)

import Mathlib
import Definitions.Def_JewellMRP_GainRate_MRP

namespace JewellMRP.GainRate

variable {N : ℕ} {α : Type*}

/-- The distinguished last state `N` (index `N - 1` in `Fin N`), whose relative value is set
to zero in (13). -/
def lastState (N : ℕ) [NeZero N] : Fin N :=
  ⟨N - 1, Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne N)) Nat.one_pos⟩

/-- The value-determination equations (13) of policy `z` (p. 955 and Fig. 2):
`v_i + g ν_i = ρ_i + ∑_j p_{ij} v_j` for every state `i`, with `v_N = 0`. -/
def MRP.SolvesValueDetermination [NeZero N] (M : MRP N α) (z : Fin N → α) (g : ℝ)
    (v : Fin N → ℝ) : Prop :=
  v (lastState N) = 0 ∧
    ∀ i, v i + g * M.ν i (z i) = M.ρ i (z i) + ∑ j, M.p i (z i) j * v j

/-- The test quantity of Fig. 2 / (D 2) for alternative `a` in state `i`, using relative
values `v`: `(1/ν^a_i) {ρ^a_i + ∑_j p^a_{ij} v_j − v_i}`. -/
noncomputable def MRP.testQuantity (M : MRP N α) (v : Fin N → ℝ) (i : Fin N) (a : α) : ℝ :=
  (1 / M.ν i a) * (M.ρ i a + ∑ j, M.p i a j * v j - v i)

/-- Schweitzer's test quantity (D 1) for alternative `a` in state `i`, using relative values
`v` and gain rate `g` of the present policy: `ρ^a_i + ∑_j p^a_{ij} v_j − g ν^a_i`. -/
noncomputable def MRP.schweitzerTestQuantity (M : MRP N α) (g : ℝ) (v : Fin N → ℝ)
    (i : Fin N) (a : α) : ℝ :=
  M.ρ i a + ∑ j, M.p i a j * v j - g * M.ν i a

/-- One policy-improvement step of Fig. 2: `z'` is obtained from `z` using the relative
values `v` of `z` if, in every state `i`, `z' i` maximizes the test quantity, and `z' i = z i`
whenever the present alternative `z i` already attains the maximum (no improvement:
retain the same alternative). -/
def MRP.IsImprovementStep (M : MRP N α) (z : Fin N → α) (v : Fin N → ℝ)
    (z' : Fin N → α) : Prop :=
  ∀ i, (∀ a, M.testQuantity v i a ≤ M.testQuantity v i (z' i)) ∧
    ((∀ a, M.testQuantity v i a ≤ M.testQuantity v i (z i)) → z' i = z i)

/-- A run of the algorithm of Fig. 2: a sequence of policies `z k` with, for each `k`,
the solution `(g k, v k)` of the value-determination equations (13) for `z k`, and `z (k+1)`
an improvement step of `z k` with respect to `v k`. The run continues (constantly) after
termination. -/
structure MRP.IsPolicyIterationRun [NeZero N] (M : MRP N α) (z : ℕ → Fin N → α) (g : ℕ → ℝ)
    (v : ℕ → Fin N → ℝ) : Prop where
  value : ∀ k, M.SolvesValueDetermination (z k) (g k) (v k)
  improve : ∀ k, M.IsImprovementStep (z k) (v k) (z (k + 1))

end JewellMRP.GainRate


