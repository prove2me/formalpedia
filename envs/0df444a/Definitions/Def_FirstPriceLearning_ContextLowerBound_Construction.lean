-- Prove2me | Definitions.Def_FirstPriceLearning_ContextLowerBound_Construction
-- name    : FirstPriceLearning_ContextLowerBound_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:14.423704+00:00
-- url     : https://prove2.me/theorems/af9bfb89-7ece-4021-95ca-232abddef6b4
-- title:
--   The hard instances of Theorem 6: graph $G$, Bernoulli laws $P^u$, block contexts
-- statement:
--   This file defines the instances used in the proof of Theorem 6.
--
--   Fix $\alpha\ge1$, $M\ge1$ and a horizon $T$, and let $K=(\alpha+1)M$. The action set is
--   $$\mathcal A=\{(i,j): i\in[M],\ j\in\{0,1,\dots,\alpha\}\},$$
--   and the feedback graph $G$ has the edges $(i_1,j_1)\to(i_2,j_2)$ for $i_1<i_2$ and $(i,j)\to(i,0)$ for $j\neq0$. Let $\Delta=\sqrt{K/(16T)}$. For $u=(u_1,\dots,u_M)\in\{0,1,\dots,\alpha\}^M$ and a context $c\in[M]$ the mean rewards are
--   $$R^u_{c,(i,j)}=\begin{cases}\tfrac14+\Delta & i=c,\ j=0,\\ \tfrac14+2\Delta & i=c,\ j\neq0,\ u_c=j,\\ \tfrac14 & i=c,\ j\neq0,\ u_c\neq j,\\ 0 & i\neq c,\end{cases}$$
--   and the reward law is the product of independent Bernoulli laws $P^u=\prod_{c,a}\mathrm{Bern}(R^u_{c,a})$. The *observed reward distribution* $P^u(i,j)$ is the law under $P^u$ of the rewards revealed when $(i,j)$ is chosen, namely of $(r_{c,b})_{c\in[M],\,b\in I}$ with $I=\{(i,j)\}$ together with the out-neighbours of $(i,j)$.
--
--   When $M$ divides $T$, the horizon is split into $M$ consecutive blocks of length $T/M$, and in the $m$-th block the context is $c_m=M+1-m$, so contexts decrease over time. Finally, for a policy $\pi$, $R_T$ denotes the largest expected regret of $\pi$ against this context sequence over the $(\alpha+1)^M$ laws $P^u$.
--
--   **Formalization Note.** Actions are `Fin M × Fin (α + 1)`; paper $i$ and $c$ are Lean index $+1$, paper $j$ is the same value. Round $t$ (Lean, $0$-based) lies in block $\lfloor t/(T/M)\rfloor$ ($0$-based), with Lean context $M-1-\lfloor t/(T/M)\rfloor$. The Bernoulli law is $(1-p)\delta_0+p\delta_1$, which is a probability measure for $p\in[0,1]$, i.e. whenever $K\le T$. The observed law is the image of $P^u$ under the map that sets every unrevealed coordinate to $0$. The maximum over the finitely many $u$ is a supremum over a finite nonempty index set.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 22 (action space, graph G, P^u, R^u, Δ, property 5's observed distributions); pp. 22–23 (context sequence); p. 23 (R_T)

import Mathlib
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Model

open MeasureTheory

namespace FirstPriceLearning.ContextLowerBound

/-! The hard instances of the proof of Theorem 6 (p. 22): the action set
`A = {(i, j) : i ∈ [M], j ∈ [α] ∪ {0}}`, the feedback graph `G`, the gap `Δ = √(K/(16T))` with
`K = (α + 1)M`, the Bernoulli product reward laws `P^u` for `u ∈ {0, 1, …, α}^M`, the block context
sequence of pp. 22–23, and the observed reward distribution `P^u(i, j)` of property 5.

Index conventions: paper `i ∈ [M]` is Lean `i + 1 : Fin M`; paper `j ∈ {0, 1, …, α}` is Lean
`j : Fin (α + 1)` with the same value; paper context `c ∈ [M]` is Lean `c + 1`. -/

/-- The action set `A = [M] × ({0} ∪ [α])`, of cardinality `K = (α + 1)M`. -/
abbrev Act (M α : ℕ) := Fin M × Fin (α + 1)

/-- The feedback graph `G` of p. 22: the edges are all `(i₁, j₁) → (i₂, j₂)` with `i₁ < i₂`, and
`(i, j) → (i, 0)` with `j ≠ 0`. -/
def feedbackGraph (M α : ℕ) (a b : Act M α) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≠ 0 ∧ b.2 = 0)

/-- The gap `Δ := √(K / (16T))` with `K = (α + 1)M`. -/
noncomputable def gap (M α T : ℕ) : ℝ :=
  Real.sqrt ((((α + 1) * M : ℕ) : ℝ) / (16 * (T : ℝ)))

/-- The mean rewards `R^u_{c,(i,j)}` of p. 22:
`1/4 + Δ` if `i = c, j = 0`; `1/4 + 2Δ` if `i = c, j ≠ 0, u_c = j`; `1/4` if `i = c, j ≠ 0,
u_c ≠ j`; `0` if `i ≠ c`. -/
noncomputable def hardMean (M α T : ℕ) (u : Fin M → Fin (α + 1)) (c : Fin M) (a : Act M α) : ℝ :=
  if a.1 = c then
    (if a.2 = 0 then 1 / 4 + gap M α T
     else if u c = a.2 then 1 / 4 + 2 * gap M α T else 1 / 4)
  else 0

/-- The Bernoulli law `Bern(p)` on `ℝ`, i.e. `(1 − p) δ₀ + p δ₁` (a probability measure for
`p ∈ [0, 1]`). -/
noncomputable def bernoulliReal (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - p) • Measure.dirac 0 + ENNReal.ofReal p • Measure.dirac 1

/-- The reward law `P^u = ∏_{c ∈ C, a ∈ A} Bern(R^u_{c,a})`: all `M·K` coordinates are
independent Bernoulli variables. -/
noncomputable def hardLaw (M α T : ℕ) (u : Fin M → Fin (α + 1)) :
    Measure (Fin M → Act M α → ℝ) :=
  Measure.pi fun c => Measure.pi fun a => bernoulliReal (hardMean M α T u c a)

/-- The observed reward distribution `P^u(i, j)` of property 5: the law, under `P^u`, of the
rewards revealed when the action `a = (i, j)` is chosen, i.e. of `(r_{c,b})_{c ∈ C, b ∈ I}` with
`I = {a} ∪ {b : (a, b) ∈ G}` (masked vector, see `reveal`). -/
noncomputable def observedLaw (M α T : ℕ) (u : Fin M → Fin (α + 1)) (a : Act M α) :
    Measure (Fin M → Act M α → ℝ) :=
  (hardLaw M α T u).map (reveal (feedbackGraph M α) a)

/-- The block context sequence of pp. 22–23 (for `M ∣ T`): the horizon is split into `M`
consecutive blocks of size `T/M`, and during the `m`-th block the context is `c_m = M + 1 − m`.
In Lean indices, round `t` lies in block `t / (T/M)` (0-based), whose context is
`M − 1 − t / (T/M)`. Contexts decrease over time. -/
def blockContext (M T : ℕ) (hM : 0 < M) (t : Fin T) : Fin M :=
  ⟨M - 1 - t.val / (T / M), Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt hM Nat.one_pos)⟩

/-- `R_T := max_u 𝔼_u[R_T(π)]`, the largest expected regret of `π` under the reward laws `P^u`,
`u ∈ {0, 1, …, α}^M`, against the block context sequence (p. 23). -/
noncomputable def maxRegret (M α T : ℕ) (hM : 0 < M) {U : Type} [MeasurableSpace U]
    (μU : Measure U) (π : Policy M (Act M α) U) : ℝ :=
  ⨆ u : Fin M → Fin (α + 1),
    expectedRegret (feedbackGraph M α) (hardLaw M α T u) μU π (blockContext M T hM)

end FirstPriceLearning.ContextLowerBound


