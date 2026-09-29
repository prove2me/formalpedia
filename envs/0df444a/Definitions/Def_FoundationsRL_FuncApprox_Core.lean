-- Prove2me | Definitions.Def_FoundationsRL_FuncApprox_Core
-- name    : FoundationsRL_FuncApprox_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:26:56.287992+00:00
-- url     : https://prove2.me/theorems/881b1911-5668-4374-b982-480b6467a3eb
-- title:
--   Bellman residual and Bellman rank (Definition 8)
-- statement:
--   This file defines the Bellman residual of a state-action value function under a policy,
--   and the Bellman rank of a Markov decision process (MDP) relative to a class of value
--   functions (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive
--   Decision Making*, arXiv:2312.16730v1, §7.3, Definition 8, p. 138).
--
--   Given a finite-horizon episodic MDP $M$ with horizon $H$, states $S$, actions $A$,
--   transition kernel $P$ and mean reward $R$ (as defined in the earlier `RLBasics.Core`
--   module), and a randomized non-stationary policy $\pi$, the **Bellman residual** of a
--   state-action value function $Q = (Q_h)_{h=1}^H$ at layer $h$ is
--   $$
--   E_h(\pi, Q) := \mathbb{E}^{M,\pi}\Big[Q_h(s_h,a_h) - r_h - \max_{a'} Q_{h+1}(s_{h+1},a')\Big],
--   $$
--   with the convention $Q_{H+1} \equiv 0$. Given a class $\mathcal Q$ of such value functions,
--   $M$ admits a **Bellman-rank-$\le d$ factorization** for $\mathcal Q$ if, at every layer $h$,
--   there are embeddings $X_h(\pi), W_h(Q) \in \mathbb R^d$ with
--   $E_h(\pi,Q) = \langle X_h(\pi), W_h(Q)\rangle$ for every valid policy $\pi$ and
--   $Q \in \mathcal Q$. The **Bellman rank** of $M$ relative to $\mathcal Q$ is the *least*
--   such $d$.
--
--   The file also records the elliptic norm $\|v\|^2_\Sigma = \sum_{x \in xs} \langle x,
--   v \rangle^2$ of a vector $v$ with respect to the Gram matrix $\Sigma = \sum_{x\in xs}
--   xx^\top$ built from a finite list of vectors, used later to state Lemma 30's
--   confidence-set bound without introducing matrix-inverse machinery.
--
--   Bellman rank is the structural assumption underlying the BiLinUCB algorithm
--   (`FuncApprox.BiLinUCB`) and Proposition 47's sample-complexity guarantee: it bounds the
--   number of directions in which a learner's policy can be surprised by a new state
--   distribution, generalizing the low-rank MDP model of §7.2.
--
--   **Formalization Note** The reward $r_h$ in $E_h(\pi,Q)$ is replaced by its conditional
--   mean $R_h(s,a)$, which is exact by the tower property of expectation and does not
--   restrict the model to deterministic rewards. Bellman rank is defined as the least $d$
--   admitting the factorization (an `IsLeast`), not as an unconstrained parameter, so a class
--   with no finite-dimensional factorization is excluded from having any rank at all, rather
--   than defaulting to $0$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 138, Definition 8 (Eq. 7.22, 7.24)

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core

/-!
Bellman rank (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive
Decision Making*, arXiv:2312.16730v1, §7.3, Definition 8, p. 138): the Bellman residual of a
state-action value function `Q` (a family of layer functions `Q h : S → A → ℝ`, with the
book's terminal convention `Q_{H+1} ≡ 0` imposed explicitly rather than read off `Q H`) under
a policy `π`, and the Bellman rank of an MDP `M` relative to a value-function class `𝒬` as the
*least* dimension `d` admitting the book's bilinear factorization (7.24) at every layer — an
actual rank, per the book's own "Equivalently, Bellman rank is the smallest dimension `d`
such that …", not an unconstrained parameter. Reuses `EpisodicMDP`, `Policy`, `IsPolicy`,
`stateDist` from the published `RLBasics.Core`.
-/

namespace FoundationsRL.FuncApprox

open FoundationsRL.RLBasics

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] {H : ℕ}

/-- Expectation of a state-action function `f` under the layer-`h` state-action marginal
induced by `M`, `π`, starting from `M.d1` (Foster–Rakhlin write `E^{M,π}[f(s_h,a_h)]`). -/
noncomputable def layerStateActionExp (M : EpisodicMDP S A H) (π : Policy S A H) (h : ℕ)
    (f : S → A → ℝ) : ℝ :=
  ∑ s0 : S, M.d1 s0 * ∑ s : S, stateDist M π s0 h s * ∑ a : A, π h s a * f s a

/-- The Bellman residual `E_h(π, Q) = E^{M,π}[Q_h(s_h,a_h) - r_h - max_a Q_{h+1}(s_{h+1},a)]`
(Foster–Rakhlin, p. 138, Eq. (7.22)), for a family `Q : ℕ → S → A → ℝ` of layer value
functions, with `Q_{H+1} ≡ 0` imposed at the horizon. The realized reward `r_h` is replaced by
its conditional mean `M.R h s a`: exact, not approximate, by the tower property
`E[r_h ∣ s_h,a_h] = M.R h s_h a_h`, regardless of whether the reward itself is random. -/
noncomputable def bellmanResidual (M : EpisodicMDP S A H) (π : Policy S A H) (h : ℕ)
    (Q : ℕ → S → A → ℝ) : ℝ :=
  layerStateActionExp M π h
    (fun s a => Q h s a -
      (M.R h s a + ∑ s' : S, M.P h s a s' * (if h + 1 < H then ⨆ a' : A, Q (h + 1) s' a' else 0)))

/-- `M` admits a Bellman-rank-`≤ d` bilinear factorization for the value-function class `𝒬`
(Foster–Rakhlin, p. 138: "Equivalently, Bellman rank is the smallest dimension `d` such that
for all `h`, there exist embeddings `X^M_h(π), W^M_h(Q) ∈ ℝ^d` such that …"): at every layer
`h < H`, the residual `E_h(π, Q)` factors as `⟨X_h(π), W_h(Q)⟩` for embeddings into `ℝ^d`. -/
def HasBellmanRankLE (M : EpisodicMDP S A H) (𝒬 : Set (ℕ → S → A → ℝ)) (d : ℕ) : Prop :=
  ∃ (X : Policy S A H → ℕ → Fin d → ℝ) (W : (ℕ → S → A → ℝ) → ℕ → Fin d → ℝ),
    ∀ π : Policy S A H, IsPolicy H π → ∀ Q ∈ 𝒬, ∀ h : ℕ, h < H →
      bellmanResidual M π h Q = ∑ j : Fin d, X π h j * W Q h j

/-- `M` has Bellman rank exactly `d` relative to `𝒬` (Definition 8, p. 138): `d` is the
*least* natural number admitting a `HasBellmanRankLE` factorization. -/
def IsBellmanRank (M : EpisodicMDP S A H) (𝒬 : Set (ℕ → S → A → ℝ)) (d : ℕ) : Prop :=
  IsLeast {d' : ℕ | HasBellmanRankLE M 𝒬 d'} d

/-- The squared elliptic norm `‖v‖²_Σ` of `v ∈ ℝ^d` with respect to the Gram matrix
`Σ = ∑_{x ∈ xs} x xᵀ` built from a list of vectors `xs`, expressed via the standard identity
`‖v‖²_Σ = ∑_{x ∈ xs} ⟨x, v⟩²` — this is the quantity `Σ^k_h` is built from throughout §7.3.2
(Lemma 30, Lemma 31), without introducing `Matrix`/matrix-inverse machinery. -/
def elliptNormSq {d : ℕ} (xs : List (Fin d → ℝ)) (v : Fin d → ℝ) : ℝ :=
  (xs.map (fun x => (∑ j : Fin d, x j * v j) ^ 2)).sum

end FoundationsRL.FuncApprox


