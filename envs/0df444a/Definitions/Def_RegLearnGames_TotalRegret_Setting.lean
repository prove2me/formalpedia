-- Prove2me | Definitions.Def_RegLearnGames_TotalRegret_Setting
-- name    : RegLearnGames_TotalRegret_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:29.525055+00:00
-- url     : https://prove2.me/theorems/ca77a916-795d-4a8f-8f90-31d601e99808
-- title:
--   §2–§3.1.2, pp. 2–5; supp. p. 3 — repeated n-player game, utility vectors, ℓ₁/ℓ∞, strongly convex regularizers, optimistic FTRL, leader sequence, smoothness
-- statement:
--   This file fixes the model of Syrgkanis, Agarwal, Luo and Schapire (§2, pp. 2–3) and the objects of its analysis of optimistic follow the regularized leader.
--
--   1. **The game.** There are $n$ players, indexed $i \in \{0,\dots,n-1\}$, each with the same finite strategy set $S_i = \{0,\dots,d-1\}$ of cardinality $d$. A pure profile is $s = (s_1,\dots,s_n)$ and player $i$'s utility is $u_i(s)$; the statements that use the game assume $u_i(s) \in [0,1]$. A mixed strategy is a point of the probability simplex $\Delta = \Delta(S_i) = \{w \in \mathbb R^d : w_x \ge 0,\ \sum_x w_x = 1\}$ and a mixed profile is $w = (w_1,\dots,w_n)$ with every $w_i \in \Delta$; expectations $\mathbb E_{s\sim w}$ are under the product distribution, using the published vocabulary `agt_games`.
--   2. **Utility vectors.** For a mixed profile $w$ and a player $i$, the utility vector $u_i(w) \in \mathbb R^d$ has entries
--   $$u_{i,x}(w) = \mathbb E_{s_{-i}\sim w_{-i}}\big[u_i(x, s_{-i})\big], \qquad x \in S_i,$$
--   the expected utility of playing the pure strategy $x$ while the others play $w_{-i}$ independently. In the repeated game, $u_i^t = u_i(w^t)$.
--   3. **Norms.** $\|v\| = \|v\|_1 = \sum_x |v_x|$ is the primal norm; its dual norm $\|v\|_* = \sup_{\|y\|_1 \le 1}\langle y, v\rangle$ is $\|v\|_\infty = \max_x |v_x|$. Inner products are $\langle a, b\rangle = \sum_x a_x b_x$.
--   4. **Regularizers.** A function $\mathcal R : \mathbb R^d \to \mathbb R$ is *1-strongly convex* (footnote 3, p. 4, with respect to $\|\cdot\|_1$ on $\Delta$) if it is continuous on $\Delta$ and
--   $$\mathcal R\Big(\frac{a+b}{2}\Big) \le \frac{\mathcal R(a) + \mathcal R(b)}{2} - \frac{\|a-b\|_1^2}{8} \qquad \text{for all } a, b \in \Delta.$$
--   5. **Optimistic FTRL** (§3.1.2, p. 5). Given a regularizer $\mathcal R$, a step size $\eta$, a utility sequence $u^1, u^2, \dots$ and a predictor sequence $M^1, M^2, \dots$ in $\mathbb R^d$, a sequence $w^0, w^1, \dots$ is a run of OFTRL if $w^0$ minimizes $\mathcal R$ over $\Delta$ and, for every $T \ge 1$,
--   $$w^T \in \operatorname*{argmax}_{w \in \Delta}\ \Big\langle w, \sum_{t=1}^{T-1} u^t + M^T \Big\rangle - \frac{\mathcal R(w)}{\eta}.$$
--   6. **Leader sequence** (supp. p. 3). A sequence $g^0, g^1, \dots$ is a leader sequence if, for every $T \ge 0$, $g^T \in \operatorname{argmax}_{g\in\Delta} \langle g, \sum_{t=1}^T u^t\rangle - \mathcal R(g)/\eta$.
--   7. **OFTRL dynamics.** A joint trajectory $w^0, w^1, \dots$ of mixed profiles is produced by every player running OFTRL with one-step recency bias if, for each player $i$, the sequence $(w_i^t)_t$ is a run of OFTRL with player $i$'s own regularizer $\mathcal R_i$, step size $\eta$, utilities $u_i^t = u_i(w^t)$ and predictors $M_i^T = u_i^{T-1}$; in particular $M_i^1 = u_i^0$ is the utility vector against $w^0_{-i}$.
--   8. **Welfare and smoothness** (p. 3). The welfare of a pure profile is $W(s) = \sum_i u_i(s)$, of a mixed profile $W(w) = \mathbb E_{s\sim w}[W(s)] = \sum_i \mathbb E_{s \sim w}[u_i(s)]$, and $\mathrm{OPT} = \max_s W(s)$. The game is $(\lambda,\mu)$-smooth (Definition 1) if there is a pure profile $s^*$ such that $\sum_i u_i(s_i^*, s_{-i}) \ge \lambda\,\mathrm{OPT} - \mu W(s)$ for every pure profile $s$.
--
--   These are the shared objects of every statement of the mission: the regret of player $i$ after $T$ rounds is $r_i(T) = \sup_{w^* \in \Delta}\sum_{t=1}^T\langle w^* - w_i^t, u_i^t\rangle$, and the theorems bound it by stating the inequality for every comparator $w^* \in \Delta$.
--
--   **Formalization Note** Players and strategies are `Fin n` and `Fin d` (0-based); time keeps the paper's indices ($t = 1,\dots,T$, with $w^0$ and $u^0$). $\|\cdot\|_*$ is Mathlib's sup norm on `Fin d → ℝ`. Continuity of $\mathcal R$ on $\Delta$ is added to footnote 3: it makes the midpoint form equivalent to the standard modulus-1 strong convexity that the appendix proofs use, and every regularizer the paper has in mind is continuous. OFTRL and the leader are predicates on a trajectory (any maximizer counts), not chosen maximizers. OPT is the maximum over the nonempty finite set of pure profiles (an instance argument `Nonempty (Fin n → Fin d)`).
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, pp. 2–5: §2 (model, regret, W, OPT, Definition 1), Definition 3 footnote 1, footnotes 2–3 (p. 4), §3.1.2 (OFTRL, p. 5); supp. p. 3 (PDF p. 12), App. C (leader sequence)

import Mathlib
import Definitions.Def_agt_games

namespace RegLearnGames.TotalRegret

open Finset

/-- The `ℓ₁` norm `‖v‖₁ = ∑ₓ |vₓ|` of a vector of `ℝ^d`; the paper's primal norm `‖·‖`.
Its dual `‖·‖_*` (footnote 1, p. 3) is the `ℓ∞` norm, which is Mathlib's default norm `‖v‖`
on `Fin d → ℝ`. -/
def l1 {d : ℕ} (v : Fin d → ℝ) : ℝ := ∑ x, |v x|

/-- The utility vector `uᵢ(w) = (𝔼_{s₋ᵢ ∼ w₋ᵢ}[uᵢ(x, s₋ᵢ)])ₓ` of player `i` against the mixed
profile `w` (§2, p. 2): its `x`-th entry is player `i`'s expected utility when `i` plays the pure
strategy `x` and every other player `j` plays `w j` independently. -/
def utilVec {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ) (w : Fin n → Fin d → ℝ) (i : Fin n) :
    Fin d → ℝ :=
  fun x => AGT.expectedPayoff (S := fun _ : Fin n => Fin d) u
    (Function.update w i (Pi.single x 1)) i

/-- A regularizer `𝓡` on the simplex `Δ = Δ(Fin d)` is **1-strongly convex with respect to
`‖·‖₁`** in the midpoint form of footnote 3, p. 4:
`𝓡((a+b)/2) ≤ (𝓡(a)+𝓡(b))/2 − ‖a−b‖₁²/8` for all `a, b ∈ Δ`, and continuous on `Δ`
(continuity is the disclosed addition that makes the midpoint form equivalent to the standard one). -/
def IsOneStronglyConvexL1 {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) : Prop :=
  ContinuousOn 𝓡 (stdSimplex ℝ (Fin d)) ∧
    ∀ a ∈ stdSimplex ℝ (Fin d), ∀ b ∈ stdSimplex ℝ (Fin d),
      𝓡 ((1 / 2 : ℝ) • (a + b)) ≤ (𝓡 a + 𝓡 b) / 2 - (l1 (a - b)) ^ 2 / 8

/-- `w` is a run of **optimistic FTRL** (§3.1.2, p. 5) with regularizer `𝓡`, step size `η`,
predictor sequence `M` and utility sequence `u` (indices `1, 2, …`): `w 0` minimizes `𝓡` over `Δ`,
and for every `T ≥ 1`, `w T` maximizes `⟨v, ∑_{t=1}^{T-1} u t + M T⟩ − 𝓡(v)/η` over `v ∈ Δ`. -/
def IsOFTRL {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η : ℝ) (M u w : ℕ → Fin d → ℝ) : Prop :=
  (w 0 ∈ stdSimplex ℝ (Fin d) ∧ ∀ v ∈ stdSimplex ℝ (Fin d), 𝓡 (w 0) ≤ 𝓡 v) ∧
    ∀ T, 1 ≤ T → w T ∈ stdSimplex ℝ (Fin d) ∧ ∀ v ∈ stdSimplex ℝ (Fin d),
      v ⬝ᵥ ((∑ t ∈ Finset.Ico 1 T, u t) + M T) - 𝓡 v / η ≤
        w T ⬝ᵥ ((∑ t ∈ Finset.Ico 1 T, u t) + M T) - 𝓡 (w T) / η

/-- `g` is the **leader sequence** of App. C (supp. p. 3): for every `T`, `g T` maximizes
`⟨v, ∑_{t=1}^{T} u t⟩ − 𝓡(v)/η` over `v ∈ Δ` (at `T = 0` the sum is empty). -/
def IsLeader {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η : ℝ) (u g : ℕ → Fin d → ℝ) : Prop :=
  ∀ T, g T ∈ stdSimplex ℝ (Fin d) ∧ ∀ v ∈ stdSimplex ℝ (Fin d),
    v ⬝ᵥ (∑ t ∈ Finset.Icc 1 T, u t) - 𝓡 v / η ≤
      g T ⬝ᵥ (∑ t ∈ Finset.Icc 1 T, u t) - 𝓡 (g T) / η

/-- The joint trajectory `w` of the repeated game `u` is produced by **every player `i` running
optimistic FTRL** with regularizer `𝓡 i`, step size `η`, one-step recency bias
`Mᵢᵀ = uᵢᵀ⁻¹`, on the utility vectors `uᵢᵗ = utilVec u (w t) i` the joint play generates
(`uᵢ⁰` is computed from `w 0`). -/
def IsOFTRLDynamics {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ)
    (𝓡 : Fin n → (Fin d → ℝ) → ℝ) (η : ℝ) (w : ℕ → Fin n → Fin d → ℝ) : Prop :=
  ∀ i, IsOFTRL (𝓡 i) η (fun T => utilVec u (w (T - 1)) i) (fun t => utilVec u (w t) i)
    (fun t => w t i)

/-- The social welfare `W(s) = ∑ᵢ uᵢ(s)` of a pure profile (p. 3). -/
def welfare {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ) (s : Fin n → Fin d) : ℝ :=
  ∑ i, u i s

/-- The expected welfare `W(w) = 𝔼_{s∼w}[W(s)] = ∑ᵢ Uᵢ(w)` of a mixed profile (p. 3). -/
def expectedWelfare {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ) (w : Fin n → Fin d → ℝ) : ℝ :=
  ∑ i, AGT.expectedPayoff (S := fun _ : Fin n => Fin d) u w i

/-- The optimal welfare `OPT = max_s W(s)` of the static game (p. 3), over the (nonempty, finite)
set of pure profiles. -/
def optWelfare {n d : ℕ} [Nonempty (Fin n → Fin d)] (u : Fin n → (Fin n → Fin d) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (welfare u)

/-- **Definition 1** (p. 3): the game is `(λ, µ)`-smooth if there is a pure profile `s*` with
`∑ᵢ uᵢ(s*ᵢ, s₋ᵢ) ≥ λ·OPT − µ·W(s)` for every pure profile `s`. -/
def IsSmooth {n d : ℕ} [Nonempty (Fin n → Fin d)] (u : Fin n → (Fin n → Fin d) → ℝ)
    (lam mu : ℝ) : Prop :=
  ∃ sstar : Fin n → Fin d, ∀ s : Fin n → Fin d,
    lam * optWelfare u - mu * welfare u s ≤ ∑ i, u i (Function.update s i (sstar i))

end RegLearnGames.TotalRegret


