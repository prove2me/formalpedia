-- Prove2me | Definitions.Def_ConvexRMDP_RMDP_regOp
-- name    : ConvexRMDP_RMDP_regOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:22.050436+00:00
-- url     : https://prove2.me/theorems/2356fa50-904e-47b4-ac16-e0ca0a5447c6
-- title:
--   Regularized robust Bellman operator $\tilde T$ with uniform reference policy
-- statement:
--   Fix an sa-rectangular robust MDP $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ and a regularization scalar $b$. For $v \in \mathbb R^{\mathcal S}$ the **worst-case expected next value** of the pair $(s,a)$ is $\min_{p \in \mathcal U_{sa}} p^\top v$.
--
--   The **regularized robust Bellman operator** $\tilde T : \mathbb R^{\mathcal S} \to \mathbb R^{\mathcal S}$ is
--   $$
--   \tilde T(v)_s = \max_{\pi_s \in \Delta(\mathcal A)} \sum_{a \in \mathcal A} \pi_{sa}\left(r_{sa} + \gamma \min_{p \in \mathcal U_{sa}} p^\top v\right) - \frac1b \mathrm{KL}(\pi_s, \nu_s), \qquad s \in \mathcal S,
--   $$
--   where $\nu_s$ is the uniform distribution on $\mathcal A$, $\nu_{sa} = 1/|\mathcal A|$.
--
--   This operator replaces the robust Bellman operator $T$ by an entropy-regularized version; its fixed point $\tilde v^\star$ is the object of the convex formulation (Theorem 4.1).
--
--   **Formalization Note** The minimum over $\mathcal U_{sa}$ is an infimum (`worst`) and the maximum over $\Delta(\mathcal A)$ is a supremum (`sSup` over `stdSimplex`). The first set is nonempty and bounded below because $\mathcal U_{sa}$ is a nonempty subset of the simplex; for nonempty $\mathcal A$ and $b > 0$ the second is nonempty and bounded above, because the divergence to the uniform distribution is nonnegative, and its supremum is attained. Since $\nu_{sa} > 0$, every $\pi_s$ is absolutely continuous with respect to $\nu_s$ and the divergence is finite.
-- source:
--   Grand-Clément & Petrik, On the Convex Formulations of Robust Markov Decision Processes, arXiv:2209.10187v2 (13 Dec 2023), §4.1, (4.1), p.10, with νₛₐ = 1/|A| as fixed on p.10

import Mathlib
import Definitions.Def_ConvexRMDP_RMDP
import Definitions.Def_ConvexRMDP_kl

namespace ConvexRMDP

namespace RMDP

variable {S A : Type*} [Fintype S] [Fintype A]

/-- The worst-case expected next value `min_{p ∈ 𝒰_{sa}} pᵀv` (Grand-Clément & Petrik,
arXiv:2209.10187v2, (4.1), p.10).

**Formalization Note.** The minimum is the infimum `sInf`; the set is nonempty (`U_nonempty`) and
bounded below (`𝒰_{sa} ⊆ Δ(S)`), so this is a genuine infimum, equal to the paper's minimum
whenever it is attained. -/
noncomputable def worst (M : RMDP S A) (v : S → ℝ) (s : S) (a : A) : ℝ :=
  sInf ((fun p : S → ℝ => ∑ s', p s' * v s') '' M.U s a)

/-- **The regularized robust Bellman operator** `T̃ : ℝ^S → ℝ^S` with uniform reference policy
(Grand-Clément & Petrik, arXiv:2209.10187v2, (4.1), p.10, with `ν_{sa} = 1/|A|` as fixed on p.10):
`T̃(v)_s = max_{π_s ∈ Δ(A)} ∑_a π_{sa} (r_{sa} + γ min_{p ∈ 𝒰_{sa}} pᵀv) − (1/b) KL(π_s, ν_s)`.

**Formalization Note.** The maximum over `Δ(A) = stdSimplex ℝ A` is `sSup`. For nonempty `A` and
`b > 0` the set is nonempty and bounded above (KL to the uniform distribution is nonnegative), so
`sSup` is the paper's maximum (attained, Lemma 4.1). Since `ν_{sa} = 1/|A| > 0`, every `π_s` is
absolutely continuous with respect to `ν_s` and `KL(π_s, ν_s)` is finite. -/
noncomputable def regOp (M : RMDP S A) (b : ℝ) (v : S → ℝ) : S → ℝ := fun s =>
  sSup ((fun π : A → ℝ => ∑ a, π a * (M.r s a + M.γ * M.worst v s a)
      - kl π (fun _ => 1 / (Fintype.card A : ℝ)) / b) '' stdSimplex ℝ A)

end RMDP

end ConvexRMDP


