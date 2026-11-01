-- Prove2me | Definitions.Def_ALAVI_IsALAVIRun
-- name    : ALAVI_IsALAVIRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:27.284489+00:00
-- url     : https://prove2.me/theorems/3fb1ff2f-198f-4df2-a172-532ee78198c3
-- title:
--   A run of ALAVI (25)–(28)
-- statement:
--   Sequences $(v^k),(u^k)\subseteq E$ and $(p^k),(q^k)\subseteq F$ form a **run of ALAVI** with parameters $\eta,\alpha,\gamma$ if for every $k\ge1$
--
--   $$
--   \begin{aligned}
--   v^k&=(1-\eta)u^k+\eta v^{k-1}, &(25)\\
--   q^k&=\Pi\big(p^k+\gamma\Theta(u^k)\big), &(26)\\
--   u^{k+1}&\in\operatorname*{arg\,min}_{u\in U}\ \langle G(u^k),u\rangle+J(u)+\langle q^k,\Theta(u)\rangle+\tfrac1{2\alpha}\|u-v^k\|^2, &(27)\\
--   p^{k+1}&=\Pi\big(p^k+\gamma\Theta(u^{k+1})\big), &(28)
--   \end{aligned}
--   $$
--
--   where $\Pi$ is the Euclidean projection onto $C^*$.
--
--   **Formalization Note.** The input $u^1, v^0$ is arbitrary, as printed. The page uses $p^1$ in (26) at $k=1$ without defining it; here $p^1$ is arbitrary, which covers both $p^1=\Pi(p^0+\gamma\Theta(u^1))$ and $p^1=p^0$. The terms $u^0,p^0,q^0$ are unused. $\Pi$ is the published `CalamaiMore.Convergence.proj` onto $C^*$.
-- source:
--   Zhao, Zhu & Zhang, An Augmented Lagrangian Approach to Conically Constrained Non-monotone Variational Inequality Problems, arXiv:2306.01214v1, ALAVI, (25)–(28), p.12; Π the projection onto C∗, p.5

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj
import Definitions.Def_ALAVI_IsSubproblemSol

namespace ALAVI

/-- **ALAVI (Augmented Lagrangian Approach to (VIP)), (25)–(28).** For every `k ≥ 1`:
`vᵏ = (1 - η)uᵏ + ηvᵏ⁻¹` (25), `qᵏ = Π(pᵏ + γΘ(uᵏ))` (26), `uᵏ⁺¹` solves the subproblem (27),
and `pᵏ⁺¹ = Π(pᵏ + γΘ(uᵏ⁺¹))` (28), where `Π` is the projection onto `C*`.

Zhao, Zhu & Zhang, arXiv:2306.01214v1, ALAVI, (25)–(28), p.12; `Π` is the projection onto `C*`
(p.5).

Formalization Notes: sequences are `ℕ → _` indexed as in the paper. The input `u¹`, `v⁰` is
arbitrary, as printed. The page reads `p¹` in (26) at `k = 1` without defining it; here `p¹` is
arbitrary (this covers `p¹ = Π(p⁰ + γΘ(u¹))` and `p¹ = p⁰`). `u⁰`, `p⁰`, `q⁰` are unused. `Π` is
the published `CalamaiMore.Convergence.proj` onto `C* = ProperCone.innerDual C`, a nonempty
closed convex set, so the nearest point exists and the junk branch of `proj` never fires. The
parameter window is not part of the run; the theorems assume `Params`. -/
def IsALAVIRun {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (G : E → E) (J : E → EReal) (Θ : E → F) (η α γ : ℝ)
    (v u : ℕ → E) (p q : ℕ → F) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    v k = (1 - η) • u k + η • v (k - 1) ∧
    q k = CalamaiMore.Convergence.proj (ProperCone.innerDual (C : Set F) : Set F)
      (p k + γ • Θ (u k)) ∧
    IsSubproblemSol U J Θ α (G (u k)) (q k) (v k) (u (k + 1)) ∧
    p (k + 1) = CalamaiMore.Convergence.proj (ProperCone.innerDual (C : Set F) : Set F)
      (p k + γ • Θ (u (k + 1)))

end ALAVI


