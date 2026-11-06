-- Prove2me | Definitions.Def_UnobservedWelfare_roundLoss
-- name    : UnobservedWelfare_roundLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:26.388259+00:00
-- url     : https://prove2.me/theorems/55d53892-d622-498d-a337-ef327ed85b1c
-- title:
--   Comparison price $p^\star$, population objective $B$ and round loss $L_t$
-- statement:
--   Let $\varepsilon_T=W/(T+1)$ and, for $p\gg0$, define the **population objective** $B(p)=\mathbb E_{\theta\sim P}[S_\theta(p)]+c^*(p)$. A **comparison price** is a deterministic $p^\star\gg0$ with
--   $$B(p^\star)\le\inf_{p\gg0}B(p)+\varepsilon_T,\qquad c^*(p^\star)\le W.\tag{34}$$
--   The **round loss** of round $t$ is
--   $$L_t=S_{\theta_t}(p^\star)-u_{\theta_t}(X_t)+p^\star\cdot X_t+c(q_t)+c^*(p^\star)-p^\star\cdot q_t+2\big[B(p_t)-B(p^\star)+\varepsilon_T\big].$$
--   The round loss is nonnegative and bounds the per-round regret contribution.
--
--   **Formalization Note** (34) is written as $B(p^\star)\le B(p)+\varepsilon_T$ for every $p\gg0$, the same condition without a real infimum. Surpluses at strictly positive prices and utilities at demand points are finite under RC, and their real values are used. `roundLoss E c W p⋆ t` takes the paper's index $t$.
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), §2, pp.18–19 (PDF pp.20–21): $B$, $\varepsilon_T$, (34); §3.1, p.21 (PDF p.23): $L_t$

import Mathlib
import Definitions.Def_UnobservedWelfare_IsRC
import Definitions.Def_UnobservedWelfare_expectedRegret

open MeasureTheory Matrix

namespace UnobservedWelfare

/-- The comparison error `ε_T := W/(T + 1)` (Cheng–Tao–Xing manuscript, §2, p.19 (PDF p.21)). -/
noncomputable def epsT (W : ℝ) (T : ℕ) : ℝ := W / ((T : ℝ) + 1)

/-- The population objective `B(p) := E_{θ∼P}[S_θ(p)] + c*(p)` for `p ≫ 0` (Cheng–Tao–Xing
manuscript, §2 "Utility Normalization", p.18 (PDF p.20)).

**Formalization Note** The surplus is finite at `p ≫ 0` under RC, so `EReal.toReal` is faithful
there; for a centered RC model it is bounded in `θ` (p.18), so the Bochner integral is the
expectation. -/
noncomputable def Bobj {m : ℕ} {Θ : Type*} [MeasurableSpace Θ] (u : Θ → (Fin m → ℝ) → EReal)
    (P : Measure Θ) (c : (Fin m → ℝ) → ℝ) (p : Fin m → ℝ) : ℝ :=
  ∫ θ, (surplus (u θ) p).toReal ∂P + costConj c p

/-- `p⋆` is a comparison price at horizon `T` (Cheng–Tao–Xing manuscript, (34) of Lemma 2.4, p.19
(PDF p.21)): `p⋆ ≫ 0`, `B(p⋆) ≤ inf_{p≫0} B(p) + ε_T` and `c*(p⋆) ≤ W`.

**Formalization Note** `B(p⋆) ≤ inf_{p≫0} B(p) + ε_T` is written as `B(p⋆) ≤ B(p) + ε_T` for every
`p ≫ 0`, which is the same condition and needs no real infimum. -/
def IsComparisonPrice {m : ℕ} {Θ : Type*} [MeasurableSpace Θ] (u : Θ → (Fin m → ℝ) → EReal)
    (P : Measure Θ) (c : (Fin m → ℝ) → ℝ) (W : ℝ) (T : ℕ) (pstar : Fin m → ℝ) : Prop :=
  pstar ∈ posOrthant m ∧ (∀ p ∈ posOrthant m, Bobj u P c pstar ≤ Bobj u P c p + epsT W T) ∧
    costConj c pstar ≤ W

/-- The round loss of paper round `t ∈ [T]` (Cheng–Tao–Xing manuscript, §3.1, p.21 (PDF p.23)):
`L_t := S_{θ_t}(p⋆) − u_{θ_t}(X_t) + p⋆·X_t + c(q_t) + c*(p⋆) − p⋆·q_t + 2[B(p_t) − B(p⋆) + ε_T]`.

**Formalization Note** `t` is the paper's (1-based) round, i.e. the execution's round `t − 1`.
`S_{θ_t}(p⋆)` and `u_{θ_t}(X_t)` are finite under RC (the latter because `X_t` is a demand point at
`p_t ≫ 0`), so `EReal.toReal` is faithful. -/
noncomputable def Execution.roundLoss {m T : ℕ} {Θ : Type*} [MeasurableSpace Θ] {P : Measure Θ}
    {u : Θ → (Fin m → ℝ) → EReal} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (E : Execution m T P u μ) (c : (Fin m → ℝ) → ℝ) (W : ℝ) (pstar : Fin m → ℝ) (t : ℕ)
    (ω : Ω) : ℝ :=
  (surplus (u (E.θ (t - 1) ω)) pstar).toReal - (u (E.θ (t - 1) ω) (E.X (t - 1) ω)).toReal
    + pstar ⬝ᵥ E.X (t - 1) ω + c (E.q (t - 1) ω) + costConj c pstar - pstar ⬝ᵥ E.q (t - 1) ω
    + 2 * (Bobj u P c (E.p (t - 1) ω) - Bobj u P c pstar + epsT W T)

end UnobservedWelfare


