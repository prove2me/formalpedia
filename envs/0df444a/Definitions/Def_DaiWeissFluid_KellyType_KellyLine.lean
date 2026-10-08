-- Prove2me | Definitions.Def_DaiWeissFluid_KellyType_KellyLine
-- name    : DaiWeissFluid_KellyType_KellyLine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T02:45:51.087996+00:00
-- url     : https://prove2.me/theorems/ceec25f1-3bbe-4737-84fd-bfee7be61637
-- title:
--   Kelly-type reentrant line, no immediate feedback, cumulative queue lengths $Q_k^+$ (§6, (2.2))
-- statement:
--   Let a reentrant line have stations $1,\dots,I$, classes $1,\dots,K$, station map $\sigma$ and mean service times $m_k$.
--
--   1. The line is of **Kelly type** with station means $\beta_1,\dots,\beta_I$ if each visit to station $i$ has mean service time $\beta_i$, regardless of the class:
--   $$ m_k = \beta_{\sigma(k)} \qquad \text{for every class } k. $$
--   2. The routing has **no immediate feedback** if consecutive stages are served at different stations: $\sigma(k+1) \neq \sigma(k)$ for $k = 1,\dots,K-1$.
--   3. The **cumulative queue length** of (2.2) is $Q_k^+(t) = \sum_{l=1}^{k} Q_l(t)$.
--   4. For a station $i$, $G_i(t) = \sum_{k \in C_i} Q_k^+(t)$, the Lyapunov component used in the proof of Theorem 6.1, and $c_{i,l} = \#\{k \in C_i : l \le k\}$, the coefficient of $Q_l$ in $G_i$, so that $G_i(t) = \sum_{l} c_{i,l} Q_l(t)$.
--
--   With two stations and no immediate feedback the route alternates between the stations; it may begin at either one. These are the hypotheses and the Lyapunov function of Theorem 6.1.
--
--   **Formalization Note** 0-based indices as in the fluid-model definition. For $K = 2n$ with the route starting at station 1, $G_1 = \sum_{l=1}^n Q^+_{2l-1}$ and $G_2 = \sum_{l=1}^n Q^+_{2l}$, which are the paper's $G_1$, $G_2$; the definition here sums over the constituency, so it covers both parities and both starting stations.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), pp. 129–130, §6 (Kelly-type network, Theorem 6.1 and its proof), p. 120, (2.2)

import Mathlib
import Definitions.Def_DaiWeissFluid_KellyType_FluidModel
import Definitions.Def_DaiWeissFluid_ThreeBuffer_Line

namespace DaiWeissFluid.KellyType

namespace ReentrantLine

variable {I K : ℕ} (L : ReentrantLine I K)

/-- Kelly type (§6, pp. 129–130): every visit to station `i` has the same mean service time
`β i`, i.e. `m_k = β_{σ(k)}` for every class `k`. -/
def IsKellyType (β : Fin I → ℝ) : Prop := ∀ k, L.m k = β (L.σ k)

/-- No immediate feedback (Theorem 6.1, p. 130): consecutive stages of the route are served at
different stations, `σ(k + 1) ≠ σ(k)`. -/
def NoImmediateFeedback : Prop :=
  ∀ (k : Fin K) (h : (k : ℕ) + 1 < K), L.σ ⟨(k : ℕ) + 1, h⟩ ≠ L.σ k

/-- `G_i(t) = ∑_{k ∈ C_i} Q_k⁺(t)`: the sum of the cumulative queue lengths `Q_k⁺` of (2.2) over
the classes served at station `i` (proof of Theorem 6.1, p. 130). -/
noncomputable def kellyG (Q : ℝ → Fin K → ℝ) (i : Fin I) (t : ℝ) : ℝ :=
  ∑ k ∈ L.C i, DaiWeissFluid.ThreeBuffer.Qplus Q k t

/-- The coefficient of `Q_l` in `G_i`: `c_{i,l} = #{k ∈ C_i : l ≤ k}`, so that
`G_i(t) = ∑_l c_{i,l} Q_l(t)`. -/
noncomputable def kellyCoeff (i : Fin I) (l : Fin K) : ℝ :=
  (((L.C i).filter (fun k => l ≤ k)).card : ℝ)

end ReentrantLine

end DaiWeissFluid.KellyType


