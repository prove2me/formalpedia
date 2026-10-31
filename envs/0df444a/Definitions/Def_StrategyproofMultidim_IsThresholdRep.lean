-- Prove2me | Definitions.Def_StrategyproofMultidim_IsThresholdRep
-- name    : StrategyproofMultidim_IsThresholdRep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:33.484963+00:00
-- url     : https://prove2.me/theorems/4b86194d-6b0d-4079-81e9-672de8c141ae
-- title:
--   Threshold representation $\{T_i^k(v_{-i})\}$
-- statement:
--   A family of functions $T_i^k$ is a **threshold representation** of the mechanism $\mu=(d,p)$ if, for every buyer $i$ and object $k$:
--
--   1. $T_i^k$ depends only on the other buyers' reports $v_{-i}$, and $T_i^k(v_{-i})>0$ at every positive profile;
--   2. buyer $i$ wins object $k$ when $v_i^k>T_i^k(v_{-i})$ and does not win it when $v_i^k<T_i^k(v_{-i})$ (ties are unrestricted);
--   3. buyer $i$ pays the sum of the thresholds of the objects it wins:
--   $$p_i(v)=\sum_{k:\,d_i^k(v)=1}T_i^k(v_{-i}).$$
--
--   By Theorem 2 these are exactly the regular SP and AS mechanisms.
--
--   **Formalization Note** $T$ is a function of the whole profile that ignores row $i$. The paper's "$k:d^k(v)=1$" in (2) is read as $d_i^k(v)=1$.
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), Theorem 2, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_StrategyproofMultidim_Mechanism
import Definitions.Def_StrategyproofMultidim_PosProfile

namespace StrategyproofMultidim

/-- **Threshold representation** (Theorem 2, p.10; Theorem 1, pp.7–8 for one buyer).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.10: "there exist functions {Tᵢᵏ : Πⱼ≠ᵢVⱼ ⟶ ℝ₊₊}ₖ∈M such that for all v ∈ 𝒱 and all
k ∈ M: (1) dᵢᵏ(v) = 1 if vᵢᵏ > Tᵢᵏ(v₋ᵢ), 0 if vᵢᵏ < Tᵢᵏ(v₋ᵢ), and
(2) pᵢ(v) = ∑_{k:dᵏ(v)=1} Tᵢᵏ(v₋ᵢ)."

`IsThresholdRep μ T` says: `T i k v` depends only on the rows of `v` other than row `i` (it is a
function of `v₋ᵢ`); at every positive profile it is positive; buyer `i` wins object `k` when
`vᵢᵏ > Tᵢᵏ(v₋ᵢ)` and loses it when `vᵢᵏ < Tᵢᵏ(v₋ᵢ)` (ties unrestricted); and buyer `i` pays the
sum of the thresholds of the objects it wins.

**Formalization Note.** A function of `v₋ᵢ` is encoded as a function of the whole profile that
ignores row `i`. The paper's "k : dᵏ(v) = 1" in (2) is read as `dᵢᵏ(v) = 1`. -/
def IsThresholdRep {n m : ℕ} (μ : Mechanism n m)
    (T : Fin n → Fin m → (Fin n → Fin m → ℝ) → ℝ) : Prop :=
  (∀ i k (v w : Fin n → Fin m → ℝ), (∀ j, j ≠ i → v j = w j) → T i k v = T i k w) ∧
  ∀ v, PosProfile v → ∀ i,
    (∀ k, 0 < T i k v) ∧
    (∀ k, T i k v < v i k → μ.q v i k = true) ∧
    (∀ k, v i k < T i k v → μ.q v i k = false) ∧
    μ.t i v = ∑ k ∈ Finset.univ.filter (fun k => μ.q v i k = true), T i k v

end StrategyproofMultidim


