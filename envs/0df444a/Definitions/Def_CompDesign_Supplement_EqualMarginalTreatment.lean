-- Prove2me | Definitions.Def_CompDesign_Supplement_EqualMarginalTreatment
-- name    : CompDesign_Supplement_EqualMarginalTreatment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:52:25.21133+00:00
-- url     : https://prove2.me/theorems/6ca24590-a97c-46c8-a756-6ef8ec4b0a82
-- title:
--   Conditions (A1)–(A2) on cost-oblivious payment rules
-- statement:
--   Write $\Delta_i(S)=v(S)-v(S\setminus\{i\})$. A cost-oblivious payment rule $v\mapsto p(v)$ (at a fixed budget) satisfies
--
--   - **(A1) equal treatment of equal marginal contributions** if for every value function $v:2^N\to\mathbb R_{\ge0}$, every $S$ and $i,i'\in S$: $\Delta_i(S)=\Delta_{i'}(S)\Rightarrow p_i(S)=p_{i'}(S)$;
--   - **(A2) positive compensation on uniformly productive coalitions** if for every $v:2^N\to\mathbb R_{\ge0}$ and nonempty $S$: if some $q>0$ has $\Delta_i(S)=q$ for all $i\in S$, then $\sum_{i\in S}p_i(S)>0$.
--
--   These are the hypotheses of Theorem 6.2.
--
--   **Formalization Note** The conditions quantify over every nonnegative value function, not only monotone ones, as on p.49.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), §6.2.1, p.49 (PDF 52)

import Mathlib

namespace CompDesign.Supplement

/-- Condition (A1), equal treatment of equal marginal contributions (§6.2.1, p.49, PDF 52, of
Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…)), for a cost-oblivious rule `P` at a fixed budget (a map from value functions to payments):
for every value function `v : 2^N → ℝ≥0`, every `S` and `i, i′ ∈ S`, `Δ_i(S) = Δ_{i′}(S)` implies
`p_i(S) = p_{i′}(S)`, where `Δ_i(S) = v(S) − v(S ∖ {i})`. -/
def EqualMarginalTreatment {n : ℕ}
    (P : (Finset (Fin n) → ℝ) → Finset (Fin n) → Fin n → ℝ) : Prop :=
  ∀ v : Finset (Fin n) → ℝ, (∀ S, 0 ≤ v S) → ∀ S, ∀ i ∈ S, ∀ i' ∈ S,
    v S - v (S.erase i) = v S - v (S.erase i') → P v S i = P v S i'

/-- Condition (A2), positive compensation on uniformly productive coalitions (§6.2.1, p.49, PDF 52,
of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…)): for every value function `v : 2^N → ℝ≥0` and nonempty `S`, if some `q > 0` has
`Δ_i(S) = q` for every `i ∈ S`, then `∑_{i∈S} p_i(S) > 0`. -/
def PositiveOnUniform {n : ℕ}
    (P : (Finset (Fin n) → ℝ) → Finset (Fin n) → Fin n → ℝ) : Prop :=
  ∀ v : Finset (Fin n) → ℝ, (∀ S, 0 ≤ v S) → ∀ S : Finset (Fin n), S.Nonempty →
    ∀ q : ℝ, 0 < q → (∀ i ∈ S, v S - v (S.erase i) = q) → 0 < ∑ i ∈ S, P v S i

end CompDesign.Supplement


