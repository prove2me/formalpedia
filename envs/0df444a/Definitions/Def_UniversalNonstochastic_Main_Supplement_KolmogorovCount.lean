-- Prove2me | Definitions.Def_UniversalNonstochastic_Main_Supplement_KolmogorovCount
-- name    : UniversalNonstochastic_Main_Supplement_KolmogorovCount
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:26:28.959225+00:00
-- url     : https://prove2.me/theorems/86ac6a42-39f8-4597-8a09-b4118466f30a
-- title:
--   Kolmogorov's count $N(k,\alpha,\beta)=|D_k\setminus S_{\alpha,\beta}|$
-- statement:
--   Let $V$ be the optimal plain decoder, $k,\alpha\in\mathbb N_0$ and $\beta\in[0,\infty]$. Define
--   $$D_k=\{\omega\in\mathcal X\mid C(\omega)\le k\},$$
--   $$S_{\alpha,\beta}=\{\omega\in\mathcal X\mid \exists\,\Omega\subseteq\mathcal X:\ |\Omega|<\infty,\ \omega\in\Omega,\ C(\Omega)\le\alpha,\ C(\omega)\ge\log|\Omega|-\beta\},$$
--   and $N(k,\alpha,\beta)=|D_k\setminus S_{\alpha,\beta}|$, the number of $(\alpha,\beta)$-nonstochastic objects (in Kolmogorov's plain, unconditional sense) of plain complexity at most $k$.
--
--   This is the count of Kolmogorov's 1981 questions, in the form the source fixes in Appendix B, and the subject of Theorem 25.
--
--   **Formalization Note** $N(k,\alpha,\beta)$ is the cardinality in $\mathbb N\cup\{\infty\}$ of the set; it is $\infty$ only for an infinite set, and $D_k$ is finite. $\log$ is $\log_2$ and $\beta=+\infty$ is allowed as an extended real.
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, Appendix B, p.28, eq. (53) and the definition of N(k, α, β)

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_Complexity
import Definitions.Def_UniversalNonstochastic_Main_Supplement_Complexities

namespace UniversalNonstochastic.Main.Supplement

/-- `D_k = {ω ∈ 𝓧 | C(ω) ≤ k}` (S, p.28, eq. (53)). -/
def plainBall (V : OptimalPlainDecoder) (k : ℕ) : Set ℕ+ :=
  {ω | Cobj V ω ≤ (k : ℕ∞)}

/-- `S_{α,β}` (S, p.28, eq. (53)), for `β ∈ [0, ∞]`: objects `ω` lying in some finite set `Ω`
with `C(Ω) ≤ α` and `C(ω) ≥ log₂ |Ω| - β` (plain, unconditional: Kolmogorov's form). -/
def kolmogorovStochastic (V : OptimalPlainDecoder) (α : ℕ) (β : EReal) : Set ℕ+ :=
  {ω | ∃ Ω : Finset ℕ+, ω ∈ Ω ∧ Cset V Ω ≤ (α : ℕ∞) ∧
      ((Real.logb 2 (Ω.card : ℝ) : ℝ) : EReal) - β ≤ toEReal (Cobj V ω)}

/-- `N(k, α, β) = |D_k ∖ S_{α,β}|` (S, p.28), the number of `(α, β)`-nonstochastic objects of
plain complexity at most `k`, as an extended natural number (`⊤` only for an infinite set;
`D_k` is finite). -/
noncomputable def kolmogorovCount (V : OptimalPlainDecoder) (k α : ℕ) (β : EReal) : ℕ∞ :=
  (plainBall V k \ kolmogorovStochastic V α β).encard

end UniversalNonstochastic.Main.Supplement


