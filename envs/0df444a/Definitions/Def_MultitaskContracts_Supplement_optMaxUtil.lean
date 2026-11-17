-- Prove2me | Definitions.Def_MultitaskContracts_Supplement_optMaxUtil
-- name    : MultitaskContracts_Supplement_optMaxUtil
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:05:47.260503+00:00
-- url     : https://prove2.me/theorems/ba1e6ba5-cd40-433a-b86e-499c1218fa3f
-- title:
--   Rewards, the principal\'s utility $u_P(t)$ and $\mathrm{OPT}^{\mathcal T}_{\mathrm{MaxUtil}}$
-- statement:
--   Let $I$ be an instance of the multitask model on a finite task set $K$. Each task $k$ yields the principal a reward $r_k$ on success, so she collects
--   $$r(Y)\;:=\;\sum_{k\in Y}r_k$$
--   on performance $Y$. For a contract $t$, let $S^*_t$ be the set of the agent's best responses, the strategies $S$ maximizing $\mathbb E_{Y\sim P_S}[t(Y)]-c(S)$. Ties are broken in favour of the principal, so her **utility** from $t$ is
--   $$u_P(t)\;:=\;\max_{S\in S^*_t}\Bigl(\mathbb E_{Y\sim P_S}[r(Y)]-\mathbb E_{Y\sim P_S}[t(Y)]\Bigr).$$
--   Over a class $\mathcal T$ of contracts she maximizes
--   $$\mathrm{OPT}^{\mathcal T}_{\mathrm{MaxUtil}}\;:=\;\sup_{t\in\mathcal T}u_P(t).$$
--
--   These are the objects of the utility-maximization comparison of Appendix A, in which Theorem 8 shows that separable contracts are a $\tfrac12$-approximation of bundle contracts.
--
--   **Formalization Note** The set of best responses is finite and nonempty (the helper lemma `exists_implements`), so the maximum is a `Finset.sup'`. The optimum is a supremum in `EReal` of the real utilities. It equals the paper's maximum wherever that maximum is attained, it is $-\infty$ for an empty class, and it never takes a junk value. Eq. (31) is a consequence, not the definition.
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), App. A.1, rewards, eq. (30) and the design objective, p.50 (PDF p.52)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance

set_option autoImplicit false

open scoped ENNReal

namespace MultitaskContracts.Supplement

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The principal's reward `r(Y) := ∑_{k∈Y} r_k` on performance `Y` (App. A.1, p.50, PDF 52). -/
def reward (r : K → ℝ) (Y : Finset K) : ℝ :=
  ∑ k ∈ Y, r k

open Classical in
/-- Every contract has a best response: a strategy maximizing the agent's expected utility
`E_{P_S}[t] − c(S)` over the finite set of strategies implements itself. -/
theorem exists_implements (I : Instance K) (t : Finset K → ℝ) :
    ((Finset.univ : Finset (Finset K)).filter (fun S => I.Implements t S)).Nonempty := by
  obtain ⟨S, -, hS⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset K))
    (fun S => I.toSetting.expect S t - I.toSetting.cost S) Finset.univ_nonempty
  exact ⟨S, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun S' => hS S' (Finset.mem_univ _)⟩⟩

open Classical in
/-- The principal's utility `u_P(t) := E_{Y∼P_S}[r(Y)] − E_{Y∼P_S}[t(Y)]` from contract `t`,
where `S ∈ S*_t` is the agent's best response, ties broken in favour of the principal
(App. A.1, p.50, PDF 52): the maximum over the best responses `S` of `t`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), App. A.1, p.50.

**Formalization Note.** The set of best responses is finite and nonempty (`exists_implements`),
so the maximum is `Finset.sup'` (membership in it is decided classically). -/
noncomputable def principalUtil (I : Instance K) (r : K → ℝ) (t : Finset K → ℝ) : ℝ :=
  ((Finset.univ : Finset (Finset K)).filter (fun S => I.Implements t S)).sup'
    (exists_implements I t) (fun S => I.expect S (reward r) - I.expect S t)

/-- **`OPT^T_MaxUtil := max_{t∈T} u_P(t)`** (App. A.1, p.50, PDF 52): the principal's optimal
utility over a class `T` of contracts, for rewards `r_k ≥ 0` on success of task `k`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), App. A.1, p.50 (PDF 52).

**Formalization Note.** The value is the supremum in `EReal` of the real utilities `u_P(t)`,
`t ∈ T`; it equals the paper's maximum wherever that maximum is attained, is `⊥` for an empty
class and is never a junk value (no real `sSup` of an unbounded set). Eq. (31) is a consequence,
not the definition. -/
noncomputable def optMaxUtil (I : Instance K) (r : K → ℝ) (T : Set (Finset K → ℝ)) : EReal :=
  ⨆ t ∈ T, ((principalUtil I r t : ℝ) : EReal)

end MultitaskContracts.Supplement


