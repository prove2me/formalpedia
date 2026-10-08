-- Prove2me | Definitions.Def_AffinePolicies_GeneralApprox_Setting
-- name    : AffinePolicies_GeneralApprox_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T13:07:17.294889+00:00
-- url     : https://prove2.me/theorems/7a1e2ec1-22a1-42ca-afaf-b4d4d6118096
-- title:
--   (66), PDF p. 35 — the dominating set 𝒰⁰ built from the shared model and Algorithm 𝒜
-- statement:
--   **The two-stage adaptive problem (1).** Let $A\in\mathbb R^{m\times n_1}$, $B\in\mathbb R^{m\times n_2}$, $c\in\mathbb R^{n_1}$, $d\in\mathbb R^{n_2}$ and let $\mathcal U\subseteq\mathbb R^m$ be a set of possible right-hand sides. A **two-stage solution** is a first-stage vector $x\in\mathbb R^{n_1}$ together with a second-stage rule $y:\mathbb R^m\to\mathbb R^{n_2}$ chosen after $b$ is revealed. It is **feasible** for $\Pi_{Adapt}(\mathcal U)$ when
--   $$x\ge 0,\qquad y(b)\ge 0,\qquad Ax+By(b)\ge b\qquad\text{for every } b\in\mathcal U,$$
--   with all inequalities componentwise. A number $t$ **bounds the worst-case cost** of $(x,y)$ when $c^Tx+d^Ty(b)\le t$ for every $b\in\mathcal U$. The optimal value is
--   $$z_{Adapt}(\mathcal U)=\inf\{t:\ \text{some feasible }(x,y)\text{ has worst-case cost at most }t\},$$
--   which is $\min_x c^Tx+\max_{b\in\mathcal U}d^Ty(b)$ of (1). An **affine policy** is a rule $y(b)=Pb+q$; $z_{Aff}(\mathcal U)$ is the same infimum over feasible solutions with an affine second stage (still required to satisfy $Pb+q\ge0$ on $\mathcal U$). A feasible $(x,y)$ is **optimal** for $\Pi_{Adapt}(\mathcal U)$ when every worst-case bound achieved by some feasible solution is also achieved by $(x,y)$; optimal affine solutions are defined in the same way.
--
--   **The argmax points (38).** For $j=1,\dots,m$, $\mu_j=\max\{b_j : b\in\mathcal U\}$ and $\beta^j\in\arg\max\{b_j: b\in\mathcal U\}$. These are not definitions here: the theorems take $\mu$ and $\beta^j$ as data with exactly these defining properties.
--
--   **Algorithm $\mathcal A$ (Fig. 1).** Start with $b^0=0$ and $J_1^0=\{1,\dots,m\}$. While some $b\in\mathcal U$ has $\sum_{j\in J_1^k}b_j/\mu_j>\sqrt m$, set $k\leftarrow k+1$, choose $u^k\in\arg\max\{\sum_{j\in J_1^{k-1}}b_j/\mu_j: b\in\mathcal U\}$, add $u^k_j$ to $b^{k-1}_j$ for $j\in J_1^{k-1}$ (other coordinates are unchanged), and let $J_1^k=\{j\in J_1^{k-1}: b^k_j<\mu_j\}$. When the test fails, $K=k$, $\beta=u^1+\dots+u^K$, $J_1=J_1^K$ and $J_2$ is its complement. Because the maximizers are not unique, a **run** is any sequence $u^1,\dots,u^K$ satisfying these rules, with the loop test true before each executed iteration and false after the last.
--
--   **The dominating set (66).** From the points $\beta^j$ and the output $\beta$ of a run,
--   $$\mathcal U^0=\operatorname{conv}\{2\sqrt m\cdot\beta^1,\dots,2\sqrt m\cdot\beta^m,\ 2\beta\}.$$
--
--   These are the objects of Section 6, where an optimal first stage for $\Pi_{Adapt}(\mathcal U^0)$ is shown to be an $O(\sqrt m)$-approximate first stage for $\Pi_{Adapt}(\mathcal U)$.
--
--   **Formalization Note** Vectors are functions on `Fin m`, so the paper's coordinate $j$ is index $j-1$. The values $z_{Adapt}$ and $z_{Aff}$ are infima of sets of achievable worst-case bounds; Lean's real infimum returns $0$ on an empty set, so the theorems state the feasibility they rely on. Algorithm $\mathcal A$ is encoded as a recursion `algState` on a choice sequence `u : ℕ → Fin m → ℝ` (`u k` is $u^k$, `u 0` unused), with `IsIteration` and `IsRun` expressing the loop test and the argmax property; `betaSum u K` is $\beta$, kept apart from the argmax points $\beta^j$. Step 2(d) of Fig. 1 is read as $J_1^k=\{j\in J_1^{k-1}: b^k_j<\mu_j\}$, the meaning used in the paper's proofs.
-- source:
--   Bertsimas & Goyal, On the power and limitations of affine policies in two-stage adaptive optimization, Math. Program. Ser. A, DOI 10.1007/s10107-011-0444-4, (1), PDF p. 2; (38), PDF p. 26; Fig. 1 (Algorithm A), PDF p. 29; (66), PDF p. 35

import Mathlib
import Definitions.Def_AffinePolicies_Simplex_Setting
import Definitions.Def_AffinePolicies_SqrtBound_Setting

namespace AffinePolicies.GeneralApprox

open Matrix

variable {m n₁ n₂ : ℕ}

/-- The dominating set (66): `𝒰⁰ = conv{2√m·β¹, …, 2√m·β^m, 2β}`, where `bstar j` is the
argmax point `βʲ` of (38) and `betaSum u K` is the output `β` of Algorithm 𝒜. -/
noncomputable def U0 (bstar : Fin m → Fin m → ℝ) (u : ℕ → Fin m → ℝ) (K : ℕ) :
    Set (Fin m → ℝ) :=
  convexHull ℝ (Set.range (fun j => (2 * Real.sqrt m) • bstar j) ∪ {(2 : ℝ) • AffinePolicies.SqrtBound.betaSum u K})

end AffinePolicies.GeneralApprox


