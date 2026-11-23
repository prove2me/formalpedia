-- Prove2me | Definitions.Def_BayesGroupHard_VertexCover_Supplement_RXC3
-- name    : BayesGroupHard_VertexCover_Supplement_RXC3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:39:14.308353+00:00
-- url     : https://prove2.me/theorems/3b87abce-25d4-496d-bfa1-a67958e5cfcc
-- title:
--   Problem 3 (RXC3), p. 31, and the solution set Σ and constants of Appendix B, pp. 31–33
-- statement:
--   **Restricted Exact Cover by Three Sets (Problem 3, p. 31).** An instance consists of a set $\hat{\mathcal E}_n$ of $n$ elements and a set $\hat{\mathcal T}_n$ of $n$ distinct subsets of $\hat{\mathcal E}_n$, each of size three, such that every element belongs to exactly three of the subsets; $n$ is divisible by three. A subfamily $\hat{\mathcal T}\subseteq\hat{\mathcal T}_n$ is an **exact cover** if every element lies in exactly one of its sets (it then has $n/3$ sets). YES instances have an exact cover, NO instances do not. $\hat N$ denotes the number of exact covers.
--
--   For an element $\varepsilon$ write $\varepsilon^{(1)},\varepsilon^{(2)},\varepsilon^{(3)}$ for the three subsets containing it. For a pair $(s_\kappa,(s_{\tau_j})_j)\in\{0,1\}^{n+1}$ the solution set of (20) is
--   $$\Sigma=\Bigl\{(s_\kappa,s_{\tau_1},\dots,s_{\tau_n}) : 2s_\kappa+\sum_{j=1}^3 s_{\varepsilon^{(j)}}=3 \text{ for all } \varepsilon\in\hat{\mathcal E}_n\Bigr\}.$$
--
--   The constants of Appendix B are $\bar p=\tfrac12$, $\underline p=\tfrac13$, $\ell_1=\log(\bar p/\underline p)=\log\tfrac32$, $\ell_0=\log\frac{1-\bar p}{1-\underline p}=\log\tfrac34$, $\bar q=\bar p^{1/3}(1-\bar p)^{2/3}$, $\underline q=\underline p^{1/3}(1-\underline p)^{2/3}$ and $\hat\ell=\log(\bar q/\underline q)$. With $\bar p^\star=\tfrac7{12}$, $\underline p^\star=\tfrac7{27}$, the likelihood of the informative signals in state $\theta$ is
--   $$w_\theta(s_\kappa,s_\tau)=(p^\star_\theta)^{s_\kappa}(1-p^\star_\theta)^{1-s_\kappa}\prod_{j=1}^n p_\theta^{s_{\tau_j}}(1-p_\theta)^{1-s_{\tau_j}},$$
--   where $p_1=\bar p$, $p_0=\underline p$, $p^\star_1=\bar p^\star$, $p^\star_0=\underline p^\star$; the sums $\sum_{\Sigma}w_1$ and $\sum_\Sigma w_0$ are the numerator and denominator of (21).
--
--   These objects carry the EXACT-COVER reduction behind Theorem 2.
--
--   **Formalization Note.** Elements and subsets are both indexed by `Fin n`; `sets j` is the $j$-th subset, and `distinct` records that $\hat{\mathcal T}_n$ is a set. A pair $(s_\kappa,s_\tau)$ is `CoreProfile n = Bool × (Fin n → Bool)` with `false = 0`; `bit` is the $0/1$ value, `selected` the subsets with signal $1$, `baseProfile n` $=(0,1,\dots,1)$. `coreWeight`, `coreMass`, `coverCount` are $w_\theta$, $\sum_\Sigma w_\theta$, $\hat N$. $\bar q,\underline q$ use real powers.
-- source:
--   Hązła, Jadbabaie, Mossel & Rahimian, Bayesian Decision Making in Groups is Hard, arXiv:1705.04770v4, p. 31 (Problem 3, ℓ_1, ℓ_0), p. 32 (Σ, (21)), p. 33 (§B.2, q̄, q̲, ℓ̂, N̂)

import Mathlib

namespace BayesGroupHard.VertexCover.Supplement

open Finset
/-- Problem 3 (RXC3, p. 31): `n` elements `Ê_n = Fin n` and a set `T̂_n` of `n` distinct
three-element subsets, indexed by `Fin n`, with every element in exactly three of them, and
`3 ∣ n` (the paper's implicit assumption). -/
structure RXC3 (n : ℕ) where
  sets : Fin n → Finset (Fin n)
  distinct : Function.Injective sets
  triple : ∀ j, (sets j).card = 3
  regular : ∀ e, (univ.filter (fun j => e ∈ sets j)).card = 3
  divisible : 3 ∣ n

/-- A subfamily `S` of the triples is an exact cover: every element lies in exactly one
triple of `S` (Problem 3, p. 31). -/
def ExactCover {n : ℕ} (X : RXC3 n) (S : Finset (Fin n)) : Prop :=
  ∀ e, (S.filter (fun j => e ∈ X.sets j)).card = 1

/-- The YES case of RXC3: an exact cover exists. -/
def HasCover {n : ℕ} (X : RXC3 n) : Prop := ∃ S, ExactCover X S

/-- The integer value `0`/`1` of a signal. -/
def bit (b : Bool) : ℕ := if b then 1 else 0

/-- The informative part `(s_κ, s_τ1, …, s_τn)` of a signal profile of the Appendix B network. -/
abbrev CoreProfile (n : ℕ) := Bool × (Fin n → Bool)

/-- The triples whose subset agent has signal `1`. -/
def selected {n : ℕ} (s : CoreProfile n) : Finset (Fin n) :=
  univ.filter (fun j => s.2 j = true)

/-- The solution set `Σ` of (20) (p. 32): `2 s_κ + Σ_{j=1}^3 s_ε(j) = 3` for every element `ε`,
where `ε(1), ε(2), ε(3)` are the three triples containing `ε`. -/
def sigma {n : ℕ} (X : RXC3 n) : Finset (CoreProfile n) :=
  univ.filter (fun s => ∀ e,
    2 * bit s.1 + ∑ j ∈ univ.filter (fun j => e ∈ X.sets j), bit (s.2 j) = 3)

/-- The profile `(0, 1, …, 1)`. -/
def baseProfile (n : ℕ) : CoreProfile n := (false, fun _ => true)

/-- `ℓ_1 = log(p̄/p̲) = log(3/2)` (p. 31). -/
noncomputable def ellOne : ℝ := Real.log ((1 / 2) / (1 / 3))

/-- `ℓ_0 = log((1-p̄)/(1-p̲)) = log(3/4)` (p. 31). -/
noncomputable def ellZero : ℝ := Real.log ((1 - 1 / 2) / (1 - 1 / 3))

/-- `q̄ = p̄^{1/3} (1-p̄)^{2/3}` with `p̄ = 1/2` (p. 33). -/
noncomputable def qBar : ℝ := (1 / 2 : ℝ) ^ (1 / 3 : ℝ) * (1 - 1 / 2 : ℝ) ^ (2 / 3 : ℝ)

/-- `q̲ = p̲^{1/3} (1-p̲)^{2/3}` with `p̲ = 1/3` (p. 33). -/
noncomputable def qUnder : ℝ := (1 / 3 : ℝ) ^ (1 / 3 : ℝ) * (1 - 1 / 3 : ℝ) ^ (2 / 3 : ℝ)

/-- `ℓ̂ = log(q̄/q̲)` (p. 33). -/
noncomputable def ellHat : ℝ := Real.log (qBar / qUnder)

/-- The likelihood `P_θ{(s_κ, s_τ) = s}` of the informative signals in (21):
`(p⋆_θ)^{s_κ} (1-p⋆_θ)^{1-s_κ} ∏_j p_θ^{s_τj} (1-p_θ)^{1-s_τj}`, with `p⋆_1 = 7/12`,
`p⋆_0 = 7/27`, `p_1 = 1/2`, `p_0 = 1/3`. -/
noncomputable def coreWeight {n : ℕ} (θ : Bool) (s : CoreProfile n) : ℝ :=
  (if s.1 then (if θ then 7 / 12 else 7 / 27)
   else 1 - (if θ then 7 / 12 else 7 / 27)) *
    ∏ j, (if s.2 j then (if θ then 1 / 2 else 1 / 3)
      else 1 - (if θ then 1 / 2 else 1 / 3))

/-- The sum over `Σ` in the numerator (`θ = 1`) or denominator (`θ = 0`) of (21). -/
noncomputable def coreMass {n : ℕ} (X : RXC3 n) (θ : Bool) : ℝ :=
  ∑ s ∈ sigma X, coreWeight θ s

/-- `N̂`, the number of exact covers (p. 33). -/
noncomputable def coverCount {n : ℕ} (X : RXC3 n) : ℕ := by
  classical
  exact (univ.filter (fun S : Finset (Fin n) => ExactCover X S)).card

end BayesGroupHard.VertexCover.Supplement


