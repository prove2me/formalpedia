-- Prove2me | Definitions.Def_LemonsPoA_TwoSided_Game
-- name    : LemonsPoA_TwoSided_Game
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:11:18.000728+00:00
-- url     : https://prove2.me/theorems/e279412a-2128-4cbe-bd0d-be4af544174a
-- title:
--   Seller-proposer signaling game: strategies, beliefs, sequential equilibrium (conditions 1-4), $W_S$, $W^-_S(I,Q)$ and $W^-_S(I)$
-- statement:
--   **The seller-proposer game on a finite menu $Q\subset\mathbb R$** (§2.1). The seller (proposer), after observing her type $\theta_S$ and signal $\sigma_S$, chooses $o\in\mathcal Q=Q\cup\{\bot\}$ ($\bot$ = exit) according to a **proposal strategy** $p_o(\theta,\sigma_S)\ge 0$, $\sum_{o\in\mathcal Q}p_o(\theta,\sigma_S)=1$. The buyer accepts a cash quote $q\in Q$ with probability $a(\theta_B,\sigma_B,q)\in[0,1]$ (**acceptance strategy**); exit is never accepted. Payoffs for a cash quote are $u_B=a(\theta_B,\Sigma_B,q)[v(C,\theta_B)-q]$ and $u_S=a(\theta_B,\Sigma_B,q)[q-v(C,\theta_S)]$ ((16)-(17)); both are $0$ at $\bot$.
--
--   **Beliefs** $\lambda:S_B\times Q\to\Delta(S_S)$, and the buyer's belief-based value
--   $$E_\lambda[v(C,\theta)\mid\tilde q=q,\Sigma_B=\sigma_B]=\sum_{\sigma_S}\lambda_{\sigma_S}(\sigma_B,q)\,E[v(C,\theta)\mid\Sigma_S=\sigma_S,\Sigma_B=\sigma_B].$$
--
--   **Sequential equilibrium** (§2.2): $(p,a,\lambda)$ such that
--   1. for each buyer signal $\sigma_B$, each $q\in Q$ and $G$-a.e. $\theta$: $a(\theta,\sigma_B,q)=1$ if $E_\lambda[v(C,\theta)\mid q,\sigma_B]-q>0$ and $a(\theta,\sigma_B,q)=0$ if it is $<0$;
--   2. (18) for each seller signal $\sigma_S$, $G$-a.e. $\theta$ and every $o\in\mathcal Q$: $p_o(\theta,\sigma_S)>0$ implies $o$ maximizes $E[u_S(o',a)\mid\Sigma_S=\sigma_S,\theta_S=\theta]$ over $o'\in\mathcal Q$, where for a cash quote $q$ this equals $\sum_{\sigma_B}\Pr[\Sigma_B=\sigma_B\mid\Sigma_S=\sigma_S]\,(q-E[v(C,\theta)\mid\sigma_S,\sigma_B])\,E[a(\theta_B,\sigma_B,q)]$;
--   3. (19)-(20) with $\ell_o(\sigma_S)=\int p_o(\theta,\sigma_S)\,dG(\theta)$: at every quote $q$ reached with positive probability given $\sigma_B$, $\lambda_{\sigma_S}(\sigma_B,q)=\ell_q(\sigma_S)\Pr[\Sigma_S=\sigma_S\mid\Sigma_B=\sigma_B]/\sum_{\sigma_S'}\ell_q(\sigma_S')\Pr[\Sigma_S=\sigma_S'\mid\Sigma_B=\sigma_B]$;
--   4. (21) there are $\ell^n_o(\sigma_S)>0$ with $\sum_{o\in\mathcal Q}\ell^n_o(\sigma_S)=1$ and $\ell^n_o(\sigma_S)\to\ell_o(\sigma_S)$ such that at every quote reached with probability zero given $\sigma_B$, $\lambda_{\sigma_S}(\sigma_B,q)$ is the limit of the same ratio with $\ell^n$ in place of $\ell$.
--
--   **Gains from trade** (22)-(25):
--   $$W_S(p,a,\lambda)=\frac{1}{FB}\,E\Big[\sum_{q\in Q}p_q(\theta_S,\Sigma_S)\,a(\theta_B,\Sigma_B,q)\,(v(C,\theta_B)-v(C,\theta_S))\Big],$$
--   $W^-_S(I,Q)=\inf$ of $W_S$ over all sequential equilibria on $Q$, and $W^-_S(I)=\inf_{(Q_n)\text{ fine}}\liminf_n W^-_S(I,Q_n)$.
--
--   **Formalization Note** Menus are `Finset ℝ`, $\mathcal Q$ is `Option Q` with `none` $=\bot$. Strategies are real-valued and measurable in the type. Conditions 1 and 3-4 range over buyer signals of positive probability and condition 2 over seller signals of positive probability (conditioning on a null signal is undefined). One tremble sequence $\ell^n$ serves all off-path pairs (Kreps-Wilson consistency). `gain e` is the expectation in (22) and `W e = gain e / FB`. `WminusQ` and `Wminus` are taken in `EReal`, so an empty set of equilibria gives $+\infty$, never $0$.
-- source:
--   Durvasula, Roughgarden, The Price of Anarchy in Markets for Lemons, STOC 2027 submission (manuscript sha256 5a158b50…), pp. 14-17, §2.1-§2.3, (16)-(25)

import Mathlib
import Definitions.Def_LemonsPoA_TwoSided_Monopoly
import Definitions.Def_LemonsPoA_TwoSided_Market

open MeasureTheory Filter Topology

namespace LemonsPoA.TwoSided

/-- A (mixed) proposal strategy of the seller on the finite menu `Q` (§2.1):
`p θ σS o` is the probability of choosing `o ∈ Q ∪ {⊥}` (`Option Q`, with `none = ⊥` the exit)
by a seller of type `θ` with signal `σS`; measurable in the type. -/
structure ProposalStrategy (Θ : Type*) [MeasurableSpace Θ] (SS : Type*) (Q : Finset ℝ) where
  p : Θ → SS → Option Q → ℝ
  nonneg : ∀ θ σ o, 0 ≤ p θ σ o
  sum_eq_one : ∀ θ σ, ∑ o, p θ σ o = 1
  measurable : ∀ σ o, Measurable fun θ => p θ σ o

/-- An acceptance strategy of the buyer (§2.1): `a θ σB q ∈ [0, 1]` is the probability that a
buyer of type `θ` with signal `σB` accepts the cash quote `q ∈ Q`; measurable in the type.
Exit is never accepted (`a(θ, σ, ⊥) = 0`, see `AcceptanceStrategy.acc`). -/
structure AcceptanceStrategy (Θ : Type*) [MeasurableSpace Θ] (SB : Type*) (Q : Finset ℝ) where
  a : Θ → SB → Q → ℝ
  mem_Icc : ∀ θ σ q, a θ σ q ∈ Set.Icc (0 : ℝ) 1
  measurable : ∀ σ q, Measurable fun θ => a θ σ q

/-- Acceptance probability extended to `Q ∪ {⊥}`, with `a(θ, σ, ⊥) = 0`. -/
def AcceptanceStrategy.acc {Θ : Type*} [MeasurableSpace Θ] {SB : Type*} {Q : Finset ℝ}
    (A : AcceptanceStrategy Θ SB Q) (θ : Θ) (σ : SB) : Option Q → ℝ
  | none => 0
  | some q => A.a θ σ q

/-- Receiver beliefs `λ : S_B × Q → Δ(S_S)` (§2.2): `lam σB q σS` is the probability the buyer
with signal `σB` assigns to the seller signal `σS` after the cash quote `q`. -/
structure Beliefs (SS SB : Type*) [Fintype SS] (Q : Finset ℝ) where
  lam : SB → Q → SS → ℝ
  nonneg : ∀ σB q σS, 0 ≤ lam σB q σS
  sum_eq_one : ∀ σB q, ∑ σS, lam σB q σS = 1

/-- An assessment `(p, a, λ)` of the seller-proposer game on menu `Q`. -/
structure Assessment (Θ : Type*) [MeasurableSpace Θ] (SS SB : Type*) [Fintype SS]
    (Q : Finset ℝ) where
  p : ProposalStrategy Θ SS Q
  a : AcceptanceStrategy Θ SB Q
  lam : Beliefs SS SB Q

namespace Market

variable {Θ : Type*} [MeasurableSpace Θ] {SS SB : Type*} [Fintype SS] [Fintype SB]
variable (M : Market Θ SS SB) {Q : Finset ℝ}

/-- The buyer's belief-based value `E_λ[v(C, θ) | q̃ = q, Σ_B = σB]
= Σ_{σS} λ_{σS}(σB, q) E[v(C, θ) | Σ_S = σS, Σ_B = σB]` (p. 16), using that `v` is affine in `c`. -/
noncomputable def buyerValue (L : Beliefs SS SB Q) (σB : SB) (q : Q) (θ : Θ) : ℝ :=
  ∑ σS, L.lam σB q σS * M.v (M.m σS σB) θ

/-- `E[a(θ_B, σB, q)]`, the acceptance probability of quote `q` by a buyer with signal `σB`,
averaged over the buyer's type `θ_B ∼ G`. -/
noncomputable def accProb (A : AcceptanceStrategy Θ SB Q) (σB : SB) (q : Q) : ℝ :=
  ∫ θ, A.a θ σB q ∂M.G

/-- The seller's interim expected payoff `E[u_S(o, a) | Σ_S = σS, θ_S = θ]` from `o ∈ Q ∪ {⊥}`
((17), with `u_S(⊥, a) = 0`): for a cash quote `q`,
`Σ_{σB} Pr[Σ_B = σB | Σ_S = σS] (q - E[v(C, θ) | Σ_S = σS, Σ_B = σB]) E[a(θ_B, σB, q)]`. -/
noncomputable def sellerPayoff (A : AcceptanceStrategy Θ SB Q) (σS : SS) (θ : Θ) :
    Option Q → ℝ
  | none => 0
  | some q => ∑ σB, M.condB σS σB * (((q : ℝ) - M.v (M.m σS σB) θ) * M.accProb A σB q)

/-- `ℓ_o(σS) = ∫ p_o(θ, σS) dG(θ)` (19). -/
noncomputable def ell (P : ProposalStrategy Θ SS Q) (o : Option Q) (σS : SS) : ℝ :=
  ∫ θ, P.p θ σS o ∂M.G

/-- `Σ_{σS} ℓ_q(σS) Pr[Σ_S = σS | Σ_B = σB]`, the probability of the quote `q` given the buyer's
signal `σB`; the denominator of (20). -/
noncomputable def reach (P : ProposalStrategy Θ SS Q) (σB : SB) (q : Q) : ℝ :=
  ∑ σS, M.ell P (some q) σS * M.condS σS σB

/-- Sequential equilibrium of the seller-proposer game (§2.2, conditions 1–4), for the market
`M` and menu `Q`. Buyer signals range over signals of positive probability, seller signals
likewise; one tremble sequence `ℓⁿ` serves every off-path pair `(σB, q)`. -/
structure IsSeqEq (e : Assessment Θ SS SB Q) : Prop where
  /-- Condition 1: sequential rationality of the buyer, for `G`-a.e. type. -/
  receiver : ∀ σB : SB, 0 < M.probB σB → ∀ q : Q, ∀ᵐ θ ∂M.G,
    (0 < M.buyerValue e.lam σB q θ - q → e.a.a θ σB q = 1) ∧
    (M.buyerValue e.lam σB q θ - q < 0 → e.a.a θ σB q = 0)
  /-- Condition 2, (18): the seller only uses interim best responses, for `G`-a.e. type. -/
  proposer : ∀ σS : SS, 0 < M.probS σS → ∀ᵐ θ ∂M.G, ∀ o : Option Q, 0 < e.p.p θ σS o →
    ∀ o' : Option Q, M.sellerPayoff e.a σS θ o' ≤ M.sellerPayoff e.a σS θ o
  /-- Condition 3, (20): Bayes' rule at quotes reached with positive probability. -/
  onPath : ∀ σB : SB, 0 < M.probB σB → ∀ q : Q, 0 < M.reach e.p σB q → ∀ σS : SS,
    e.lam.lam σB q σS = M.ell e.p (some q) σS * M.condS σS σB / M.reach e.p σB q
  /-- Condition 4, (21): consistency off path with one full-support tremble sequence. -/
  offPath : ∃ ℓn : ℕ → SS → Option Q → ℝ,
    (∀ n σS o, 0 < ℓn n σS o) ∧ (∀ n σS, ∑ o, ℓn n σS o = 1) ∧
    (∀ σS o, Tendsto (fun n => ℓn n σS o) atTop (𝓝 (M.ell e.p o σS))) ∧
    ∀ σB : SB, 0 < M.probB σB → ∀ q : Q, M.reach e.p σB q = 0 → ∀ σS : SS,
      Tendsto (fun n => ℓn n σS (some q) * M.condS σS σB /
          ∑ σS', ℓn n σS' (some q) * M.condS σS' σB) atTop (𝓝 (e.lam.lam σB q σS))

/-- Expected gains from trade at an assessment, the expectation in (22):
`E[Σ_{q ∈ Q} p_q(θ_S, Σ_S) a(θ_B, Σ_B, q) (v(C, θ_B) - v(C, θ_S))]`. -/
noncomputable def gain (e : Assessment Θ SS SB Q) : ℝ :=
  M.expect fun c σS σB θS θB =>
    ∑ q : Q, e.p.p θS σS (some q) * e.a.a θB σB q * (M.v c θB - M.v c θS)

/-- `W_S(p, a, λ)` (22): gains from trade as a fraction of first-best. -/
noncomputable def W (e : Assessment Θ SS SB Q) : ℝ := M.gain e / M.FB

variable (Q) in
/-- `W⁻_S(I, Q)` (23): the infimum of `W_S` over all sequential equilibria on menu `Q`, in
`EReal` (`+∞` if there are none). -/
noncomputable def WminusQ : EReal :=
  ⨅ (e : Assessment Θ SS SB Q) (_ : M.IsSeqEq e), ((M.W e : ℝ) : EReal)

/-- `W⁻_S(I)` (25): the infimum over fine menu sequences `(Q n)` of
`liminf_n W⁻_S(I, Q n)`, in `EReal`. -/
noncomputable def Wminus : EReal :=
  ⨅ (Qs : ℕ → Finset ℝ) (_ : IsFine Qs), liminf (fun n => M.WminusQ (Qs n)) atTop

end Market

end LemonsPoA.TwoSided


