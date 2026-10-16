-- Prove2me | Definitions.Def_ContextualAuctions_RevEquiv_Auctions
-- name    : ContextualAuctions_RevEquiv_Auctions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T19:28:46.605553+00:00
-- url     : https://prove2.me/theorems/3ccdf609-b3b5-43b2-aa03-cd07898141ed
-- title:
--   §4 — anonymous standard auction families {A_α}, the equilibrium oracle ψ (properties 1–4), Ψ^µ (display (1)), symmetric equilibrium (Definition 4)
-- statement:
--   This file fixes the standard-auction objects of §4.
--
--   **Families of anonymous standard auctions.** For each context $\alpha$, the auction $\mathcal A_\alpha=(r(\alpha),M_\alpha)$ has reserve price $r(\alpha)$ and allocates the item to every highest bid that meets the reserve (ties win). $M_\alpha(b,\{b_i\}_{i=1}^{n-1})$ is the payment of a buyer bidding $b$ when the others bid $b_1,\dots,b_{n-1}$. The family is assumed to satisfy:
--   1. payments of nonnegative bids are nonnegative;
--   2. anonymity: $M_\alpha(b,\{b_i\})$ is invariant under any permutation of the competing bids;
--   3. measurability: for measurable bidding functions, $\alpha\mapsto M_\alpha(b(\alpha),\{b_i(\alpha)\})$ is measurable (stated for measurable maps on any measurable space).
--
--   **The oracle.** For every context $\alpha\in A$ and every atomless probability law $\mathcal H$ on $[0,\omega]$, the oracle returns a bidding strategy $\psi^{\mathcal H}_\alpha$ such that, for all $x\in[0,\omega]$:
--   1. $\psi^{\mathcal H}_\alpha(x)\in\arg\max_{b\ge0}\ \mathbb E_{X_i\sim\mathcal H}\big[x\,\mathbb 1\{b\ge\max(r(\alpha),\{\psi^{\mathcal H}_\alpha(X_i)\}_i)\}-M_\alpha(b,\{\psi^{\mathcal H}_\alpha(X_i)\}_i)\big]$, with $X_1,\dots,X_{n-1}$ i.i.d. $\mathcal H$;
--   2. $\psi^{\mathcal H}_\alpha$ is nondecreasing on $[0,\omega]$, and $\psi^{\mathcal H}_\alpha(x)\ge r(\alpha)$ if and only if $x\ge r(\alpha)$;
--   3. the expected payment of a zero-value bidder is zero: $\mathbb E[M_\alpha(\psi^{\mathcal H}_\alpha(0),\{\psi^{\mathcal H}_\alpha(X_i)\}_i)]=0$;
--   4. the law of $\psi^{\mathcal H}_\alpha(X)$, $X\sim\mathcal H$, is atomless.
--
--   **Paced strategy.** With $\lambda^\mu_\alpha$ the law of the paced value $w^T\alpha/(1+\mu(w,B))$ under $(w,B)\sim G$ and $\psi^\mu_\alpha:=\psi^{\lambda^\mu_\alpha}_\alpha$,
--   $$\Psi^\mu(w,B,\alpha)=\psi^\mu_\alpha\Big(\frac{w^T\alpha}{1+\mu(w,B)}\Big).\qquad(1)$$
--
--   **Definition 4.** A strategy $\beta^*$ is a symmetric equilibrium for the family if it is jointly measurable and, for $G$-almost every $(w,B)$, the bid function $\beta^*(w,B,\cdot)$ solves
--   $$\max_{b}\ \mathbb E_{\alpha,\{\theta_i\}}\big[w^T\alpha\,\mathbb 1\{b(\alpha)\ge\max(r(\alpha),\{\beta^*(\theta_i,\alpha)\}_i)\}-M_\alpha(b(\alpha),\{\beta^*(\theta_i,\alpha)\}_i)\big]\ \text{ s.t. }\ \mathbb E_{\alpha,\{\theta_i\}}\big[M_\alpha(b(\alpha),\{\beta^*(\theta_i,\alpha)\}_i)\big]\le B,$$
--   over admissible $b$ (measurable, almost surely nonnegative, with integrable payment). The file also defines the dual function of this problem when the competitors use $\Psi^\mu$:
--   $$q^\mu_{\mathcal A}(w,B,t)=\sup_b\ \mathbb E\big[w^T\alpha\,\mathbb 1\{\text{win}\}-(1+t)M_\alpha(b(\alpha),\{\Psi^\mu(\theta_i,\alpha)\}_i)\big]+tB .$$
--
--   **Formalization Note** The allocation rule is fixed by "highest bidder wins", so a family is given by its payment rule and its oracle; the reserve price is the model's $r$. In property 1, expected payments are taken in $[0,\infty]$; the maximizer has finite expected payment and is compared with every $b\ge0$ of finite expected payment (a bid with infinite expected payment has payoff $-\infty$). Property 4 is stated as $\mathcal H(\{x:\psi^{\mathcal H}_\alpha(x)=y\})=0$ for every $y$. Joint measurability in Definition 4 makes the expectations genuine.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, pp. 11–12, §4: anonymous standard auctions and oracle properties 1–4 (p. 11), Definition 4 (p. 11), display (1) (p. 11)

import Mathlib
import Definitions.Def_ContextualAuctions_RevEquiv_Setting

namespace ContextualAuctions.RevEquiv

open MeasureTheory

open Classical

noncomputable section

/-- A family `{A_α = (r(α), M_α)}` of anonymous standard auctions (§4), with its equilibrium
oracle. The reserve price of `A_α` is the model's `r α`; the allocation rule is "highest bidder
wins" (ties win, as in `wins`), so it is not a field.
* `pay α b bs` is the payment `M_α(b, {b_i})` of a buyer bidding `b` when the other `n - 1`
  buyers bid `bs`;
* `psi α H` is the oracle's bidding strategy `ψ^H_α` for auction `A_α` and value law `H`. -/
structure StdFamily (M : Model) where
  pay : Context M → ℝ → (Fin (M.n - 1) → ℝ) → ℝ
  psi : Context M → Measure ℝ → ℝ → ℝ

/-- `n - 1` i.i.d. draws from `H`. -/
def iidLaw (M : Model) (H : Measure ℝ) : Measure (Fin (M.n - 1) → ℝ) :=
  Measure.pi fun _ : Fin (M.n - 1) => H

/-- Single-auction winning probability of bid `b` in `A_α` when the `n - 1` competitors draw
values i.i.d. from `H` and bid `ψ^H_α`: `P(b ≥ max(r(α), {ψ^H_α(X_i)}))`. -/
def oracleWinProb (M : Model) (fam : StdFamily M) (α : Context M) (H : Measure ℝ) (b : ℝ) : ℝ :=
  (iidLaw M H {ys | M.r α ≤ b ∧ ∀ i, fam.psi α H (ys i) ≤ b}).toReal

/-- Single-auction expected payment `E[M_α(b, {ψ^H_α(X_i)})]`, in `ℝ≥0∞`. -/
def oraclePay (M : Model) (fam : StdFamily M) (α : Context M) (H : Measure ℝ) (b : ℝ) :
    ENNReal :=
  ∫⁻ ys, ENNReal.ofReal (fam.pay α b (fun i => fam.psi α H (ys i))) ∂iidLaw M H

/-- The paper's assumptions on the family (§4, p. 11):
* payments of nonnegative bids are nonnegative (`M : ℝ^n_≥0 → ℝ^n_≥0`);
* anonymity: the payment depends on the competing bids only as a multiset;
* measurability: for measurable bidding functions `b`, `b_i` and context map `a` on any measurable
  space, `x ↦ M_{a(x)}(b(x), {b_i(x)})` is measurable;
* oracle properties 1–4, for every context `α ∈ A` and every atomless probability law `H`
  on `[0, ω]`, at every value `x ∈ [0, ω]`. -/
structure StdFamily.Valid (M : Model) (fam : StdFamily M) : Prop where
  pay_nonneg : ∀ α b (bs : Fin (M.n - 1) → ℝ), 0 ≤ b → (∀ i, 0 ≤ bs i) → 0 ≤ fam.pay α b bs
  anonymous : ∀ α b (bs : Fin (M.n - 1) → ℝ) (σ : Equiv.Perm (Fin (M.n - 1))),
    fam.pay α b (bs ∘ σ) = fam.pay α b bs
  measurable_pay : ∀ (X : Type) [MeasurableSpace X] (a : X → Context M) (b : X → ℝ)
    (bs : Fin (M.n - 1) → X → ℝ), Measurable a → Measurable b → (∀ i, Measurable (bs i)) →
    Measurable (fun x => fam.pay (a x) (b x) (fun i => bs i x))
  /-- Property 1: `ψ^H(x) ∈ argmax_{b ≥ 0} E[x 1{b ≥ max(r, {ψ^H(X_i)})} − M(b, {ψ^H(X_i)})]`.
  The maximizer has finite expected payment, and it beats every `b ≥ 0` of finite expected
  payment (a bid with infinite expected payment has payoff `−∞`). -/
  oracle_eq : ∀ α ∈ M.A, ∀ (H : Measure ℝ), IsProbabilityMeasure H → (∀ y, H {y} = 0) →
    H (Set.Icc 0 (omega M))ᶜ = 0 → ∀ x ∈ Set.Icc 0 (omega M),
      0 ≤ fam.psi α H x ∧ oraclePay M fam α H (fam.psi α H x) < ⊤ ∧
      ∀ b, 0 ≤ b → oraclePay M fam α H b < ⊤ →
        x * oracleWinProb M fam α H b - (oraclePay M fam α H b).toReal ≤
          x * oracleWinProb M fam α H (fam.psi α H x) -
            (oraclePay M fam α H (fam.psi α H x)).toReal
  /-- Property 2: `ψ^H` is nondecreasing, and `ψ^H(x) ≥ r` iff `x ≥ r`. -/
  oracle_mono : ∀ α ∈ M.A, ∀ (H : Measure ℝ), IsProbabilityMeasure H → (∀ y, H {y} = 0) →
    H (Set.Icc 0 (omega M))ᶜ = 0 →
      MonotoneOn (fam.psi α H) (Set.Icc 0 (omega M)) ∧
      ∀ x ∈ Set.Icc 0 (omega M), (M.r α ≤ fam.psi α H x ↔ M.r α ≤ x)
  /-- Property 3: a bidder with zero value has zero payoff at the single-auction equilibrium,
  i.e. `E[M(ψ^H(0), {ψ^H(X_i)})] = 0`. -/
  oracle_zero : ∀ α ∈ M.A, ∀ (H : Measure ℝ), IsProbabilityMeasure H → (∀ y, H {y} = 0) →
    H (Set.Icc 0 (omega M))ᶜ = 0 → oraclePay M fam α H (fam.psi α H 0) = 0
  /-- Property 4: the law of `ψ^H(X)`, `X ~ H`, is atomless. -/
  oracle_atomless : ∀ α ∈ M.A, ∀ (H : Measure ℝ), IsProbabilityMeasure H → (∀ y, H {y} = 0) →
    H (Set.Icc 0 (omega M))ᶜ = 0 → ∀ y, H (fam.psi α H ⁻¹' {y}) = 0

/-- `λ^μ_α`: the law of the paced value `w^T α / (1 + μ(w, B))` when `(w, B) ~ G`. -/
def lam (M : Model) (μ : Buyer M → ℝ) (α : Context M) : Measure ℝ :=
  M.G.map (fun θ => paced M μ θ α)

/-- The value pacing-based strategy `Ψ^μ(w, B, α) := ψ^μ_α(w^T α / (1 + μ(w, B)))` of display (1),
with `ψ^μ_α := ψ^{λ^μ_α}_α`. -/
def Psi (M : Model) (fam : StdFamily M) (μ : Buyer M → ℝ) (θ : Buyer M) (α : Context M) : ℝ :=
  fam.psi α (lam M μ α) (paced M μ θ α)

/-- The payment `M_α(b(α), {β(θ_i, α)})` at the joint draw `ω = (α, (θ_i))`. -/
def payStd (M : Model) (fam : StdFamily M) (β : Buyer M → Context M → ℝ) (b : Context M → ℝ)
    (ω : Context M × (Fin (M.n - 1) → Buyer M)) : ℝ :=
  fam.pay ω.1 (b ω.1) (fun i => β (ω.2 i) ω.1)

/-- An admissible bid in the standard-auction family: measurable, nonnegative for `F`-almost
every context, with an integrable payment. -/
def AdmissibleStd (M : Model) (fam : StdFamily M) (β : Buyer M → Context M → ℝ)
    (b : Context M → ℝ) : Prop :=
  Measurable b ∧ (∀ᵐ α ∂M.F, 0 ≤ b α) ∧ Integrable (payStd M fam β b) (P M)

/-- Expected payment `E[M_α(b(α), {β(θ_i, α)})]`. -/
def paymentStd (M : Model) (fam : StdFamily M) (β : Buyer M → Context M → ℝ)
    (b : Context M → ℝ) : ℝ :=
  ∫ ω, payStd M fam β b ω ∂P M

/-- Expected utility `E[w^T α 1{b(α) ≥ max(r(α), {β(θ_i, α)})} − M_α(b(α), {β(θ_i, α)})]`. -/
def utilityStd (M : Model) (fam : StdFamily M) (β : Buyer M → Context M → ℝ) (θ : Buyer M)
    (b : Context M → ℝ) : ℝ :=
  ∫ ω, ((if wins M β b ω then val M θ ω.1 else 0) - payStd M fam β b ω) ∂P M

/-- `b` solves the budget-constrained problem of Definition 4 for buyer `θ` against `β`. -/
def IsOptimalStd (M : Model) (fam : StdFamily M) (β : Buyer M → Context M → ℝ) (θ : Buyer M)
    (b : Context M → ℝ) : Prop :=
  AdmissibleStd M fam β b ∧ paymentStd M fam β b ≤ θ.2 ∧
  ∀ b', AdmissibleStd M fam β b' → paymentStd M fam β b' ≤ θ.2 →
    utilityStd M fam β θ b' ≤ utilityStd M fam β θ b

/-- Definition 4: `β` is a symmetric equilibrium for the family: jointly measurable, and for
`G`-almost every type, `β(w, B, ·)` is optimal. -/
def IsSymEq (M : Model) (fam : StdFamily M) (β : Buyer M → Context M → ℝ) : Prop :=
  Measurable (Function.uncurry β) ∧ ∀ᵐ θ ∂M.G, IsOptimalStd M fam β θ (β θ)

/-- The dual function of the standard-auction problem when competitors use `Ψ^μ`:
`sup_b E[w^T α 1{wins} − (1 + t) M_α(b(α), {Ψ^μ(θ_i, α)})] + t B`. -/
def qDualStd (M : Model) (fam : StdFamily M) (μ : Buyer M → ℝ) (θ : Buyer M) (t : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ b : Context M → ℝ, AdmissibleStd M fam (Psi M fam μ) b ∧
    v = ∫ ω, ((if wins M (Psi M fam μ) b ω then val M θ ω.1 else 0) -
      (1 + t) * payStd M fam (Psi M fam μ) b ω) ∂P M} + t * θ.2

end

end ContextualAuctions.RevEquiv


