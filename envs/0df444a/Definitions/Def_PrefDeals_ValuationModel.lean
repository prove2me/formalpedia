-- Prove2me | Definitions.Def_PrefDeals_ValuationModel
-- name    : PrefDeals_ValuationModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:18:03.225945+00:00
-- url     : https://prove2.me/theorems/cab3f1bd-b19e-4dfd-b672-6cd922c29479
-- title:
--   Common-value valuation model: $v_j=\eta_0+\nu_j$ with independent components
-- statement:
--   Fix a probability space $(\Omega,\mathcal F,P)$ and $n$ buyers $j\in\{0,\dots,n-1\}$. A **valuation model** consists of
--
--   1. a **common value component** $\eta_0:\Omega\to\mathbb R$ with $\eta_0\in[\underline\eta,\bar\eta]$ almost surely, where $0\le\underline\eta\le\bar\eta$;
--   2. **private signals** $\nu_j:\Omega\to\mathbb R$, where $\nu_j$ has a Lebesgue density $f_j$ (the paper's $f^{\nu_j}$, p.25) that vanishes outside $[\underline\nu_j,\bar\nu_j]$, with $0\le\underline\nu_j<\bar\nu_j$;
--   3. joint independence of the $n+1$ random variables $\eta_0,\nu_0,\dots,\nu_{n-1}$.
--
--   The valuation of buyer $j$ for an impression is
--
--   $$
--   v_j=\eta_0+\nu_j .
--   $$
--
--   The paper's *independent valuations* are the case $\eta_0=0$; its *correlated valuations* are the general case.
--
--   The model is the paper's §4 setting: impressions arrive i.i.d., each with a valuation vector $(v_0,\dots,v_{n-1})$ correlated only through the common component. The probability space plays the role of the stream: an impression is a point $\omega$, and per-impression revenues and utilities are expectations.
--
--   **Formalization Note** The law of $\eta_0$ may be any law on $[\underline\eta,\bar\eta]$ (the paper's proofs use a density of $\eta_0$); the private signals keep the paper's densities $f^{\nu_j}$ (p.25), which make ties between buyers null events; they need not be bounded or positive on $[\underline\nu_j,\bar\nu_j]$ (the paper's boundedness and positivity, p.10, concern the margins of $v_i$). The nonnegativity of $\eta_0$ and $\nu_j$ is the paper's normalization "without loss of generality" (p.10).
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, §4, p.10 (valuation model, common value component)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace PrefDeals

/-- **The common-value valuation model of §4.**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, §4, p.10: "Let
`v = (v₁, …, vₙ)` denote the vector of valuations of the buyers for an impression. … We allow the
valuations of the buyers to be correlated via a common value component. More specifically,
`vᵢ = η₀ + νᵢ` where `η₀` is the common value component distributed over `[η̲, η̄]`, and `νᵢ` is the
private signal of buyer `i` distributed over `[ν̲ᵢ, ν̄ᵢ]`, independently from other buyers'
valuations. … we may assume, without loss of generality, that the common value component and
private signals are nonnegative", with `0 ≤ v̲ᵢ < v̄ᵢ` and "the margins are bounded and positive on
`[v̲ᵢ, v̄ᵢ]`".

A `ValuationModel P n` on a probability space `(Ω, P)` consists of
1. a common value `eta0 : Ω → ℝ` with `eta0 ∈ [etaLo, etaHi]` almost surely, `0 ≤ etaLo ≤ etaHi`;
2. private signals `nu j : Ω → ℝ`, `j : Fin n`, where `nu j` has a Lebesgue density `dens j` (the
   paper's p.d.f. `f^{νⱼ}`, p.25) that vanishes outside `[nuLo j, nuHi j]`, with `0 ≤ nuLo j < nuHi j`;
3. joint independence of the `n + 1` random variables `eta0` and `nu j`, `j : Fin n` (indexed by
   `Option (Fin n)`, `none ↦ eta0`, `some j ↦ nu j`).

The valuation of buyer `j` is `ValuationModel.v M j = eta0 + nu j`. The independent case of the
paper (`η₀ = 0`) is `eta0 = 0` almost surely.

**Formalization Note.** The stream of impressions is the probability space `(Ω, P)`: an impression
is a point `ω`, and "drawn independently and identically for each impression" (p.10) is encoded by
working with one draw and computing every per-impression quantity as an expectation (the paper's
minimum purchase constraint is "met (only) in expectation", p.6). The law of `η₀` is any law on
`[η̲, η̄] ⊂ [0, ∞)`; the paper's proofs use a density of `η₀` (p.27), which is not required here.
The signal densities are not required to be bounded or positive on `[ν̲ⱼ, ν̄ⱼ]`: the paper assumes
boundedness and positivity for the margins of `vᵢ` (p.10), not for `νⱼ`, and every model of the
paper is a model here. The existence of the densities `f^{νⱼ}` (p.25) makes ties `vⱼ = vₖ` null. The
nonnegativity of `η₀` and `νⱼ` is the paper's "without loss of generality" shift (p.10). -/
structure ValuationModel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ) where
  /-- The common value component `η₀`. -/
  eta0 : Ω → ℝ
  /-- The private signals `νⱼ`. -/
  nu : Fin n → Ω → ℝ
  measurable_eta0 : Measurable eta0
  measurable_nu : ∀ j, Measurable (nu j)
  /-- `η₀` and the signals `νⱼ` are jointly independent. -/
  indep : iIndepFun (fun o : Option (Fin n) => Option.elim o eta0 nu) P
  /-- The lower end `η̲` of the support of `η₀`. -/
  etaLo : ℝ
  /-- The upper end `η̄` of the support of `η₀`. -/
  etaHi : ℝ
  etaLo_nonneg : 0 ≤ etaLo
  etaLo_le_etaHi : etaLo ≤ etaHi
  eta0_mem : ∀ᵐ ω ∂P, eta0 ω ∈ Set.Icc etaLo etaHi
  /-- The lower end `ν̲ⱼ` of the support of `νⱼ`. -/
  nuLo : Fin n → ℝ
  /-- The upper end `ν̄ⱼ` of the support of `νⱼ`. -/
  nuHi : Fin n → ℝ
  nuLo_nonneg : ∀ j, 0 ≤ nuLo j
  nuLo_lt_nuHi : ∀ j, nuLo j < nuHi j
  /-- The density `fⱼ` of `νⱼ` with respect to Lebesgue measure. -/
  dens : Fin n → ℝ → ℝ
  measurable_dens : ∀ j, Measurable (dens j)
  dens_zero : ∀ j, ∀ x, x ∉ Set.Icc (nuLo j) (nuHi j) → dens j x = 0
  law_nu : ∀ j, P.map (nu j) = volume.withDensity (fun x => ENNReal.ofReal (dens j x))

/-- The valuation `vⱼ = η₀ + νⱼ` of buyer `j` (p.10). -/
def ValuationModel.v {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : ValuationModel P n) (j : Fin n) (ω : Ω) : ℝ :=
  M.eta0 ω + M.nu j ω

end PrefDeals


