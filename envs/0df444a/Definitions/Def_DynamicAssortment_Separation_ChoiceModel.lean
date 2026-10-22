-- Prove2me | Definitions.Def_DynamicAssortment_Separation_ChoiceModel
-- name    : DynamicAssortment_Separation_ChoiceModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T09:59:50.027187+00:00
-- url     : https://prove2.me/theorems/c04e00eb-e7af-46e6-b656-445a339e8540
-- title:
--   Random-utility choice model: noise density, choice probabilities p_i(S, μ), single-sale profit r(S, μ), assortments 𝒮, optimal selection, ‖·‖_A, gap δ(μ)
-- statement:
--   A retailer sells $N$ products, indexed by $i \in \mathcal N = \{1,\dots,N\}$ (0-based in Lean: `Fin N`). Product $i$ has margin $w_i$ and mean utility $\mu_i \in \mathbb R$; the no-purchase alternative $0$ has mean utility $\mu_0 = 0$. Customer utilities are $U_i = \mu_i + \zeta_i$ with i.i.d. shocks of distribution $F$.
--
--   1. **Noise.** `IsNoiseDensity f` says that $f:\mathbb R\to\mathbb R$ is integrable, positive everywhere and $\int f = 1$; its distribution function is $F(x) = \int_{-\infty}^x f(y)\,dy$ (`noiseCDF`). This is the paper's standing assumption that $F$ is absolutely continuous with an everywhere-positive density.
--   2. **Choice probabilities.** For an assortment $S\subseteq\mathcal N$ and $i\in S$,
--   $$p_i(S,\mu) = \int_{-\infty}^{\infty} \prod_{j\in S\cup\{0\}\setminus\{i\}} F(x-\mu_j)\, dF(x-\mu_i) = \int_{-\infty}^{\infty} \Big(\prod_{j\in S\setminus\{i\}} F(x-\mu_j)\Big) F(x)\, f(x-\mu_i)\,dx,$$
--   and $p_i(S,\mu)=0$ for $i\notin S$ (`choiceProb`). The no-purchase probability is $p_0(S,\mu)=\int \prod_{j\in S}F(x-\mu_j)\,f(x)\,dx$ (`noPurchaseProb`).
--   3. **Profit.** $r(S,\mu)=\sum_{i\in S} w_i\,p_i(S,\mu)$ (`profit`), and $\mathcal S=\{S\subseteq\mathcal N: |S|\le C\}$ (`assortments`).
--   4. **Optimal assortments.** `IsOptimalSelection f w C opt` says that the map $\nu\mapsto S^*(\nu)$ (`opt`) picks, at every mean-utility vector $\nu$, an element of $\arg\max_{S\in\mathcal S} r(S,\nu)$ as in (1). `UniqueOptimum f w C μ S` says that $S$ is the only maximizer at $\mu$.
--   5. **Norm on a set.** $\|\nu\|_A=\max\{|\nu_i|: i\in A\}$, and $0$ for $A=\emptyset$ (`normOn`).
--   6. **Optimality gap.** $\delta(\mu)=\min\{(r(S^*,\mu)-r(S,\mu))/r(S^*,\mu): S\in\mathcal S,\ S\ne S^*\}$ (`optimalityGap`, with value $0$ if no such $S$ exists).
--
--   These objects are the static layer of the model of Sauré and Zeevi (2013): every regret statement of the mission is phrased through them.
--
--   **Formalization Note** The density `f` is a primitive and $F$ is defined from it, so absolute continuity is built in. The no-purchase alternative enters as the factor $F(x)=F(x-\mu_0)$ with $\mu_0=0$. The paper prints $\|\nu\|_A=\max\{\nu_i\}$ without absolute values; it only applies the norm to differences, and the absolute value is used here. $\delta(\mu)$ is defined in the paper's online companion ((13)), which is not available; the local definition is the minimum relative optimality gap named on p. 402. The argmax is a selection, because Algorithm 1 evaluates $S^*$ at estimated vectors where ties are possible.
-- source:
--   Sauré, Zeevi, Optimal Dynamic Assortment Planning with Demand Learning, Manuf. Serv. Oper. Manag. 15(3), 2013, pp. 390–392, §3.1–3.2 (choice probabilities, r(S, μ), 𝒮, (1)), §4.1 (density assumption, p. 392); p. 402, App. A (‖ν‖_A, δ(μ))

import Mathlib

namespace DynamicAssortment.Separation

open MeasureTheory

/-- The idiosyncratic shocks have a density `f`: it is integrable, positive everywhere and
integrates to one (Sauré–Zeevi 2013, §4.1, p. 392: `F` is absolutely continuous with a density
that is positive everywhere). -/
structure IsNoiseDensity (f : ℝ → ℝ) : Prop where
  integrable : Integrable f
  pos : ∀ x, 0 < f x
  integral_eq_one : ∫ x, f x = 1

/-- The distribution function `F x = ∫_{-∞}^x f`. -/
noncomputable def noiseCDF (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in Set.Iic x, f y

/-- Choice probability (p. 391, §3.2): for `i ∈ S`,
`p_i(S, μ) = ∫ ∏_{j ∈ S ∪ {0} \ {i}} F(x - μ_j) dF(x - μ_i)`, with `μ_0 = 0` (the factor
`F x` is the no-purchase alternative) and `dF(x - μ_i) = f(x - μ_i) dx`; `p_i(S, μ) = 0` for
`i ∉ S`. -/
noncomputable def choiceProb {N : ℕ} (f : ℝ → ℝ) (μ : Fin N → ℝ) (S : Finset (Fin N))
    (i : Fin N) : ℝ :=
  if i ∈ S then
    ∫ x, (∏ j ∈ S.erase i, noiseCDF f (x - μ j)) * noiseCDF f x * f (x - μ i)
  else 0

/-- No-purchase probability `p_0(S, μ) = ∫ ∏_{j ∈ S} F(x - μ_j) dF(x)`: the no-purchase
alternative (mean utility `μ_0 = 0`) has the highest utility. -/
noncomputable def noPurchaseProb {N : ℕ} (f : ℝ → ℝ) (μ : Fin N → ℝ)
    (S : Finset (Fin N)) : ℝ :=
  ∫ x, (∏ j ∈ S, noiseCDF f (x - μ j)) * f x

/-- Expected single-sale profit `r(S, μ) = ∑_{i ∈ S} w_i p_i(S, μ)` (p. 391). -/
noncomputable def profit {N : ℕ} (f : ℝ → ℝ) (w : Fin N → ℝ) (μ : Fin N → ℝ)
    (S : Finset (Fin N)) : ℝ :=
  ∑ i ∈ S, w i * choiceProb f μ S i

/-- The feasible assortments `𝒮 = {S ⊆ 𝒩 : |S| ≤ C}` (p. 391). -/
def assortments (N C : ℕ) : Finset (Finset (Fin N)) :=
  (Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card ≤ C)

/-- `opt` is a selection from the argmax (1) at every mean-utility vector:
`opt ν ∈ 𝒮` and `r(S, ν) ≤ r(opt ν, ν)` for all `S ∈ 𝒮`. -/
structure IsOptimalSelection {N : ℕ} (f : ℝ → ℝ) (w : Fin N → ℝ) (C : ℕ)
    (opt : (Fin N → ℝ) → Finset (Fin N)) : Prop where
  mem : ∀ ν, opt ν ∈ assortments N C
  le_opt : ∀ ν, ∀ S ∈ assortments N C, profit f w ν S ≤ profit f w ν (opt ν)

/-- The single-sale problem (1) at `μ` has a unique solution, namely `Sstar`. -/
def UniqueOptimum {N : ℕ} (f : ℝ → ℝ) (w : Fin N → ℝ) (C : ℕ) (μ : Fin N → ℝ)
    (Sstar : Finset (Fin N)) : Prop :=
  ∀ S ∈ assortments N C, profit f w μ S = profit f w μ Sstar → S = Sstar

/-- The max-norm on the coordinates in `A`: `‖ν‖_A = max {|ν_i| : i ∈ A}` (`0` for `A = ∅`).
(App. A, p. 402, prints `max {ν_i : i ∈ A}`; every use is on a difference.) -/
noncomputable def normOn {N : ℕ} (A : Finset (Fin N)) (ν : Fin N → ℝ) : ℝ :=
  ((A.sup fun i => ‖ν i‖₊ : NNReal) : ℝ)

/-- Minimum relative optimality gap
`δ(μ) = min {(r(S*, μ) - r(S, μ)) / r(S*, μ) : S ∈ 𝒮, S ≠ S*}` (defined locally; the paper's
definition, (13), is in its online companion). Value `0` if no feasible `S ≠ S*` exists. -/
noncomputable def optimalityGap {N : ℕ} (f : ℝ → ℝ) (w : Fin N → ℝ) (C : ℕ)
    (μ : Fin N → ℝ) (Sstar : Finset (Fin N)) : ℝ :=
  if h : ((assortments N C).erase Sstar).Nonempty then
    ((assortments N C).erase Sstar).inf' h
      (fun S => (profit f w μ Sstar - profit f w μ S) / profit f w μ Sstar)
  else 0

end DynamicAssortment.Separation


