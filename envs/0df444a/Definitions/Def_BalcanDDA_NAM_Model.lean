-- Prove2me | Definitions.Def_BalcanDDA_NAM_Model
-- name    : BalcanDDA_NAM_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:17:16.748242+00:00
-- url     : https://prove2.me/theorems/5565f5c5-9f70-4209-9d31-4a7944076a84
-- title:
--   Neutral affine maximizers: admissible weights, argmax outcome rule, welfare utility $u_\rho$ and the class $\mathcal U$
-- statement:
--   This file sets up the voting model of §5 of Balcan et al. There are $n$ agents and $m$ alternatives. Each agent $i$ has a value $v_i(j)\in\mathbb R$ for each alternative $j$, and a **valuation profile** is the collection $v=(v_1,\dots,v_n)\in\mathbb R^{nm}$.
--
--   1. **Admissible NAM parameters.** A neutral affine maximizer (NAM) is defined by one weight per agent, $\rho=(\rho[1],\dots,\rho[n])\in\mathbb R^n_{\ge 0}$, such that at least one agent is assigned a weight of zero:
--   $$\rho[i]\ge 0\ \text{for all } i,\qquad \{\,i \mid \rho[i]=0\,\}\neq\emptyset .$$
--   An agent of weight zero is called a *sink agent*.
--   2. **Outcome rule.** The social choice function $\psi_\rho$ returns an alternative maximizing the agents' weighted values,
--   $$\psi_\rho(v)\in\operatorname*{argmax}_{j\in[m]}\ \sum_{i=1}^n \rho[i]\,v_i(j).$$
--   The paper fixes no tie-breaking rule, so an outcome rule here is any map $\psi$ that returns, for every weight vector $\rho$ and every profile $v$, some maximizer of the weighted value.
--   3. **Utility.** The utility of the NAM with parameter $\rho$ is the social welfare of its outcome,
--   $$u_\rho(v)=\sum_{i=1}^n v_i\bigl(\psi_\rho(v)\bigr).$$
--   4. **The class.** $\mathcal U=\{\,u_\rho \mid \rho\in\mathbb R^n_{\ge0},\ \{i\mid\rho[i]=0\}\neq\emptyset\,\}$, a set of real-valued functions on valuation profiles.
--
--   The NAM's VCG-style payments (p. 22) do not enter $u_\rho$ and are not modelled. The class $\mathcal U$ is the object whose pseudo-dimension Theorem 5.2 bounds from below.
--
--   **Formalization Note** A profile is `v : Fin n → Fin m → ℝ`, with 0-based indices: the paper's agent $i$ is `i - 1` and its alternatives $1,2,\dots$ are `0, 1, …`. `IsNAMParam ρ` is the admissibility condition, `IsArgmaxSelector ψ` says that `ψ ρ v` maximizes `∑ i, ρ i * v i j` over `j` (for every `ρ`, admissible or not), `welfare ψ ρ v` is $u_\rho(v)$ and `namClass ψ` is $\mathcal U$ for the outcome rule `ψ`. Statements about $\mathcal U$ quantify over every argmax selector `ψ`.
-- source:
--   Balcan et al., How Much Data Is Sufficient to Learn High-Performing Algorithms?, arXiv:1908.02894v4, p. 22, §5 (NAM parameters, social choice function ψ_ρ, utility u_ρ); p. 23, Lemma 5.1 and Theorem 5.2 (the class U)

import Mathlib

namespace BalcanDDA.NAM

/-- An admissible NAM parameter vector (Balcan et al., arXiv:1908.02894v4, p. 22): a weight
`ρ i ≥ 0` for each of the `n` agents, with at least one agent of weight zero (a *sink agent*).
Agents are indexed `0, …, n-1` (the paper's agent `i` is `i - 1`). -/
def IsNAMParam {n : ℕ} (ρ : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ ρ i) ∧ ∃ i, ρ i = 0

/-- `ψ` is a social choice rule that returns, for every weight vector `ρ` and every valuation
profile `v` (`v i j` is agent `i`'s value for alternative `j`), an alternative maximizing the
weighted value `∑ i, ρ i * v i j` (p. 22). No tie-breaking rule is fixed: any maximizer may be
returned. -/
def IsArgmaxSelector {n m : ℕ} (ψ : (Fin n → ℝ) → (Fin n → Fin m → ℝ) → Fin m) : Prop :=
  ∀ (ρ : Fin n → ℝ) (v : Fin n → Fin m → ℝ) (j : Fin m),
    ∑ i, ρ i * v i j ≤ ∑ i, ρ i * v i (ψ ρ v)

/-- The NAM utility (social welfare of its outcome), `u_ρ(v) = ∑ i, v_i(ψ_ρ(v))` (p. 22). -/
def welfare {n m : ℕ} (ψ : (Fin n → ℝ) → (Fin n → Fin m → ℝ) → Fin m)
    (ρ : Fin n → ℝ) (v : Fin n → Fin m → ℝ) : ℝ :=
  ∑ i, v i (ψ ρ v)

/-- The class `U = {u_ρ | ρ ∈ ℝ^n_{≥0}, {i | ρ[i] = 0} ≠ ∅}` of NAM welfare functions on
valuation profiles (p. 22–23), for the outcome rule `ψ`. -/
def namClass {n m : ℕ} (ψ : (Fin n → ℝ) → (Fin n → Fin m → ℝ) → Fin m) :
    Set ((Fin n → Fin m → ℝ) → ℝ) :=
  {u | ∃ ρ : Fin n → ℝ, IsNAMParam ρ ∧ u = welfare ψ ρ}

end BalcanDDA.NAM


