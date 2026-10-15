-- Prove2me | Definitions.Def_SeqLoss_FixedFraction_Setting
-- name    : SeqLoss_FixedFraction_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:32.824109+00:00
-- url     : https://prove2.me/theorems/0dfe13e5-74c9-4456-a991-8cba927e1700
-- title:
--   pp. 7–10 — loss vectors $L^n$, allocations $X(\ell)$, continuous rules, the fixed-fraction rule $\varphi^\lambda$ (Definition 1), elementary problems $e_n$
-- statement:
--   **Loss problems.** A loss chain has agents $N=\{1,\dots,n\}$: agent 1 initiates the chain and agent $i$ causes a loss $\ell_i\ge 0$ to agent $i+1$. An *$n$-loss problem* is a vector $\ell=(\ell_1,\dots,\ell_n)\in L^n=\mathbb R^n_{\ge 0}$, with total loss $L=\ell_1+\dots+\ell_n$.
--
--   **Allocations.** An allocation $x=(x_1,\dots,x_n)$ of $\ell$ assigns each agent a liability $x_i\ge 0$ such that no group of earlier agents is charged less than the losses it caused and the liabilities balance the total loss:
--   $$x_1+\dots+x_m\ \ge\ \ell_1+\dots+\ell_m\quad(m=1,\dots,n-1),\qquad x_1+\dots+x_n=L .$$
--   $X(\ell)$ is the set of allocations of $\ell$.
--
--   **Rules.** The number of agents varies, so a rule $\varphi$ is defined for every $n$: it maps each problem $\ell\in L^n$ to an allocation $\varphi(\ell)=(\varphi_1(\ell),\dots,\varphi_n(\ell))\in X(\ell)$. Rules are continuous in the minimal sense of the paper's footnote 3: $\lim_{a\to 1}\varphi(a\ell)=\varphi(\ell)$ for every $\ell\in L^n$.
--
--   **Fixed-fraction rules (Definition 1).** For $\lambda\in[0,1]$, the rule $\varphi^\lambda$ makes every agent pay the fraction $\lambda$ of the loss she causes and the initiator in addition the residual $(1-\lambda)L$:
--   $$\varphi^\lambda_1(\ell)=\lambda\ell_1+(1-\lambda)L,\qquad \varphi^\lambda_i(\ell)=\lambda\ell_i\quad(i=2,\dots,n).$$
--   $\lambda=1$ is the direct liability rule $\varphi^1(\ell)=\ell$ and $\lambda=0$ the indirect liability rule $\varphi^0(\ell)=(L,0,\dots,0)$.
--
--   **Elementary problems.** The elementary $n$-loss problem is $e_n=(0,\dots,0,1)\in L^n$: only the last agent causes a (unit) loss.
--
--   These objects are the setting of the paper's axiomatic characterization (Theorem 1).
--
--   **Formalization Note.** Agents are `Fin n`, 0-based: the paper's agent $i$ is index $i-1$. A rule is a function `φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)`, total on $\mathbb R^n$; `IsRule φ` requires, for every $n$ and every $\ell\ge 0$, that $\varphi(\ell)\in X(\ell)$ and that $\varphi(a\ell)\to\varphi(\ell)$ as $a\to 1$ (in the product topology on $\mathbb R^n$). Values of $\varphi$ outside $L^n$ carry no meaning, and the limit only involves $a$ near $1$. The prefix constraints run over $m+1=1,\dots,n-1$ agents. $n=0$ is allowed (the paper's $\mathbb N$ starts at 1): the empty vector has exactly one allocation, and every statement is trivial there. `fixedFraction lam` is defined for every real `lam`; the restriction $\lambda\in[0,1]$ is stated wherever the paper makes it.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses: Automated Conflict Resolution Through Smart Contracts, accepted manuscript (2023), Management Science 70(3) 1773–1786, doi:10.1287/mnsc.2023.4772, pp. 7–10: §2 (model, footnotes 2–3, p. 7), §3 Definition 1 (p. 8), elementary problems (p. 10)

import Mathlib

namespace SeqLoss.FixedFraction

/-- A loss vector `ℓ ∈ L^n = ℝ^n_{≥0}`: agent `i` (0-based) causes loss `ℓ i ≥ 0` to agent `i + 1`. -/
def IsLoss {n : ℕ} (ℓ : Fin n → ℝ) : Prop := ∀ i, 0 ≤ ℓ i

/-- The total loss `L = ℓ_1 + ⋯ + ℓ_n`. -/
def total {n : ℕ} (ℓ : Fin n → ℝ) : ℝ := ∑ i, ℓ i

/-- `x ∈ X(ℓ)` (p. 7): liabilities are nonnegative, every proper prefix of agents `1, …, m + 1`
(`m + 1 < n`) pays at least the losses it caused, and the liabilities sum to `L`. -/
def IsAllocation {n : ℕ} (ℓ x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧
  (∀ m : ℕ, m + 1 < n →
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ m), ℓ i ≤
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val ≤ m), x i) ∧
  ∑ i, x i = ∑ i, ℓ i

/-- A (continuous) rule (p. 7 and footnote 3): for every number of agents `n` and every loss
vector `ℓ ∈ L^n`, `φ n ℓ ∈ X(ℓ)`, and `φ(aℓ) → φ(ℓ)` as `a → 1`. Only the values of `φ` on
loss vectors carry meaning. -/
def IsRule (φ : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ n (ℓ : Fin n → ℝ), IsLoss ℓ →
    IsAllocation ℓ (φ n ℓ) ∧
    Filter.Tendsto (fun a : ℝ => φ n (a • ℓ)) (nhds 1) (nhds (φ n ℓ))

/-- The fixed-fraction rule `φ^λ` (Definition 1, p. 8): `φ^λ_1(ℓ) = λ ℓ_1 + (1 - λ) L` and
`φ^λ_i(ℓ) = λ ℓ_i` for `i ≥ 2`. Agent 1 is index `0`. -/
def fixedFraction (lam : ℝ) (n : ℕ) (ℓ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => lam * ℓ i + if i.val = 0 then (1 - lam) * ∑ j, ℓ j else 0

/-- The elementary `n`-loss problem `e_n = (0, …, 0, 1) ∈ L^n` (p. 10): the unit loss is caused
by the last agent, index `n - 1`. -/
def elem (n : ℕ) : Fin n → ℝ := fun i => if i.val + 1 = n then 1 else 0

end SeqLoss.FixedFraction


