-- Prove2me | Definitions.Def_MakespanSparse_Thin_ConfIP
-- name    : MakespanSparse_Thin_ConfIP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:03:27.771868+00:00
-- url     : https://prove2.me/theorems/9d679262-85fc-4321-959f-a16bd27868f4
-- title:
--   §1 (1)–(3), p. 2, and §2–§3, pp. 4–7 — configurations of the knapsack polytope, [conf-IP] and [conf-LP] solutions, simple and complex configurations, the potential Φ
-- statement:
--   Fix a dimension $d \in \mathbb{N}$, a vector of job sizes $\pi \in \mathbb{Z}_{>0}^d$ and a capacity $T \in \mathbb{Z}_{>0}$. The **knapsack polytope** is $\mathcal{P} = \{c \in \mathbb{R}^d_{\ge 0} : \pi \cdot c \le T\}$, and its integral points
--
--   $$Q = \mathbb{Z}^d \cap \mathcal{P} = \{c \in \mathbb{Z}^d_{\ge 0} : \pi \cdot c \le T\}$$
--
--   are the **configurations**: $c_k$ is the number of jobs of size $\pi_k$ packed on one machine of capacity $T$. This module defines the following objects.
--
--   1. **Support.** For $c \in \mathbb{Z}^d_{\ge 0}$, $\operatorname{supp}(c) = \{k : c_k \neq 0\}$.
--   2. **Simple and complex configurations.** A configuration $c$ is *simple* if $|\operatorname{supp}(c)| \le \log_2(T+1)$, and *complex* otherwise.
--   3. **[conf-IP].** Given $b \in \mathbb{Z}^d_{\ge 0}$ and $m \in \mathbb{Z}_{\ge 0}$, a feasible solution is a vector $x \in \mathbb{Z}^Q_{\ge 0}$ of multiplicities with
--      $$\sum_{c \in Q} c\, x_c = b, \qquad \sum_{c \in Q} x_c = m.$$
--      Its support is $\operatorname{supp}(x) = \{c \in Q : x_c \ne 0\}$.
--   4. **The potential** of such an $x$ is $\Phi(x) = \sum_{c \text{ complex}} x_c\, |\operatorname{supp}(c)|$.
--   5. **[conf-LP].** Given $b \in \mathbb{R}^d$ and $m \in \mathbb{R}$, a feasible solution of the LP relaxation is a vector $x \in \mathbb{R}^Q_{\ge 0}$ with the same two equality systems.
--   6. **$Q$ as a point set** in $\mathbb{R}^d$ (used for $\operatorname{conv.hull}(Q)$), and the finite set of simple configurations.
--
--   These are the objects of the configuration integer program for makespan scheduling on identical machines: a solution decomposes the job vector $b$ into $m$ machine packings.
--
--   **Formalization Note** Configurations are functions `Fin d → ℕ`; a configuration is a vector satisfying $\sum_k \pi_k c_k \le T$. A solution $x$ is a finitely supported function `(Fin d → ℕ) →₀ ℕ` (real-valued for [conf-LP]) that is required to vanish off $Q$. The paper allows $b \in \mathbb{R}^d$ for [conf-IP]; every feasible right-hand side is a nonnegative integer vector, so $b$ is taken in $\mathbb{N}^d$ without losing a feasible instance. The logarithm is $\log_2$ (`Real.logb 2`), as fixed on p. 4. The finite set of simple configurations is cut from the box $\{0,\dots,T\}^d$, which contains every configuration when all $\pi_k \ge 1$.
-- source:
--   arXiv:1604.07153v1, §1 (1)–(3), p. 2; §2, p. 4; §1.2 and §3, pp. 3, 5; proof of Theorem 1, p. 6; Corollaries 5–6, pp. 6–7

import Mathlib

namespace MakespanSparse.Thin

/-- `c ∈ Q = ℤ^d ∩ 𝒫`, where `𝒫 = {c ∈ ℝ^d_{≥0} : π · c ≤ T}` is the knapsack polytope (pp. 2, 4).
A configuration is a nonnegative integer vector `c : Fin d → ℕ` with `π · c ≤ T`. -/
def IsConfig {d : ℕ} (π : Fin d → ℕ) (T : ℕ) (c : Fin d → ℕ) : Prop :=
  ∑ k, π k * c k ≤ T

/-- `supp(c) = {k : c_k ≠ 0}` (p. 4). -/
def supp {d : ℕ} (c : Fin d → ℕ) : Finset (Fin d) :=
  Finset.univ.filter (fun k => c k ≠ 0)

/-- A configuration is simple if `|supp(c)| ≤ log₂(T + 1)`, and complex otherwise (pp. 3, 5). -/
def IsSimple {d : ℕ} (T : ℕ) (c : Fin d → ℕ) : Prop :=
  ((supp c).card : ℝ) ≤ Real.logb 2 ((T : ℝ) + 1)

noncomputable instance {d : ℕ} (T : ℕ) : DecidablePred (IsSimple (d := d) T) :=
  fun c => by unfold IsSimple; infer_instance

/-- `x` is a feasible solution of [conf-IP] (1)–(3) (p. 2): `x_c ∈ ℤ_{≥0}` vanishes outside `Q`,
`∑_{c ∈ Q} c · x_c = b` and `∑_{c ∈ Q} x_c = m`. -/
def IsConfIPSolution {d : ℕ} (π : Fin d → ℕ) (T : ℕ) (b : Fin d → ℕ) (m : ℕ)
    (x : (Fin d → ℕ) →₀ ℕ) : Prop :=
  (∀ c ∈ x.support, IsConfig π T c) ∧
  x.sum (fun c n => n • c) = b ∧
  x.sum (fun _ n => n) = m

/-- The potential `Φ(x) = ∑_{complex c} x_c |supp(c)|` (proof of Theorem 1, p. 6). -/
noncomputable def potential {d : ℕ} (T : ℕ) (x : (Fin d → ℕ) →₀ ℕ) : ℕ :=
  ∑ c ∈ x.support.filter (fun c => ¬ IsSimple T c), x c * (supp c).card

/-- `x` is a feasible solution of [conf-LP], the LP relaxation of [conf-IP] (Corollary 6, p. 7):
`x_c ≥ 0` vanishes outside `Q`, `∑_{c ∈ Q} c · x_c = b` and `∑_{c ∈ Q} x_c = m`, with `b ∈ ℝ^d`,
`m ∈ ℝ`. -/
def IsConfLPSolution {d : ℕ} (π : Fin d → ℕ) (T : ℕ) (b : Fin d → ℝ) (m : ℝ)
    (x : (Fin d → ℕ) →₀ ℝ) : Prop :=
  (∀ c ∈ x.support, IsConfig π T c ∧ 0 ≤ x c) ∧
  x.sum (fun c r => r • (fun k => (c k : ℝ))) = b ∧
  x.sum (fun _ r => r) = m

/-- The configurations `Q`, viewed as points of `ℝ^d` (Corollary 5, p. 6). -/
def configSet {d : ℕ} (π : Fin d → ℕ) (T : ℕ) : Set (Fin d → ℝ) :=
  {v | ∃ c : Fin d → ℕ, IsConfig π T c ∧ v = fun k => (c k : ℝ)}

/-- The simple configurations in `Q`, as a finite set (proof of Corollary 5, p. 7). Each
configuration has `c_k ≤ T` once every `π_k ≥ 1`, so the box `{0, …, T}^d` loses none of them. -/
noncomputable def simpleConfigs {d : ℕ} (π : Fin d → ℕ) (T : ℕ) : Finset (Fin d → ℕ) :=
  by classical exact
    (Fintype.piFinset fun _ => Finset.range (T + 1)).filter (fun c => IsConfig π T c ∧ IsSimple T c)

end MakespanSparse.Thin


