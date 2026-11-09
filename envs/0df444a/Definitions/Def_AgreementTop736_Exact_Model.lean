-- Prove2me | Definitions.Def_AgreementTop736_Exact_Model
-- name    : AgreementTop736_Exact_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:19.801764+00:00
-- url     : https://prove2.me/theorems/81b40e2e-03d4-4e7a-97c9-0ceb59ba4d47
-- title:
--   Sampling scheme, agreement test, element-conditioned down-up walks, Poincaré spectral gap and coordinatewise majority
-- statement:
--   This file fixes the finite model of Theorem 7 and of §1.1.
--
--   **Sampling scheme.** $V$ is a finite ground set. A distribution $\mu$ on subsets of $V$ is supported on $N$-element sets, the **top sets** $K$. For every top set $K$ of positive mass, a **downward kernel** $D(\cdot\mid K)$ is a probability distribution on $n$-element subsets $H\subseteq K$, where $0<n<N$, and
--   $$\rho=\frac nN .$$
--   The **induced marginal** and the **upward kernel** are
--   $$\mu_H(H)=\sum_K\mu(K)D(H\mid K),\qquad U(K\mid H)=\frac{\mu(K)D(H\mid K)}{\mu_H(H)} .$$
--
--   **The agreement test.** Given local functions $F_K:K\to\Sigma$ into a finite alphabet $\Sigma$, the test samples $H\sim\mu_H$, then $K,K'$ independently from $U(\cdot\mid H)$, and rejects iff $F_K|_H\ne F_{K'}|_H$. Its rejection probability is
--   $$\tau=\sum_{H,K,K'}\mu_H(H)\,U(K\mid H)\,U(K'\mid H)\,\mathbf 1[\exists x\in H:\ F_K(x)\ne F_{K'}(x)] .$$
--
--   **Element-conditioned walks.** For an element $x$ with $P_K[x\in K]>0$, $\mu_x=\mu(\cdot\mid x\in K)$. The walk $M_x$ moves from $K$ by sampling $H\sim D(\cdot\mid K)$ conditioned on $x\in H$ and then $K'\sim U(\cdot\mid H)$:
--   $$M_x(K,K')=\sum_H\frac{D(H\mid K)\mathbf 1[x\in H]}{P_{H\sim D(\cdot\mid K)}[x\in H]}\,U(K'\mid H).$$
--   It has **spectral gap at least $\gamma$** if for every real function $f$ on top sets
--   $$\gamma\,\mathrm{Var}_{\mu_x}(f)\le\frac12\,\mathbb E_{K\sim\mu_x,\,K'\sim M_x(K,\cdot)}\big(f(K)-f(K')\big)^2 .$$
--   Hypothesis 3 of Theorem 7 asks this for every element of positive marginal mass.
--
--   **Hypotheses 1 and 2.** For every top set $K$ of positive mass: every $x\in K$ satisfies $P_{H\sim D(\cdot\mid K)}[x\in H]=\rho$ (hypothesis 1); and for every $E\subseteq K$, with $m=|E|$ and $Z=|E\cap H|$, $H\sim D(\cdot\mid K)$,
--   $$\mathbb E[Z\mid K]=\rho m,\qquad \mathrm{Var}(Z\mid K)\le\rho(1-\rho)m\qquad\text{(hypothesis 2, display (1))}.$$
--
--   **Majority and disagreement.** $g:V\to\Sigma$ is a **coordinatewise majority** of $F$ if for every element $x$ of positive marginal mass, $g(x)$ maximizes $P_{K\sim\mu_x}[F_K(x)=s]$ over $s\in\Sigma$ (ties broken arbitrarily). The disagreement probability is $P_{K\sim\mu}[F_K\ne g|_K]$.
--
--   These are the objects quantified over by Theorem 7 and by every step of its proof.
--
--   **Formalization Note** Probabilities are finite weighted sums over `Finset V`. $U$ and $\mu_x$ use Lean's convention $t/0=0$, which only touches terms of zero weight. The kernel $D(\cdot\mid K)$ is constrained only for $K$ of positive mass. $F$ is a function `Finset V → V → α`; only its values $F_K(x)$ with $x\in K$ matter, and every comparison is restricted to $K$ or $H$.
-- source:
--   Tali Kaufman, Huy Tuan Pham, Exact Agreement Expansion up to the Top via Non-polarity, STOC 2027 submission #736 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/736.pdf (source.pdf sha256 04ba433ef4a669f9160de90c29bfff3152be2a1d08e50186f52e514c298f5d49), p.4, §1.1 (The agreement test and its associated walks; Spectral gap); p.7, §2 and §2.1 (conventions, coordinatewise majority); p.9, Theorem 7 (hypotheses 1–3, τ)

import Mathlib

/-!
Kaufman–Pham, *Exact Agreement Expansion up to the Top via Non-polarity*, STOC 2027 submission #736:
the sampling scheme of §1.1 (p.4) and Theorem 7 (p.9), the agreement test, the element-conditioned
down-up walks `M_x`, the spectral gap in the paper's Poincaré form (p.4), hypotheses 1–2 of
Theorem 7, coordinatewise majority (§2.1, p.7) and the disagreement probability `P_K[F_K ≠ g|_K]`.
Everything is finite: probabilities are finite weighted sums over `Finset V`.
-/

namespace AgreementTop736.Exact

open Finset

noncomputable section

/-- The data of a sampling scheme on the subsets of a finite ground set `V`: the top distribution
`μ K`, the downward kernel `D K H = D(H | K)`, the top size `N` and the tested size `n`. -/
structure Scheme (V : Type*) where
  /-- `μ K`: the probability of the top set `K`. -/
  μ : Finset V → ℝ
  /-- `D K H = D(H | K)`: the probability of sampling `H` from `K`. -/
  D : Finset V → Finset V → ℝ
  /-- The size of the top sets. -/
  N : ℕ
  /-- The size of the tested sets. -/
  n : ℕ

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Scheme

/-- Standing assumptions of Theorem 7 (p.9) and §1.1 (p.4): `μ` is a probability distribution on
`N`-element sets; for every top set `K` of positive mass, `D(· | K)` is a probability distribution
on `n`-element subsets of `K`; and `0 < n < N`. Nothing is required of `D(· | K)` for `K` of zero
mass ("faces of zero mass are omitted", §2, p.7). -/
structure IsValid (S : Scheme V) : Prop where
  μ_nonneg : ∀ K, 0 ≤ S.μ K
  μ_sum : ∑ K, S.μ K = 1
  card_top : ∀ K, 0 < S.μ K → K.card = S.N
  D_nonneg : ∀ K, 0 < S.μ K → ∀ H, 0 ≤ S.D K H
  D_sum : ∀ K, 0 < S.μ K → ∑ H, S.D K H = 1
  D_support : ∀ K, 0 < S.μ K → ∀ H, 0 < S.D K H → H ⊆ K ∧ H.card = S.n
  n_pos : 0 < S.n
  n_lt_N : S.n < S.N

/-- `ρ = n / N`. -/
def ρ (S : Scheme V) : ℝ := (S.n : ℝ) / S.N

/-- The induced marginal `μ_H(H) = ∑_K μ(K) D(H | K)`. -/
def μH (S : Scheme V) (H : Finset V) : ℝ := ∑ K, S.μ K * S.D K H

/-- The upward kernel `U(K | H) = μ(K) D(H | K) / μ_H(H)` (value `0` when `μ_H(H) = 0`, in which
case the numerator is `0` as well). -/
def U (S : Scheme V) (H K : Finset V) : ℝ := S.μ K * S.D K H / S.μH H

/-- The marginal mass of an element: `P_{K∼μ}[x ∈ K]`. -/
def pointMass (S : Scheme V) (x : V) : ℝ := ∑ K, S.μ K * (if x ∈ K then 1 else 0)

/-- `μ_x(K) = μ(K | x ∈ K)`. Meaningful when `pointMass x > 0`. -/
def μx (S : Scheme V) (x : V) (K : Finset V) : ℝ :=
  S.μ K * (if x ∈ K then 1 else 0) / S.pointMass x

/-- The inclusion probability `P_{H∼D(·|K)}[x ∈ H]`. -/
def incl (S : Scheme V) (K : Finset V) (x : V) : ℝ :=
  ∑ H, S.D K H * (if x ∈ H then 1 else 0)

/-- The element-conditioned down-up walk `M_x(K, K')`: from `K`, sample `H ∼ D(· | K)` conditioned
on `x ∈ H`, then `K' ∼ U(· | H)` (§1.1, p.4; Theorem 7, hypothesis 3). -/
def Mx (S : Scheme V) (x : V) (K K' : Finset V) : ℝ :=
  ∑ H, (S.D K H * (if x ∈ H then 1 else 0) / S.incl K x) * S.U H K'

/-- The variance `Var_π f = ∑ π f² − (∑ π f)²` of `f` under weights `π` (a probability vector in
every use). -/
def variance (π : Finset V → ℝ) (f : Finset V → ℝ) : ℝ :=
  ∑ K, π K * f K ^ 2 - (∑ K, π K * f K) ^ 2

/-- The Dirichlet form `½ E_{K∼μ_x, K'∼M_x(K,·)} (f(K) − f(K'))²` of the walk `M_x`. -/
def dirichlet (S : Scheme V) (x : V) (f : Finset V → ℝ) : ℝ :=
  (1 / 2) * ∑ K, ∑ K', S.μx x K * S.Mx x K K' * (f K - f K') ^ 2

/-- Hypothesis 3 of Theorem 7 in the paper's Poincaré form (§1.1, p.4): for every element `x` of
positive marginal mass, the walk `M_x` has spectral gap at least `γ`, i.e. for every real `f`,
`½ E_{K∼μ_x, K'∼M_x(K,·)} (f(K) − f(K'))² ≥ γ Var_{μ_x}(f)`. -/
def HasConditionedGap (S : Scheme V) (γ : ℝ) : Prop :=
  ∀ x, 0 < S.pointMass x → ∀ f : Finset V → ℝ, γ * variance (S.μx x) f ≤ S.dirichlet x f

/-- Hypothesis 1 of Theorem 7: every element of a top set `K` (of positive mass) lies in
`H ∼ D(· | K)` with probability `ρ`. -/
def UniformInclusion (S : Scheme V) : Prop :=
  ∀ K, 0 < S.μ K → ∀ x ∈ K, S.incl K x = S.ρ

/-- `E[Z | K] = ∑_H D(H | K) Z(H)`. -/
def condMean (S : Scheme V) (K : Finset V) (Z : Finset V → ℝ) : ℝ := ∑ H, S.D K H * Z H

/-- `Var(Z | K) = ∑_H D(H | K) (Z(H) − E[Z | K])²`. -/
def condVar (S : Scheme V) (K : Finset V) (Z : Finset V → ℝ) : ℝ :=
  ∑ H, S.D K H * (Z H - S.condMean K Z) ^ 2

/-- Hypothesis 2 of Theorem 7, display (1): for every top set `K` (of positive mass) and every
`E ⊆ K`, with `m = |E|` and `Z = |E ∩ H|`, `H ∼ D(· | K)`: `E[Z | K] = ρ m` and
`Var(Z | K) ≤ ρ (1 − ρ) m`. -/
def VarianceBound (S : Scheme V) : Prop :=
  ∀ K, 0 < S.μ K → ∀ E, E ⊆ K →
    S.condMean K (fun H => ((E ∩ H).card : ℝ)) = S.ρ * E.card ∧
    S.condVar K (fun H => ((E ∩ H).card : ℝ)) ≤ S.ρ * (1 - S.ρ) * E.card

/-- The joint law of the agreement test: `H ∼ μ_H`, then `K, K'` independent from `U(· | H)`. -/
def testWeight (S : Scheme V) (H K K' : Finset V) : ℝ := S.μH H * S.U H K * S.U H K'

/-- `P[x ∈ H]` for `H ∼ μ_H`. -/
def probInH (S : Scheme V) (x : V) : ℝ := ∑ H, S.μH H * (if x ∈ H then 1 else 0)

variable {α : Type*} [DecidableEq α]

/-- The rejection probability `τ = P_{H,K,K'}[F_K|_H ≠ F_{K'}|_H]` of the agreement test, for local
functions `F K : K → α` (only the values `F K x` with `x ∈ K` matter). -/
def rejectionProb (S : Scheme V) (F : Finset V → V → α) : ℝ :=
  ∑ H, ∑ K, ∑ K', S.testWeight H K K' * (if ∃ x ∈ H, F K x ≠ F K' x then 1 else 0)

/-- `P_{K∼μ_x}[F_K(x) = s]`. -/
def labelFreq (S : Scheme V) (F : Finset V → V → α) (x : V) (s : α) : ℝ :=
  ∑ K, S.μx x K * (if F K x = s then 1 else 0)

/-- `g` is a coordinatewise majority of `F` (§2.1, p.7): for every element `x` of positive marginal
mass, `g x` is a most frequent value of `F_K(x)` under `μ(· | x ∈ K)` (ties broken arbitrarily). -/
def IsCoordMajority (S : Scheme V) (F : Finset V → V → α) (g : V → α) : Prop :=
  ∀ x, 0 < S.pointMass x → ∀ s : α, S.labelFreq F x s ≤ S.labelFreq F x (g x)

/-- The disagreement probability `P_{K∼μ}[F_K ≠ g|_K]`. -/
def disagreementProb (S : Scheme V) (F : Finset V → V → α) (g : V → α) : ℝ :=
  ∑ K, S.μ K * (if ∃ x ∈ K, F K x ≠ g x then 1 else 0)

end Scheme

end

end AgreementTop736.Exact


