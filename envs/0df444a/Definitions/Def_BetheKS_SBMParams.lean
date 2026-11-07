-- Prove2me | Definitions.Def_BetheKS_SBMParams
-- name    : BetheKS_SBMParams
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:34:07.420512+00:00
-- url     : https://prove2.me/theorems/4dbb4f30-9d07-4853-bdba-2a1f5dc7e88e
-- title:
--   Fixed parameters of the stochastic block model with common expected degree $d>1$
-- statement:
--   Fix $r\ge 2$ communities, a symmetric matrix $P\in\mathbb R^{r\times r}$ with nonnegative entries, and a probability distribution $\pi$ on $[r]$ with every $\pi_a>0$. The standing assumption (2.1) is that every community has the same expected degree
--   $$
--   d:=\sum_{j=1}^r P_{ij}\pi_j>1\qquad\text{for every } i\in[r].
--   $$
--   The file also defines:
--
--   1. the **signal matrix** $Q:=P\Pi$, $\Pi=\operatorname{diag}(\pi)$, so $Q_{ij}=P_{ij}\pi_j$;
--   2. the eigenvalues $\mu_1,\dots,\mu_r$ of $Q$ counted with multiplicity (they are real, as $Q$ is similar to $\Pi^{1/2}P\Pi^{1/2}$), and the **informative** ones, $\mu^2>d$ (Definition 2.1);
--   3. the positive informative eigenvalues $\mu^+_1\ge\dots\ge\mu^+_{r_+}>\sqrt d$ and the negative ones $\mu^-_1\le\dots\le\mu^-_{r_-}<-\sqrt d$, with $r_\pm$ their numbers;
--   4. $\pi_{\min}=\min_a\pi_a$;
--   5. the exact-size convention $|\sigma^{-1}(i)|=\pi_i n$ for a label map $\sigma:[n]\to[r]$, and the limit $n\to\infty$ along $\mathcal N_\pi=\{n:\pi_i n\in\mathbb N\ \forall i\}$;
--   6. a **planted eigenbasis**: real eigenfunctions $Q\phi_i=\mu_i\phi_i$, orthonormal in $L^2(\pi)$, with $\mu_1=d$, $\phi_1\propto\mathbf 1$ and $d=\mu_1\ge|\mu_2|\ge\dots\ge|\mu_r|$ (2.2).
--
--   These are the objects every statement of the mission is about.
--
--   **Formalization Note** Communities are `Fin r`, index $0$ being the paper's index $1$. Eigenvalues with multiplicity are the real roots of the characteristic polynomial of $Q$; since $Q$ is diagonalizable, algebraic and geometric multiplicities agree. $\pi_a>0$ is required because the paper's $r$ eigenfunctions orthonormal in $L^2(\pi)$ exist only then. If some $\pi_i$ is irrational, $\mathcal N_\pi$ is empty; that is the paper's own deterministic community-size convention.
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), §2.1, p.3–4 (2.1); §2.2, p.4 (2.2), Definition 2.1; §2.3, p.4; Theorem 2.2, p.4

import Mathlib

set_option autoImplicit false

open Filter

namespace BetheKS

/-- **Fixed parameters of the stochastic block model** — Dong, McKenzie, *Bethe Hessian Recovery
through the Kesten–Stigum Regime*, arXiv:2610.41802 (held version, sha256 4da41e16…), §2.1, p.3–4,
and (2.1), p.4: `r ≥ 2` communities, a symmetric nonnegative matrix `P ∈ ℝ^{r×r}`, a distribution
`π` on `[r]`, and the standing assumption that every vertex has the same expected degree
`d = ∑ⱼ P i j π j > 1`.

**Formalization Note.** Communities are `Fin r`. The distribution is the field `pi`. Every `π a`
is assumed strictly positive: the paper's eigenfunctions `ϕ₁,…,ϕ_r`, orthonormal in `L²(π)`
(§2.3, p.4), exist only then. The common degree `d` is carried as a field together with the
equations `∑ⱼ P i j π j = d`. -/
structure SBMParams (r : ℕ) where
  /-- the connectivity matrix `P` -/
  P : Matrix (Fin r) (Fin r) ℝ
  /-- the community distribution `π` -/
  pi : Fin r → ℝ
  /-- the common expected degree `d` -/
  d : ℝ
  two_le_r : 2 ≤ r
  P_symm : P.IsSymm
  P_nonneg : ∀ i j, 0 ≤ P i j
  pi_pos : ∀ i, 0 < pi i
  pi_sum : ∑ i, pi i = 1
  degree_eq : ∀ i, ∑ j, P i j * pi j = d
  one_lt_d : 1 < d

variable {r : ℕ}

/-- The signal matrix `Q := P Π`, `Π = diag(π)` (§2.2, p.4): `Q i j = P i j π j`. -/
noncomputable def signal (p : SBMParams r) : Matrix (Fin r) (Fin r) ℝ :=
  p.P * Matrix.diagonal p.pi

/-- The eigenvalues `μ₁,…,μ_r` of `Q`, counted with multiplicity, as the multiset of real roots
of its characteristic polynomial (`Q` is similar to the symmetric `Π^{1/2} P Π^{1/2}`, so all of
its eigenvalues are real and algebraic and geometric multiplicities agree). -/
noncomputable def qRoots (p : SBMParams r) : Multiset ℝ :=
  (signal p).charpoly.roots

/-- The informative eigenvalues (Definition 2.1, p.4: `μ² > d`), with multiplicity. -/
noncomputable def informative (p : SBMParams r) : Multiset ℝ :=
  (qRoots p).filter (fun μ => p.d < μ ^ 2)

/-- `μ⁺₁ ≥ ⋯ ≥ μ⁺_{r₊} > √d`: the positive informative eigenvalues, with multiplicity,
in decreasing order (Theorem 2.2, p.4). Index `0` is `μ⁺₁`. -/
noncomputable def posInf (p : SBMParams r) : List ℝ :=
  ((qRoots p).filter (fun μ => Real.sqrt p.d < μ)).sort (· ≥ ·)

/-- `μ⁻₁ ≤ ⋯ ≤ μ⁻_{r₋} < −√d`: the negative informative eigenvalues, with multiplicity,
in increasing order (Theorem 2.2, p.4). Index `0` is `μ⁻₁`. -/
noncomputable def negInf (p : SBMParams r) : List ℝ :=
  ((qRoots p).filter (fun μ => μ < -Real.sqrt p.d)).sort (· ≤ ·)

/-- `r₊`, the number of positive informative eigenvalues with multiplicity. -/
noncomputable def rplus (p : SBMParams r) : ℕ := (posInf p).length

/-- `r₋`, the number of negative informative eigenvalues with multiplicity. -/
noncomputable def rminus (p : SBMParams r) : ℕ := (negInf p).length

/-- The informative eigenvalues of sign `s` (`s = 1`: `µ⁺`, otherwise `µ⁻`), as relabelled in §7,
p.11: "relabel the positive informative eigenvalues … as `µ₁,…,µ_{r₊}`"; for `s = −1` the negative
ones, as used in the proof of Theorem 2.2, p.12. -/
noncomputable def sgnInf (p : SBMParams r) (s : ℝ) : List ℝ := if s = 1 then posInf p else negInf p

/-- `π_min := min_a π_a` (Theorem 2.3, p.5). -/
noncomputable def piMin (p : SBMParams r) : ℝ :=
  Finset.univ.inf' ⟨⟨0, by have := p.two_le_r; omega⟩, Finset.mem_univ _⟩ p.pi

/-- The label map `σ : [n] → [r]` has the exact community sizes `|σ⁻¹(i)| = π_i n` (§2.1, step 1). -/
def IsExactSize (p : SBMParams r) {n : ℕ} (σ : Fin n → Fin r) : Prop :=
  ∀ i, ((Finset.univ.filter (fun u => σ u = i)).card : ℝ) = p.pi i * n

/-- The limit `n → ∞` along `𝒩_π = {n : π_i n ∈ ℕ for all i}`, the sizes for which the exact-size
convention of §2.1 can be met.

**Formalization Note.** If some `π_i` is irrational, `𝒩_π` is empty and this filter is `⊥`; that is
the paper's own deterministic community-size convention (§2.3, p.4). -/
def sizeFilter (p : SBMParams r) : Filter ℕ :=
  atTop ⊓ Filter.principal {n : ℕ | ∀ i, ∃ k : ℕ, p.pi i * n = k}

/-- A **planted eigenbasis** (§2.2, (2.2), and §2.3, p.4): real eigenfunctions `Q ϕ_i = μ_i ϕ_i`,
orthonormal in `L²(π)`, with `μ_1 = d`, `ϕ_1 ∝ 1`, and `d = μ₁ ≥ |μ₂| ≥ ⋯ ≥ |μ_r|`.
Index `0 : Fin r` is the paper's index `1`. -/
def IsPlantedEigenbasis (p : SBMParams r) (μ : Fin r → ℝ) (ϕ : Fin r → Fin r → ℝ) : Prop :=
  (∀ i, (signal p).mulVec (ϕ i) = μ i • ϕ i) ∧
  (∀ i j, ∑ a, p.pi a * ϕ i a * ϕ j a = if i = j then 1 else 0) ∧
  (∀ i : Fin r, i.val = 0 → μ i = p.d ∧ ∃ c : ℝ, ∀ a, ϕ i a = c) ∧
  Antitone (fun i => |μ i|)

end BetheKS


