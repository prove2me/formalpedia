-- Prove2me | Definitions.Def_SliceLinearity_Tests_FiniteFourier
-- name    : SliceLinearity_Tests_FiniteFourier
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:37:14.16555+00:00
-- url     : https://prove2.me/theorems/d8e509c6-14e9-4ebf-8d4c-98ac75aa384c
-- title:
--   Weighted norms and Fourier analysis on a finite vector space; the mixed Kiwi test average $\Lambda_{k,\lambda}$
-- statement:
--   Let $V$ be a finite vector space over a finite field $\mathbb F_q$. Distributions on $V$ are real weight functions.
--
--   1. $\langle f,g\rangle_\mu=\mathbb E_{x\sim\mu}[f(x)\overline{g(x)}]$ and $\|f\|_{2,\mu}=(\mathbb E_{x\sim\mu}|f(x)|^2)^{1/2}$ (Definition 2.1). $\|h\|_{L^1}=\mathbb E_{x\sim V}|h(x)|$ is the uniform $L^1$ norm.
--   2. The characters of $V$ are its additive characters $\psi:V\to\mathbb C$. The Fourier coefficient is $\hat u(\psi)=\mathbb E_{x\sim V}[u(x)\overline{\psi(x)}]$, and $\|\hat u\|_{\ell_1}=\sum_\psi|\hat u(\psi)|$ uses counting measure on characters (Definition 2.2).
--   3. **Kiwi relation** (11). Fix $k\ge3$ and write $k=2r+s$ with $s\in\{1,2\}$. For $\lambda\in\mathbb F_q^*$, list the queries as $x_1,\dots,x_s,y_1,z_1,\dots,y_r,z_r$. Then
--   $$P_{k,\lambda}=\Big\{(x,y,z)\in H^k:\ \lambda\sum_{i=1}^s(-1)^{i-1}x_i+\sum_{j=1}^r(y_j-z_j)=0\Big\}.$$
--   4. **Mixed test average** (Definition 4.3). Over uniform tuples of $P_{k,\lambda}$,
--   $$\Lambda_{k,\lambda}(u_1,\dots,u_k)=\mathbb E\Big[u_1(x_1)\prod_{i=2}^s\overline{u_i(x_i)}\prod_{j=1}^r u_{s+2j-1}(y_j)\overline{u_{s+2j}(z_j)}\Big].$$
--
--   **Formalization Note** The space $H$ (the paper's span of a support) is an arbitrary finite $\mathbb F$-vector space, and characters are Mathlib's `AddChar V ℂ`. Queries are 0-indexed: query $i<s$ is $x_{i+1}$, and after those the queries alternate $y_j,z_j$.
-- source:
--   Aydin, Larsen, Mittal, Richelson, Roy, Low Soundness Linearity Testing on Subsets of the Hypercube, STOC 2027 submission (manuscript sha256 457be236…), §2 pp. 8–9 (PDF 10–11): Definitions 2.1, 2.2; §4.1 p. 21 (PDF 23): relation (11), Definition 4.3

import Mathlib

set_option autoImplicit false

namespace SliceLinearity.Tests

/-! # Weighted norms and Fourier analysis on a finite vector space; the Kiwi mixed test average

Aydin, Larsen, Mittal, Richelson, Roy, *Low Soundness Linearity Testing on Subsets of the Hypercube*,
STOC 2027 submission (manuscript sha256 457be236…), §2 pp. 8–9 (PDF 10–11, Definitions 2.1, 2.2),
§4.1 p. 21 (PDF 23, relation (11) and Definition 4.3).

`V` is a finite vector space over a finite field `F`; distributions on `V` are real weight
functions. Characters are the additive characters `ψ : V → ℂ` (Mathlib's `AddChar V ℂ`); the
Fourier coefficient `û(ψ) = ⟨u, ψ⟩ = E_{x∼V}[u(x) · conj(ψ(x))]` uses the uniform measure, and
`ℓ1` norms of coefficients use counting measure on the characters. -/

open Classical in
/-- `⟨f, g⟩_μ = E_{x∼μ}[f(x) · conj(g(x))]` for a weight function `μ` on a finite type. -/
noncomputable def innerV {V : Type*} [Fintype V] (μ : V → ℝ) (f g : V → ℂ) : ℂ :=
  ∑ x, (μ x : ℂ) * f x * (starRingEnd ℂ) (g x)

/-- `‖f‖_{2,μ} = (E_{x∼μ}|f(x)|²)^{1/2}`. -/
noncomputable def normV {V : Type*} [Fintype V] (μ : V → ℝ) (f : V → ℂ) : ℝ :=
  Real.sqrt (∑ x, μ x * ‖f x‖ ^ 2)

/-- The uniform `L¹` norm `‖h‖₁ = E_{x∼V}|h(x)|`. -/
noncomputable def l1Unif {V : Type*} [Fintype V] (h : V → ℂ) : ℝ :=
  (∑ x, ‖h x‖) / (Fintype.card V : ℝ)

/-- The Fourier coefficient `û(ψ) = E_{x∼V}[u(x) · conj(ψ(x))]` (Definition 2.2). -/
noncomputable def fourierV {V : Type*} [AddCommGroup V] [Fintype V] (u : V → ℂ)
    (ψ : AddChar V ℂ) : ℂ :=
  (∑ x, u x * (starRingEnd ℂ) (ψ x)) / (Fintype.card V : ℂ)

/-- `‖û‖_{ℓ1} = ∑_ψ |û(ψ)|`, summed over all additive characters of `V`. -/
noncomputable def fourierL1V {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
    (u : V → ℂ) : ℝ :=
  ∑ ψ : AddChar V ℂ, ‖fourierV u ψ‖

/-- `s ∈ {1, 2}` with `k = 2r + s`: `s = 2` for even `k`, `s = 1` for odd `k` (p. 21). -/
def kiwiS (k : ℕ) : ℕ := if Even k then 2 else 1

/-- The coefficient of query `i` (0-indexed) in relation (11):
`λ · ∑_{i=1}^{s} (−1)^{i−1} xᵢ + ∑_{j=1}^{r} (y_j − z_j) = 0`, with the queries listed as
`x₁, …, x_s, y₁, z₁, …, y_r, z_r`. -/
def kiwiCoeff {F : Type*} [Field F] (k : ℕ) (lam : F) (i : Fin k) : F :=
  if i.val < kiwiS k then lam * (-1) ^ i.val
  else if Even (i.val - kiwiS k) then 1 else -1

/-- Whether query `i` (0-indexed) is conjugated in `Λ_{k,λ}` (Definition 4.3): `x₂` (when `s = 2`)
and every `z_j`. -/
def kiwiConj (k : ℕ) (i : Fin k) : Prop :=
  (i.val < kiwiS k ∧ i.val = 1) ∨ (kiwiS k ≤ i.val ∧ Odd (i.val - kiwiS k))

open Classical in
/-- The relation `P_{k,λ} ⊆ H^k` of (11). -/
noncomputable def kiwiRel {F H : Type*} [Field F] [AddCommGroup H] [Module F H] [Fintype H]
    (k : ℕ) (lam : F) : Finset (Fin k → H) :=
  Finset.univ.filter fun t => ∑ i, kiwiCoeff k lam i • t i = 0

open Classical in
/-- The mixed test average `Λ_{k,λ}(u₁, …, u_k) = E_{(x,y,z)∼P_{k,λ}}[u₁(x₁) ∏_{i=2}^{s} conj(uᵢ(xᵢ))
∏_{j=1}^{r} u_{s+2j−1}(y_j) conj(u_{s+2j}(z_j))]` over uniform tuples of `P_{k,λ}` (Definition 4.3). -/
noncomputable def mixedAvg {F H : Type*} [Field F] [AddCommGroup H] [Module F H] [Fintype H]
    (k : ℕ) (lam : F) (u : Fin k → H → ℂ) : ℂ :=
  (∑ t ∈ kiwiRel (F := F) (H := H) k lam,
      ∏ i, if kiwiConj k i then (starRingEnd ℂ) (u i (t i)) else u i (t i)) /
    ((kiwiRel (F := F) (H := H) k lam).card : ℂ)

end SliceLinearity.Tests


