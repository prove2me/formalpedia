-- Prove2me | Definitions.Def_WrightPDIPM_Termination_Setup
-- name    : WrightPDIPM_Termination_Setup
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:32.127902+00:00
-- url     : https://prove2.me/theorems/2d86aec0-5842-4720-92bc-d30555c3e226
-- title:
--   Finite-termination setting: F°, μ, N₂(θ), N₋∞(γ), the solution sets and optimal partition B, N, ε(A, b, c), the affine-scaling direction (7.1), the estimate (7.40) and the projection (7.41)
-- statement:
--   Let $A \in \mathbb{R}^{m\times n}$, $b \in \mathbb{R}^m$, $c \in \mathbb{R}^n$, with no assumption on the rank of $A$, and consider the standard-form linear program $\min c^{\mathsf T}x$ s.t. $Ax = b$, $x \ge 0$ and its dual $\max b^{\mathsf T}\lambda$ s.t. $A^{\mathsf T}\lambda + s = c$, $s \ge 0$. Vector inequalities are componentwise, $\|\cdot\|$ is the Euclidean norm, and for an index set $S$ we write $v_S$ for the subvector of $v$ with indices in $S$. This file defines:
--
--   1. the **strictly feasible set** $\mathcal F^\circ = \{(x,\lambda,s) : Ax = b,\ A^{\mathsf T}\lambda + s = c,\ x > 0,\ s > 0\}$ and the **duality measure** $\mu = x^{\mathsf T}s/n$;
--   2. the neighborhoods $\mathcal N_2(\theta) = \{(x,\lambda,s) \in \mathcal F^\circ : \|XSe - \mu e\| \le \theta\mu\}$ and $\mathcal N_{-\infty}(\gamma) = \{(x,\lambda,s) \in \mathcal F^\circ : x_i s_i \ge \gamma\mu \text{ for all } i\}$, where $XSe$ is the vector with entries $x_i s_i$;
--   3. the primal and dual **solution sets** $\Omega_P$, $\Omega_D$ (optimal solutions of the two programs) and $\Omega = \Omega_P \times \Omega_D$;
--   4. the **optimal partition** $\mathcal B = \{j : x^*_j \neq 0 \text{ for some } x^* \in \Omega_P\}$, $\mathcal N = \{j : s^*_j \neq 0 \text{ for some } (\lambda^*, s^*) \in \Omega_D\}$, and a **strictly complementary solution**: $(x^*,\lambda^*,s^*) \in \Omega$ with $x^*_i > 0$ for $i \in \mathcal B$ and $s^*_i > 0$ for $i \in \mathcal N$;
--   5. the quantity
--   $$\epsilon(A,b,c) = \min\Bigl(\min_{i\in\mathcal B}\ \sup_{x^*\in\Omega_P} x^*_i,\ \min_{i\in\mathcal N}\ \sup_{(\lambda^*,s^*)\in\Omega_D} s^*_i\Bigr)$$
--   and the constant $C_3 = \epsilon(A,b,c)/n$;
--   6. the **affine-scaling direction**: $(\Delta x, \Delta\lambda, \Delta s)$ with $A^{\mathsf T}\Delta\lambda + \Delta s = 0$, $A\Delta x = 0$, $s_i\Delta x_i + x_i\Delta s_i = -x_i s_i$ for all $i$;
--   7. a solution $\bar w$ of the weighted least-squares problem $\min_w \tfrac12\|\Sigma w\|^2$ s.t. $Hw = h$, for a diagonal $\Sigma$;
--   8. the **partition estimate** $\mathcal B(x,s) = \{i : x_i \ge s_i\}$, $\mathcal N(x,s) = \{1,\dots,n\}\setminus\mathcal B(x,s)$;
--   9. a solution of the **projection problem** of Ye's finite termination procedure:
--   $$\min_{(x^*,\lambda^*,s^*)} \tfrac12\|x^* - x\|^2 + \tfrac12\|s^* - s\|^2 \ \text{ s.t. } Ax^* = b,\ A^{\mathsf T}\lambda^* + s^* = c,\ x^*_i = 0\ (i \in \mathcal N(x,s)),\ s^*_i = 0\ (i \in \mathcal B(x,s)).$$
--
--   These are the objects of Chapter 7 of Wright's book: the affine-scaling step is shown to be $O(\mu)$ near the solution set, and below a threshold on $\mu$ the projection returns an exact strictly complementary solution.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`, matrices `Matrix (Fin m) (Fin n) ℝ`, points are triples `(x, lam, s)`. The Euclidean norm is defined explicitly (`norm2`, `norm2Pair` for a stacked pair, `norm2On` for a subvector) because Mathlib's default norm on `Fin n → ℝ` is the sup norm. $\epsilon(A,b,c)$ is the minimum over all $n$ indices of a per-index term: $\sup_{\Omega_P} x^*_i$ for $i \in \mathcal B$, $\sup_{\Omega_D} s^*_i$ for $i \in \mathcal N$, and $0$ for an index in neither set (impossible when $\Omega \ne \emptyset$ by the Goldman–Tucker theorem). The sups are real `sSup`s; they agree with the book's whenever $\mathcal F^\circ \ne \emptyset$, because then $\Omega_P$ and the $s^*$-components of $\Omega_D$ are nonempty and bounded; every theorem using $\epsilon$ is vacuous when $\mathcal F^\circ = \emptyset$. For $n = 0$ the empty minimum is $0$ (the book's would be $+\infty$); no statement depends on that value. Directions are given by their linear equations, never by a closed-form solution. In the projection problem $\lambda^*$ does not enter the objective.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 5, Eq. (1.7b); p. 7, Eq. (1.11); p. 9, Eqs. (1.15)–(1.16); p. 24 (Ω_P, Ω_D, Ω); p. 27, Eq. (2.11); p. 56, Eq. (3.5); p. 101, Eq. (5.26); p. 102, Eq. (5.32); p. 129, Eq. (7.1); p. 131, Eq. (7.7); p. 146, Eq. (7.40); p. 147, Eq. (7.41)

import Mathlib

/-!
# Wright, *Primal-Dual Interior-Point Methods* (SIAM 1997), Chapter 7: termination setting

The standard-form pair (2.1) `min cᵀx s.t. Ax = b, x ≥ 0` and (2.2) `max bᵀλ s.t. Aᵀλ + s = c,
s ≥ 0` (p. 22), with `A ∈ ℝ^{m×n}` arbitrary (no rank assumption). Vectors are `Fin n → ℝ`,
primal-dual points are triples `(x, λ, s)`, vector inequalities are componentwise.

* `norm2`, `norm2Pair`, `norm2On` — the Euclidean norm of a vector, of a stacked pair `(u, v)`,
  and of the subvector `v_S` indexed by `S` (Notation, p. xvii).
* `Fo` — the strictly feasible set `F°` (1.7b) (p. 5).
* `mu` — the duality measure `μ = xᵀs/n` (1.11) (p. 7).
* `N2`, `NegInf` — the neighborhoods `N₂(θ)` (1.15) and `N_{-∞}(γ)` (1.16) (p. 9).
* `OmegaP`, `OmegaD`, `Omega` — the primal, dual and primal-dual solution sets (p. 24).
* `indexB`, `indexN` — the optimal partition (2.11a), (2.11b) (p. 27).
* `IsStrictlyComplementary` — a strictly complementary solution (5.26) (p. 101).
* `epsABC`, `C3` — the quantity `ε(A, b, c)` (3.5) (p. 56) and `C₃ = ε(A, b, c)/n` (5.32), (7.4).
* `IsAffineStep` — the affine-scaling direction (7.1) (p. 129).
* `IsWLSSolution` — a solution of the weighted least-squares problem (7.7) (p. 131).
* `Bset`, `Nset` — the partition estimate (7.40) (p. 146).
* `IsFTMinimizer` — a solution of the projection problem (7.41) of Procedure FT (p. 147).
-/

namespace WrightPDIPM.Termination

open Matrix

/-- The Euclidean norm `‖v‖ = (∑ᵢ vᵢ²)^{1/2}` (Notation, p. xvii). Mathlib's default norm on
`Fin n → ℝ` is the sup norm, hence the explicit definition. -/
noncomputable def norm2 {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The Euclidean norm of the stacked vector `(u, v)`: `‖(u, v)‖ = (‖u‖² + ‖v‖²)^{1/2}`. -/
noncomputable def norm2Pair {p q : ℕ} (u : Fin p → ℝ) (v : Fin q → ℝ) : ℝ :=
  Real.sqrt (∑ i, u i ^ 2 + ∑ j, v j ^ 2)

/-- The Euclidean norm `‖v_S‖ = (∑_{i ∈ S} vᵢ²)^{1/2}` of the subvector of `v` indexed by `S`
(e.g. `‖Δx_N‖`, `‖Δs_B‖`, p. 130). -/
noncomputable def norm2On {n : ℕ} (S : Set (Fin n)) (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, S.indicator (fun j => v j ^ 2) i)

/-- The strictly feasible set `F°` (1.7b) (p. 5): triples `(x, λ, s)` with `Ax = b`,
`Aᵀλ + s = c`, `x > 0`, `s > 0`. -/
def Fo {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | A *ᵥ p.1 = b ∧ Aᵀ *ᵥ p.2.1 + p.2.2 = c ∧ (∀ i, 0 < p.1 i) ∧ (∀ i, 0 < p.2.2 i)}

/-- The duality measure `μ = xᵀs/n` (1.11) (p. 7). -/
noncomputable def mu {n : ℕ} (x s : Fin n → ℝ) : ℝ :=
  (x ⬝ᵥ s) / (n : ℝ)

/-- The 2-norm neighborhood (1.15) (p. 9):
`N₂(θ) = {(x, λ, s) ∈ F° | ‖XSe − μe‖ ≤ θμ}`, where `XSe − μe` has entries `xᵢsᵢ − μ`. -/
def N2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (θ : ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | p ∈ Fo A b c ∧ norm2 (fun i => p.1 i * p.2.2 i - mu p.1 p.2.2) ≤ θ * mu p.1 p.2.2}

/-- The one-sided ∞-norm neighborhood (1.16) (p. 9):
`N_{-∞}(γ) = {(x, λ, s) ∈ F° | xᵢsᵢ ≥ γμ for all i = 1, …, n}`. -/
def NegInf {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (γ : ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | p ∈ Fo A b c ∧ ∀ i, γ * mu p.1 p.2.2 ≤ p.1 i * p.2.2 i}

/-- Primal feasibility for (2.1): `Ax = b`, `x ≥ 0`. -/
def PrimalFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ ∀ i, 0 ≤ x i

/-- Dual feasibility for (2.2): `Aᵀλ + s = c`, `s ≥ 0`. -/
def DualFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (lam : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  Aᵀ *ᵥ lam + s = c ∧ ∀ i, 0 ≤ s i

/-- The primal solution set `Ω_P = {x* | x* solves (2.1)}` (p. 24). -/
def OmegaP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {x | PrimalFeasible A b x ∧ ∀ x', PrimalFeasible A b x' → c ⬝ᵥ x ≤ c ⬝ᵥ x'}

/-- The dual solution set `Ω_D = {(λ*, s*) | (λ*, s*) solves (2.2)}` (p. 24). -/
def OmegaD {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | DualFeasible A c p.1 p.2 ∧
    ∀ lam' s', DualFeasible A c lam' s' → b ⬝ᵥ lam' ≤ b ⬝ᵥ p.1}

/-- The primal-dual solution set `Ω = Ω_P × Ω_D` (p. 24), as triples `(x*, λ*, s*)`. -/
def Omega {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | p.1 ∈ OmegaP A b c ∧ (p.2.1, p.2.2) ∈ OmegaD A b c}

/-- The index set `B` (2.11a) (p. 27): `j` with `x*_j ≠ 0` for some `x* ∈ Ω_P`. -/
def indexB {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set (Fin n) :=
  {j | ∃ x ∈ OmegaP A b c, x j ≠ 0}

/-- The index set `N` (2.11b) (p. 27): `j` with `s*_j ≠ 0` for some `(λ*, s*) ∈ Ω_D`. -/
def indexN {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set (Fin n) :=
  {j | ∃ p ∈ OmegaD A b c, p.2 j ≠ 0}

/-- A strictly complementary solution (5.26) (p. 101): `(x*, λ*, s*) ∈ Ω` with `x*ᵢ > 0` for
`i ∈ B` and `s*ᵢ > 0` for `i ∈ N`. -/
def IsStrictlyComplementary {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (p : (Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) : Prop :=
  p ∈ Omega A b c ∧ (∀ i ∈ indexB A b c, 0 < p.1 i) ∧ (∀ i ∈ indexN A b c, 0 < p.2.2 i)

/-- The per-index term of (3.5): `sup_{x* ∈ Ω_P} x*ᵢ` for `i ∈ B` and
`sup_{(λ*, s*) ∈ Ω_D} s*ᵢ` for `i ∈ N`. An index in neither set (which cannot occur when
`Ω ≠ ∅`, by the Goldman–Tucker theorem 2.4) gets `0`. The sups are real `sSup`s; they are the
book's sups whenever `F° ≠ ∅`, since then `Ω_P` and the `s*`-part of `Ω_D` are nonempty and
bounded (Theorem 2.3). -/
noncomputable def epsTerm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (i : Fin n) : ℝ := by
  classical
  exact if i ∈ indexB A b c then sSup ((fun x : Fin n → ℝ => x i) '' OmegaP A b c)
    else if i ∈ indexN A b c then
      sSup ((fun p : (Fin m → ℝ) × (Fin n → ℝ) => p.2 i) '' OmegaD A b c)
    else 0

/-- The quantity (3.5) (p. 56):
`ε(A, b, c) = min( min_{i ∈ B} sup_{x* ∈ Ω_P} x*ᵢ , min_{i ∈ N} sup_{(λ*, s*) ∈ Ω_D} s*ᵢ )`,
taken as the minimum of `epsTerm` over all indices `i = 1, …, n` (`B ∪ N = {1, …, n}` when
`Ω ≠ ∅`, by Theorem 2.4). For `n = 0` the value is `0` (an empty `⨅`); no statement uses it
there. -/
noncomputable def epsABC {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) : ℝ :=
  ⨅ i : Fin n, epsTerm A b c i

/-- The constant `C₃ = ε(A, b, c)/n` of (5.32) (p. 102) and (7.4) (p. 130). -/
noncomputable def C3 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) : ℝ :=
  epsABC A b c / (n : ℝ)

/-- The affine-scaling direction (7.1) (p. 129) at `(x, λ, s) ∈ F°`:
`AᵀΔλ + Δs = 0`, `AΔx = 0`, `SΔx + XΔs = −XSe`, i.e. `sᵢΔxᵢ + xᵢΔsᵢ = −xᵢsᵢ` for every `i`.
The direction is defined by these linear equations, not by a closed-form solution. -/
def IsAffineStep {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ)
    (dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ) : Prop :=
  Aᵀ *ᵥ dlam + ds = 0 ∧ A *ᵥ dx = 0 ∧ ∀ i, s i * dx i + x i * ds i = -(x i * s i)

/-- `w̄` solves the weighted least-squares problem (7.7) (p. 131)
`min_w ½‖Σw‖² subject to Hw = h`, with `Σ = diag(σ)`. -/
def IsWLSSolution {p q : ℕ} (H : Matrix (Fin p) (Fin q) ℝ) (σ : Fin q → ℝ) (h : Fin p → ℝ)
    (wbar : Fin q → ℝ) : Prop :=
  H *ᵥ wbar = h ∧
    ∀ w : Fin q → ℝ, H *ᵥ w = h → ∑ j, (σ j * wbar j) ^ 2 ≤ ∑ j, (σ j * w j) ^ 2

/-- The partition estimate (7.40) (p. 146): `B(x, s) = {i ∈ {1, …, n} | xᵢ ≥ sᵢ}`. -/
def Bset {n : ℕ} (x s : Fin n → ℝ) : Set (Fin n) :=
  {i | s i ≤ x i}

/-- The partition estimate (7.40) (p. 146): `N(x, s) = {1, …, n} \ B(x, s)`. -/
def Nset {n : ℕ} (x s : Fin n → ℝ) : Set (Fin n) :=
  (Bset x s)ᶜ

/-- `(x*, λ*, s*)` solves the projection problem (7.41) of Procedure FT (p. 147) at `(x, s)`:
it satisfies `Ax* = b`, `Aᵀλ* + s* = c` (7.41b), `x*ᵢ = 0` for `i ∈ N(x, s)` and `s*ᵢ = 0` for
`i ∈ B(x, s)` (7.41c), and minimizes `½‖x* − x‖² + ½‖s* − s‖²` (7.41a) among all such
triples. (`λ*` does not enter the objective.) -/
def IsFTMinimizer {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x s : Fin n → ℝ) (p : (Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) : Prop :=
  let feas : (Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ) → Prop := fun q =>
    A *ᵥ q.1 = b ∧ Aᵀ *ᵥ q.2.1 + q.2.2 = c ∧
      (∀ i ∈ Nset x s, q.1 i = 0) ∧ (∀ i ∈ Bset x s, q.2.2 i = 0)
  let obj : (Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ) → ℝ := fun q =>
    (1 / 2) * ∑ i, (q.1 i - x i) ^ 2 + (1 / 2) * ∑ i, (q.2.2 i - s i) ^ 2
  feas p ∧ ∀ q, feas q → obj p ≤ obj q

end WrightPDIPM.Termination


