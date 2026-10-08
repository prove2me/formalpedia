-- Prove2me | Definitions.Def_L0BnB_DualGap_Setup
-- name    : L0BnB_DualGap_Setup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:27:26.011324+00:00
-- url     : https://prove2.me/theorems/61bf5d97-ab1c-4d19-83bb-5bf02abf4b66
-- title:
--   The reduced relaxation (5), the coordinate problems (12)–(13), the boxed soft-thresholding operator T and the set V of Algorithm 2
-- statement:
--   Let $X\in\mathbb R^{n\times p}$ with columns $X_1,\dots,X_p$, $y\in\mathbb R^n$, regularization parameters $\lambda_0,\lambda_2>0$ and a Big-M bound $M>0$. Write $[p]=\{1,\dots,p\}$ and $\langle a,X_i\rangle=a^\top X_i$.
--
--   **The reduced relaxation (5).** With the reverse Huber penalty $\mathcal B(t)=|t|$ for $|t|\le1$ and $\mathcal B(t)=(t^2+1)/2$ for $|t|\ge1$, set
--   $$
--   \psi(b;\lambda_0,\lambda_2,M)=\begin{cases}\psi_1(b;\lambda_0,\lambda_2):=2\lambda_0\,\mathcal B\big(b\sqrt{\lambda_2/\lambda_0}\big) & \text{if } \sqrt{\lambda_0/\lambda_2}\le M,\\[2pt] \psi_2(b;\lambda_0,\lambda_2,M):=\big(\tfrac{\lambda_0}{M}+\lambda_2M\big)|b| & \text{if } \sqrt{\lambda_0/\lambda_2}> M,\end{cases}
--   $$
--   and $F(\beta)=\tfrac12\|y-X\beta\|_2^2+\sum_{i\in[p]}\psi(\beta_i;\lambda_0,\lambda_2,M)$. Problem (5) minimizes $F$ over the box $\|\beta\|_\infty\le M$; a point $\beta^*$ is an **optimal solution** of (5) when it lies in the box and $F(\beta^*)\le F(\beta)$ for every $\beta$ in the box. The residual of $\beta$ is $r=y-X\beta$.
--
--   **Coordinate problems.** For a point $\hat\beta$ and a coordinate $i$, problem (12) of cyclic coordinate descent minimizes $t\mapsto F(\hat\beta_1,\dots,t,\dots,\hat\beta_p)$ over $|t|\le M$. Problem (13) minimizes $t\mapsto\tfrac12(t-\tilde\beta_i)^2+\psi(t;\lambda_0,\lambda_2,M)$ over $|t|\le M$ for a given scalar $\tilde\beta_i$; a number $b$ is **the solution** of (13) when $|b|\le M$ and every other feasible $t$ has a strictly larger objective.
--
--   **Boxed soft thresholding.** For $a,m\ge0$,
--   $$
--   T(t;a,m)=\begin{cases}0 & |t|\le a,\\ (|t|-a)\operatorname{sign}(t) & a<|t|\le a+m,\\ m\operatorname{sign}(t) & \text{otherwise.}\end{cases}
--   $$
--
--   **The threshold of Proposition 3**: $c(\lambda_0,\lambda_2,M)=2\sqrt{\lambda_0\lambda_2}$ if $\sqrt{\lambda_0/\lambda_2}\le M$ and $c(\lambda_0,\lambda_2,M)=\lambda_0/M+\lambda_2M$ otherwise.
--
--   **Support, the set $V$ and the primal gap.** $\operatorname{Supp}(\beta)=\{i:\beta_i\ne0\}$ and $\|\beta\|_0=|\operatorname{Supp}(\beta)|$. Step 2 of the active-set Algorithm 2 forms
--   $$
--   V=\{\,i\in\operatorname{Supp}(\hat\beta)^c \;:\; 0\ne\operatorname*{arg\,min}_{|\beta_i|\le M}F(\hat\beta_1,\dots,\beta_i,\dots,\hat\beta_p)\,\},
--   $$
--   the coordinates outside the support at which $0$ is not a minimizer of the coordinate problem (12); the algorithm terminates only when $V=\emptyset$. For two points $\beta^*,\hat\beta$ the primal gap is $\epsilon=\|X(\beta^*-\hat\beta)\|_2$.
--
--   These objects are the primal vocabulary of the dual-bound analysis (Theorem 3 of the paper).
--
--   **Formalization Note** Indices are `Fin p`; all norms are explicit sums. `sign` is `Real.sign`, with $\operatorname{sign}(0)=0$. "$0\ne\arg\min$" is encoded as "$0$ is not a minimizer" (`¬ IsMinOn … 0`); for unit-norm columns the coordinate problem is strictly convex, so its argmin is a singleton and the two readings agree. No normalization of $X$ or $y$ is built in: the unit-norm assumption of Section 3 is a hypothesis of each theorem that uses it.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 6, (4), Theorem 1, (5); pp. 9–11, Algorithm 1, (12), (13), boxed soft-thresholding operator T, Algorithm 2 (Step 2, Step 3), Remark 1; p. 12, Proposition 3 (definition of c); p. 15, Theorem 3 (ϵ, k)

import Mathlib
import Definitions.Def_L0BnB_Reduced_ReverseHuber
import Definitions.Def_L0BnB_Reduced_Setup
import Definitions.Def_L0BnB_Strength_Penalties
import Definitions.Def_L0BnB_Strength_Relaxations

namespace L0BnB.DualGap

/-! Primal objects of Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted
in First-Order Optimization*, arXiv:2004.06152v2: the reverse Huber penalty (4) and the reduced
relaxation (5) of Theorem 1 (p. 6), the coordinate problems (12)–(13) of Algorithm 1 (pp. 9–10), the
boxed soft-thresholding operator `T` (p. 10), the threshold `c(λ₀, λ₂, M)` of Proposition 3 (p. 12),
and the set `V` of Step 2 of Algorithm 2 (p. 11).

Conventions: `X : Matrix (Fin n) (Fin p) ℝ`, `y : Fin n → ℝ`, `β : Fin p → ℝ`; the paper's
`[p] = {1, …, p}` is `Fin p`; `‖y − Xβ‖₂²` is the explicit sum `∑ r, (y r − Matrix.mulVec X β r)²`,
`‖β‖_∞ ≤ M` is `∀ i, |β i| ≤ M`, and `⟨a, Xᵢ⟩ = aᵀXᵢ` is `∑ r, a r * X r i`. `sign` is
`Real.sign` (`sign 0 = 0`). No normalization of `X` or `y` is built in: the unit-norm assumption of
Section 3 (p. 9) is a hypothesis of the theorems that use it. -/

/-- The residual `r = y − Xβ`. -/
noncomputable def resid {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (β : Fin p → ℝ) : Fin n → ℝ :=
  fun r => y r - Matrix.mulVec X β r

/-- The inner product `⟨a, Xᵢ⟩ = aᵀXᵢ` of `a ∈ ℝⁿ` with the `i`-th column of `X`. -/
def colInner {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (a : Fin n → ℝ) (i : Fin p) : ℝ :=
  ∑ r, a r * X r i

/-- `β*` is an optimal solution to (5): it lies in the box and minimizes `F` over the box. -/
def IsOptimal {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (βs : Fin p → ℝ) : Prop :=
  βs ∈ L0BnB.Reduced.box p M ∧ ∀ β ∈ L0BnB.Reduced.box p M, L0BnB.Reduced.F X y lam0 lam2 M βs ≤ L0BnB.Reduced.F X y lam0 lam2 M β

/-- The objective of the coordinate problem (12) of Algorithm 1 (p. 9):
`βᵢ ↦ F(β̂₁, …, βᵢ, …, β̂ₚ)`, to be minimized over `|βᵢ| ≤ M`. -/
noncomputable def coordObj {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (βhat : Fin p → ℝ) (i : Fin p) : ℝ → ℝ :=
  fun t => L0BnB.Reduced.F X y lam0 lam2 M (Function.update βhat i t)

/-- The objective of the one-dimensional problem (13), p. 9:
`βᵢ ↦ ½(βᵢ − β̃ᵢ)² + ψ(βᵢ; λ₀, λ₂, M)`, to be minimized over `|βᵢ| ≤ M`; `bt` is `β̃ᵢ`. -/
noncomputable def obj13 (lam0 lam2 M bt : ℝ) : ℝ → ℝ :=
  fun t => (1 / 2) * (t - bt) ^ 2 + L0BnB.Reduced.psi lam0 lam2 M t

/-- `b` is the solution of (13): it is feasible (`|b| ≤ M`) and every other feasible point has a
strictly larger objective, so `b` is the unique minimizer. -/
def IsSolution13 (lam0 lam2 M bt b : ℝ) : Prop :=
  b ∈ Set.Icc (-M) M ∧
    ∀ t ∈ Set.Icc (-M) M, t ≠ b → obj13 lam0 lam2 M bt b < obj13 lam0 lam2 M bt t

/-- The boxed soft-thresholding operator (p. 10), for non-negative `a, m`:
`T(t; a, m) = 0` if `|t| ≤ a`, `(|t| − a) sign(t)` if `a < |t| ≤ a + m`, `m sign(t)` otherwise. -/
noncomputable def boxedSoftThreshold (t a m : ℝ) : ℝ :=
  if |t| ≤ a then 0 else if |t| ≤ a + m then (|t| - a) * Real.sign t else m * Real.sign t

/-- The threshold of Proposition 3 (p. 12): `c(λ₀, λ₂, M) = 2√(λ₀λ₂)` if `√(λ₀/λ₂) ≤ M`, and
`λ₀/M + λ₂M` if `√(λ₀/λ₂) > M`. -/
noncomputable def cThr (lam0 lam2 M : ℝ) : ℝ :=
  if Real.sqrt (lam0 / lam2) ≤ M then 2 * Real.sqrt (lam0 * lam2) else lam0 / M + lam2 * M

/-- `Supp(β) = {i ∈ [p] | βᵢ ≠ 0}`; its cardinality is `‖β‖₀`. -/
noncomputable def supp {p : ℕ} (β : Fin p → ℝ) : Finset (Fin p) :=
  open Classical in Finset.univ.filter (fun i => β i ≠ 0)

/-- The set `V` of Step 2 of Algorithm 2 (p. 11):
`V = {i ∈ Supp(β̂)ᶜ | 0 ≠ argmin_{|βᵢ| ≤ M} F(β̂₁, …, βᵢ, …, β̂ₚ)}`, i.e. the coordinates outside the
support of `β̂` at which `0` is not a minimizer of the coordinate problem (12). Algorithm 2
terminates only when `V = ∅` (Step 3 and Remark 1, p. 11). -/
noncomputable def Vset {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (βhat : Fin p → ℝ) : Finset (Fin p) :=
  open Classical in
  Finset.univ.filter
    (fun i => βhat i = 0 ∧ ¬ IsMinOn (coordObj X y lam0 lam2 M βhat i) (Set.Icc (-M) M) 0)

/-- The primal gap `ϵ = ‖X(β* − β̂)‖₂` of Lemma 2 and Theorem 3 (pp. 15, 31). -/
noncomputable def primalGap {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (βs βhat : Fin p → ℝ) : ℝ :=
  Real.sqrt (∑ r, (Matrix.mulVec X (βs - βhat) r) ^ 2)

end L0BnB.DualGap


