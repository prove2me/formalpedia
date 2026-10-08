-- Prove2me | Definitions.Def_FastBestSubset_CDSS_Setting
-- name    : FastBestSubset_CDSS_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T19:02:38.043283+00:00
-- url     : https://prove2.me/theorems/c7961949-9330-4e8d-a879-fe21a223e4bd
-- title:
--   Problem (2): F, f, β̃ᵢ, Supp, the thresholding operators T̃ (7) and T (12), stationary solutions, CW minima, Assumptions 1–2 and the CDSS iterates (Algorithm 1)
-- statement:
--   This file fixes the objects of Hazimeh and Mazumder's analysis of cyclic coordinate descent for $L_0$-regularized least squares.
--
--   **Problem (2).** Let $X\in\mathbb R^{n\times p}$ be a model matrix with columns $X_1,\dots,X_p$, let $y\in\mathbb R^n$, and let $\lambda_0,\lambda_1,\lambda_2$ be real parameters. For $\beta\in\mathbb R^p$ put
--   $$f(\beta)=\tfrac12\|y-X\beta\|^2+\lambda_1\|\beta\|_1+\lambda_2\|\beta\|_2^2,\qquad F(\beta)=f(\beta)+\lambda_0\|\beta\|_0,$$
--   where $\|\beta\|_0$ is the number of nonzero coordinates of $\beta$. Write $\mathrm{Supp}(\beta)=\{i:\beta_i\neq0\}$, $U_S\beta$ for the vector that keeps the coordinates in $S$ and zeroes the others, and
--   $$\tilde\beta_i=\Big\langle y-\sum_{j\neq i}X_j\beta_j,\;X_i\Big\rangle .$$
--
--   **Thresholding.** For a scalar $a$ let $g(u)=\frac{1+2\lambda_2}{2}\big(u-\frac{a}{1+2\lambda_2}\big)^2+\lambda_1|u|+\lambda_0\mathbf 1[u\neq0]$. The set-valued operator $\tilde T(a,\lambda_0,\lambda_1,\lambda_2)$ is the set of minimizers of $g$ over $\mathbb R$ (7). The single-valued operator (12) is
--   $$T(a,\lambda_0,\lambda_1,\lambda_2)=\begin{cases}\mathrm{sign}(a)\,\dfrac{|a|-\lambda_1}{1+2\lambda_2} & \text{if } \dfrac{|a|-\lambda_1}{1+2\lambda_2}\ge\sqrt{\dfrac{2\lambda_0}{1+2\lambda_2}},\\[2mm] 0 & \text{otherwise,}\end{cases}$$
--   which picks the nonzero minimizer on ties.
--
--   **Minima.** The lower directional derivative of $F$ at $\beta$ in direction $d$ is $F'(\beta;d)=\liminf_{\alpha\downarrow0}(F(\beta+\alpha d)-F(\beta))/\alpha$, an extended real number. $\beta$ is a *stationary solution* (Definition 1) if $F'(\beta;d)\ge0$ for every $d$. $\beta$ is a *coordinate-wise (CW) minimum* (Definition 2) if for every $i$ and every $t\in\mathbb R$, replacing $\beta_i$ by $t$ does not decrease $F$.
--
--   **Assumptions.** Assumption 1: with $m=\min\{n,p\}$, every set of $m$ columns of $X$ is linearly independent. Assumption 2 (used when $p>n$): in the (L0) problem ($\lambda_1=0$) the initial point satisfies $F(\beta^0)\le\lambda_0 n$; in the (L0L1) problem $F(\beta^0)\le\min_\beta f(\beta)+\lambda_0 n$.
--
--   **Algorithm 1 (CDSS).** Fix a positive integer $C$. The algorithm cycles through the coordinates $1,\dots,p$. A *non-spacer step* replaces $\beta_i$ by $T(\tilde\beta_i,\lambda_0,\lambda_1,\lambda_2)$ for the current coordinate $i$, then increments a counter $\mathrm{Count}[S]$ for the new support $S$. When that counter reaches $Cp$, the next step is a *spacer step*: one sequential pass over the coordinates of the current support, each set to $T(\tilde\beta_i,0,\lambda_1,\lambda_2)$ (Subroutine 1). After it, the counter of the pre-spacer support is reset to $0$. The iterate $\beta^k$ is the vector after $k$ steps of either kind.
--
--   These are the objects in every statement of the mission.
--
--   **Formalization Note** Vectors are functions `Fin p → ℝ` (coordinates indexed from 0), and every norm is written as an explicit sum, never with Mathlib's sup norm. $\mathrm{sign}$ is `Real.sign` (so $\mathrm{sign}(0)=0$). $F'$ is valued in `EReal`, because it is $+\infty$ in directions leaving the support. The algorithm is a deterministic state machine `(beta, ptr, count, pending)`, so the iterates are defined, not quantified over. The next coordinate is `ptr % p`; the pointer does not advance on spacer steps, following the pseudocode box rather than the prose "i = (k+1) mod (p+1)" on p. 10. "$\beta^k$ is a spacer step" means that step $k-1\to k$ was a spacer step. In Assumption 2 "$\lambda n$" is read as $\lambda_0 n$, as in the proof of Lemma 6, and "$\le\min f+\lambda_0 n$" is written as "$\le f(\beta)+\lambda_0 n$ for every $\beta$". Assumption 2 is only ever imposed together with $\lambda_2=0$ and $p>n$ (the theorems carry `lam2 = 0 → (Assumption 1 ∧ (n < p → Assumption 2))`), so its $f$ is the lasso objective of the page; the branch on $\lambda_1=0$ separates the (L0) and (L0L1) cases. The data carry no hypotheses: unit-norm columns, $\lambda_0>0$, $\lambda_1,\lambda_2\ge0$ and the restriction to the named problems ($\lambda_1=0$ or $\lambda_2=0$) are binders of each theorem.
-- source:
--   Hazimeh, Mazumder, Fast Best Subset Selection: Coordinate Descent and Local Combinatorial Optimization Algorithms, arXiv:1803.01454v3, (2), (3), §1.1, Definition 1, Definition 2, (7), (12), Algorithm 1, Subroutine 1, Assumptions 1–2, pp. 1, 4–6, 10–12

import Mathlib

open Filter Topology

namespace FastBestSubset.CDSS

/-- The data of Problem (2) (pp. 1, 4–5): the model matrix `X ∈ ℝ^{n×p}`, the response `y ∈ ℝⁿ`
and the three regularization parameters `λ₀, λ₁, λ₂` (written `lam0, lam1, lam2`). The standing
hypotheses (unit-norm columns, `λ₀ > 0`, `λ₁, λ₂ ≥ 0`) are stated in each theorem. -/
structure Data (n p : ℕ) where
  X : Matrix (Fin n) (Fin p) ℝ
  y : Fin n → ℝ
  lam0 : ℝ
  lam1 : ℝ
  lam2 : ℝ

variable {n p : ℕ}

/-- `‖β‖₀`, the number of nonzero coordinates of `β` (p. 4). -/
noncomputable def l0 (β : Fin p → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => β i ≠ 0)).card

/-- `Supp(β) = {i : βᵢ ≠ 0}` (§1.1, p. 4). -/
noncomputable def supp (β : Fin p → ℝ) : Finset (Fin p) :=
  Finset.univ.filter (fun i => β i ≠ 0)

/-- `f(β) = ½‖y − Xβ‖² + λ₁‖β‖₁ + λ₂‖β‖₂²` (3), p. 5, with every norm written as a sum. -/
noncomputable def f (D : Data n p) (β : Fin p → ℝ) : ℝ :=
  (1 / 2) * ∑ r, (D.y r - ∑ j, D.X r j * β j) ^ 2 + D.lam1 * ∑ j, |β j|
    + D.lam2 * ∑ j, β j ^ 2

/-- The objective of Problem (2), `F(β) = f(β) + λ₀‖β‖₀` (p. 4). -/
noncomputable def F (D : Data n p) (β : Fin p → ℝ) : ℝ :=
  f D β + D.lam0 * (l0 β : ℝ)

/-- `β̃ᵢ = ⟨y − Σ_{j≠i} X_j β_j, X_i⟩` (§1.1, p. 4). -/
noncomputable def btilde (D : Data n p) (β : Fin p → ℝ) (i : Fin p) : ℝ :=
  ∑ r, (D.y r - ∑ j ∈ Finset.univ.erase i, D.X r j * β j) * D.X r i

/-- `U_S β`: keep the coordinates in `S`, zero the others (§1.1, p. 4). -/
def U (S : Finset (Fin p)) (β : Fin p → ℝ) : Fin p → ℝ :=
  fun i => if i ∈ S then β i else 0

/-- The scalar objective of (7), p. 6:
`g(u) = ((1 + 2λ₂)/2)(u − a/(1 + 2λ₂))² + λ₁|u| + λ₀·1[u ≠ 0]`. -/
noncomputable def gScalar (a lam0 lam1 lam2 u : ℝ) : ℝ :=
  (1 + 2 * lam2) / 2 * (u - a / (1 + 2 * lam2)) ^ 2 + lam1 * |u| + lam0 * (if u ≠ 0 then 1 else 0)

/-- The set-valued thresholding operator `T̃(a, λ₀, λ₁, λ₂) = argmin_u g(u)` (7), p. 6. -/
def Ttilde (a lam0 lam1 lam2 : ℝ) : Set ℝ :=
  {u | ∀ v : ℝ, gScalar a lam0 lam1 lam2 u ≤ gScalar a lam0 lam1 lam2 v}

/-- The single-valued thresholding operator `T` (12), p. 10: the nonzero solution on ties.
`sign` is `Real.sign` (so `sign 0 = 0`). -/
noncomputable def T (a lam0 lam1 lam2 : ℝ) : ℝ :=
  if Real.sqrt (2 * lam0 / (1 + 2 * lam2)) ≤ (|a| - lam1) / (1 + 2 * lam2) then
    Real.sign a * (|a| - lam1) / (1 + 2 * lam2)
  else 0

/-- Definition 2 (CW minimum), p. 6: for every `i`, `βᵢ` minimizes `F` in coordinate `i` with the
others held fixed. -/
def IsCWMin (D : Data n p) (β : Fin p → ℝ) : Prop :=
  ∀ (i : Fin p) (t : ℝ), F D β ≤ F D (Function.update β i t)

/-- The lower directional derivative `g′(β; d) = liminf_{α↓0} (g(β + αd) − g(β))/α` (p. 5),
valued in `EReal` (it is `+∞` in directions leaving the support, (27) p. 36). -/
noncomputable def lowerDirDeriv (g : (Fin p → ℝ) → ℝ) (β d : Fin p → ℝ) : EReal :=
  Filter.liminf (fun α : ℝ => (((g (β + α • d) - g β) / α : ℝ) : EReal)) (𝓝[>] (0 : ℝ))

/-- Definition 1 (stationary solution), p. 6: `F′(β; d) ≥ 0` for every direction `d`. -/
def IsStationary (D : Data n p) (β : Fin p → ℝ) : Prop :=
  ∀ d : Fin p → ℝ, (0 : EReal) ≤ lowerDirDeriv (F D) β d

/-- Assumption 1, p. 12: with `m = min{n, p}`, every set of `m` columns of `X` is linearly
independent. -/
def Assumption1 (D : Data n p) : Prop :=
  ∀ S : Finset (Fin p), S.card = min n p →
    LinearIndependent ℝ (fun j : S => fun r => D.X r (j : Fin p))

/-- Assumption 2 (initialization), p. 12, for the case `p > n` (the caller adds `n < p →`):
in the (L0) problem (`λ₁ = 0`) `F(β⁰) ≤ λ₀ n`; in the (L0L1) problem
`F(β⁰) ≤ min_β f(β) + λ₀ n`, written as `F(β⁰) ≤ f(β) + λ₀ n` for every `β`
(with `λ₂ = 0`, `f` is the lasso objective). -/
def Assumption2 (D : Data n p) (β0 : Fin p → ℝ) : Prop :=
  if D.lam1 = 0 then F D β0 ≤ D.lam0 * (n : ℝ)
  else ∀ β : Fin p → ℝ, F D β0 ≤ f D β + D.lam0 * (n : ℝ)

/-! ### Algorithm 1 (CDSS), pp. 10–11 -/

/-- The state of Algorithm 1: the current iterate, the cyclic pointer (the next coordinate is
`ptr % p`), the associative array `Count[·]`, and whether the next step is a spacer step. -/
structure State (p : ℕ) where
  beta : Fin p → ℝ
  ptr : ℕ
  count : Finset (Fin p) → ℕ
  pending : Bool

/-- Subroutine 1 (`SpacerStep`), p. 11: one sequential (Gauss–Seidel) pass over the coordinates of
`Supp(β)` of the input, in increasing order, each set to `T(β̃ᵢ, 0, λ₁, λ₂)` evaluated at the
current vector. -/
noncomputable def spacer (D : Data n p) (β : Fin p → ℝ) : Fin p → ℝ :=
  (List.finRange p).foldl
    (fun b i => if β i ≠ 0 then Function.update b i (T (btilde D b i) 0 D.lam1 D.lam2) else b) β

/-- The coordinate updated by a non-spacer step from state `s`. -/
def coord [NeZero p] (s : State p) : Fin p :=
  ⟨s.ptr % p, Nat.mod_lt _ (Nat.pos_of_neZero p)⟩

/-- One step of Algorithm 1 with parameter `C`. A spacer step applies `SpacerStep` and resets
`Count` of the pre-spacer support. A non-spacer step sets coordinate `i = ptr % p` to
`T(β̃ᵢ, λ₀, λ₁, λ₂)`, increments `Count` of the new support, and schedules a spacer step when that
count equals `C p`. -/
noncomputable def step [NeZero p] (D : Data n p) (C : ℕ) (s : State p) : State p :=
  if s.pending then
    { beta := spacer D s.beta
      ptr := s.ptr
      count := Function.update s.count (supp s.beta) 0
      pending := false }
  else
    let b' := Function.update s.beta (coord s)
      (T (btilde D s.beta (coord s)) D.lam0 D.lam1 D.lam2)
    let c' := Function.update s.count (supp b') (s.count (supp b') + 1)
    { beta := b'
      ptr := s.ptr + 1
      count := c'
      pending := decide (c' (supp b') = C * p) }

/-- The initial state: `β⁰`, pointer at coordinate `0`, all counts `0`, no spacer step pending. -/
def init (β0 : Fin p → ℝ) : State p :=
  { beta := β0, ptr := 0, count := fun _ => 0, pending := false }

/-- The state of Algorithm 1 after `k` steps (spacer and non-spacer steps both counted). -/
noncomputable def stateAt [NeZero p] (D : Data n p) (C : ℕ) (β0 : Fin p → ℝ) (k : ℕ) : State p :=
  (step D C)^[k] (init β0)

/-- The iterate `βᵏ` of Algorithm 1 started at `β⁰` with parameter `C`. -/
noncomputable def iter [NeZero p] (D : Data n p) (C : ℕ) (β0 : Fin p → ℝ) (k : ℕ) : Fin p → ℝ :=
  (stateAt D C β0 k).beta

/-- `βᵏ` is the result of a spacer step: `k ≥ 1` and step `k − 1 → k` was a spacer step. -/
def IsSpacer [NeZero p] (D : Data n p) (C : ℕ) (β0 : Fin p → ℝ) (k : ℕ) : Prop :=
  1 ≤ k ∧ (stateAt D C β0 (k - 1)).pending = true

end FastBestSubset.CDSS


