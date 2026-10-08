-- Prove2me | Definitions.Def_LLLFactor_Reduction_Algorithm
-- name    : LLLFactor_Reduction_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:25:44.254124+00:00
-- url     : https://prove2.me/theorems/2105714e-fac7-4f34-b700-6ef14cebf780
-- title:
--   Sect. 1, pp. 516–522 — Gram–Schmidt data (1.2)–(1.3), reduced bases (1.4)–(1.5), the reduction algorithm (1.15), d_i (1.24), D and m(L) (1.23)
-- statement:
--   This module fixes the objects of Sect. 1 of Lenstra, Lenstra and Lovász that the analysis of the basis reduction algorithm is about.
--
--   **Lattices and Gram–Schmidt data.** Let $b_1,\dots,b_n\in\mathbb R^n$. The lattice they span is $L=\sum_{i=1}^n\mathbb Z b_i$, and $b_1,\dots,b_n$ is a *basis for* $L$ when the $b_i$ are linearly independent over $\mathbb R$ and span $L$ over $\mathbb Z$. The determinant is $d(L)=|\det(b_1,\dots,b_n)|$, the $b_i$ written as columns (1.1). The Gram–Schmidt vectors $b_i^*$ and coefficients $\mu_{ij}$ are given by (1.2)–(1.3):
--   $$b_i^*=b_i-\sum_{j=1}^{i-1}\mu_{ij}b_j^*,\qquad \mu_{ij}=\frac{(b_i,b_j^*)}{(b_j^*,b_j^*)}.$$
--   The basis is *reduced* if (1.4) $|\mu_{ij}|\le\tfrac12$ for $1\le j<i\le n$ and (1.5) $|b_i^*+\mu_{i,i-1}b_{i-1}^*|^2\ge\tfrac34|b_{i-1}^*|^2$ for $1<i\le n$.
--
--   **The algorithm (1.15).** A *state* is a pair $(b,k)$ of the current vectors $b_1,\dots,b_n$ and the current subscript $k$. One step from a state with $1\le k\le n$ is one of two cases.
--
--   1. *Achieving (1.18).* If $k>1$ and $|\mu_{k,k-1}|>\tfrac12$, let $r$ be an integer nearest to $\mu_{k,k-1}$ and replace $b_k$ by $b_k-rb_{k-1}$; otherwise nothing changes.
--   2. *Case 1.* If $k\ge2$ and, after achieving (1.18), (1.19) $|b_k^*+\mu_{k,k-1}b_{k-1}^*|^2<\tfrac34|b_{k-1}^*|^2$ holds, interchange $b_{k-1}$ and $b_k$ and replace $k$ by $k-1$.
--   3. *Case 2.* If $k=1$ or, after achieving (1.18), (1.20) $|b_k^*+\mu_{k,k-1}b_{k-1}^*|^2\ge\tfrac34|b_{k-1}^*|^2$ holds, then repeatedly let $l$ be the largest index $<k$ with $|\mu_{kl}|>\tfrac12$, let $r$ be an integer nearest to $\mu_{kl}$ and replace $b_k$ by $b_k-rb_l$, until (1.21) $|\mu_{kj}|\le\tfrac12$ for $1\le j\le k-1$; then replace $k$ by $k+1$.
--
--   The algorithm starts from the given basis with $k=2$ and stops when $k=n+1$. A state is *reachable* from $b$ if a finite sequence of steps leads to it from $(b,2)$. The *situation* at $(b,k)$ is the pair of conditions (1.16) $|\mu_{ij}|\le\tfrac12$ for $1\le j<i<k$ and (1.17) $|b_i^*+\mu_{i,i-1}b_{i-1}^*|^2\ge\tfrac34|b_{i-1}^*|^2$ for $1<i<k$.
--
--   **Quantities of the termination proof (1.23)–(1.24).** For $0\le i\le n$,
--   $$d_i=\det\big((b_j,b_l)\big)_{1\le j,l\le i},\qquad d_0=1,$$
--   and $D=\prod_{i=1}^{n-1}d_i$. For a lattice $L$, $m(L)=\min\{|x|^2:x\in L,\ x\ne0\}$.
--
--   These are the objects every statement of this mission is about: the termination theorem, the invariants of the algorithm, and the potential function $D$ that bounds the number of steps.
--
--   **Formalization Note.** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`; Lean's index $i\in\{0,\dots,n-1\}$ is the paper's $i+1$. $b_i^*$ is Mathlib's unnormalised `InnerProductSpace.gramSchmidt`. A state is `(b, k)` with `k` stored as **the paper's** subscript, so the paper's $b_k$ is Lean's `b ⟨k-1, _⟩`, and every such index carries the guard ($1\le k$ or $2\le k$) that makes it valid. Only $(b,k)$ is stored: $b^*$ and $\mu$ are recomputed from $b$, which is what "update the $b_i^*$ and $\mu_{ij}$ in such a way that (1.2) and (1.3) remain valid" means; the update formulae (1.22) are consequences and are not part of the definition. "The integer nearest to $x$" is any integer $r$ with $|x-r|\le\tfrac12$, so both choices at a tie are allowed and every statement covers each tie rule. The step relation follows the text of (1.15), not Fig. 1 (which never visits $k=1$ and stops at $k=n$). `gram b i` is set to $0$ for $i>n$, where the paper does not define $d_i$; `minSqNorm` is an infimum, which is the paper's minimum whenever $L$ has a basis.
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), pp. 516–522, (1.1)–(1.5), (1.15)–(1.21), (1.23)–(1.24)

import Mathlib
import Definitions.Def_LLLFactor_RedBasis_Setting

namespace LLLFactor.Reduction
noncomputable section

/-- A state of the algorithm (1.15): the current vectors `b₁, …, bₙ` (Lean index `i` is the
paper's `b_{i+1}`) and the current subscript `k`, stored as **the paper's** subscript. -/
abbrev State (n : ℕ) := (Fin n → LLLFactor.RedBasis.Vec n) × ℕ

/-- `r` is an integer nearest to `x`. Both nearest integers are allowed at a tie. -/
def IsNearestInt (r : ℤ) (x : ℝ) : Prop :=
  |x - (r : ℝ)| ≤ 1 / 2

/-- Replace `b_κ` by `b_κ − r b_l` (Lean indices), all other vectors unchanged. -/
def reduceBy {n : ℕ} (b : Fin n → LLLFactor.RedBasis.Vec n) (κ l : Fin n) (r : ℤ) : Fin n → LLLFactor.RedBasis.Vec n :=
  Function.update b κ (b κ - (r : ℝ) • b l)

/-- Condition (1.19) at the paper's subscript `k` (`2 ≤ k ≤ n`):
`|b_k^* + μ_{k,k−1} b_{k−1}^*|² < ¾ |b_{k−1}^*|²`. False outside `2 ≤ k ≤ n`. -/
def Cond119 {n : ℕ} (b : Fin n → LLLFactor.RedBasis.Vec n) (k : ℕ) : Prop :=
  ∃ h : 2 ≤ k ∧ k ≤ n,
    ‖LLLFactor.RedBasis.gs b ⟨k - 1, by omega⟩ + LLLFactor.RedBasis.mu b ⟨k - 1, by omega⟩ ⟨k - 2, by omega⟩ • LLLFactor.RedBasis.gs b ⟨k - 2, by omega⟩‖ ^ 2
      < (3 / 4 : ℝ) * ‖LLLFactor.RedBasis.gs b ⟨k - 2, by omega⟩‖ ^ 2

/-- Condition (1.20) (equivalently (1.17) at `i = k`) at the paper's subscript `k`
(`2 ≤ k ≤ n`): `|b_k^* + μ_{k,k−1} b_{k−1}^*|² ≥ ¾ |b_{k−1}^*|²`. False outside `2 ≤ k ≤ n`. -/
def Cond120 {n : ℕ} (b : Fin n → LLLFactor.RedBasis.Vec n) (k : ℕ) : Prop :=
  ∃ h : 2 ≤ k ∧ k ≤ n,
    (3 / 4 : ℝ) * ‖LLLFactor.RedBasis.gs b ⟨k - 2, by omega⟩‖ ^ 2 ≤
      ‖LLLFactor.RedBasis.gs b ⟨k - 1, by omega⟩ + LLLFactor.RedBasis.mu b ⟨k - 1, by omega⟩ ⟨k - 2, by omega⟩ • LLLFactor.RedBasis.gs b ⟨k - 2, by omega⟩‖ ^ 2

/-- Achieving (1.18) at the paper's subscript `k`: if `k > 1` (and `k ≤ n`) and
`|μ_{k,k−1}| > ½`, replace `b_k` by `b_k − r b_{k−1}` with `r` an integer nearest to
`μ_{k,k−1}`; otherwise nothing changes. -/
def Achieve118 {n : ℕ} (b : Fin n → LLLFactor.RedBasis.Vec n) (k : ℕ) (b' : Fin n → LLLFactor.RedBasis.Vec n) : Prop :=
  if h : 2 ≤ k ∧ k ≤ n then
    (|LLLFactor.RedBasis.mu b ⟨k - 1, by omega⟩ ⟨k - 2, by omega⟩| ≤ 1 / 2 ∧ b' = b) ∨
    (1 / 2 < |LLLFactor.RedBasis.mu b ⟨k - 1, by omega⟩ ⟨k - 2, by omega⟩| ∧
      ∃ r : ℤ, IsNearestInt r (LLLFactor.RedBasis.mu b ⟨k - 1, by omega⟩ ⟨k - 2, by omega⟩) ∧
        b' = reduceBy b ⟨k - 1, by omega⟩ ⟨k - 2, by omega⟩ r)
  else b' = b

/-- One pass of the loop of case 2 for the vector with Lean index `κ` (the paper's `b_k`,
`κ = k − 1`): `l` is the largest index `< κ` with `|μ_{κ l}| > ½`, `r` an integer nearest to
`μ_{κ l}`, and `b_κ` is replaced by `b_κ − r b_l`. -/
def LoopStep {n : ℕ} (κ : Fin n) (c c' : Fin n → LLLFactor.RedBasis.Vec n) : Prop :=
  ∃ l : Fin n, l < κ ∧ 1 / 2 < |LLLFactor.RedBasis.mu c κ l| ∧
    (∀ l' : Fin n, l < l' → l' < κ → |LLLFactor.RedBasis.mu c κ l'| ≤ 1 / 2) ∧
    ∃ r : ℤ, IsNearestInt r (LLLFactor.RedBasis.mu c κ l) ∧ c' = reduceBy c κ l r

/-- Case 1 of (1.15), from state `s = (b, k)` to `s'`: `2 ≤ k ≤ n`; achieve (1.18); (1.19)
holds; interchange `b_{k−1}` and `b_k`; replace `k` by `k − 1`. -/
def Case1 {n : ℕ} (s s' : State n) : Prop :=
  ∃ h : 2 ≤ s.2 ∧ s.2 ≤ n, ∃ b' : Fin n → LLLFactor.RedBasis.Vec n,
    Achieve118 s.1 s.2 b' ∧ Cond119 b' s.2 ∧
    s'.1 = b' ∘ Equiv.swap (⟨s.2 - 2, by omega⟩ : Fin n) ⟨s.2 - 1, by omega⟩ ∧
    s'.2 = s.2 - 1

/-- Case 2 of (1.15), from state `s = (b, k)` to `s'`: `1 ≤ k ≤ n`; achieve (1.18);
`k = 1` or (1.20) holds; run the loop of case 2 until (1.21) holds; replace `k` by `k + 1`. -/
def Case2 {n : ℕ} (s s' : State n) : Prop :=
  ∃ h : 1 ≤ s.2 ∧ s.2 ≤ n, ∃ b' : Fin n → LLLFactor.RedBasis.Vec n,
    Achieve118 s.1 s.2 b' ∧ (s.2 = 1 ∨ Cond120 b' s.2) ∧
    Relation.ReflTransGen (LoopStep (⟨s.2 - 1, by omega⟩ : Fin n)) b' s'.1 ∧
    (∀ j : Fin n, (j : ℕ) < s.2 - 1 → |LLLFactor.RedBasis.mu s'.1 ⟨s.2 - 1, by omega⟩ j| ≤ 1 / 2) ∧
    s'.2 = s.2 + 1

/-- One step of the algorithm (1.15), from a situation (1.16)–(1.17) to the next. -/
def Step {n : ℕ} (s s' : State n) : Prop :=
  Case1 s s' ∨ Case2 s s'

/-- `s` is reachable by the algorithm started on the basis `b` (with `k = 2`). -/
def Reachable {n : ℕ} (b : Fin n → LLLFactor.RedBasis.Vec n) (s : State n) : Prop :=
  Relation.ReflTransGen Step (b, 2) s

/-- The situation (1.16)–(1.17) at the paper's subscript `k`:
(1.16) `|μ_{ij}| ≤ ½` for `1 ≤ j < i < k` (Lean: `j < i`, `i + 1 < k`);
(1.17) `|b_i^* + μ_{i,i−1} b_{i−1}^*|² ≥ ¾ |b_{i−1}^*|²` for `1 < i < k` (paper `i`, `i ≤ n`). -/
def Situation {n : ℕ} (b : Fin n → LLLFactor.RedBasis.Vec n) (k : ℕ) : Prop :=
  (∀ i j : Fin n, j < i → (i : ℕ) + 1 < k → |LLLFactor.RedBasis.mu b i j| ≤ 1 / 2) ∧
  (∀ i : ℕ, 2 ≤ i → i < k → i ≤ n → Cond120 b i)

/-- `d_i = det((b_j, b_l))_{1 ≤ j,l ≤ i}` of (1.24), for `0 ≤ i ≤ n` (`d₀ = 1`, the empty
determinant); set to `0` for `i > n`, where the paper does not define it. -/
def gram {n : ℕ} (b : Fin n → LLLFactor.RedBasis.Vec n) (i : ℕ) : ℝ :=
  if h : i ≤ n then
    Matrix.det (Matrix.of fun (j l : Fin i) => inner ℝ (b (Fin.castLE h j)) (b (Fin.castLE h l)))
  else 0

/-- `D = ∏_{i=1}^{n−1} d_i` of (1.23). -/
def potD {n : ℕ} (b : Fin n → LLLFactor.RedBasis.Vec n) : ℝ :=
  ∏ i ∈ Finset.Ioo 0 n, gram b i

/-- `m(L) = min{|x|² : x ∈ L, x ≠ 0}` of (1.23), written as an infimum. -/
def minSqNorm {n : ℕ} (L : Submodule ℤ (LLLFactor.RedBasis.Vec n)) : ℝ :=
  sInf {r : ℝ | ∃ x ∈ L, x ≠ 0 ∧ r = ‖x‖ ^ 2}

end
end LLLFactor.Reduction


