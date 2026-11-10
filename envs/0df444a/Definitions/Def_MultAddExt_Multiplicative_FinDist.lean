-- Prove2me | Definitions.Def_MultAddExt_Multiplicative_FinDist
-- name    : MultAddExt_Multiplicative_FinDist
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:46:35.432606+00:00
-- url     : https://prove2.me/theorems/efa393d9-8474-4f82-ac95-5bd9272d69fd
-- title:
--   Finite distributions, min-entropy, statistical distance, conditioning, prefixes and block-wise sources (Definitions 4.1, 4.2, 4.19)
-- statement:
--   A **distribution** on a finite set $\Omega$ is a function $p:\Omega\to\mathbb R$ with $p(a)\ge 0$ for all $a$ and $\sum_a p(a)=1$ (`IsDist p`). For such distributions:
--
--   1. The **min-entropy** (Definition 4.2) is $H_\infty(X) = -\log_2 \max_x \Pr[X=x]$; logarithms are base $2$ throughout (p. 18).
--   2. The **statistical distance** (Definition 4.1) is $\mathrm{SD}(X,Y)=\tfrac12\sum_{a\in\Omega}\bigl|\Pr[X=a]-\Pr[Y=a]\bigr|$.
--   3. $U_\Omega$ is the uniform distribution, $f(X)$ is the law of $f$ applied to $X$ (push-forward), $\Pr[X\in E]$ is the mass of a set $E$, $(X\mid X\in E)$ is the conditional distribution, $\mathrm{Supp}(X)=\{x:\Pr[X=x]>0\}$, and the product of two distributions is the law of an independent pair.
--   4. For $x\in(\{0,1\}^b)^\ell=\{0,1\}^n$, the prefix $x_{[1,i]}$ consists of the first $i$ blocks, i.e. the first $ib$ bits; it is represented as the $n$-bit string that keeps those bits and sets the rest to $0$.
--   5. (Definition 4.19) A pair $(A,B)$ is an **$(r_1,r_2)$-block-wise source** if $H_\infty(A)\ge r_1$ and, for every $a\in\mathrm{Supp}(A)$, $H_\infty(B\mid A=a)\ge r_2$.
--
--   These are the probabilistic notions every statement of the mission is phrased in.
--
--   **Formalization Note** The maximum in $H_\infty$ is `Finset.sup'` over a nonempty finite type, a true maximum. The conditional distribution divides by $\Pr[X\in E]$ and is only used where this is positive. The prefix is kept inside $\{0,1\}^n$ by zero-padding; the padding map is injective on prefixes, so point probabilities and min-entropy of the prefix are unchanged.
-- source:
--   Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, Multiplicative and Additive Extractors for Low Entropy Samplable Sources Under Reduced Assumptions, STOC 2027 submission (manuscript sha256 5ac077d7…), §4.1, pp. 18–19 (PDF 22–23), Definitions 4.1–4.3; p. 18 notation x_[1,i]; Definition 4.19, p. 21 (PDF 25)

import Mathlib

set_option autoImplicit false

namespace MultAddExt.Multiplicative

/-! # Finite distributions, min-entropy, statistical distance, conditioning (Definitions 4.1–4.3, 4.19)

Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, *Multiplicative and Additive Extractors for Low
Entropy Samplable Sources Under Reduced Assumptions*, STOC 2027 submission (manuscript sha256
5ac077d7…), §4.1, pp. 18–19 (PDF 22–23), Definition 4.19, p. 21 (PDF 25).

A distribution on a finite type `α` is a real mass function `p : α → ℝ` with `IsDist p`.
Logarithms are base 2 (p. 18). -/

/-- `p` is a probability distribution on the finite type `α`: nonnegative masses summing to one. -/
def IsDist {α : Type*} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

/-- Min-entropy `H∞(X) = −log₂ maxₓ Pr[X = x]` (Definition 4.2). -/
noncomputable def minEntropy {α : Type*} [Fintype α] [Nonempty α] (p : α → ℝ) : ℝ :=
  -Real.logb 2 (Finset.univ.sup' Finset.univ_nonempty p)

/-- Statistical distance `SD(X, Y) = ½ ∑ₐ |Pr[X = a] − Pr[Y = a]|` (Definition 4.1). -/
noncomputable def statDist {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (∑ a, |p a - q a|) / 2

/-- The uniform distribution `U_α` on a finite type. -/
noncomputable def uniform (α : Type*) [Fintype α] : α → ℝ :=
  fun _ => 1 / (Fintype.card α : ℝ)

/-- The law of `f(X)` when `X` has law `p` (push-forward). -/
noncomputable def pushforward {α β : Type*} [Fintype α] (f : α → β) (p : α → ℝ) : β → ℝ :=
  open Classical in fun b => ∑ a, if f a = b then p a else 0

/-- `Pr_{a ← p}[a ∈ E]`. -/
noncomputable def probEvent {α : Type*} [Fintype α] (p : α → ℝ) (E : Set α) : ℝ :=
  open Classical in ∑ a, if a ∈ E then p a else 0

/-- The conditional distribution `(X | X ∈ E)`; it is a distribution when `Pr[X ∈ E] > 0`. -/
noncomputable def condDist {α : Type*} [Fintype α] (p : α → ℝ) (E : Set α) : α → ℝ :=
  open Classical in fun a => if a ∈ E then p a / probEvent p E else 0

/-- The support `Supp(X) = {x : Pr[X = x] > 0}` (Definition 4.2). -/
def support {α : Type*} (p : α → ℝ) : Set α := {a | 0 < p a}

/-- The prefix `x_[1,i]` of `x ∈ ({0,1}^b)^ℓ`: its first `i` blocks of `b` bits, i.e. its first
`i·b` coordinates, with the remaining coordinates set to `0` (so prefixes stay in `{0,1}ⁿ`; the
map from `x_[1,i]` to this string is injective). -/
def prefixBits {n : ℕ} (b i : ℕ) (x : Fin n → Bool) : Fin n → Bool :=
  fun j => if j.val < i * b then x j else false

/-- The product (independent) distribution of `p` on `α` and `q` on `β`. -/
def prodDist {α β : Type*} (p : α → ℝ) (q : β → ℝ) : α × β → ℝ :=
  fun z => p z.1 * q z.2

/-- **Block-wise source** (Definition 4.19): the pair `(A, B)` with joint law `P` is an
`(r₁, r₂)`-block-wise source if `H∞(A) ≥ r₁` and `H∞(B | A = a) ≥ r₂` for every `a ∈ Supp(A)`. -/
noncomputable def IsBlockwiseSource {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    [Nonempty β] (P : α × β → ℝ) (r₁ r₂ : ℝ) : Prop :=
  r₁ ≤ minEntropy (pushforward Prod.fst P) ∧
    ∀ a ∈ support (pushforward Prod.fst P),
      r₂ ≤ minEntropy (pushforward Prod.snd (condDist P {z | z.1 = a}))

end MultAddExt.Multiplicative


