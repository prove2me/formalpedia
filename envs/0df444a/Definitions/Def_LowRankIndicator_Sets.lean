-- Prove2me | Definitions.Def_LowRankIndicator_Sets
-- name    : LowRankIndicator_Sets
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:17:56.515486+00:00
-- url     : https://prove2.me/theorems/5e7718d9-57e1-41e7-86ba-fbb9afee1742
-- title:
--   The set $Q$ of (2), the pieces $X(I)$, $Z(I)$, $V(I)$ of (3), and the ray set $R$ of (5) (corrected)
-- statement:
--   Fix $n,k\in\mathbb N$, a $k\times n$ real matrix $A$, a vector $c\in\mathbb R^n$, a subset $I_+\subseteq[n]$ and a function $g:\mathbb R^k\to\overline{\mathbb R}$, and put
--
--   $$f(x)=g(Ax)+c^\top x .$$
--
--   This file defines the sets on which the paper's main theorem is stated, all in the space of triples $(t,x,z)\in\mathbb R\times\mathbb R^n\times\mathbb R^n$ unless noted otherwise.
--
--   1. The mixed-integer epigraph with indicator variables (2): $Q=\{(t,x,z)\in\mathbb R^{n+1}\times\{0,1\}^n: t\ge f(x),\ x_i\ge0\ \forall i\in I_+,\ x_i(1-z_i)=0\ \forall i\in[n]\}$.
--   2. The continuous relaxation $X=\{(t,x)\in\mathbb R^{n+1}: t\ge f(x),\ x_i\ge0\ \forall i\in I_+\}$.
--   3. For $I\subseteq[n]$, the pieces (3): $X(I)=X\cap\{(t,x):x_i=0\ \forall i\notin I\}$, $Z(I)=\{z\in\{0,1\}^n:z_i=1\ \forall i\in I\}$ and $V(I)=X(I)\times Z(I)$.
--   4. The ray set (5), corrected: $R=\{(t,x,z):t\ge c^\top x,\ Ax=0,\ x_i\ge0\ \forall i\in I_+,\ z_i=1\ \forall i\in[n]\}$.
--   5. The union $\bigcup_{I:|I|\le k}V(I)$, the cone $\{x\in\mathbb R^n:Ax=0,\ x_i\ge0\ \forall i\in I_+\}$, and the support $\operatorname{supp}(y)=\{i:y_i\ne0\}$.
--
--   The pieces $V(I)$ are the support patterns of $Q$; the theorem of the paper shows that those with $|I|\le k$, together with $R$, generate the closed convex hull of $Q$.
--
--   **Formalization Note** The paper prints $t\ge0$ in (5). That is false for $c\ne0$: take $n=k=1$, $A=0$, $g\equiv0$, $c=1$, $I_+=\emptyset$; then $f(x)=x$, the printed $R$ contains $(0,1,1)$, and $Q$ lies in the closed half-space $\{t\ge x\}$. The condition $t\ge c^\top x$ is what the paper's proof uses (the point $(rc^\top d,rd,\mathbf e)\in R$ on p.7), and it agrees with the printed one for $c=0$, which is the case of Section 3. In Lean $\mathbb R^n$ is `Fin n → ℝ`, so indices are $0$-based, $g$ takes values in `EReal`, $I$ is a `Finset (Fin n)`, and $z\in\{0,1\}^n$ is `∀ i, z i = 0 ∨ z i = 1`. No property of $g$ is built into the definitions.
-- source:
--   Han & Gómez, Compact Extended Formulations for Low-Rank Functions with Indicator Variables, arXiv:2110.14884v2, (2), p.2; X and (3), (5), supp, p.5; union and cone, Theorem 1, p.6. (5) corrected to t ≥ c⊤x.

import Mathlib

open scoped Matrix

namespace LowRankIndicator

/-- The ambient space `ℝ × ℝⁿ × ℝⁿ` of the points `(t, x, z)` of Han & Gómez, *Compact Extended
Formulations for Low-Rank Functions with Indicator Variables*, arXiv:2110.14884v2, (2), p.2.

**Formalization Note.** `ℝⁿ` is `Fin n → ℝ` and `[n]` is `Fin n`, so indices are 0-based. The
product topology is the Euclidean one; closures and convex hulls are taken in this space. -/
abbrev Point (n : ℕ) : Type := ℝ × (Fin n → ℝ) × (Fin n → ℝ)

/-- The function `f(x) = g(Ax) + c⊤x` of arXiv:2110.14884v2, (2), p.2.

**Formalization Note.** `g` is extended-valued in `EReal`, so `f x = ⊤` outside the effective
domain. The linear term is a real number coerced to `EReal`, so `⊤ + r = ⊤` and no `⊤ + ⊥` occurs.
The `k × n` matrix is `Matrix (Fin k) (Fin n) ℝ`. -/
noncomputable def objective {n k : ℕ} (g : (Fin k → ℝ) → EReal)
    (A : Matrix (Fin k) (Fin n) ℝ) (c : Fin n → ℝ) (x : Fin n → ℝ) : EReal :=
  g (A.mulVec x) + ((c ⬝ᵥ x : ℝ) : EReal)

/-- The mixed-integer set `Q` of arXiv:2110.14884v2, (2), p.2 (repeated p.5):
`Q = {(t, x, z) ∈ ℝⁿ⁺¹ × {0,1}ⁿ : t ≥ f(x), xᵢ ≥ 0 ∀i ∈ I₊, xᵢ(1 − zᵢ) = 0 ∀i ∈ [n]}`.

**Formalization Note.** `t ≥ f(x)` is `objective … x ≤ (t : EReal)`; `z ∈ {0,1}ⁿ` is
`∀ i, z i = 0 ∨ z i = 1`. -/
def Q {n k : ℕ} (g : (Fin k → ℝ) → EReal) (A : Matrix (Fin k) (Fin n) ℝ) (c : Fin n → ℝ)
    (Iplus : Set (Fin n)) : Set (Point n) :=
  {p | objective g A c p.2.1 ≤ (p.1 : EReal) ∧ (∀ i ∈ Iplus, 0 ≤ p.2.1 i) ∧
    (∀ i, p.2.2 i = 0 ∨ p.2.2 i = 1) ∧ ∀ i, p.2.1 i * (1 - p.2.2 i) = 0}

/-- The set `X = {(t, x) ∈ ℝⁿ⁺¹ : t ≥ f(x), xᵢ ≥ 0 ∀i ∈ I₊}` of arXiv:2110.14884v2, p.5. -/
def Xset {n k : ℕ} (g : (Fin k → ℝ) → EReal) (A : Matrix (Fin k) (Fin n) ℝ) (c : Fin n → ℝ)
    (Iplus : Set (Fin n)) : Set (ℝ × (Fin n → ℝ)) :=
  {p | objective g A c p.2 ≤ (p.1 : EReal) ∧ ∀ i ∈ Iplus, 0 ≤ p.2 i}

/-- The set `X(I) = X ∩ {(t, x) : xᵢ = 0 ∀i ∉ I}` of arXiv:2110.14884v2, (3), p.5.

**Formalization Note.** `I ⊆ [n]` is a `Finset (Fin n)`, and `|I|` is `I.card`. -/
def XI {n k : ℕ} (g : (Fin k → ℝ) → EReal) (A : Matrix (Fin k) (Fin n) ℝ) (c : Fin n → ℝ)
    (Iplus : Set (Fin n)) (I : Finset (Fin n)) : Set (ℝ × (Fin n → ℝ)) :=
  Xset g A c Iplus ∩ {p | ∀ i, i ∉ I → p.2 i = 0}

/-- The set `Z(I) = {z ∈ {0,1}ⁿ : zᵢ = 1 ∀i ∈ I}` of arXiv:2110.14884v2, (3), p.5. -/
def ZI {n : ℕ} (I : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {z | (∀ i, z i = 0 ∨ z i = 1) ∧ ∀ i ∈ I, z i = 1}

/-- The piece `V(I) = X(I) × Z(I)` of arXiv:2110.14884v2, (3), p.5, as a subset of the
space of triples `(t, x, z)`. -/
def VI {n k : ℕ} (g : (Fin k → ℝ) → EReal) (A : Matrix (Fin k) (Fin n) ℝ) (c : Fin n → ℝ)
    (Iplus : Set (Fin n)) (I : Finset (Fin n)) : Set (Point n) :=
  {p | (p.1, p.2.1) ∈ XI g A c Iplus I ∧ p.2.2 ∈ ZI I}

/-- The ray set `R` of arXiv:2110.14884v2, (5), p.5, **corrected**:
`R = {(t, x, z) : t ≥ c⊤x, Ax = 0, xᵢ ≥ 0 ∀i ∈ I₊, zᵢ = 1 ∀i ∈ [n]}`.

**Formalization Note.** The paper prints `t ≥ 0`, which is false for `c ≠ 0`: for `n = 1`,
`A = 0`, `g ≡ 0`, `c = 1`, `I₊ = ∅` the printed `R` contains `(0, 1, 1)`, while `Q` and hence
`cl conv(Q)` lie in `{t ≥ x}`. The corrected condition is what the proof uses ("(rc⊤d, rd, e) ∈ R",
p.7), and it agrees with the printed one for `c = 0`, the case of §3. -/
def R {n k : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (c : Fin n → ℝ) (Iplus : Set (Fin n)) :
    Set (Point n) :=
  {p | c ⬝ᵥ p.2.1 ≤ p.1 ∧ A.mulVec p.2.1 = 0 ∧ (∀ i ∈ Iplus, 0 ≤ p.2.1 i) ∧ ∀ i, p.2.2 i = 1}

/-- The union `⋃_{I : |I| ≤ k} V(I)` of arXiv:2110.14884v2, Theorem 1, p.6, where `k` is the
number of rows of `A`. -/
def lowRankPieces {n k : ℕ} (g : (Fin k → ℝ) → EReal) (A : Matrix (Fin k) (Fin n) ℝ)
    (c : Fin n → ℝ) (Iplus : Set (Fin n)) : Set (Point n) :=
  ⋃ I : Finset (Fin n), ⋃ _ : I.card ≤ k, VI g A c Iplus I

/-- The cone `{x ∈ ℝⁿ : Ax = 0, xᵢ ≥ 0 ∀i ∈ I₊}` of arXiv:2110.14884v2, Theorem 1, p.6. -/
def recCone {n k : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (Iplus : Set (Fin n)) :
    Set (Fin n → ℝ) :=
  {x | A.mulVec x = 0 ∧ ∀ i ∈ Iplus, 0 ≤ x i}

open Classical in
/-- The support `supp(y) = {i : yᵢ ≠ 0}` of arXiv:2110.14884v2, p.5. -/
noncomputable def supp {n : ℕ} (y : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => y i ≠ 0

end LowRankIndicator


