-- Prove2me | Definitions.Def_KAdaptability_Bilinear_Problem
-- name    : KAdaptability_Bilinear_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:01:24.318783+00:00
-- url     : https://prove2.me/theorems/2f78f7d2-e25d-48f3-869a-4816be728d3d
-- title:
--   The two-stage robust binary program under constraint uncertainty and its ε-approximation (6_ε)
-- statement:
--   An instance of the two-stage robust binary program with uncertain constraints consists of the following data. There are $N$ first-stage variables, $M$ second-stage variables, $L$ second-stage constraints and $Q$ uncertain parameters; the paper uses the letter $Q$ both for this dimension and for a matrix, so in Lean the dimension is called `nQ` and the matrix `Q`.
--
--   1. Matrices $C\in\mathbb R^{Q\times N}$, $Q\in\mathbb R^{Q\times M}$, $T\in\mathbb R^{L\times N}$, $W\in\mathbb R^{L\times M}$ and $H\in\mathbb R^{L\times Q}$.
--   2. An uncertainty set $\Xi=\{\xi\in\mathbb R^Q : A\xi\le b\}$ with $A\in\mathbb R^{R\times Q}$, $b\in\mathbb R^R$ and componentwise inequality, assumed **nonempty and bounded**.
--   3. A first-stage feasible set $\mathcal X\subseteq\{0,1\}^N$ (the standing assumption of §3) and a second-stage feasible set $\mathcal Y\subseteq\{0,1\}^M$.
--
--   A decision is a tuple $(x,\{y^k\}_{k\in\mathcal K})\in\mathcal X\times\mathcal Y^K$, $\mathcal K=\{1,\dots,K\}$. Let $\mathcal L=\{0,1,\dots,L\}^K$, $\mathcal L_+=\{\ell\in\mathcal L:\ell_k\neq 0\ \forall k\}$ and $\partial\mathcal L=\mathcal L\setminus\mathcal L_+$. For $\epsilon>0$ the approximate uncertainty sets are
--   $$\Xi_\epsilon(\ell)=\left\{\xi\in\Xi:\ \begin{array}{ll} Tx+Wy^k\le H\xi & \forall k\in\mathcal K:\ell_k=0\\ [Tx+Wy^k]_{\ell_k}\ge[H\xi]_{\ell_k}+\epsilon & \forall k\in\mathcal K:\ell_k\neq 0\end{array}\right\},$$
--   where $[v]_i$ is the $i$-th component of $v$, and problem $(6_\epsilon)$ minimizes over $\mathcal X\times\mathcal Y^K$ the objective
--   $$\varphi_\epsilon(x,\{y^k\})=\sup_{\ell\in\mathcal L}\ \sup_{\xi\in\Xi_\epsilon(\ell)}\Big[\xi^\top Cx+\min_{k\in\mathcal K:\ \ell_k=0}\xi^\top Qy^k\Big].$$
--
--   This is the problem that Theorem 5 reformulates as the mixed-integer bilinear program (7).
--
--   **Formalization Note** Objective values live in the extended reals: a minimum over an empty index set is $+\infty$, a supremum over an empty set is $-\infty$, and the optimal value of $(6_\epsilon)$ is the infimum of $\varphi_\epsilon$ over all decisions. An index $\ell\in\mathcal L$ is a function `Fin K → Fin (L+1)`; the value $\ell_k=i+1$ refers to row $i+1$ of $T$, $W$, $H$, which is row `i : Fin L` in Lean. $\mathcal Y$ is a set of 0/1 vectors (a subset of $\{0,1\}^M$ is exactly the set of binary points of a polyhedron). Nonemptiness and boundedness of $\Xi$ and the binarity of $\mathcal X$, $\mathcal Y$ are fields of the structure.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. 6 (problem (P), its data, Ξ a nonempty bounded polyhedron, 𝒴 ⊆ {0,1}^M), p. 8 (𝒫_K, +∞ convention), p. 14 (𝒳 ⊆ {0,1}^N), p. 17 (ℒ, ℒ₊, ∂ℒ), p. 18 (problem (6_ε) and Ξ_ε(ℓ))

import Mathlib

open Matrix

namespace KAdaptability.Bilinear

/-- The data of the two-stage robust binary program with constraint uncertainty (𝒫), p. 6 of
Hanasusanto–Kuhn–Wiesemann, under the standing assumption of §3 (p. 14) that `𝒳 ⊆ {0,1}^N`.
Dimensions: `N` first-stage variables, `M` second-stage variables, `L` second-stage constraints,
`nQ` uncertain parameters (the paper's `Q`), `R` rows of the uncertainty set's description.
The matrix the paper calls `Q` is the field `Q`.
The standing assumptions are part of the data: every point of `𝒳` is a 0/1 vector, every point
of `𝒴` is a 0/1 vector, and `Ξ = {ξ : Aξ ≤ b}` is a nonempty bounded polyhedron (p. 6). -/
structure Problem (N M L nQ R : ℕ) where
  /-- First-stage objective matrix `C ∈ ℝ^{Q×N}`. -/
  C : Matrix (Fin nQ) (Fin N) ℝ
  /-- Second-stage objective matrix `Q ∈ ℝ^{Q×M}`. -/
  Q : Matrix (Fin nQ) (Fin M) ℝ
  /-- Technology matrix `T ∈ ℝ^{L×N}`. -/
  T : Matrix (Fin L) (Fin N) ℝ
  /-- Recourse matrix `W ∈ ℝ^{L×M}`. -/
  W : Matrix (Fin L) (Fin M) ℝ
  /-- Right-hand side matrix `H ∈ ℝ^{L×Q}`. -/
  H : Matrix (Fin L) (Fin nQ) ℝ
  /-- Uncertainty set description `A ∈ ℝ^{R×Q}`. -/
  A : Matrix (Fin R) (Fin nQ) ℝ
  /-- Uncertainty set description `b ∈ ℝ^R`. -/
  b : Fin R → ℝ
  /-- First-stage feasible set `𝒳`. -/
  X : Set (Fin N → ℝ)
  /-- Second-stage feasible set `𝒴`. -/
  Y : Set (Fin M → ℝ)
  /-- `𝒳 ⊆ {0,1}^N` (standing assumption of §3, p. 14). -/
  X_binary : ∀ x ∈ X, ∀ i, x i = 0 ∨ x i = 1
  /-- `𝒴 ⊆ {0,1}^M` (p. 6). -/
  Y_binary : ∀ y ∈ Y, ∀ i, y i = 0 ∨ y i = 1
  /-- `Ξ` is nonempty (p. 6). -/
  Xi_nonempty : {ξ : Fin nQ → ℝ | A *ᵥ ξ ≤ b}.Nonempty
  /-- `Ξ` is bounded (p. 6). -/
  Xi_bounded : Bornology.IsBounded {ξ : Fin nQ → ℝ | A *ᵥ ξ ≤ b}

namespace Problem

variable {N M L nQ R : ℕ} (P : Problem N M L nQ R)

/-- The uncertainty set `Ξ = {ξ ∈ ℝ^Q : Aξ ≤ b}` (componentwise inequality). -/
def Xi : Set (Fin nQ → ℝ) :=
  {ξ | P.A *ᵥ ξ ≤ P.b}

/-- The left-hand side `Tx + Wy` of the second-stage constraints `Tx + Wy ≤ Hξ`. -/
def lhs (x : Fin N → ℝ) (y : Fin M → ℝ) : Fin L → ℝ :=
  P.T *ᵥ x + P.W *ᵥ y

/-- The right-hand side `Hξ` of the second-stage constraints. -/
def rhs (ξ : Fin nQ → ℝ) : Fin L → ℝ :=
  P.H *ᵥ ξ

/-- The first-stage cost `ξ⊤Cx`. -/
def firstCost (ξ : Fin nQ → ℝ) (x : Fin N → ℝ) : ℝ :=
  ξ ⬝ᵥ (P.C *ᵥ x)

/-- The second-stage cost `ξ⊤Qy`. -/
def secondCost (ξ : Fin nQ → ℝ) (y : Fin M → ℝ) : ℝ :=
  ξ ⬝ᵥ (P.Q *ᵥ y)

/-- A decision `(x, {y^k}_{k∈𝒦}) ∈ 𝒳 × 𝒴^K` with `K` second-stage policies. -/
def IsDecision {K : ℕ} (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) : Prop :=
  x ∈ P.X ∧ ∀ k, y k ∈ P.Y

/-- `ℒ₊ = {ℓ ∈ ℒ : ℓ > 0}` (p. 17): every component of `ℓ` is nonzero. Here
`ℒ = {0,…,L}^K` is encoded as `Fin K → Fin (L + 1)`. -/
def LPlus (K L : ℕ) : Set (Fin K → Fin (L + 1)) :=
  {ℓ | ∀ k, ℓ k ≠ 0}

/-- `∂ℒ = ℒ ∖ ℒ₊` (p. 17): some component of `ℓ` is zero. -/
def LBdry (K L : ℕ) : Set (Fin K → Fin (L + 1)) :=
  {ℓ | ∃ k, ℓ k = 0}

/-- The closed inner approximation `Ξ_ε(ℓ)` (p. 18):
`Ξ_ε(ℓ) = {ξ ∈ Ξ : Tx + Wy^k ≤ Hξ ∀k : ℓ_k = 0;  [Tx + Wy^k]_{ℓ_k} ≥ [Hξ]_{ℓ_k} + ε ∀k : ℓ_k ≠ 0}`.
`ℓ_k = 0` means policy `k` satisfies every constraint; `ℓ_k = i + 1` (`i : Fin L`, the paper's
row `i + 1 ∈ {1,…,L}`) means policy `k` violates row `i + 1` by at least `ε`. -/
def XiEps (ε : ℝ) {K : ℕ} (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1)) :
    Set (Fin nQ → ℝ) :=
  {ξ | ξ ∈ P.Xi ∧ (∀ k, ℓ k = 0 → P.lhs x (y k) ≤ P.rhs ξ) ∧
    ∀ k (i : Fin L), ℓ k = i.succ → P.rhs ξ i + ε ≤ P.lhs x (y k) i}

/-- The bracket `ξ⊤Cx + min_{k∈𝒦 : ℓ_k = 0} ξ⊤Qy^k` of problem (6_ε), in `EReal`; the minimum
over the empty set (every `ℓ_k ≠ 0`) is `⊤ = +∞`, as the paper prescribes (p. 8, p. 17). -/
noncomputable def bracket {K : ℕ} (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ)
    (ℓ : Fin K → Fin (L + 1)) (ξ : Fin nQ → ℝ) : EReal :=
  ((P.firstCost ξ x : ℝ) : EReal) +
    ⨅ k ∈ {k : Fin K | ℓ k = 0}, ((P.secondCost ξ (y k) : ℝ) : EReal)

/-- The objective of problem (6_ε) (p. 18) at the decision `(x, {y^k})`:
`φ_ε(x, y) = sup_{ℓ∈ℒ} sup_{ξ∈Ξ_ε(ℓ)} [ξ⊤Cx + min_{k : ℓ_k = 0} ξ⊤Qy^k]`, in `EReal`
(a supremum over the empty set is `⊥ = −∞`). -/
noncomputable def obj6Eps (ε : ℝ) {K : ℕ} (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) : EReal :=
  ⨆ ℓ : Fin K → Fin (L + 1), ⨆ ξ ∈ P.XiEps ε x y ℓ, P.bracket x y ℓ ξ

/-- The optimal value of problem (6_ε) (p. 18): the infimum of `φ_ε` over `𝒳 × 𝒴^K`
(`⊤` if there is no decision). -/
noncomputable def opt6Eps (ε : ℝ) (K : ℕ) : EReal :=
  ⨅ (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (_ : P.IsDecision x y), P.obj6Eps ε x y

end Problem

end KAdaptability.Bilinear


