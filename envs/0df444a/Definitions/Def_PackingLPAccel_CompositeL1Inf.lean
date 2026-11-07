-- Prove2me | Definitions.Def_PackingLPAccel_CompositeL1Inf
-- name    : PackingLPAccel_CompositeL1Inf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:41:35.504056+00:00
-- url     : https://prove2.me/theorems/41f8cd6c-9b16-4262-8ead-0c2f4f2e1bcc
-- title:
--   Composite $\ell_{1,\infty}$-regression, packing LP $\ell_{1,\infty}$ instances, and the instances $I(\lambda)$
-- statement:
--   An instance of composite $\ell_{1,\infty}$-regression has blocks $\mathcal X_j\subseteq\mathbb R^m_{\ge0}$, each nonempty, convex and compact, with convex costs $\psi_j$ on them. The problem is
--
--   $$\min_{X\in\bigotimes_j\mathcal X_j}\ \mathcal E_{1,\infty}(X),\qquad \mathcal E_{1,\infty}(X)=\sum_j\psi_j(X_j)+\|X\|_{1,\infty},\qquad \|X\|_{1,\infty}=\max_i\sum_j|X_{ij}|.$$
--
--   A point $\hat X$ has relative-additive error $(\varepsilon,\delta)$ against a minimizer $X^\star$ if $\mathcal E_{1,\infty}(\hat X)\le\psi(X^\star)+(1+\varepsilon)\|X^\star\|_{1,\infty}+\delta$. A packing LP $\ell_{1,\infty}$ instance has blocks $\{(A_{1,j}x,\dots,A_{m,j}x):x\in[l_j,u_j]\}$ for a nonnegative matrix without empty rows or columns, and linear costs.
--
--   The instance $I(\lambda)$ of the reduction adds one row and one column holding the constant $1$, with $x_j\in[0,1/\|A_{:,j}\|_\infty]$ and $\psi_j^{(\lambda)}(Y_j)=-A_{i^*(j),j}^{-1}Y_{i^*(j),j}/\lambda$. In the coordinates $x$ its objective is $\max\{1,\|Ax\|_\infty\}-\langle\mathbf 1,x\rangle/\lambda$. The module also defines the rescaling $\hat x=x/\max\{1,\|Ax\|_\infty\}$ and the oracle of Lemma 3.5.
--
--   **Formalization Note** The paper's sum index $j\in[m]$ in $\|X\|_{1,\infty}$ (pp.3, 7) is a slip for $j\in[k]$. The argmax choice $i^*(j,A)$ is a free parameter $\mathsf{iStar}$, and the theorems hold for every such choice.
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), Problem 1.2, pp.3, 8 (pdf 4, 9); Definition 3.1, p.9 (pdf 10); relative-additive error, p.5 (pdf 6); proof of Lemma 3.5, p.11 (pdf 12)

import Mathlib
import Definitions.Def_PackingLPAccel_PackingLP

namespace PackingLPAccel

/-!
# Composite `ℓ₁,∞`-regression and the instances `I(λ)`

Chen, Chen, Graur, Sidford, *Accelerated Parallel Algorithms for Packing Linear Programming*,
STOC 2027 submission (manuscript sha256 1dac7711…), Problem 1.2 (pp.3, 8), Definition 3.1 (p.9), the
relative-additive error (p.5), and the instance of the proof of Lemma 3.5 (p.11).

**Formalization Note.**
* `∥X∥_{1,∞} := max_i ∑_{j ∈ [k]} |X_ij|`; the paper's sum index `j ∈ [m]` (pp.3, 7) is a slip for
  `j ∈ [k]`.
* An instance has total functions `ψ_j` on `ℝ^m`; only their values on `X_j` matter.
* `I(λ)` has one extra row and one extra column holding the constant `1`. `packingEmbed A x` is its
  point with coordinates `x`; its objective is `max{1, ∥Ax∥_∞} - ⟨1, x⟩ / λ`.
* `i*(j, A)` of (5) is a free argmax choice `iStar`, and every theorem holds for each such choice.
-/

variable {m k n : ℕ}

/-- The data of Problem 1.2: blocks `X_j ⊆ ℝ^m` and costs `ψ_j`. -/
structure CompositeInstance (m k : ℕ) where
  /-- The block `X_j`. -/
  X : Fin k → Set (Fin m → ℝ)
  /-- The cost `ψ_j`. -/
  ψ : Fin k → (Fin m → ℝ) → ℝ

/-- The conditions of Problem 1.2: each `X_j` is a nonempty, convex, compact subset of `ℝ^m_{≥0}`, and
each `ψ_j` is convex on it. -/
def CompositeInstance.IsValid (I : CompositeInstance m k) : Prop :=
  ∀ j, (I.X j).Nonempty ∧ Convex ℝ (I.X j) ∧ IsCompact (I.X j) ∧ (∀ x ∈ I.X j, ∀ i, 0 ≤ x i) ∧
    ConvexOn ℝ (I.X j) (I.ψ j)

/-- `X ∈ ⊗_j X_j`. -/
def CompositeInstance.Mem (I : CompositeInstance m k) (X : Matrix (Fin m) (Fin k) ℝ) : Prop :=
  ∀ j, (fun i => X i j) ∈ I.X j

/-- `ψ(X) = ∑_j ψ_j(X_j)`. -/
noncomputable def CompositeInstance.psi (I : CompositeInstance m k)
    (X : Matrix (Fin m) (Fin k) ℝ) : ℝ :=
  ∑ j, I.ψ j (fun i => X i j)

/-- `∥X∥_{1,∞}`. -/
noncomputable def l1InfNorm (X : Matrix (Fin m) (Fin k) ℝ) : ℝ := ⨆ i, ∑ j, |X i j|

/-- `E_{1,∞}(X) = ψ(X) + ∥X∥_{1,∞}`, display (2). -/
noncomputable def CompositeInstance.energy (I : CompositeInstance m k)
    (X : Matrix (Fin m) (Fin k) ℝ) : ℝ :=
  I.psi X + l1InfNorm X

/-- `X⋆` minimizes `E_{1,∞}` over `⊗_j X_j`. -/
def CompositeInstance.IsMinimizer (I : CompositeInstance m k)
    (X : Matrix (Fin m) (Fin k) ℝ) : Prop :=
  I.Mem X ∧ ∀ Y, I.Mem Y → I.energy X ≤ I.energy Y

/-- `E(X̂) ≤ ψ(X⋆) + (1 + ε) ∥X⋆∥_{1,∞} + δ`: relative-additive error `(ε, δ)` against the
minimizer `X⋆` (p.5). -/
def CompositeInstance.ErrorAgainst (I : CompositeInstance m k) (ε δ : ℝ)
    (Xhat Xstar : Matrix (Fin m) (Fin k) ℝ) : Prop :=
  I.psi Xhat + l1InfNorm Xhat ≤ I.psi Xstar + (1 + ε) * l1InfNorm Xstar + δ

/-- Definition 3.1: a packing LP `ℓ₁,∞` instance, with bounds `0 ≤ l_j ≤ u_j`, a nonnegative matrix
without empty rows or columns, and linear `ψ_j`. -/
def CompositeInstance.IsPackingL1Inf (I : CompositeInstance m k) : Prop :=
  ∃ (l u : Fin k → ℝ) (B : Matrix (Fin m) (Fin k) ℝ),
    (∀ j, 0 ≤ l j ∧ l j ≤ u j) ∧ (∀ i j, 0 ≤ B i j) ∧ (∀ i, ∃ j, B i j ≠ 0) ∧
    (∀ j, ∃ i, B i j ≠ 0) ∧
    (∀ j, I.X j = {y | ∃ x ∈ Set.Icc (l j) (u j), y = fun i => B i j * x}) ∧
    ∀ j, ∃ c : Fin m → ℝ, ∀ y, I.ψ j y = ∑ i, c i * y i

/-- The matrix `B` of the proof of Lemma 3.5: `A` with one extra row and column, and `B_{m+1,n+1} = 1`. -/
def extMatrix (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ := fun i j =>
  Fin.lastCases (motive := fun _ => ℝ)
    (Fin.lastCases (motive := fun _ => ℝ) 1 (fun _ => 0) j)
    (fun i' => Fin.lastCases (motive := fun _ => ℝ) 0 (fun j' => A i' j') j) i

/-- `x_j ∈ [0, 1 / ∥A_{:,j}∥_∞]` for `j ≤ n`, and `x_{n+1} = 1`, the blocks of `I(λ)`. -/
noncomputable def extBox (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin (n + 1)) : Set ℝ :=
  Fin.lastCases (motive := fun _ => Set ℝ) (Set.Icc 1 1)
    (fun j' => Set.Icc 0 (1 / colNorm A j')) j

/-- The instance `I(λ)` of the proof of Lemma 3.5 (p.11): `ψ_j^{(λ)}(Y_j) = -A⁻¹_{i*(j),j} Y_{i*(j),j} / λ`
and `ψ_{n+1} = 0`. -/
noncomputable def packingInstance (A : Matrix (Fin m) (Fin n) ℝ) (iStar : Fin n → Fin m) (lam : ℝ) :
    CompositeInstance (m + 1) (n + 1) where
  X j := {y | ∃ x ∈ extBox A j, y = fun i => extMatrix A i j * x}
  ψ j := Fin.lastCases (motive := fun _ => (Fin (m + 1) → ℝ) → ℝ) (fun _ => 0)
    (fun j' y => -(A (iStar j') j')⁻¹ * y (iStar j').castSucc / lam) j

/-- The point of `I(λ)` with coordinates `x`. -/
def packingEmbed (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ := fun i j =>
  extMatrix A i j * Fin.lastCases (motive := fun _ => ℝ) 1 x j

/-- `x̂ = x / max{1, ∥Ax∥_∞}`, the rescaling of the proof of Lemma 3.5. -/
noncomputable def rescale (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => x j / max 1 (rowMax A x)

/-- The number of instances of Lemma 3.5: `⌈log₂ n⌉ + 2`. -/
def lemma35Count (n : ℕ) : ℕ := Nat.clog 2 n + 2

/-- The oracle of Lemma 3.5. The index `τ < ⌈log₂ n⌉ + 2` is at integer cell `-1` (block cell `0`), and
the answer is written from real block cell `0`: `x` with relative-additive error `(ε/4, ε/(8n))` for
`I(2^τ)` against some minimizer. Any other query has no answer. The paper's `τ ∈ [T]`, `I(2^{τ-1})`
is shifted by one. -/
def IsL1InfOracle (A : Matrix (Fin m) (Fin n) ℝ) (iStar : Fin n → Fin m) (ε : ℝ) (O : OracleModel) :
    Prop :=
  ∀ st : State,
    (∀ τ : ℕ, st.I (blockAddr 0) = τ → τ < lemma35Count n →
      ∃ x : Fin n → ℝ,
        (packingInstance A iStar (2 ^ τ)).Mem (packingEmbed A x) ∧
        (∃ Xs, (packingInstance A iStar (2 ^ τ)).IsMinimizer Xs ∧
          (packingInstance A iStar (2 ^ τ)).ErrorAgainst (ε / 4) (ε / (8 * n))
            (packingEmbed A x) Xs) ∧
        O.answer st = some (writeBlock st.M 0 n (fun k => if h : k < n then x ⟨k, h⟩ else 0), st.I)) ∧
    ((¬ ∃ τ : ℕ, st.I (blockAddr 0) = τ ∧ τ < lemma35Count n) → O.answer st = none)

end PackingLPAccel


