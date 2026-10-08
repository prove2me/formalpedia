-- Prove2me | Definitions.Def_InputSparsity_Regress_Basic
-- name    : InputSparsity_Regress_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T11:02:23.577357+00:00
-- url     : https://prove2.me/theorems/0c39b7d6-d553-4235-8bfa-5b5e676c97f3
-- title:
--   §1.2, §7.1–7.3, pp. 3, 22–24 — squared norms, least-squares and sketched minimizers, subspace embedding, the Lemma 32 event, Penrose equations
-- statement:
--   Throughout, matrices are real. For a vector $v\in\mathbb R^n$ and a matrix $M\in\mathbb R^{m\times n}$ write
--   $$\|v\|_2^2=\sum_i v_i^2,\qquad \|M\|_F^2=\sum_{i,j}M_{ij}^2 .$$
--   Let $A\in\mathbb R^{n\times d}$, $B\in\mathbb R^{n\times d'}$ and a sketching matrix $S\in\mathbb R^{t\times n}$ be given.
--
--   1. A matrix $U\in\mathbb R^{n\times k}$ has **orthonormal columns** if $U^\top U=I_k$; it is an **orthonormal basis of the column space** $C(A)=\{Ax : x\in\mathbb R^d\}$ if in addition $C(U)=C(A)$.
--   2. $Y^*\in\mathbb R^{d\times d'}$ is a **least-squares minimizer**, a solution of problem (8), if $\|AY^*-B\|_F^2\le\|AY-B\|_F^2$ for every $Y$.
--   3. $\tilde Y$ is a **sketched minimizer**, a solution of problem (7), if $\|S(A\tilde Y-B)\|_F^2\le\|S(AY-B)\|_F^2$ for every $Y$.
--   4. $S$ is a **subspace embedding for $A$ with parameter $\eta$** if for every $x\in\mathbb R^d$
--   $$\bigl|\,\|SAx\|_2^2-\|Ax\|_2^2\,\bigr|\le\eta\,\|Ax\|_2^2 .$$
--   5. $S$ satisfies the **approximate matrix multiplication event** of Lemma 32 for a pair $(A,B)$ of matrices with $n$ rows, with error parameter $e$, if
--   $$\|A^\top S^\top S B-A^\top B\|_F^2\le e^2\,\|A\|_F^2\,\|B\|_F^2 .$$
--   6. $G\in\mathbb R^{d\times n}$ is the **Moore–Penrose inverse** $C^-$ of $C\in\mathbb R^{n\times d}$ if it satisfies the four Penrose equations $CGC=C$, $GCG=G$, $(CG)^\top=CG$, $(GC)^\top=GC$.
--
--   These are the objects of §7 of Clarkson and Woodruff: the sketch-and-solve guarantee (Theorem 36) and the affine-embedding theorem (Theorem 39) are statements about a fixed matrix $S$ satisfying items 4 and 5.
--
--   **Formalization Note** Norms appear squared, as explicit sums. The subspace-embedding property is in squared form; Theorem 36 and Lemma 37 use it with $\eta$ in the role of the paper's $\epsilon_0^2$ (see those items). The Lemma 32 event uses $\le$ for the printed strict $<$: with $<$ the event fails whenever $B=0$, and a non-strict hypothesis is weaker. The randomness of Lemma 32 (a random $S$ and a probability $1-\delta$) is not part of the definition: only the event inside $\Pr[\cdot]$ is used, as a property of a fixed $S$. The Penrose equations characterize $C^-$ uniquely; no pseudoinverse function is defined. Indices are zero-based `Fin` types and no relation between $n$, $d$, $d'$, $t$, $k$ is assumed (the paper's "we assume $n>d$" concerns running times only).
-- source:
--   Clarkson and Woodruff, Low Rank Approximation and Regression in Input Sparsity Time, arXiv:1207.6365v4, p. 3, §1.2 (subspace embedding); p. 22, §7.1 (multiple-response regression); pp. 22–23, Lemma 32 (event); p. 23, Fact 35 (Moore–Penrose inverse); p. 24, (7) and (8)

import Mathlib
import Definitions.Def_InputSparsity_Embed_SparseEmbedding

namespace InputSparsity.Regress
open Matrix

/-- The columns of `U` form an orthonormal basis of the column space `C(A)`. -/
def IsOrthonormalBasisOf {n k d : ℕ} (U : Matrix (Fin n) (Fin k) ℝ)
    (A : Matrix (Fin n) (Fin d) ℝ) : Prop :=
  InputSparsity.Embed.HasOrthonormalCols U ∧
    LinearMap.range (Matrix.mulVecLin U) = LinearMap.range (Matrix.mulVecLin A)

/-- (8): `Y` minimizes `‖AY − B‖_F²` over all `Y`. -/
def IsLSMinimizer {n d d' : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (B : Matrix (Fin n) (Fin d') ℝ)
    (Y : Matrix (Fin d) (Fin d') ℝ) : Prop :=
  ∀ Y' : Matrix (Fin d) (Fin d') ℝ, InputSparsity.Embed.frobSq (A * Y - B) ≤ InputSparsity.Embed.frobSq (A * Y' - B)

/-- (7): `Y` minimizes the sketched objective `‖S(AY − B)‖_F²` over all `Y`. -/
def IsSketchedMinimizer {t n d d' : ℕ} (S : Matrix (Fin t) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin d) ℝ) (B : Matrix (Fin n) (Fin d') ℝ)
    (Y : Matrix (Fin d) (Fin d') ℝ) : Prop :=
  ∀ Y' : Matrix (Fin d) (Fin d') ℝ, InputSparsity.Embed.frobSq (S * (A * Y - B)) ≤ InputSparsity.Embed.frobSq (S * (A * Y' - B))

/-- Subspace embedding in squared form:
`|‖SAx‖₂² − ‖Ax‖₂²| ≤ η ‖Ax‖₂²` for every `x`. -/
def IsSubspaceEmbedding {t n d : ℕ} (S : Matrix (Fin t) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin d) ℝ) (η : ℝ) : Prop :=
  ∀ x : Fin d → ℝ, |InputSparsity.Embed.sqNorm (S *ᵥ (A *ᵥ x)) - InputSparsity.Embed.sqNorm (A *ᵥ x)| ≤ η * InputSparsity.Embed.sqNorm (A *ᵥ x)

/-- The event of Lemma 32 (approximate matrix multiplication) for the pair `(A, B)`
with error parameter `e`: `‖AᵀSᵀSB − AᵀB‖_F² ≤ e² ‖A‖_F² ‖B‖_F²`. -/
def AMMEvent {t n k m : ℕ} (S : Matrix (Fin t) (Fin n) ℝ) (A : Matrix (Fin n) (Fin k) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (e : ℝ) : Prop :=
  InputSparsity.Embed.frobSq (Aᵀ * Sᵀ * S * B - Aᵀ * B) ≤ e ^ 2 * InputSparsity.Embed.frobSq A * InputSparsity.Embed.frobSq B

/-- `G` satisfies the four Penrose equations for `C`, i.e. `G = C⁻` is the
Moore–Penrose inverse of `C`. -/
def IsMoorePenrose {n d : ℕ} (C : Matrix (Fin n) (Fin d) ℝ) (G : Matrix (Fin d) (Fin n) ℝ) :
    Prop :=
  C * G * C = C ∧ G * C * G = G ∧ (C * G)ᵀ = C * G ∧ (G * C)ᵀ = G * C

end InputSparsity.Regress


