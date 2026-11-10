-- Prove2me | Definitions.Def_RandTensorIso_Smoothed_Spectral
-- name    : RandTensorIso_Smoothed_Spectral
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:36:06.683891+00:00
-- url     : https://prove2.me/theorems/a8b6814f-fe97-48f1-9267-74c909dbe22d
-- title:
--   Flattenings, Gram matrices $G_d(A)$, sorted eigenvalues, minimum eigenvalue gap, HOSVD cores; singular values, operator norm and incompressible vectors
-- statement:
--   For $d\in[3]$ the **mode-$d$ flattening** $A_{[d]}\in\mathbb C^{n\times n^2}$ has rows indexed by the mode-$d$ coordinate and columns by the pair of the other two coordinates; the **Gram matrix** $G_d(A)=A_{[d]}A_{[d]}^*$ is Hermitian and positive semidefinite, so $(G_1(A))_{ij}=\sum_{q,r}A_{iqr}\overline{A_{jqr}}$ and similarly for $d=2,3$ (the column order of the flattening does not matter). Its eigenvalues are $\lambda_1(G)\ge\lambda_2(G)\ge\dots$. The Gram matrices of $A$ have **minimum eigenvalue gap at least $\delta$** if $\lambda_i(G_d(A))-\lambda_{i+1}(G_d(A))\ge\delta$ for every $d\in[3]$ and $1\le i<n$. A tensor $S$ is an **HOSVD core** of $A$ if $S=(U_1^*,U_2^*,U_3^*)\curvearrowright A$ for unitary $U_d$ whose columns are unit eigenvectors of $G_d(A)$ ordered by decreasing eigenvalue, i.e. $G_d(A)U_d=U_d\operatorname{diag}(\lambda_1,\dots,\lambda_n)$.
--
--   For a complex $m\times k$ matrix $B$, the **singular values** $\sigma_1(B)\ge\dots\ge\sigma_k(B)$ are the square roots of the eigenvalues of $B^*B$ in nonincreasing order, $\sigma_{\min}(B)=\sigma_k(B)$, and $\|B\|$ is the operator norm. Following Definition 4.8 with $\mathbb C^k$ in place of $\mathbb R^k$ (§4.4): $x\in\mathbb C^k$ is **$c_0$-sparse** if it has at most $\lfloor c_0k\rfloor$ nonzero coordinates, and a unit vector $y$ is in $\mathrm{Incomp}_k(c_0,c_1)$ if no $c_0$-sparse $x$ has $\|y-x\|\le c_1$.
--
--   **Formalization Note.** Modes are 0-based (`d : Fin 3`); `pos d x a b` places $x$ in mode $d$ and $a,b$ in the other two modes in increasing order. `sortedEig` uses Mathlib's `IsHermitian.eigenvalues₀`, which is antitone, so index `0` is the largest eigenvalue; `sv B i` is $\sigma_{i+1}(B)$. `sigmaMin` is set to $0$ for a matrix with no columns, excluded in Lemma 4.6 and harmless in the empty-matrix corner of Lemma 4.7. `opNorm` is Mathlib's $L^2$ operator norm `Matrix.instL2OpNormedAddCommGroup`. `IsCore A S` asks for some admissible eigenvector matrices; when the spectra are simple all choices differ by diagonal unitaries and give the same moduli $|S(p)|$.
-- source:
--   Chizewer, Everett, Mithal, Qiao, Random tensor isomorphism under orthogonal and unitary actions: Smoothed and average-case analysis, STOC 2027 submission (manuscript sha256 f4a12b77…), pp. 14, 24, 50, 53, 59 (PDF 16, 26, 52, 55, 61), §2 preamble, §2.3, §4 (σ_i, ‖·‖), Definition 4.8, §4.4

import Mathlib
import Definitions.Def_RandTensorIso_Smoothed_Tensor

namespace RandTensorIso.Smoothed

open Matrix

/-- The position of `[n]³` with coordinate `x` in mode `d` and coordinates `a`, `b` in the two
other modes `e < e'` (in this order). Modes are 0-based: `d ∈ {0, 1, 2}` is the paper's
`d ∈ {1, 2, 3}`. -/
def pos {n : ℕ} (d : Fin 3) (x a b : Fin n) : Fin n × Fin n × Fin n :=
  if d = 0 then (x, a, b) else if d = 1 then (a, x, b) else (a, b, x)

/-- The mode-`d` flattening `A_[d] ∈ ℂ^{n × n²}` (columns indexed by the pair of the other two
coordinates; the column order does not affect the Gram matrix). -/
def flat {n : ℕ} (d : Fin 3) (A : Tensor3 n) : Matrix (Fin n) (Fin n × Fin n) ℂ :=
  fun x ab => A (pos d x ab.1 ab.2)

/-- The Gram matrix `G_d(A) = A_[d] A_[d]^*` (Hermitian, positive semidefinite, `n × n`). -/
def gram {n : ℕ} (d : Fin 3) (A : Tensor3 n) : Matrix (Fin n) (Fin n) ℂ :=
  flat d A * (flat d A)ᴴ

theorem gram_isHermitian {n : ℕ} (d : Fin 3) (A : Tensor3 n) : (gram d A).IsHermitian :=
  Matrix.isHermitian_mul_conjTranspose_self _

/-- The eigenvalues `λ₁(G) ≥ λ₂(G) ≥ ⋯` of a Hermitian `m × m` matrix, in nonincreasing order,
0-based (`sortedEig G hG 0` is the largest). -/
noncomputable def sortedEig {m : ℕ} (G : Matrix (Fin m) (Fin m) ℂ) (hG : G.IsHermitian) :
    Fin m → ℝ :=
  fun i => hG.eigenvalues₀ (Fin.cast (Fintype.card_fin m).symm i)

/-- The eigenvalues of `G_d(A)` in nonincreasing order (0-based). -/
noncomputable def gramEig {n : ℕ} (d : Fin 3) (A : Tensor3 n) : Fin n → ℝ :=
  sortedEig (gram d A) (gram_isHermitian d A)

/-- The Gram matrices of `A` have minimum eigenvalue gap at least `δ`:
`λ_i(G_d(A)) − λ_{i+1}(G_d(A)) ≥ δ` for every `d ∈ [3]` and `1 ≤ i < n`. -/
def MinEigGap {n : ℕ} (A : Tensor3 n) (δ : ℝ) : Prop :=
  ∀ d : Fin 3, ∀ i j : Fin n, j.val = i.val + 1 → δ ≤ gramEig d A i - gramEig d A j

/-- `V` is a unitary matrix whose columns are unit eigenvectors of `G_d(A)`, ordered by
decreasing eigenvalue: `G_d(A) V = V diag(λ₁, …, λ_n)`. -/
def IsGramEigBasis {n : ℕ} (d : Fin 3) (A : Tensor3 n) (V : U n) : Prop :=
  gram d A * (V : Matrix (Fin n) (Fin n) ℂ) =
    (V : Matrix (Fin n) (Fin n) ℂ) * diagonal (fun i => ((gramEig d A i : ℝ) : ℂ))

/-- `S` is an HOSVD core of `A`: `S = (U₁^*, U₂^*, U₃^*) ↷ A` for unitary `U_d` whose columns are
unit eigenvectors of `G_d(A)` ordered by decreasing eigenvalue. (When the spectra are simple the
core is determined up to diagonal unitaries, so the moduli `|S(p)|` do not depend on the choice.) -/
def IsCore {n : ℕ} (A S : Tensor3 n) : Prop :=
  ∃ V : Fin 3 → U n, (∀ d, IsGramEigBasis d A (V d)) ∧
    S = act (star (V 0 : Matrix (Fin n) (Fin n) ℂ)) (star (V 1 : Matrix (Fin n) (Fin n) ℂ))
      (star (V 2 : Matrix (Fin n) (Fin n) ℂ)) A

/-- The operator (spectral) norm `‖X‖` of a complex `m × k` matrix (Mathlib's `L²` operator
norm on matrices). -/
noncomputable def opNorm {m k : ℕ} (X : Matrix (Fin m) (Fin k) ℂ) : ℝ :=
  @Norm.norm _ (Matrix.instL2OpNormedAddCommGroup (𝕜 := ℂ) (m := Fin m) (n := Fin k)).toNorm X

/-- The singular values of a complex `m × k` matrix `B`, in nonincreasing order, 0-based:
`sv B i = σ_{i+1}(B) = (λ_{i+1}(B^* B))^{1/2}`. -/
noncomputable def sv {m k : ℕ} (B : Matrix (Fin m) (Fin k) ℂ) : Fin k → ℝ :=
  fun i => Real.sqrt (sortedEig (Bᴴ * B) (Matrix.isHermitian_conjTranspose_mul_self B) i)

/-- The smallest singular value `σ_min(B) = σ_k(B)` of a complex `m × k` matrix with `k ≥ 1`
(set to `0` when `k = 0`, a case every statement using it excludes). -/
noncomputable def sigmaMin {m k : ℕ} (B : Matrix (Fin m) (Fin k) ℂ) : ℝ :=
  if h : 0 < k then sv B ⟨k - 1, by omega⟩ else 0

/-- The Euclidean norm of a vector of `ℂ^k`. -/
noncomputable def vecNorm {k : ℕ} (x : Fin k → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖x i‖ ^ 2)

/-- Definition 4.8 (complex, §4.4): `x ∈ ℂ^k` is `c₀`-sparse if it is supported on at most
`⌊c₀ k⌋` coordinates. -/
def IsSparse {k : ℕ} (c₀ : ℝ) (x : Fin k → ℂ) : Prop :=
  (Finset.univ.filter (fun i => x i ≠ 0)).card ≤ ⌊c₀ * k⌋₊

/-- Definition 4.8 (complex, §4.4): `y` lies in `Incomp_k(c₀, c₁)`: it is a unit vector of `ℂ^k`
and it is not `(c₀, c₁)`-compressible, i.e. no `c₀`-sparse `x` has `‖y − x‖ ≤ c₁`. -/
def Incomp {k : ℕ} (c₀ c₁ : ℝ) (y : Fin k → ℂ) : Prop :=
  vecNorm y = 1 ∧ ¬ ∃ x : Fin k → ℂ, IsSparse c₀ x ∧ vecNorm (y - x) ≤ c₁

end RandTensorIso.Smoothed


