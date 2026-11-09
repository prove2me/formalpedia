-- Prove2me | Definitions.Def_SongZhangKLS_appellPoly
-- name    : SongZhangKLS_appellPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:06:10.949201+00:00
-- url     : https://prove2.me/theorems/1ee93064-6013-4195-816d-f1fde10eec86
-- title:
--   Appell polynomials $P_k^\mu[T]$, the tensor family $\mathcal A_k^\mu$ and Appell pairings $Q_k^\mu f$
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R^n$. A $k$-tensor $T\in(\mathbb R^n)^{\otimes k}$ has entries $T_i$, $i=(i_1,\dots,i_k)\in[n]^k$; it is **symmetric** if $T_{i\circ\sigma}=T_i$ for every permutation $\sigma$ of the $k$ slots, $\langle T,S\rangle_{HS}=\sum_iT_iS_i$ and $\|T\|_{HS}=\langle T,T\rangle_{HS}^{1/2}$. For a polynomial $p$, $D^jp$ is the order-$j$ derivative tensor with entries $\partial_{i_1}\cdots\partial_{i_j}p$, and $T[x,\dots,x]=\sum_iT_ix_{i_1}\cdots x_{i_k}$.
--
--   1. **Appell polynomial.** Start with $p(x)=T[x,\dots,x]$ and, for $j=k-1,k-2,\dots,0$, replace $p$ by
--   $$p(x)-\frac1{j!}\big(\mathbb E_\mu[D^jp]\big)[x,\dots,x].$$
--   The result is $P_k^\mu[T]$; for $k=0$ there are no corrections and $P_0^\mu[T]=T$.
--   2. **Tensor form.** The entry $(\mathcal A_k^\mu)_i$ is the Appell correction (the same loop) of the ordered monomial $x_{i_1}\cdots x_{i_k}$, so that $P_k^\mu[T](x)=\langle T,\mathcal A_k^\mu(x)\rangle$ for symmetric $T$.
--   3. **Appell pairing.** For $f\in L^2(\mu)$, $Q_k^\mu f=\mathbb E_\mu[\mathcal A_k^\mu(X)f(X)]\in(\mathbb R^n)^{\otimes k}$.
--   4. $\mu$ has **finite moments through order $s$** if $\int\|x\|^r\,d\mu<\infty$ for every integer $1\le r\le s$.
--
--   The module also provides directional derivatives $D_hp$, iterated ones $D_{h_1}\cdots D_{h_j}p$, and the contractions $T(h,\cdot)$ and $T(h_1,\dots,h_j,\cdot)$ of the first slots.
--
--   These polynomials are the centered basis in which the paper expands every polynomial and measures its variance.
--
--   **Formalization Note** Polynomials are `MvPolynomial (Fin n) ℝ`, evaluated at $x\in\mathbb R^n$ by `polyEval`. Expectations are Bochner integrals; Definition 3.3 assumes finite moments through order at least $k$ (and Definition 4.2 through $2k$), and every statement using these objects carries that hypothesis or implies it.
-- source:
--   Z. Song, X. Zhang, An O(1) Bound for the KLS Constant, arXiv:2610.01447 (preprint; version of October 2026, sha256 c7d2264f…8a6c), §3, p.12 (notation $D^jf$); Definition 3.3, p.13; p.14 (entries of $\mathcal A_k^\mu$); Definition 4.2, p.22; Lemma 4.3, p.22 (finite moments)

import Mathlib

open MeasureTheory MvPolynomial

noncomputable section

namespace SongZhangKLS

variable {n : ℕ}

/-! Tensors on `ℝⁿ` and polynomials (Song, Zhang, *An O(1) Bound for the KLS Constant*,
arXiv:2610.01447, version of October 2026, sha256 c7d2264f…8a6c, §3, p.12 and §3.2, pp.13–14).
A `k`-tensor `T ∈ (ℝⁿ)^{⊗k}` is its array of entries `T : (Fin k → Fin n) → ℝ`. -/

/-- A `k`-tensor is **symmetric** if its entries are invariant under every permutation of the
`k` index slots. -/
def IsSymmetricTensor {k : ℕ} (T : (Fin k → Fin n) → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin k)) (i : Fin k → Fin n), T (i ∘ σ) = T i

/-- The Hilbert–Schmidt inner product `⟨T, S⟩_HS = Σ_i T_i S_i` of two `k`-tensors. -/
def hsInner {k : ℕ} (T S : (Fin k → Fin n) → ℝ) : ℝ :=
  ∑ i, T i * S i

/-- The Hilbert–Schmidt norm `‖T‖_HS = (Σ_i T_i²)^{1/2}` of a `k`-tensor. -/
def hsNorm {k : ℕ} (T : (Fin k → Fin n) → ℝ) : ℝ :=
  Real.sqrt (∑ i, T i ^ 2)

/-- Evaluation of a real polynomial in `n` variables at a point `x ∈ ℝⁿ`. -/
def polyEval (p : MvPolynomial (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  MvPolynomial.eval (fun i => x i) p

/-- The homogeneous polynomial `T[x, …, x] = Σ_i T_i x_{i₁} ⋯ x_{i_k}` of a `k`-tensor `T`. -/
def tensorPoly {k : ℕ} (T : (Fin k → Fin n) → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i : Fin k → Fin n, C (T i) * ∏ m, X (i m)

/-- The iterated partial derivative `∂_{i₁} ⋯ ∂_{i_j} p` of a polynomial: the entry `i` of the
order-`j` derivative tensor `D^j p` ("For a smooth function f, we write D^j f as its order-j
derivative tensor, with entries ∂_{i₁} ⋯ ∂_{i_j} f", p.12). -/
def iterPderiv {j : ℕ} (i : Fin j → Fin n) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  (List.ofFn i).foldr (fun a q => pderiv a q) p

/-- The expected derivative tensor `E_µ[D^j p]`, with entries `E_µ[∂_{i₁} ⋯ ∂_{i_j} p]`. -/
def expectedDeriv (μ : Measure (EuclideanSpace ℝ (Fin n))) (j : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    (Fin j → Fin n) → ℝ :=
  fun i => ∫ x, polyEval (iterPderiv i p) x ∂μ

/-- The directional derivative `D_h p = Σ_a h_a ∂_a p` of a polynomial along `h ∈ ℝⁿ`. -/
def dirDeriv (h : EuclideanSpace ℝ (Fin n)) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ a, C (h a) * pderiv a p

/-- The iterated directional derivative `D_{h₁} ⋯ D_{h_j} p`. -/
def iterDirDeriv {j : ℕ} (h : Fin j → EuclideanSpace ℝ (Fin n)) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  (List.ofFn h).foldr dirDeriv p

/-- The contraction `T(h, ·)` of the first slot of a `(k+1)`-tensor with `h ∈ ℝⁿ`. -/
def contractOne {k : ℕ} (h : EuclideanSpace ℝ (Fin n)) (T : (Fin (k + 1) → Fin n) → ℝ) :
    (Fin k → Fin n) → ℝ :=
  fun i => ∑ a, h a * T (Fin.cons a i)

/-- The contraction `T(h₁, …, h_j, ·)` of the first `j` slots of a `(j+m)`-tensor with
`h₁, …, h_j ∈ ℝⁿ`. -/
def contractFirst {j m : ℕ} (h : Fin j → EuclideanSpace ℝ (Fin n))
    (T : (Fin (j + m) → Fin n) → ℝ) : (Fin m → Fin n) → ℝ :=
  fun i => ∑ a : Fin j → Fin n, (∏ r, h r (a r)) * T (Fin.append a i)

/-- `µ` has **finite moments through order `s`**: `∫ ‖x‖^r dµ < ∞` for every integer
`1 ≤ r ≤ s` (the gloss in Lemma 4.3, p.22). -/
def HasFiniteMoments (μ : Measure (EuclideanSpace ℝ (Fin n))) (s : ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → r ≤ s → Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ r) μ

/-- One correction step of Definition 3.3: replace `p` by
`p(x) − (1/j!) (E_µ[D^j p])[x, …, x]`. -/
def appellCorrect (μ : Measure (EuclideanSpace ℝ (Fin n))) (j : ℕ)
    (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  p - C ((Nat.factorial j : ℝ)⁻¹) * tensorPoly (expectedDeriv μ j p)

/-- The correction loop of Definition 3.3: `appellSteps µ k p` applies the corrections for
`j = k − 1, k − 2, …, 0`, in this order, each to the current polynomial. -/
def appellSteps (μ : Measure (EuclideanSpace ℝ (Fin n))) :
    ℕ → MvPolynomial (Fin n) ℝ → MvPolynomial (Fin n) ℝ
  | 0, p => p
  | m + 1, p => appellSteps μ m (appellCorrect μ m p)

/-- The **Appell polynomial** `P_k^µ[T]` (Song, Zhang, *An O(1) Bound for the KLS Constant*,
arXiv:2610.01447, version of October 2026, sha256 c7d2264f…8a6c, Definition 3.3, p.13): start with
`p(x) = T[x, …, x]` and, for `j = k − 1, k − 2, …, 0`, replace `p` by
`p(x) − (1/j!)(E_µ[D^j p])[x, …, x]`; for `k = 0` there are no corrections and `P_0^µ[T] = T`.

**Formalization Note.** Polynomials are `MvPolynomial (Fin n) ℝ`, evaluated by `polyEval`.
Expectations are Bochner integrals; Definition 3.3 assumes finite moments through order `s ≥ k`,
which every statement using `appellPoly` carries as a hypothesis (or which follows from its
hypotheses), so that every integral is a genuine expectation. -/
def appellPoly (μ : Measure (EuclideanSpace ℝ (Fin n))) (k : ℕ) (T : (Fin k → Fin n) → ℝ) :
    MvPolynomial (Fin n) ℝ :=
  appellSteps μ k (tensorPoly T)

/-- The entry `i` of the tensor-valued Appell polynomial `A_k^µ`: the Appell correction of the
ordered monomial `x_{i₁} ⋯ x_{i_k}` (Definition 3.3, p.13, and p.14: "The entries of A_k^µ are the
Appell corrections of the ordered monomials"). For symmetric `T`,
`P_k^µ[T](x) = ⟨T, A_k^µ(x)⟩` by linearity of the correction loop. -/
def appellTensor (μ : Measure (EuclideanSpace ℝ (Fin n))) (k : ℕ) (i : Fin k → Fin n) :
    MvPolynomial (Fin n) ℝ :=
  appellSteps μ k (∏ m, X (i m))

/-- The **Appell pairing** `Q_k^µ f = E_µ[A_k^µ(X) f(X)] ∈ (ℝⁿ)^{⊗k}` (Definition 4.2, p.22, of
Song, Zhang, arXiv:2610.01447, version of October 2026, sha256 c7d2264f…8a6c), as its array of
entries `E_µ[(A_k^µ)_i(X) f(X)]`. -/
def appellPairing (μ : Measure (EuclideanSpace ℝ (Fin n))) (k : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : (Fin k → Fin n) → ℝ :=
  fun i => ∫ x, polyEval (appellTensor μ k i) x * f x ∂μ

end SongZhangKLS


