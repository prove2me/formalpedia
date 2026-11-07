-- Prove2me | Definitions.Def_CodeSW_fk
-- name    : CodeSW_fk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:25:00.215794+00:00
-- url     : https://prove2.me/theorems/81bbc817-8654-4998-ad4c-d2c3fca01d71
-- title:
--   The generalized FK measure $\mu$, the operators $M$, $M^*$, $T_e$ and the space $L_2(\mu)$
-- statement:
--   The **generalized FK measure** on pairs $(x,A)\in\{0,1\}^n\times 2^E$ is
--   $$\mu(x,A)\propto\Bigl(\frac{p}{1-p}\Bigr)^{|A|}\mathbf 1(A\subseteq E(x)).$$
--   It couples the Gibbs distribution to the random cluster model. The operators comparing the Swendsen-Wang and single-check dynamics are
--   $$M(B,(x,A)):=2^{-k(A)}\mathbf 1(A=B)\mathbf 1(x\in X(A)),\qquad M^*((x,A),B)=\mathbf 1(A=B),$$
--   $$T_e((x,A),(y,B)):=\mathbf 1(x=y)\begin{cases}p&B=A\cup e\text{ and }e\in E(x),\\1-p&B=A\setminus e\text{ and }e\in E(x),\\1&B=A\text{ and }e\notin E(x),\\0&\text{otherwise.}\end{cases}$$
--   The space $L_2(\mu)$ has inner product $\langle f,g\rangle_\mu=\sum_u f(u)g(u)\mu(u)$, norm $\|f\|_\mu$ and operator norm $\|K\|_\mu=\max_{\|f\|_\mu\le 1}\|Kf\|_\mu$. A matrix acts on functions by $(Kf)(u)=\sum_v K(u,v)f(v)$, and $K$ is self-adjoint in $L_2(\mu)$ when $\langle f,Kg\rangle_\mu=\langle Kf,g\rangle_\mu$ for all $f,g$.
--
--   **Formalization Note** The page prints $\sum f(x)f(g)\pi(x)$, a typo for $\sum f(x)g(x)\pi(x)$, and writes $\|f\|_\pi:=\langle f,f\rangle_\pi$; the norm here is the square root of the inner product. The operator norm is a real supremum over the nonempty set of $f$ with $\|f\|_\mu\le1$.
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), eq. (10), p.16; Appendix A, pp.33–34

import Definitions.Def_CodeSW_kerA
open Matrix
noncomputable section

namespace CodeSW

/-- The unnormalized **generalized FK weight** `(p/(1−p))^{|A|} 1(A ⊆ E(x))` of a joint
configuration `(x, A) ∈ X × Ω`, `X = {0,1}^n`, `Ω = 2^E` (Hangleiter, Ju, Vazirani,
*Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript sha256 4e4abb5e…, eq. (10), p.16). -/
def fkWeight {c n : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2)) (p : ℝ)
    (u : (Fin n → ZMod 2) × Finset (Fin c)) : ℝ :=
  (p / (1 - p)) ^ u.2.card * (if u.2 ⊆ satChecks h u.1 then 1 else 0)

/-- The **generalized FK measure** `µ(x, A) ∝ (p/(1−p))^{|A|} 1(A ⊆ E(x))`, normalized
(arXiv:2510.08446, manuscript sha256 4e4abb5e…, eq. (10), p.16). -/
def fk {c n : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2)) (p : ℝ)
    (u : (Fin n → ZMod 2) × Finset (Fin c)) : ℝ :=
  fkWeight h p u / ∑ v : (Fin n → ZMod 2) × Finset (Fin c), fkWeight h p v

open Classical in
/-- The lift `M : L²(µ) → L²(ϕ)`, `M(B, (x, A)) := 2^{−k(A)} 1(A = B) 1(x ∈ X(A))`, with
`X(A) = ker(h_A)` (arXiv:2510.08446, manuscript sha256 4e4abb5e…, Appendix A, p.34). -/
def liftM {c n : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2)) :
    Matrix (Finset (Fin c)) ((Fin n → ZMod 2) × Finset (Fin c)) ℝ :=
  fun B u => ((2 : ℝ) ^ kDim h u.2)⁻¹ * (if u.2 = B then 1 else 0) *
    (if u.1 ∈ kerA h u.2 then 1 else 0)

/-- The adjoint `M*((x, A), B) = 1(A = B)` of `M` (arXiv:2510.08446, manuscript sha256
4e4abb5e…, Appendix A, p.34). -/
def liftMStar {c n : ℕ} :
    Matrix ((Fin n → ZMod 2) × Finset (Fin c)) (Finset (Fin c)) ℝ :=
  fun u B => if u.2 = B then 1 else 0

/-- The FK update `T_e` of a single check `e` (arXiv:2510.08446, manuscript sha256 4e4abb5e…,
Appendix A, p.34):
`T_e((x, A), (y, B)) := 1(x = y) · { p if B = A ∪ e and e ∈ E(x); 1 − p if B = A \ e and
e ∈ E(x); 1 if B = A and e ∉ E(x); 0 otherwise }`.

**Formalization Note** `A ∪ e` and `A \ e` never coincide, so the cases are disjoint. -/
def resample {c n : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2)) (p : ℝ) (e : Fin c) :
    Matrix ((Fin n → ZMod 2) × Finset (Fin c)) ((Fin n → ZMod 2) × Finset (Fin c)) ℝ :=
  fun u v =>
    if u.1 = v.1 then
      (if e ∈ satChecks h u.1 then
        (if v.2 = insert e u.2 then p else if v.2 = u.2.erase e then 1 - p else 0)
      else (if v.2 = u.2 then 1 else 0))
    else 0

/-- The inner product `⟨f, g⟩_µ = ∑_u f(u) g(u) µ(u)` of `L²(µ)` (arXiv:2510.08446, manuscript
sha256 4e4abb5e…, Appendix A, p.33).

**Formalization Note** The page prints `∑ f(x)f(g)π(x)`, a typo for `∑ f(x)g(x)π(x)`. -/
def innerMu {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (f g : Ω → ℝ) : ℝ :=
  ∑ u, f u * g u * μ u

/-- The norm `‖f‖_µ = ⟨f, f⟩_µ^{1/2}` of `L²(µ)` (arXiv:2510.08446, manuscript sha256 4e4abb5e…,
Appendix A, p.34).

**Formalization Note** The page writes `‖f‖_π := ⟨f, f⟩_π`; the square root is the norm of
`L²(π)` that the operator norm on the same page refers to. -/
def normMu {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  Real.sqrt (innerMu μ f f)

/-- The operator norm `‖K‖_µ = max_{‖f‖_µ ≤ 1} ‖K f‖_µ` of a matrix acting on `L²(µ)` by
`(K f)(u) = ∑_v K(u, v) f(v)` (arXiv:2510.08446, manuscript sha256 4e4abb5e…, Appendix A, p.34).

**Formalization Note** A real supremum over the nonempty set `{f : ‖f‖_µ ≤ 1}` (it contains
`f = 0`). -/
def opNormMu {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (K : Matrix Ω Ω ℝ) : ℝ :=
  ⨆ f : {f : Ω → ℝ // normMu μ f ≤ 1}, normMu μ (K *ᵥ f.1)

/-- A matrix `K` is **self-adjoint in `L²(µ)`**: `⟨f, K g⟩_µ = ⟨K f, g⟩_µ` for all `f, g`
(arXiv:2510.08446, manuscript sha256 4e4abb5e…, Lemma 28 (i), p.34).

**Formalization Note** Stated with the inner product itself, for all real functions. -/
def IsSelfAdjointMu {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (K : Matrix Ω Ω ℝ) : Prop :=
  ∀ f g : Ω → ℝ, innerMu μ f (K *ᵥ g) = innerMu μ (K *ᵥ f) g

end CodeSW


