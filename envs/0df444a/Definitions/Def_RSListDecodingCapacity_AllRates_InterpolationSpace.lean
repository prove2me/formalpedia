-- Prove2me | Definitions.Def_RSListDecodingCapacity_AllRates_InterpolationSpace
-- name    : RSListDecodingCapacity_AllRates_InterpolationSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:41.85739+00:00
-- url     : https://prove2.me/theorems/04f7fde3-786e-4d1c-be40-874272f7d477
-- title:
--   The interpolation space $\mathcal Q\subseteq\mathbb F[X,Y_0,\dots,Y_d]$ of (19)
-- statement:
--   With the parameters $d,A,m,B,W$ and the set $\mathcal B$ of Section 3, the **interpolation space** $\mathcal Q\subseteq\mathbb F[X,Y_0,\dots,Y_d]$ is the linear span of the monomials
--   $$X^aY_0^{b_0}Y_1^{b_1}Y^c,\qquad Y^c=\prod_{j=2}^dY_j^{c_j},$$
--   over all $a,b_0\in\mathbb Z_{\ge0}$, $c\in\mathcal B$ and $0\le b_1\le m$ with
--   $$b_0+b_1+|c|\le B\qquad\text{and}\qquad a+(k-1)(b_0+b_1+|c|)<mA .$$
--
--   The interpolating polynomial of the decoder is chosen in $\mathcal Q$; the constraints on $b_1$ and $c$ restrict the degrees in $Y_1,\dots,Y_d$ and the weighted degree $\omega$, while the last inequality bounds the $X$-degree after substituting a polynomial of degree below $k$.
--
--   **Formalization Note** The space is Mathlib's `MvPolynomial.restrictSupport` of the set of exponent vectors above (variables `none` $=X$, `some j` $=Y_j$). It is defined first for arbitrary numerical parameters and then at the parameters of Section 3.
-- source:
--   Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, Kai Zhe Zheng, Algorithmic List Decoding of Reed–Solomon Codes up to Capacity, STOC 2027 submission #565 (October 2026), §3.1, p.15, (19); Algorithm 1, step 2, p.26

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Parameters

namespace RSListDecodingCapacity.AllRates

/-!
# The interpolation space `𝒬` of (19)

Brakensiek–Chen–Putterman–Zhang–Zheng, STOC 2027 submission #565, §3.1, p.15, (19); Algorithm 1,
step 2, p.26.

The variables of `𝔽[X, Y₀, …, Y_d]` are indexed by `Option (Fin (d+1))`: `none` is `X`, `some j` is
`Y_j`. A monomial is an exponent vector `s : Option (Fin (d+1)) →₀ ℕ`.
-/

/-- The exponent of `Y_j` in the monomial `s`, for `0 ≤ j ≤ d` (and `0` for `j > d`). -/
def yExp {d : ℕ} (s : Option (Fin (d + 1)) →₀ ℕ) (j : ℕ) : ℕ :=
  if h : j < d + 1 then s (some ⟨j, h⟩) else 0

/-- The vector `c = (c₂, …, c_d)` of exponents of `Y₂, …, Y_d` in the monomial `s`
(Lean index `i` is `c_{i+2}`). -/
def cOfQ {d : ℕ} (s : Option (Fin (d + 1)) →₀ ℕ) : Fin (d - 1) → ℕ :=
  fun i => yExp s ((i : ℕ) + 2)

/-- The monomials `X^a Y₀^{b₀} Y₁^{b₁} Y^c` spanning `𝒬` in (19): `a, b₀ ≥ 0`, `c ∈ 𝓑`,
`0 ≤ b₁ ≤ m`, `b₀ + b₁ + |c| ≤ B` and `a + (k − 1)(b₀ + b₁ + |c|) < mA`. -/
def IsQMonomial (θ : ℝ) (d m A B k W : ℕ) (s : Option (Fin (d + 1)) →₀ ℕ) : Prop :=
  cOfQ s ∈ scriptB θ d m W ∧ yExp s 1 ≤ m ∧
    yExp s 0 + yExp s 1 + absC (cOfQ s) ≤ B ∧
    s none + (k - 1) * (yExp s 0 + yExp s 1 + absC (cOfQ s)) < m * A

/-- The span of the monomials of (19), for given numerical parameters `θ, d, m, A, B, k, W`. -/
noncomputable def Qspace (F : Type*) [CommRing F] (θ : ℝ) (d m A B k W : ℕ) :
    Submodule F (MvPolynomial (Option (Fin (d + 1))) F) :=
  MvPolynomial.restrictSupport F {s | IsQMonomial θ d m A B k W s}

/-- **The interpolation space `𝒬 ⊆ 𝔽[X, Y₀, …, Y_d]` of (19)** at the parameters of §3:
`d = ⌈ε^{−3/θ}⌉`, `A = ⌈εn⌉`, `m = d³`, `B = ⌈mA/(k − 1)⌉` ((11)–(12)) and `W` of (18). -/
noncomputable def sourceQ (F : Type*) [CommRing F] (ε θ : ℝ) (n k : ℕ) :
    Submodule F (MvPolynomial (Option (Fin (paramD ε θ + 1))) F) :=
  Qspace F θ (paramD ε θ) (paramM (paramD ε θ)) (paramA ε n)
    (paramB (paramM (paramD ε θ)) (paramA ε n) k) k
    (paramW θ (paramD ε θ) (paramM (paramD ε θ)))

end RSListDecodingCapacity.AllRates


