-- Prove2me | Definitions.Def_EffRobustLearn_Supplement_psi
-- name    : EffRobustLearn_Supplement_psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:16:41.19745+00:00
-- url     : https://prove2.me/theorems/3189e7b1-ce34-403b-815b-f5e1bb7c0ec9
-- title:
--   Monomial vector $x^{\otimes\ell}$, moment matrix $M_\ell$, normalized features $\psi_\ell$, $q_w$ and the projection onto $K$
-- statement:
--   Fix degree $\ell$ and a reference sample $S_{\mathrm{ref}}=(x_1,\dots,x_m)$ of points of $\mathbb R^d$.
--
--   1. $x^{\otimes\ell}\in\mathbb R^N$ is the vector of **all monomials** $\prod_i x_i^{e_i}$ of degree at most $\ell$ (not the homogeneous tensor power), indexed by exponent vectors $e$ with $\sum_ie_i\le\ell$; $N=\binom{d+\ell}{\ell}$.
--   2. $M_\ell=\frac1{|S_{\mathrm{ref}}|}\sum_{x\in S_{\mathrm{ref}}}x^{\otimes\ell}(x^{\otimes\ell})^\top$ is the empirical moment matrix.
--   3. $\psi_\ell(x)=M_\ell^{-1/2}x^{\otimes\ell}$, where $M_\ell^{-1/2}$ is the Moore–Penrose pseudoinverse of $M_\ell^{1/2}$ when $M_\ell$ is singular.
--   4. $q_w(x)=\langle w,\psi_\ell(x)\rangle$ for $w\in\mathbb R^N$ (Eq. (4.1)), the feasible polynomials are $Q=\{q_w:\|w\|_2\le2\}$ (Eq. (4.2)) and the coefficient set is $K=\{w:\|w\|_2\le2\}$ (Eq. (4.6)).
--   5. The Euclidean projection onto $K$ is $w$ itself if $\|w\|_2\le2$ and $2w/\|w\|_2$ otherwise.
--
--   These are the coordinates in which Algorithm 3 runs projected gradient ascent.
--
--   **Formalization Note** $M_\ell^{-1/2}$ is the continuous functional calculus of the symmetric matrix $M_\ell$ applied to $t\mapsto t^{-1/2}$ for $t>0$ and $0$ otherwise; for the positive semidefinite $M_\ell$ this is exactly the pseudoinverse of $M_\ell^{1/2}$. The Euclidean norm is written out (Mathlib's default norm on function types is the sup norm). The projection is given in its closed form, which is the unique minimizer of $\|u-w\|_2^2$ over $K$.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), §2 Notation and footnote 6, p.11 (PDF p.12); Eqs. (4.1), (4.2), footnote 8, pp.18–19 (PDF pp.19–20); Eq. (4.6), p.21 (PDF p.22)

import Mathlib

open Matrix

namespace EffRobustLearn

namespace Supplement

/-- Index set of the monomials in `d` variables of degree at most `ℓ`: exponent vectors `e` with
`∑ᵢ eᵢ ≤ ℓ`. Its cardinality is `N = C(d + ℓ, ℓ)` (§2, Notation, p.11). -/
abbrev MonoIdx (d ℓ : ℕ) := {e : Fin d → Fin (ℓ + 1) // ∑ i, (e i : ℕ) ≤ ℓ}

/-- The monomial vector `x^{⊗ℓ} ∈ ℝ^N` of Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), §2, p.11 and footnote 6: the vector of **all**
monomials `∏ᵢ xᵢ^{eᵢ}` of degree **at most** `ℓ` (not the homogeneous tensor power). -/
noncomputable def monoVec {d : ℕ} (ℓ : ℕ) (x : Fin d → ℝ) : MonoIdx d ℓ → ℝ :=
  fun e => ∏ i, x i ^ (e.1 i : ℕ)

/-- The empirical moment matrix `M_ℓ := (1/|Sref|) ∑_{x∈Sref} x^{⊗ℓ}(x^{⊗ℓ})ᵀ`, p.19 (PDF p.20). -/
noncomputable def momentMatrix {d m : ℕ} (ℓ : ℕ) (Sref : Fin m → Fin d → ℝ) :
    Matrix (MonoIdx d ℓ) (MonoIdx d ℓ) ℝ :=
  (1 / (m : ℝ)) • ∑ j, vecMulVec (monoVec ℓ (Sref j)) (monoVec ℓ (Sref j))

/-- The scalar function `t ↦ t^{-1/2}` for `t > 0` and `0` otherwise. Applied to the positive semidefinite
`M_ℓ` by the functional calculus it gives the Moore–Penrose pseudoinverse of `M_ℓ^{1/2}` (footnote 8). -/
noncomputable def pinvSqrt (t : ℝ) : ℝ := if 0 < t then 1 / Real.sqrt t else 0

/-- The normalized feature map `ψ_ℓ(x) := M_ℓ^{−1/2} x^{⊗ℓ}`, p.19 (PDF p.20), where `M_ℓ^{−1/2}` is the
Moore–Penrose pseudoinverse of `M_ℓ^{1/2}` when `M_ℓ` is singular (footnote 8).

**Formalization Note.** `M_ℓ^{−1/2}` is `cfc pinvSqrt M_ℓ`, the continuous functional calculus of the
symmetric matrix `M_ℓ`: `U diag(pinvSqrt λᵢ) Uᵀ` for an orthonormal eigenbasis `U`, which is the pseudoinverse of
`M_ℓ^{1/2} = U diag(√λᵢ) Uᵀ` because `M_ℓ` is positive semidefinite. The verification file proves `M_ℓ`
self-adjoint, so the calculus applies (and `pinvSqrt` is continuous on the finite spectrum). -/
noncomputable def psi {d m : ℕ} (ℓ : ℕ) (Sref : Fin m → Fin d → ℝ) (x : Fin d → ℝ) :
    MonoIdx d ℓ → ℝ :=
  (cfc pinvSqrt (momentMatrix ℓ Sref)) *ᵥ monoVec ℓ x

/-- The polynomial `q_w(x) := ⟨w, ψ_ℓ(x)⟩` of Eq. (4.1), p.18. -/
noncomputable def qw {d m : ℕ} (ℓ : ℕ) (Sref : Fin m → Fin d → ℝ) (w : MonoIdx d ℓ → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  ∑ k, w k * psi ℓ Sref x k

/-- The Euclidean norm `‖w‖₂ = (∑ₖ wₖ²)^{1/2}` (the sup norm Mathlib puts on function types is not used). -/
noncomputable def l2norm {ι : Type*} [Fintype ι] (w : ι → ℝ) : ℝ := Real.sqrt (∑ k, w k ^ 2)

/-- The Euclidean projection onto `K = {w : ‖w‖₂ ≤ 2}` of Eq. (4.6), p.21 (PDF p.22), in its closed form:
`w` itself if `‖w‖₂ ≤ 2`, and `(2/‖w‖₂) w` otherwise. This is the unique `argmin_{u∈K} ‖u − w‖₂²`. -/
noncomputable def projK {ι : Type*} [Fintype ι] (w : ι → ℝ) : ι → ℝ :=
  if l2norm w ≤ 2 then w else (2 / l2norm w) • w

end Supplement

end EffRobustLearn


