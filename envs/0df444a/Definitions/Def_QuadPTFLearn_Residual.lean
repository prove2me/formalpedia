-- Prove2me | Definitions.Def_QuadPTFLearn_Residual
-- name    : QuadPTFLearn_Residual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:51.952532+00:00
-- url     : https://prove2.me/theorems/24d7240a-562e-4a57-89b5-d2e38428d6c8
-- title:
--   Residual coefficient directions $u=(b,L,A)$, $N_u$, $d_uF$ and $T_up$ (Section 9)
-- statement:
--   The coefficient space of Section 9.
--
--   Fix a subspace $V$, $z=\mathrm{proj}_Vx$, $w=\mathrm{proj}_{V^\perp}x$. A residual coefficient direction is $u=(b,L,A)$ with $b\in V^\perp$, $L:V^\perp\to V$ linear and $A$ symmetric on $V^\perp$. Define
--
--   1. $N_u(z,w)=(b+L^\top z)^\top w+w^\top Aw-\mathrm{tr}(A)$;
--   2. $\langle u,u'\rangle=b^\top b'+\langle L,L'\rangle_F+2\langle A,A'\rangle_F$, so that $u$ is a unit direction when $\|b\|_2^2+\|L\|_F^2+2\|A\|_F^2=1$;
--   3. for a $C^2$ function $F$, $d_uF=(b+L^\top z)^\top\nabla_wF+\mathrm{tr}(A\nabla_w^2F)$;
--   4. for a polynomial $p$, $T_up=p\,N_u(z,w)-(b+L^\top z+2Aw)^\top\nabla_wp+\mathrm{tr}(A\nabla_w^2p)$.
--
--   $d_u$ replaces the directional derivative of Section 5 when directions are polynomials $N_u$ rather than vectors.
--
--   **Formalization Note** $(b,L,A)$ are stored as a vector and two $d\times d$ matrices, constrained so that $L$ and $A$ vanish on $V$ and map $V^\perp$ into $V$ and $V^\perp$; with this representation the trace and Frobenius products are the intrinsic ones, and $d_uF$, $T_up$ may be written with the full gradient and Hessian.
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), §9 coefficient space; d_u f; Lemmas 9.4, 9.5, p.82 (PDF p.84); p.88 (PDF p.90); p.89 (PDF p.91); p.90 (PDF p.92)

import Mathlib
import Definitions.Def_QuadPTFLearn_Regularity

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-!
# Residual coefficient directions, `N_u`, `d_v F` and `T_v p` (Section 9)

I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
§9, p.82 (PDF p.84): `u = (b, L, A)` and the space `S`; p.88 (PDF p.90): `d_u f`; Lemma 9.4,
p.89, with the unit normalization and inner product of its proof; Lemma 9.5, p.90 (PDF p.92).

**Formalization Note.**
* A residual coefficient direction `u = (b, L, A)` for a subspace `V` (with `z = proj_V x`,
  `w = proj_{V⊥} x`) is stored with `b ∈ ℝᵈ`, `L, A ∈ ℝ^{d×d}`, constrained so that the
  representation is the intrinsic one: `b ∈ V⊥`; `L` maps `V⊥` into `V` and vanishes on `V`
  (`L y = proj_V (L proj_{V⊥} y)`); `A` is symmetric, maps `V⊥` into `V⊥` and vanishes on `V`.
  Then `zᵀ L w` is the mixed term of p.82 (`L : ℝ^m → ℝ^n` there, `(Lᵀ z)ᵀ w = zᵀ L w`), and
  `tr(A)` is the trace of `A` on `V⊥`.
* `N_u(z, w) = (b + Lᵀz)ᵀ w + wᵀ A w − tr(A)`.
* `⟨u, u′⟩ = bᵀb′ + ⟨L, L′⟩_F + 2⟨A, A′⟩_F`, and `u` is a unit direction when `⟨u, u⟩ = 1`
  (p.89, proof of Lemma 9.4). For constrained representations these equal the intrinsic
  Frobenius quantities.
* `d_u F = (b + Lᵀz)ᵀ ∇_w F + tr(A ∇²_w F)`. Since `b + Lᵀz ∈ V⊥` and `A` is supported on
  `V⊥`, this equals `(b + Lᵀz) · ∇F + Σ_{ij} A_{ij} ∂_i∂_j F` with the full gradient and Hessian,
  which is how it is written here.
* `T_u p = p N_u − (b + Lᵀz + 2Aw)ᵀ ∇_w p + tr(A ∇²_w p)` for a polynomial `p`, with the same
  remark about full derivatives.
-/

/-- A residual coefficient direction `u = (b, L, A)` (unconstrained data). -/
structure ResDir (d : ℕ) where
  b : Pt d
  L : Matrix (Fin d) (Fin d) ℝ
  A : Matrix (Fin d) (Fin d) ℝ

/-- Matrix action on `ℝᵈ`. -/
noncomputable def matApp {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (y : Pt d) : Pt d :=
  Matrix.toEuclideanLin M y

/-- The constraints that make `(b, L, A)` an element of the coefficient space `S` for `V`. -/
def IsResDir {d : ℕ} (V : Submodule ℝ (Pt d)) (u : ResDir d) : Prop :=
  u.b ∈ Vᗮ ∧ (∀ y, matApp u.L y = projV V (matApp u.L (projV Vᗮ y))) ∧
    u.A.IsSymm ∧ (∀ y, matApp u.A y = projV Vᗮ (matApp u.A (projV Vᗮ y)))

/-- `⟨u, u′⟩ = bᵀb′ + ⟨L, L′⟩_F + 2⟨A, A′⟩_F`. -/
noncomputable def resInner {d : ℕ} (u u' : ResDir d) : ℝ :=
  ⟪u.b, u'.b⟫ + ∑ i, ∑ j, u.L i j * u'.L i j + 2 * ∑ i, ∑ j, u.A i j * u'.A i j

/-- `N_u(z, w) = (b + Lᵀz)ᵀ w + wᵀ A w − tr(A)`, as a function of `x = z + w`. -/
noncomputable def resPoly {d : ℕ} (V : Submodule ℝ (Pt d)) (u : ResDir d) (x : Pt d) : ℝ :=
  ⟪u.b + matApp u.L.transpose (projV V x), projV Vᗮ x⟫ + ⟪projV Vᗮ x, matApp u.A (projV Vᗮ x)⟫ -
    Matrix.trace u.A

/-- The `(i, j)` entry of the Hessian of `F : ℝᵈ → ℝ` at `x`. -/
noncomputable def hessEntry {d : ℕ} (F : Pt d → ℝ) (x : Pt d) (i j : Fin d) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ F y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)

/-- `d_u F = (b + Lᵀz)ᵀ ∇_w F + tr(A ∇²_w F)`. -/
noncomputable def dRes {d : ℕ} (V : Submodule ℝ (Pt d)) (u : ResDir d) (F : Pt d → ℝ)
    (x : Pt d) : ℝ :=
  ⟪u.b + matApp u.L.transpose (projV V x), gradient F x⟫ + ∑ i, ∑ j, u.A i j * hessEntry F x j i

/-- The gradient of a polynomial at `x`. -/
noncomputable def gradPoly {d : ℕ} (p : Poly d) (x : Pt d) : Pt d :=
  WithLp.toLp 2 (fun i => peval (MvPolynomial.pderiv i p) x)

/-- `T_u p = p N_u − (b + Lᵀz + 2Aw)ᵀ ∇_w p + tr(A ∇²_w p)`. -/
noncomputable def resAdj {d : ℕ} (V : Submodule ℝ (Pt d)) (u : ResDir d) (p : Poly d)
    (x : Pt d) : ℝ :=
  peval p x * resPoly V u x -
    ⟪u.b + matApp u.L.transpose (projV V x) + (2 : ℝ) • matApp u.A (projV Vᗮ x), gradPoly p x⟫ +
    ∑ i, ∑ j, u.A i j * peval (MvPolynomial.pderiv j (MvPolynomial.pderiv i p)) x

end QuadPTFLearn


