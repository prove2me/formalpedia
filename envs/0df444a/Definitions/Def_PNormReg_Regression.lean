-- Prove2me | Definitions.Def_PNormReg_Regression
-- name    : PNormReg_Regression
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:38:55.009376+00:00
-- url     : https://prove2.me/theorems/ed895c92-7d84-4613-a889-7a48e9eea31e
-- title:
--   Generalized regression (11) and the residual problem (12)
-- statement:
--   Fix $p\in[2,\infty)$. Problem (11) is
--
--   $$\min_{Cx=\ell} f(x),\qquad f(x)=a^\top x+x^\top Qx+\|Nx-b\|_p^p,$$
--
--   with $N\in\mathbb R^{n\times d}$ of full column rank, $Q\in\mathbb R^{d\times d}$ positive semidefinite, $a\in\mathbb R^d$, $b\in\mathbb R^n$, $C\in\mathbb R^{m\times d}$, $m\le d$, and $Cx=\ell$ feasible. $C$ need not have full row rank, and $f^\star$ is the optimal value.
--
--   At a point $x$, the residual problem (12) is
--
--   $$\mathrm{res}^\star_p=\max_{C\Delta=0}\mathrm{res}_p(\Delta),\qquad \mathrm{res}_p(\Delta)=g^\top\Delta-\Delta^\top R\Delta-\|N\Delta\|_p^p,$$
--
--   where $g=(a+2Qx)/p+N^\top\mathrm{Diag}(|Nx-b|^{p-2})(Nx-b)$ and $R=2Q/p^2+2N^\top\mathrm{Diag}(|Nx-b|^{p-2})N$, with $|r_i|^0=1$ at $p=2$.
--
--   Iterative refinement reduces (11) to a sequence of residual problems, each solved to constant accuracy.
--
--   **Formalization Note** $f^\star$ and $\mathrm{res}^\star_p$ are the real `sInf` and `sSup`. Their attainment under the standing hypotheses is a clause of the milestone (13)–(14).
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), §3, eqs. (11)–(12), pp.18–19

import Mathlib
import Definitions.Def_PNormReg_Norms

open Matrix

namespace PNormReg

/-!
# Generalized regression (11) and the residual problem (12)

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*,
STOC 2027 submission (manuscript sha256 e335b2fa…), §3, eqs. (11)–(12), pp.18–19.

**Formalization Note.** `fStar` and `resStar` are computed from the data as `sInf` and `sSup`, so they
carry no extra binder. The real `sInf`/`sSup` have junk value `0` on an empty or unbounded set; under
`IsStanding` with `p ≥ 2` the feasible set is nonempty and both optima are attained, which is a clause
of `PNormReg.eq_13_14`. `m` may be `0` (no constraints), and `C` need not have full row rank.
-/

/-- The data `a, Q, N, b, C, ℓ` of problem (11), with `N ∈ ℝ^{n×d}` and `C ∈ ℝ^{m×d}`. -/
structure GenRegression (n d m : ℕ) where
  a : Fin d → ℝ
  Q : Matrix (Fin d) (Fin d) ℝ
  N : Matrix (Fin n) (Fin d) ℝ
  b : Fin n → ℝ
  C : Matrix (Fin m) (Fin d) ℝ
  ell : Fin m → ℝ

namespace GenRegression

variable {n d m : ℕ}

/-- `Cx = ℓ`. -/
def Feasible (G : GenRegression n d m) (x : Fin d → ℝ) : Prop := G.C *ᵥ x = G.ell

/-- The standing hypotheses of (11): `N` has full column rank, `Q` is positive semidefinite, `m ≤ d`,
and `Cx = ℓ` is feasible. -/
def IsStanding (G : GenRegression n d m) : Prop :=
  Function.Injective G.N.mulVec ∧ G.Q.PosSemidef ∧ m ≤ d ∧ ∃ x, G.Feasible x

/-- The objective `f(x) = a⊤x + x⊤Qx + ∥Nx − b∥_p^p` of (11). -/
noncomputable def obj (G : GenRegression n d m) (p : ℝ) (x : Fin d → ℝ) : ℝ :=
  G.a ⬝ᵥ x + x ⬝ᵥ (G.Q *ᵥ x) + lpPow p (G.N *ᵥ x - G.b)

/-- `f⋆ = min_{Cx=ℓ} f(x)`. -/
noncomputable def fStar (G : GenRegression n d m) (p : ℝ) : ℝ :=
  sInf (G.obj p '' {x | G.Feasible x})

/-- The weights `|Nx − b|^{p−2}`, with `|r_i|⁰ = 1` at `p = 2` (`Real.rpow`, as on p.19). -/
noncomputable def powerWeight (G : GenRegression n d m) (p : ℝ) (x : Fin d → ℝ) : Fin n → ℝ :=
  fun i => |(G.N *ᵥ x - G.b) i| ^ (p - 2)

/-- `g := (a + 2Qx)/p + N⊤Diag(|Nx − b|^{p−2})(Nx − b)` of (12). -/
noncomputable def grad (G : GenRegression n d m) (p : ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  (1 / p) • (G.a + (2 : ℝ) • (G.Q *ᵥ x)) +
    G.Nᵀ *ᵥ (fun i => G.powerWeight p x i * (G.N *ᵥ x - G.b) i)

/-- `R := 2Q/p² + 2N⊤Diag(|Nx − b|^{p−2})N` of (12). -/
noncomputable def hess (G : GenRegression n d m) (p : ℝ) (x : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (2 / p ^ 2) • G.Q + (2 : ℝ) • (G.Nᵀ * Matrix.diagonal (G.powerWeight p x) * G.N)

/-- `res_p(∆) := g⊤∆ − ∆⊤R∆ − ∥N∆∥_p^p` of (12), at the base point `x`. -/
noncomputable def res (G : GenRegression n d m) (p : ℝ) (x Δ : Fin d → ℝ) : ℝ :=
  G.grad p x ⬝ᵥ Δ - Δ ⬝ᵥ (G.hess p x *ᵥ Δ) - lpPow p (G.N *ᵥ Δ)

/-- `res⋆_p := max_{C∆=0} res_p(∆)` of (12). -/
noncomputable def resStar (G : GenRegression n d m) (p : ℝ) (x : Fin d → ℝ) : ℝ :=
  sSup (G.res p x '' {Δ | G.C *ᵥ Δ = 0})

end GenRegression

end PNormReg


