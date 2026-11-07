-- Prove2me | Definitions.Def_EllipsoidFitting_Fpos
-- name    : EllipsoidFitting_Fpos
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:12.454495+00:00
-- url     : https://prove2.me/theorems/eeebb86f-b084-4369-b2f9-c3369aa0d3fa
-- title:
--   The function $F(x)=\max(2x,0)$, the polynomials $P_j$, $C_F$, $b_j$ and the higher-order part
-- statement:
--   1. $F(x)=\max(2x,0)$.
--   2. $P_j(x)=U_j(x/2)$, $U_j$ the $j$-th Chebyshev polynomial of the second kind.
--   3. $C_F=\mathbb E_{x\sim\mu_{\mathrm{sc}}}[F(x)]$ and $b_j=\mathbb E_{x\sim\mu_{\mathrm{sc}}}[F(x)P_j(x)]$.
--   4. For a normalizer $c$ and a symmetric matrix $X$, the higher-order part
--   $$
--   G_c(X)=F(X)-c\,I-X,
--   $$
--   where $F(X)$ is the spectral map ($X=\sum_k\lambda_ku_ku_k^\top\mapsto\sum_kF(\lambda_k)u_ku_k^\top$). For $c=C_F$ this is the paper's $\sum_{j\ge2}b_jP_j(X)$.
--
--   **Formalization Note** $F(X)$ is Mathlib's continuous functional calculus `cfc Fpos X`. The series $\sum_{j\ge2}b_jP_j(X)$ is not used as a matrix series: it does not converge absolutely on $[-2,2]$ and diverges off it, while $F-C_F-x$ is the function it represents in $L^2(\mu_{\mathrm{sc}})$. The normalizer $c$ is a parameter; the paper's is $c=C_F$.
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), Definition 2.1, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_EllipsoidFitting_muSC

set_option autoImplicit false

namespace EllipsoidFitting

open MeasureTheory Polynomial

/-- **The function `F`, the polynomials `P_j`, the constants `C_F`, `b_j` and the higher-order
part.** de la Cerda, Potechin, Tulsiani, Xu, *Sharp Phase Transition for Ellipsoid Fitting*,
arXiv:2608.12415 (version of Nov 3, 2026), Definition 2.1, p.7: "F(x) = max(2x, 0)"; "Let Pj(x)
:= Uj(x/2), where Uj is the j-th Chebyshev polynomial of the second kind"; "CF = Ex∼µsc[F(x)]";
"bj := Ex∼µsc[F(x)Pj(x)]".

`Fpos x = max(2x, 0)`. -/
noncomputable def Fpos (x : ℝ) : ℝ := max (2 * x) 0

/-- `chebP j` is the polynomial `P_j(x) = U_j(x/2)`, `U_j` the Chebyshev polynomial of the second
kind (Mathlib's `Polynomial.Chebyshev.U ℝ j`). -/
noncomputable def chebP (j : ℕ) : ℝ[X] :=
  (Chebyshev.U ℝ (j : ℤ)).comp (C (1 / 2 : ℝ) * X)

/-- `CF` is `C_F = E_{x∼µsc}[F(x)]`. -/
noncomputable def CF : ℝ := ∫ x, Fpos x ∂muSC

/-- `bcoef j` is `b_j = E_{x∼µsc}[F(x) P_j(x)]` (the paper uses it for `j ≥ 2`; `b_0 = C_F`). -/
noncomputable def bcoef (j : ℕ) : ℝ := ∫ x, Fpos x * (chebP j).eval x ∂muSC

/-- `Ghigh c X` is the spectral higher-order part `F(X) − c·I − X`. With `c = C_F` this is the
paper's `∑_{j≥2} b_j P_j(X)`, the remainder of the expansion `F = C_F + x + ∑_{j≥2} b_j P_j`
applied to a symmetric matrix `X`.

**Formalization Note** `F(X)` is `cfc Fpos X`, Mathlib's continuous functional calculus
(the spectral map `X = ∑ λ u uᵀ ↦ ∑ F(λ) u uᵀ` for symmetric `X`; `0` for a non-self-adjoint
`X`). The series `∑_{j≥2} b_j P_j(X)` is not used as a matrix series: it is not absolutely
convergent on `[−2, 2]` and diverges off it; the remainder `F(X) − C_F I − X` is the function the
series represents in `L²(µsc)`. The constant `c` is a parameter so that the iteration identities
can be stated for any nonzero normalizer; the paper's choice is `c = C_F`. -/
noncomputable def Ghigh {d : ℕ} (c : ℝ) (X : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  cfc Fpos X - c • (1 : Matrix (Fin d) (Fin d) ℝ) - X

end EllipsoidFitting


