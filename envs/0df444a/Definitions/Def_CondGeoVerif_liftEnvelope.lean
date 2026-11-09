-- Prove2me | Definitions.Def_CondGeoVerif_liftEnvelope
-- name    : CondGeoVerif_liftEnvelope
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:25:36.693173+00:00
-- url     : https://prove2.me/theorems/23609d57-afc3-45c2-98e2-c33f09d6f6c5
-- title:
--   Revealed coordinates, residual statistics $A_{C,R}$, $V_{C,R}$ and the lifted envelope $L_{C,R}$
-- statement:
--   Let $P\in\mathbb R^{d\times m}$ be an orthonormal basis whose first $k$ columns are a candidate frame $V$, and write
--   $$U=P^\top X\in\mathbb R^m,\quad T=(U_1,\dots,U_k),\quad Z=(I-PP^\top)X,\quad E_V=\mathbf 1\{Y\ne f(T)\}.$$
--   For $C\in\mathbb R^{m\times k}$, $R\in\mathbb R^{r\times k}$ and rules $f$ (anchor) and $g$ (competitor), the **conditional disagreement** is $D_{C,R}(u,z)=\mathbf 1\{g(C^\top u+R^\top z)\ne f(t)\}$, $t=(u_1,\dots,u_k)$. For a scalar dual $\alpha(u)$ and a vector dual $\gamma(u)\in\mathbb R^r$,
--   $$A_{C,R}=\mathbb E[\alpha(U)(E_V-\eta)],\qquad V_{C,R}=\mathbb E[Z\gamma(U)^\top E_V]\in\mathbb R^{d\times r},$$
--   the matrix observation is $W=Z\gamma(U)^\top E_V$, and the **lifted envelope** is
--   $$L_{C,R}=\mathbb E_U\big[2M_{1,\eta}(D_{C,R}(U,\cdot))-\mathbb E_GD_{C,R}(U,G)\big],\qquad U\sim N(0,I_m),\ G\sim N(0,I_r).$$
--   The fixed-rule objects of §A.4 are the case $g=f$; the family objects $A_{g,C,R}$, $V_{g,C,R}$ of §A.9 the general case.
--
--   These are the certificate statistics that the square-root protocol estimates.
--
--   **Formalization Note** Expectations under the law of $(X,Y)$ are Bochner integrals; matrix expectations are entrywise. The outer expectation in $L_{C,R}$ has a bounded integrand, measurable for Borel rules.
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), §A.4, p.16 (PDF p.19); §A.5, p.17 (PDF p.20); §A.9, p.22 (PDF p.25)

import Mathlib
import Definitions.Def_CondGeoVerif_Mprog

set_option autoImplicit false

namespace CondGeoVerif

open MeasureTheory
open scoped Matrix

/-- The revealed coordinates `U = Pᵀ X ∈ ℝᵐ` of a feature vector for a proposed basis
`P ∈ ℝ^{d×m}` (Chen, *The Conditional Geometry of Statistical Verification*, manuscript,
October 2026, sha256 07a66d18…, §A.4, p.16 = PDF p.19). -/
noncomputable def revealed {d m : ℕ} (P : Matrix (Fin d) (Fin m) ℝ) (x : Vec d) : Vec m :=
  matVec Pᵀ x

/-- The anchor coordinates `T = (U₁, …, U_k)` of `u ∈ ℝᵐ` (§A.4, p.16), i.e. `[I_k; 0]ᵀ u`; for
`k ≤ m` these are the first `k` coordinates. -/
noncomputable def anchorCoords {m : ℕ} (k : ℕ) (u : Vec m) : Vec k :=
  matVec (coordFrame m k)ᵀ u

/-- The residual `Z = (I − PPᵀ) X ∈ ℝᵈ` (§A.4, p.16). -/
noncomputable def resid {d m : ℕ} (P : Matrix (Fin d) (Fin m) ℝ) (x : Vec d) : Vec d :=
  x - matVec P (matVec Pᵀ x)

/-- The conditional disagreement of a coefficient pair (§A.4, p.16; family form §A.9, p.22):
for an anchor rule `f`, a competitor rule `g`, `C ∈ ℝ^{m×k}` and `R ∈ ℝ^{r×k}`,
`D_{C,R}(u, z) = 1{g(Cᵀu + Rᵀz) ≠ f(t)}`, `t = (u₁, …, u_k)`. The fixed-rule disagreement of
§A.4 is the case `g = f`. -/
noncomputable def condDisagree {k m r : ℕ} (f g : Vec k → Bool) (C : Matrix (Fin m) (Fin k) ℝ)
    (R : Matrix (Fin r) (Fin k) ℝ) (u : Vec m) (z : Vec r) : Bool :=
  decide (g (matVec Cᵀ u + matVec Rᵀ z) ≠ f (anchorCoords k u))

/-- The error indicator `E_V = 1{Y ≠ f(T)}` of the candidate `h_V(X) = f(VᵀX) = f(T)`, where `V`
is the first `k` columns of `P` (§A.4, p.16). -/
noncomputable def errInd {d m k : ℕ} (f : Vec k → Bool) (P : Matrix (Fin d) (Fin m) ℝ)
    (p : Vec d × Bool) : ℝ :=
  ind (decide (p.2 ≠ f (anchorCoords k (revealed P p.1))))

/-- The scalar residual statistic `A_{C,R} = E[α_{C,R}(U)(E_V − η)]` under a law `μ` of `(X, Y)`
(§A.4, p.16; family form `A_{g,C,R}`, §A.9, p.22), for a scalar dual `α : ℝᵐ → ℝ`. -/
noncomputable def scalarStat {d m k : ℕ} (μ : Measure (Vec d × Bool)) (η : ℝ) (f : Vec k → Bool)
    (P : Matrix (Fin d) (Fin m) ℝ) (α : Vec m → ℝ) : ℝ :=
  ∫ p, α (revealed P p.1) * (errInd f P p - η) ∂μ

/-- The matrix observation `W = Z γ_{C,R}(U)ᵀ E_V ∈ ℝ^{d×r}` (§A.5, p.17), for a vector dual
`γ : ℝᵐ → ℝʳ`. -/
noncomputable def matObs {d m k r : ℕ} (f : Vec k → Bool) (P : Matrix (Fin d) (Fin m) ℝ)
    (γ : Vec m → Vec r) (p : Vec d × Bool) : Matrix (Fin d) (Fin r) ℝ :=
  fun a b => resid P p.1 a * γ (revealed P p.1) b * errInd f P p

/-- The residual matrix statistic `V_{C,R} = E[Z γ_{C,R}(U)ᵀ E_V] ∈ ℝ^{d×r}` under a law `μ`
(§A.4, p.16; family form `V_{g,C,R}`, §A.9, p.22), the entrywise expectation of `matObs`. -/
noncomputable def vecStat {d m k r : ℕ} (μ : Measure (Vec d × Bool)) (f : Vec k → Bool)
    (P : Matrix (Fin d) (Fin m) ℝ) (γ : Vec m → Vec r) : Matrix (Fin d) (Fin r) ℝ :=
  fun a b => ∫ p, matObs f P γ p a b ∂μ

/-- **The lifted envelope** `L_{C,R} = E_U[2M_{1,η}(D_{C,R}(U, ·)) − E_G D_{C,R}(U, G)]`, with
`U ∼ N(0, I_m)` and `G ∼ N(0, I_r)` independent (Chen, Oct. 2026, §A.4, p.16 = PDF p.19). The
fixed-rule envelope of §A.4 is `liftEnvelope η f f C R`.

**Formalization Note** As for `Jprog`, the outer expectation is a Bochner integral of a bounded
integrand (`|·| ≤ 2`), measurable for Borel rules by the measurability argument of Lemma B.2. For
`r = 0` the program value is `η D` (the paper's convention, built into `Mprog`). -/
noncomputable def liftEnvelope {k m r : ℕ} (η : ℝ) (f g : Vec k → Bool)
    (C : Matrix (Fin m) (Fin k) ℝ) (R : Matrix (Fin r) (Fin k) ℝ) : ℝ :=
  ∫ u, (2 * Mprog 1 η (condDisagree f g C R u) -
    (gauss r {z | condDisagree f g C R u z = true}).toReal) ∂(gauss m)

end CondGeoVerif


