-- Prove2me | Definitions.Def_PFRelease_Supplement_potMech
-- name    : PFRelease_Supplement_potMech
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:44:12.161785+00:00
-- url     : https://prove2.me/theorems/60db082a-6679-4dd5-a8c2-8be1a3221360
-- title:
--   Edge records $x_e=\sqrt{w_e}(\chi_u-\chi_{u'})$, effective resistance, potential vectors $M_{\mathrm{pot}}$ and $\widehat R_{\mathrm{eff}}$
-- statement:
--   Let $V$ be a public finite vertex set. An edge $e=\{u,u'\}$ of weight $w_e\ge0$ is recorded as the vector
--   $$
--   x_e:=\sqrt{w_e}\,(\chi_u-\chi_{u'})\in\mathbb R^V,
--   $$
--   where $\chi_u$ is the standard basis vector of $u$; padding slots hold the ordinary zero record. For a dataset $s$ of edge records, $\mathbf L_s=\sum_{e\in s}x_ex_e^T$ is its Laplacian (null records contribute zero). The **effective resistance** with respect to a Laplacian $\mathbf L$ is
--   $$
--   R_{\mathrm{eff}}(u,u'):=(\chi_u-\chi_{u'})^T\mathbf L^\dagger(\chi_u-\chi_{u'}).
--   $$
--   The release mechanism draws $r$ independent **potential vectors** $M_{\mathrm{pot}}(s):=(Y_1,\dots,Y_r)$ with $Y_j\sim\mathcal N(0,\mathbf L_s^\dagger)$, which answer every pairwise query by
--   $$
--   \widehat R_{\mathrm{eff}}(u,u'):=\frac1r\sum_{j\in[r]}\big(Y_j(u)-Y_j(u')\big)^2 .
--   $$
--
--   Since $Y_j(u)-Y_j(u')$ has variance $R_{\mathrm{eff}}(u,u')$ when $u,u'$ are connected, the potentials estimate all resistances at once.
--
--   **Formalization Note** An edge slot is an ordered pair $(u,u')$, fixing the orientation of $\chi_u-\chi_{u'}$; every quantity is quadratic in the record, so the orientation is immaterial. $\mathbf L^\dagger$ is the pseudoinverse `pinv` (from the published Moore–Penrose pseudoinverse), $\mathbf L_s$ is `gram`, and $\mathcal N(0,A)$ is Mathlib's `multivariateGaussian 0 A`, defined for singular positive semidefinite $A$.
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), §5.4, eq. (4), p.20 (PDF p.22); §D.4, Setting, Score and release mechanism, p.50 (PDF p.52)

import Mathlib
import Definitions.Def_PFRelease_Supplement_phiLam

open MeasureTheory ProbabilityTheory Matrix

namespace PFRelease.Supplement

/-- The record `x_e := √w_e (χ_u − χ_{u′}) ∈ ℝ^V` of the edge `e = {u, u′}` of weight `w_e ≥ 0`
(Shenfeld, Tsfadia, Ligett, arXiv:2610.40654, held version sha256 e1d516b3…, §D.4, p.50 = PDF p.52;
§5.4, p.20). A padding slot (`none`) holds the ordinary zero record, which is not `⊥`.

**Formalization Note** An ordered pair `(u, u′)` fixes the orientation of `χ_u − χ_{u′}`; every score
and covariance below is quadratic in the record, so the orientation never matters. -/
noncomputable def edgeRec {V : Type*} [Fintype V] [DecidableEq V] (w : V → V → ℝ) :
    Option (V × V) → EuclideanSpace ℝ V
  | none => 0
  | some (u, u') => Real.sqrt (w u u') • (EuclideanSpace.single u 1 - EuclideanSpace.single u' 1)

/-- The effective resistance `R_eff(u, u′) := (χ_u − χ_{u′})ᵀ L† (χ_u − χ_{u′})` with respect to a
Laplacian `L` (§5.4, p.20 = PDF p.22; §D.4, p.50). -/
noncomputable def effRes {V : Type*} [Fintype V] [DecidableEq V] (L : Matrix V V ℝ) (u u' : V) : ℝ :=
  let χ : V → ℝ := Pi.single u 1 - Pi.single u' 1
  χ ⬝ᵥ (pinv L *ᵥ χ)

/-- The release mechanism `M_pot(s) := (Y₁, …, Y_r)` with independent `Y_j ∼ N(0, L_s†)` (eq. (4),
p.20 = PDF p.22), where `L_s = Σ_{e∈s} x_e x_eᵀ` (`gram`).

**Formalization Note** `N(0, A)` is Mathlib's `multivariateGaussian 0 A`, defined for singular positive
semidefinite `A` (the pushforward of a standard Gaussian by `A^{1/2}`). -/
noncomputable def potMech {V : Type*} [Fintype V] [DecidableEq V] (r : ℕ) {n : ℕ}
    (s : Fin n → Option (EuclideanSpace ℝ V)) : Measure (Fin r → EuclideanSpace ℝ V) :=
  Measure.pi fun _ : Fin r => multivariateGaussian 0 (pinv (gram (toList s)))

/-- The estimate `R̂_eff(u, u′) := r⁻¹ Σ_{j∈[r]} (Y_j(u) − Y_j(u′))²` (§D.4, p.50 = PDF p.52). -/
noncomputable def effResHat {V : Type*} {r : ℕ} (Y : Fin r → EuclideanSpace ℝ V) (u u' : V) : ℝ :=
  (r : ℝ)⁻¹ * ∑ j, (Y j u - Y j u') ^ 2

end PFRelease.Supplement


