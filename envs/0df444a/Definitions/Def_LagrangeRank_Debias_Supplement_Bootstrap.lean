-- Prove2me | Definitions.Def_LagrangeRank_Debias_Supplement_Bootstrap
-- name    : LagrangeRank_Debias_Supplement_Bootstrap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:46:22.118802+00:00
-- url     : https://prove2.me/theorems/51494e6b-1db9-4bb8-8e44-4d854ec5d3e7
-- title:
--   Gaussian multiplier statistic, conditional upper-tail quantile and calibration error
-- statement:
--   Let $\mathcal E$ denote the observed comparison graph and $E$ a fixed inference pair set, separate from $\mathcal E$. Define
--   $$T=\max_{(i,j)\in E}\sqrt{npL}\bigl(\hat\theta_i^d-\theta_i-\hat\theta_j^d+\theta_j\bigr).$$
--   For repetition $\ell$, use the score contribution in (3.12), with coefficient $-\sqrt{np}$, Bernoulli residual at the true score, and contrast of rows of $\Theta^*_{11}$. For the bootstrap replace the true score and inverse block by $\hat\theta$ and $\hat\Theta_{11}$. With shared independent $z_\ell\sim N(0,1)$,
--   $$W=\max_{(i,j)\in E}\frac1{\sqrt L}\sum_{\ell=1}^L\hat x_{ij}^{(\ell)}z_\ell,\qquad c_W(\alpha,E)=\inf\{q:P_z(W>q\mid\text{data})\le\alpha\}.$$
--   The finite maximum defaults to zero only on the empty index set. Calibration theorems explicitly exclude empty sets and all zero contrasts. For $0<\alpha<1$ the Gaussian tail quantile set is nonempty and bounded below, so the real infimum has its usual meaning, including $c_W=0$ for the degenerate zero statistic. `tailError` is the supremum over $0<\alpha<1$ of the absolute unconditional rejection-probability error; its values lie in $[0,1]$. No bootstrap approximation is assumed in these definitions. The star set consists of $(i,j)$ with $j\ne i$.
-- source:
--   Liu, Fang, Lu, Lagrangian Inference for Ranking Problems, arXiv:2110.00151v1, p. 22, (3.11)–(3.14)

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Supplement_BTL

namespace LagrangeRank.Debias.Supplement

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

/-- A real finite maximum, with zero on the empty family. Empty sets are never used to claim calibration. -/
noncomputable def finiteMax {ι : Type*} [Fintype ι] (E : Finset ι) (v : ι → ℝ) : ℝ :=
  if h : E.Nonempty then E.sup' h v else 0

/-- x^(ℓ) in (3.12); substituting θ̂ and Θ̂ gives the coefficients in W. -/
noncomputable def multiplierCoeff {n L : ℕ} (p : ℝ) (s : Data n L) (θ : Vec n)
    (A : Matrix (Fin n) (Fin n) ℝ) (l : Fin L) (ij : Fin n × Fin n) : ℝ :=
  -Real.sqrt ((n : ℝ) * p) * ∑ e : Edge n, if s.1 e then
    (-(if s.2 (l,e) then (1 : ℝ) else 0) + (winProb θ e : ℝ)) *
      ((A ij.1 e.val.2 - A ij.2 e.val.2) - (A ij.1 e.val.1 - A ij.2 e.val.1)) else 0
noncomputable def Tstat {n L : ℕ} (p c : ℝ) (θ : Vec n)
    (E : Finset (Fin n × Fin n)) (s : Data n L) : ℝ :=
  finiteMax E (fun ij => Real.sqrt ((n : ℝ) * p * L) *
    (thetaD p c s ij.1 - θ ij.1 - thetaD p c s ij.2 + θ ij.2))
noncomputable def Wstat {n L : ℕ} (p c : ℝ) (E : Finset (Fin n × Fin n))
    (s : Data n L) (z : Fin L → ℝ) : ℝ :=
  finiteMax E (fun ij => (∑ l, multiplierCoeff p s (thetaHat p c s)
    (inverseAt s (thetaHat p c s)).toBlocks₁₁ l ij * z l) / Real.sqrt L)
noncomputable def multiplierLaw (L : ℕ) : Measure (Fin L → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)
/-- Upper-tail conditional quantile (3.14), conditional on all the observed data. -/
noncomputable def cW {n L : ℕ} (p c α : ℝ) (E : Finset (Fin n × Fin n))
    (s : Data n L) : ℝ :=
  sInf {q : ℝ | (multiplierLaw L {z | Wstat p c E s z > q}).toReal ≤ α}
noncomputable def tailError {n L : ℕ} (p : unitInterval) (c : ℝ) (θ : Vec n)
    (E : Finset (Fin n × Fin n)) : ℝ :=
  ⨆ α ∈ Set.Ioo (0 : ℝ) 1,
    |(dataLaw L p θ {s | Tstat p c θ E s > cW p c α E s}).toReal - α|

/-- All nonzero star contrasts, with the item in the first coordinate. -/
noncomputable def star (n : ℕ) (i : Fin n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun ij => ij.1 = i ∧ ij.2 ≠ i)

end LagrangeRank.Debias.Supplement


