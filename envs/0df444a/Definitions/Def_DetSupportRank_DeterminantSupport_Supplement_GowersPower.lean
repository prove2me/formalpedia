-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_GowersPower
-- name    : DetSupportRank_DeterminantSupport_Supplement_GowersPower
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:07:54.415128+00:00
-- url     : https://prove2.me/theorems/aca76296-8bf7-48e0-bf62-3eae88732fcc
-- title:
--   Normalized Gowers cube average and its real power quantity
-- statement:
--   For a complex function $f$ on a finite additive commutative group $A$, define the normalized cube average
--   $$C_d(f)=\frac{1}{|A|^{d+1}}\sum_{x\in A}\sum_{h_1,\ldots,h_d\in A}\prod_{\omega\in\{0,1\}^d}\mathcal C^{|\omega|}f\left(x+\sum_i\omega_i h_i\right),$$
--   where $\mathcal C$ is complex conjugation. The real quantity used in the statements is $\operatorname{Re}C_d(f)$, precisely $\|f\|_{U^d}^{2^d}$ on the source domain $d\ge3$. It is defined by the full cube average, independently of any bias formula or desired bound. The complex average is retained for subsequent identities. All directions and the base point range independently and uniformly over $A$.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), §4.3, definition of Gowers norm, p. 15 (PDF p. 15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Mathlib

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport.Supplement

/-- The normalized complex cube average, p.15, for a general finite additive group.
The d directions and base point are independent and uniform. -/
def gowersCubeAverage {A : Type*} [AddCommGroup A] [Fintype A]
    (d : ℕ) (f : A → ℂ) : ℂ := by
  classical
  exact (∑ x : A, ∑ h : Fin d → A, ∏ ω : Fin d → Bool,
    if Even (Finset.univ.filter (fun i => ω i = true)).card then
      f (x + ∑ i, if ω i then h i else 0)
    else star (f (x + ∑ i, if ω i then h i else 0))) /
      (Fintype.card A : ℂ) ^ (d + 1)

/-- Exactly ‖f‖_{U^d}^{2^d} on the source domain, represented by the real cube average.
No replacement by bias, absolute value, or a desired lower bound is made. -/
def gowersPower {A : Type*} [AddCommGroup A] [Fintype A]
    (d : ℕ) (f : A → ℂ) : ℝ := (gowersCubeAverage d f).re
end DetSupportRank.DeterminantSupport.Supplement


