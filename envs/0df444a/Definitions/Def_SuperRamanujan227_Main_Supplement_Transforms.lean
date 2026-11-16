-- Prove2me | Definitions.Def_SuperRamanujan227_Main_Supplement_Transforms
-- name    : SuperRamanujan227_Main_Supplement_Transforms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:42:08.455201+00:00
-- url     : https://prove2.me/theorems/dd2c4ea4-0f0c-462b-9f9e-14ce07f917c1
-- title:
--   Empirical-root Cauchy transform and its right inverse
-- statement:
--   Let $p$ be a nonzero real-rooted polynomial of degree $m\ge1$, and list its roots with multiplicity as $\alpha_1\ge\cdots\ge\alpha_m$. For $x>\alpha_1$ and $y>0$, define
--
--   $$
--   G_p(x)=\frac1m\sum_{j=1}^m\frac1{x-\alpha_j},\qquad K_p(y)=\text{the unique }x>\alpha_1\text{ with }G_p(x)=y.
--   $$
--
--   The total inverse function returns zero when that unique right inverse does not exist. No desired estimate is imposed on the inverse. For positive even $n$, the matching characteristic polynomial is $(x-1)^{n/2}(x+1)^{n/2}$ and its reduction $p_M$ deletes one factor $x-1$. The $d$-fold convolution uses the published additive finite free convolution in degree $n-1$, starting with its neutral polynomial $x^{n-1}$. Finally $y_0=\sqrt{d-1}/(d-2)$ and $\eta=4(d-2)\sqrt{d-1}/(d^2(n-1))$. These definitions supply exactly the inherited data of Claims 3.2 and 3.3. Outside their stated domains the finite-sum and truncated-power expressions merely totalize the definitions.
-- source:
--   Gil Cohen, Gal Maor, STOC 2027 submission #227 (October 2026), pp. 9–12, Eqs. (5), (8), (11), (15), and §3

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Spectra
import Definitions.Def_SuperRamanujan227_Main_FiniteFreeConvolution

namespace SuperRamanujan227.Main.Supplement

/-- Normalized Cauchy transform of the empirical root distribution, roots with multiplicity.
Intended domain: nonzero real-rooted polynomial of positive degree and x above its top root.
On other inputs this is the displayed total finite sum, with Lean's inverse-zero convention. -/
noncomputable def cauchy (p : Polynomial ℝ) (x : ℝ) : ℝ :=
  (p.natDegree : ℝ)⁻¹ * (p.roots.map (fun a => (x - a)⁻¹)).sum

/-- The actual unique right inverse. Zero is only a fallback where the inverse does not
exist uniquely (outside the positive-y, positive-degree real-rooted domain). -/
noncomputable def inverseCauchy (p : Polynomial ℝ) (y : ℝ) : ℝ := by
  classical
  exact if h : ∃! x : ℝ, kthLargestRoot p 1 < x ∧ cauchy p x = y then
    Classical.choose h.exists else 0

/-- Characteristic polynomial of any perfect matching on n vertices, for positive even n. -/
noncomputable def matchingChar (n : ℕ) : Polynomial ℝ :=
  (Polynomial.X - 1) ^ (n / 2) * (Polynomial.X + 1) ^ (n / 2)

/-- Delete exactly one occurrence of the root +1. Intended domain: even n ≥ 2. -/
noncomputable def reducedMatching (n : ℕ) : Polynomial ℝ :=
  (Polynomial.X - 1) ^ (n / 2 - 1) * (Polynomial.X + 1) ^ (n / 2)

/-- d-fold finite free additive convolution in degree n-1; X^(n-1) is its neutral element. -/
noncomputable def matchingConvolution (n d : ℕ) : Polynomial ℝ :=
  (fun p => ffAdd (n - 1) p (reducedMatching n))^[d] (Polynomial.X ^ (n - 1))

/-- The optimizing positive transform argument of Eq. (11), for d ≥ 3. -/
noncomputable def yZero (d : ℕ) : ℝ := Real.sqrt ((d : ℝ) - 1) / ((d : ℝ) - 2)

/-- Exact radicand correction of Eq. (15), not an assumed bound or inverse formula. -/
noncomputable def eta (n d : ℕ) : ℝ :=
  4 * ((d : ℝ) - 2) * Real.sqrt ((d : ℝ) - 1) / ((d : ℝ)^2 * ((n : ℝ) - 1))

end SuperRamanujan227.Main.Supplement


