-- Prove2me | Definitions.Def_FracRiccati_Radius_Supplement_DoubleSeries
-- name    : FracRiccati_Radius_Supplement_DoubleSeries
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:53:33.658601+00:00
-- url     : https://prove2.me/theorems/dc2b7926-7a74-44ed-ab4e-d1c26decd834
-- title:
--   (6.36)–(6.38), (C.63) — double coefficients, valuations and normal convergence
-- statement:
--   For complex $\lambda,\mu,\nu,u,v$, the double coefficient array has $a_{0,\ell}=0$, $a_{1,0}=\nu/\Gamma(\alpha+1)$, $a_{1,1}=u/\Gamma(\alpha)$, $a_{1,2}=v/\Gamma(\alpha-1)$ and $a_{1,\ell}=0$ for $\ell\ge3$. For $k\ge2$, define
--   $$a_{k,\ell}=(\mu a_{k-1,\ell}+\lambda a^{*2}_{k-1,\ell})\frac{\Gamma(\alpha(k-1)-\ell+1)}{\Gamma(\alpha k-\ell+1)},\qquad a^{*2}_{k,\ell}=\sum_{i=1}^{k-1}\sum_{r=0}^{\ell}a_{i,r}a_{k-i,\ell-r}.$$
--   Case (a) sets $v=0$. The valuation $k(\ell)$ is the least positive first index with nonzero coefficient, or $+\infty$ for a zero level. The series function is the sum of $a_{k,\ell}t^{\alpha k-\ell}$ over pairs. Normal convergence on $(0,R)$ means that on each $[x,y]\subset(0,R)$ the norms of all pair terms have a summable uniform majorant. This is equivalent to summability of their suprema and avoids real suprema of unbounded sets.
--
--   The auxiliary sequence in Proposition C.1 is also fixed here:
--   $$c_0=0,\quad c_1=1,\quad c_\ell=\frac{\Gamma((2\alpha-1)(\ell-1))}{\Gamma((2\alpha-1)\ell+1-\alpha)}\sum_{j=1}^{\ell-1}c_jc_{\ell-j}\quad(\ell\ge2).$$
--
--   **Formalization Note** The recursion is defined at every $k\ge2$, not circularly through the valuation. Indices below the valuation have zero prefactors in case (a). The valuation uses a complete lattice $\mathbb N\cup\{\infty\}$, with infimum of the empty set infinity. The term at $k=0$ vanishes. All time assertions use $t>0$. The case-(b) total extension can encounter Gamma poles, e.g. $\alpha=3/2,k=3,\ell=4$; no existence theorem is asserted for that extension. The case-(b) counterexample instead uses $\alpha=2$, with positive Gamma arguments in the nonzero calculation.
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, pp. 24, 35–40, (6.36)–(6.38), (C.63); p. 41, Lemma C.2(b)

import Mathlib

namespace FracRiccati.Radius.Supplement

/-- The double coefficient recursion (6.37)–(6.38); use `v = 0` for case (a).
The zeroth row is zero. Below the valuation the zero prefactor makes the extension harmless
in case (a). For case (b) the printed formula can hit Gamma poles; see DISPROOF.md. -/
noncomputable def doubleCoeff (α : ℝ) (lam mu nu u v : ℂ) : ℕ → ℕ → ℂ
  | 0, _ => 0
  | 1, 0 => nu / (Real.Gamma (α + 1) : ℂ)
  | 1, 1 => u / (Real.Gamma α : ℂ)
  | 1, 2 => v / (Real.Gamma (α - 1) : ℂ)
  | 1, _ + 3 => 0
  | j + 2, ℓ =>
      (mu * doubleCoeff α lam mu nu u v (j + 1) ℓ +
        lam * ∑ i ∈ (Finset.Ico 1 (j + 1)).attach,
          ∑ r ∈ Finset.range (ℓ + 1),
            doubleCoeff α lam mu nu u v i.1 r *
            doubleCoeff α lam mu nu u v (j + 1 - i.1) (ℓ - r)) *
      ((Real.Gamma (α * (j + 1 : ℕ) - (ℓ : ℝ) + 1) /
        Real.Gamma (α * (j + 2 : ℕ) - (ℓ : ℝ) + 1) : ℝ) : ℂ)
termination_by k _ => k
decreasing_by
  all_goals
    first
    | (have := (Finset.mem_Ico.mp i.2).2; omega)
    | omega

/-- The convolution in (6.38); only positive first indices contribute. -/
noncomputable def doubleConvolution (a : ℕ → ℕ → ℂ) (k ℓ : ℕ) : ℂ :=
  ∑ i ∈ Finset.Ico 1 k, ∑ r ∈ Finset.range (ℓ + 1), a i r * a (k - i) (ℓ - r)

/-- Minimum nonzero positive first index, with infinity for an identically zero level. -/
noncomputable def valuation (a : ℕ → ℕ → ℂ) (ℓ : ℕ) : ℕ∞ :=
  sInf {k | ∃ n : ℕ, 1 ≤ n ∧ a n ℓ ≠ 0 ∧ k = (n : ℕ∞)}

/-- A single monomial of (6.36), indexed by `(k, ℓ)`. -/
noncomputable def doubleTerm (α : ℝ) (a : ℕ → ℕ → ℂ) (i : ℕ × ℕ) (t : ℝ) : ℂ :=
  a i.1 i.2 * (t ^ (α * (i.1 : ℝ) - (i.2 : ℝ)) : ℝ)

noncomputable def doublePsi (α : ℝ) (a : ℕ → ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑' i : ℕ × ℕ, doubleTerm α a i t

/-- Normal convergence, equivalently summability of the suprema of the term norms
on each compact interval; summable majorants avoid conditional real suprema. -/
def NormallyConvergent (α : ℝ) (a : ℕ → ℕ → ℂ) (R : ℝ) : Prop :=
  ∀ x y : ℝ, 0 < x → x ≤ y → y < R →
    ∃ M : ℕ × ℕ → ℝ, Summable M ∧
      ∀ i t, t ∈ Set.Icc x y → ‖doubleTerm α a i t‖ ≤ M i

/-- The positive starting-value sequence of (C.63), with a dummy value at zero. -/
noncomputable def startingValues (α : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | j + 2 =>
      (Real.Gamma ((2 * α - 1) * (j + 1 : ℕ)) /
        Real.Gamma ((2 * α - 1) * (j + 2 : ℕ) + 1 - α)) *
      ∑ i ∈ (Finset.Ico 1 (j + 2)).attach,
        startingValues α i.1 * startingValues α (j + 2 - i.1)
termination_by k => k
decreasing_by
  all_goals
    have := (Finset.mem_Ico.mp i.2)
    omega

end FracRiccati.Radius.Supplement


