-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_MinimumChartCost
-- name    : WeierstrassEllipticZeta_MinimumChartCost
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-22T19:03:06.533921+00:00
-- url     : https://prove2.me/theorems/5d7a6a97-7b2b-4cfc-95f1-659c7b32ed6f
-- title:
--   Finite valid chart points and minimum local chart cost
-- statement:
--   For an entire sigma lift S and a finite set X, form the finite set V of pairs (c,z), where c is one of the two affine charts, z belongs to X+X+X, and the corresponding denominator S_0(z) or S_2(z) is nonzero. For a period pair L, polynomial Q and natural truncation parameters N,T, define E_min as the minimum of the existing canonical capped chart costs over V. Its value is defined to be zero when V is empty. A separate theorem proves that V is nonempty for normalized sigma coordinates when 0 belongs to X, so this fallback is never used in the A.1 application.
--
--   The definition refers only to the existing chart costs and denominator test. It does not contain the desired geometric inequality, the constant C, or the anchor weight W_min. It uses classical equality and local algebra lengths; no effective cost-evaluation algorithm is asserted.
-- source:
--   Derived finite chart minimum for the A.1 frontier https://prove2.me/theorems/62ce1ff0-7017-488f-b92c-d199923e4da4. The normalized sigma lift satisfies S_2(0)=-2, by the identity S_2=-2(sigma prime)^3+3*sigma*sigma prime*sigma double-prime-sigma^2*sigma triple-prime, analytic continuation, and sigma(0)=0, sigma prime(0)=1. The derivative of zeta is the already-Proved dependency https://prove2.me/theorems/9d009034-3d4c-416b-90eb-35a15f91a612. Over the triple sumset the finite valid chart set has at most 2*|X+X+X| elements, is nonempty when 0 is in X, and the positive natural local cost attains its minimum E_min. For any natural weight W, the existential chart budget is exactly equivalent to W*E_min<=R. Primary pinned source for finite minimum attainment: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Finset/Max.lean (Finset.exists_min_image), and finite infimum laws: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Finset/Lattice/Fold.lean. Mission context: Appendix A of Senthil Kumar K (2026), https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2#app1. This is a derived selection lemma, not the uniform geometric estimate. The remaining frontier is W_min*E_min<=C*(m+1)*n^2, with the same C, hypotheses and anchor weight. The chosen chart and its cost may change. No effective computation of local lengths or numeric improvement to the global or integer-search bounds is asserted.

import Definitions.Def_WeierstrassEllipticZeta_CanonicalChartCost
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.Max

noncomputable section
open scoped Classical Pointwise
namespace WeierstrassEllipticZeta

/-- Valid denominator charts at points of the triple sumset. -/
def validChartPoints (S : Fin 5 → ℂ → ℂ) (X : Finset ℂ) : Finset (Fin 2 × ℂ) :=
  (Finset.univ ×ˢ (X + X + X)).filter
    (fun p => S (extensionChartDenominator p.1) p.2 ≠ 0)

/-- Least local chart cost on the finite valid chart set; zero if that set is empty.
For normalized sigma coordinates and `0 ∈ X`, nonemptiness and attainment are proved separately. -/
def minimumChartCost (L : PeriodPair) (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (N T : ℕ) (X : Finset ℂ) : ℕ :=
  if h : (validChartPoints S X).Nonempty then
    (validChartPoints S X).inf' h (fun p => cappedChartCost L S Q N T p.1 p.2)
  else 0

end WeierstrassEllipticZeta


