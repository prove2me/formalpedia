-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_Permutations
-- name    : DetSupportRank_DeterminantSupport_Permutations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:34.999438+00:00
-- url     : https://prove2.me/theorems/8eb6d1fa-f783-41d9-8d99-d265c8bdf0a6
-- title:
--   Uniform permutation probabilities and complex roots
-- statement:
--   For a predicate $P$ on $S_n$, define the exact rational probability and the complex root vector by
--   $$\Pr_{\sigma\in S_n}[P(\sigma)]=\frac{|\{\sigma:P(\sigma)\}|}{n!},\qquad \boldsymbol\zeta=(1,\zeta,\ldots,\zeta^{n-1}),\quad\zeta=e^{2\pi i/n}.$$
--   Probability counts all permutations with multiplicity. The vector is used only for $n\ge2$, although the formula is total.
--
--   This supplies the same permutation action $v^\sigma_i=v_{\sigma(i)}$ as the source, and roots always live in $\mathbb C$, never in the coefficient field.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), §6 and §6.1, p. 27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_DeterminantFamily
import Definitions.Def_DetSupportRank_DeterminantSupport_DegreeVarieties

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport

/-- Uniform probability on all n! permutations, with multiplicity. -/
def permutationProbability {n : ℕ} (P : Equiv.Perm (Fin n) → Prop) : ℚ := by
  classical
  exact (Fintype.card {σ : Equiv.Perm (Fin n) // P σ} : ℚ) / (Nat.factorial n : ℚ)

/-- §6, p.27: the fixed complex root, independent of the coefficient field. -/
def rootVector (n : ℕ) : Fin n → ℂ :=
  fun i => Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) ^ i.val

end DetSupportRank.DeterminantSupport


