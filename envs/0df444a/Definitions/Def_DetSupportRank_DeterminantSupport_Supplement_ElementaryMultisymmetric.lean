-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_ElementaryMultisymmetric
-- name    : DetSupportRank_DeterminantSupport_Supplement_ElementaryMultisymmetric
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:06:50.962045+00:00
-- url     : https://prove2.me/theorems/9ad6b15c-4423-44b8-80f2-c60ce268909a
-- title:
--   Elementary multisymmetric formal polynomials
-- statement:
--   For $d$ independent row parts, each containing $n$ variables, define
--   $$E_{d,n}(x_1,\ldots,x_d)=\sum_{a:[d]\hookrightarrow[n]}\prod_{i=1}^d x_{i,a(i)}.$$
--   Each injective column assignment contributes once. This definition is over an arbitrary commutative semiring, and retains rectangular $d\times n$ inputs. It is one at $d=0$ and zero when $d>n$. There is no factorial division or diagonal-specialization convention. The Gowers conclusions instead use Mathlib's squarefree elementary symmetric polynomial $e_{d,n}=\sum_{|I|=d}\prod_{i\in I}x_i$.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), §4.3, definition of E_{d,n}, p. 13 (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Mathlib

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport.Supplement

/-- E_{d,n}, §4.3, p.13: injective column assignments, with independent row variables. -/
def elementaryMultisymmetric (F : Type*) [CommSemiring F] (d n : ℕ) :
    MvPolynomial (Fin d × Fin n) F := by
  classical
  exact ∑ a : Fin d ↪ Fin n, ∏ i : Fin d, MvPolynomial.X (i, a i)
end DetSupportRank.DeterminantSupport.Supplement


