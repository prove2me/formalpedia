-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_DegreeRelations
-- name    : DetSupportRank_DeterminantSupport_DegreeRelations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:08.843692+00:00
-- url     : https://prove2.me/theorems/67168feb-f473-4eb1-8ac9-2ca55f22f299
-- title:
--   Polynomial witnesses for degree relations
-- statement:
--   For a polynomial $f$ in row-partitioned variables and equally sized tuples $a,b$ of nonnegative multidegrees, define
--   $$a\sim_f b\iff\exists A,\ k\ge0:\quad A_{ij}\text{ is homogeneous of degree }a_j-b_i,\quad\det A\mid f^k.$$
--   The matrix is over the actual polynomial ring over the given field. Zero entries are allowed in every indicated degree. Finite tuple relabelings allow the even and odd subset index sets in the Koszul relation. Row and column weights and the bilinear complex degree dot product are also specified.
--
--   The definition includes the empty matrix, whose determinant is one. It does not replace divisibility by equality to $f$ or by any desired consequence of a relation.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Definition 3.1 and §2, p. 5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_PartitionRank
import Definitions.Def_DetSupportRank_DeterminantSupport_PolynomialGrading

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport

def rowWeight {d m : ℕ} (v : Fin d × Fin m) : Fin d → ℤ :=
  fun i => if v.1 = i then 1 else 0

def columnWeight {d m : ℕ} (v : Fin d × Fin m) : Fin m → ℤ :=
  fun j => if v.2 = j then 1 else 0

/-- Definition 3.1, p.5, allowing arbitrary finite tuple indices and a relabeling of one tuple. -/
def DegreeRelation {K : Type*} [Field K] {d m : ℕ}
    (f : MvPolynomial (Fin d × Fin m) K)
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (a : I → Fin d → ℕ) (b : J → Fin d → ℕ) : Prop :=
  ∃ e : I ≃ J, ∃ A : Matrix J J (MvPolynomial (Fin d × Fin m) K),
    (∀ i j, Homogeneous rowWeight
      (fun t => (a (e.symm j) t : ℤ) - (b i t : ℤ)) (A i j)) ∧
    ∃ k : ℕ, A.det ∣ f ^ k

/-- Nonnegative degree vectors are cast coordinatewise, with the bilinear dot product over ℂ. -/
def degreeDot {d : ℕ} (a : Fin d → ℕ) (y : Fin d → ℂ) : ℂ :=
  ∑ i, (a i : ℂ) * y i

end DetSupportRank.DeterminantSupport


