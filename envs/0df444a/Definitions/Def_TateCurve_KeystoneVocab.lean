-- Prove2me | Definitions.Def_TateCurve_KeystoneVocab
-- name    : TateCurve_KeystoneVocab
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/5226c6ea-3392-599b-8c30-6ae209832eb7
-- title:
--   Defect, ψ₂ and lattice vocabulary for the Tate parametrisation
-- statement:
--   Over a complete nontrivially normed field $K$ with ultrametric norm, these are the notions in which the additivity of the Tate parametrisation $u \mapsto (\mathrm{pointX}\,q\,u, \mathrm{pointY}\,q\,u)$ on `curve q` is expressed. `pointPsiTwo q w` is $2\,\mathrm{pointY}(q,w) + \mathrm{pointX}(q,w)$, and `psifun w` is its rational-function analogue $2\,\mathrm{yfun}(w) + \mathrm{xfun}(w)$ with $\mathrm{xfun}(w) = w/(1-w)^2$, $\mathrm{yfun}(w) = w^2/(1-w)^3$. `addDefectDiff q u v` is $(\mathrm{pointX}(q,uv) - \mathrm{pointX}(q,uv^{-1}))(\mathrm{pointX}(q,u)-\mathrm{pointX}(q,v))^2 + \mathrm{pointPsiTwo}(q,u)\,\mathrm{pointPsiTwo}(q,v)$, and `DiffHyp q` asserts that this quantity vanishes for all $u,v$ satisfying `AddParams q u v`, i.e. $q,u,v \neq 0$ and none of $u$, $v$, $uv$, $uv^{-1}$ lying in $q^{\mathbb Z}$ (the predicate `OffLattice`). `ExpansionRegion q u v` is a structure whose fields are `AddParams q u v`, $\Vert q\Vert < 1$, and, for each $w \in \{u,v,uv,uv^{-1}\}$, the two annulus bounds $\Vert q\Vert < \Vert w\Vert$ and $\Vert q\Vert\,\Vert w\Vert < 1$.
--
--   On the coefficient side, `psiCoeffFull u N` is $2\,\mathrm{yCoeffFull}(u,N) + \mathrm{xCoeffFull}(u,N)$, and `addDefectSumCoeff u v N`, `addDefectDiffCoeff u v N` are explicit twelve- and seven-term integer combinations of iterated `cauchyMul` convolutions of the sequences $\mathrm{xCoeffFull}(uv)$, $\mathrm{xCoeffFull}(uv^{-1})$, $\mathrm{xCoeffFull}(u)$, $\mathrm{xCoeffFull}(v)$, `psiCoeffFull`, `a₄Coeff`, `a₆Coeff`; they are the intended $N$-th $q$-coefficients of the sum and difference defects. `cauchyMulIntTriple c d e N` is $\sum_{i=1}^{N-1} c(i)\,\mathrm{cauchyMulInt}(d,e)(N-i)$, an interior triple convolution, and `svComplex u v M` is a four-block expression in $\mathrm{xfun}$, $\mathrm{xCoeff}$, `psifun`, `psiCoeffFull` and the divisor sums $\sum_{d \mid a} d\,Gz(u,d)\,Gz(v,d)$, the single-variable normal form of the difference defect at level $M$.
--
--   Finally `LatticeRep q w w'` says $w' = q^m w$ or $w' = q^m w^{-1}$ for some $m \in \mathbb Z$; `OnHalfLattice q w` says $\Vert q^m w\Vert^2 = \Vert q\Vert$ for some $m \in \mathbb Z$ (a condition on norms); and `MuTranslation q ζ p`, stated in characteristic zero, asserts that for every $a$ with $1 \le a < p$ and every $u \neq 0$ with $u$ and $\zeta^a u$ off the lattice, the affine point of `curve q` at parameter $\zeta^a u$ is the sum, in Mathlib's group of points, of the points at parameters $\zeta^a$ and $u$ (nonsingularity witnesses for the three points being taken as explicit arguments).
--
--   **Relation to Mathlib.** `MuTranslation` is phrased using Mathlib's group structure on `WeierstrassCurve.Affine.Point` for the curve `curve q`; the parametrisation `pointX`/`pointY`, the coefficient sequences and convolutions, and all the predicates here are the project's own, Mathlib carrying no Tate parametrisation.
--
--   **Where it is used.** These are the notions in which the symmetric and antisymmetric addition identities for the Tate parametrisation are formulated and proved by $q$-expansion in the annulus cut out by `ExpansionRegion`; the resulting additivity gives the description of $E_q[p]$ for a curve with multiplicative reduction, and with it the action of inertia at such a prime on the mod $p$ representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_TateCurve_KeystoneVocab.lean

import Mathlib
import Definitions.Def_TateCurve_XMultIdentities

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal
open IsUltrametricDist Filter
open WeierstrassCurve.Affine

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

section PsiTwo

variable [CompleteSpace K] {q w : K}

variable (q w) in

noncomputable def pointPsiTwo : K := 2 * pointY q w + pointX q w

end PsiTwo

section Defect

variable [CompleteSpace K] {q u v : K}

variable (q u v)

noncomputable def addDefectDiff : K :=
  (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 +
    pointPsiTwo q u * pointPsiTwo q v

variable {q u v}

end Defect

end TateCurve
set_option linter.unusedSectionVars false

open WeierstrassCurve.Affine

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]
variable {q u v w ζ : K} {p : ℕ}

variable (q) in

def DiffHyp : Prop :=
  ∀ u v : K, AddParams q u v →
    (pointX q (u * v) - pointX q (u * v⁻¹)) * (pointX q u - pointX q v) ^ 2 =
      -((2 * pointY q u + pointX q u) * (2 * pointY q v + pointX q v))

end TateCurve

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal
open IsUltrametricDist Filter Finset

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Region

variable {q u v : K}

structure ExpansionRegion (q u v : K) : Prop where
  params : AddParams q u v
  norm_q_lt_one : ‖q‖ < 1
  u_lo : ‖q‖ < ‖u‖
  u_hi : ‖q‖ * ‖u‖ < 1
  v_lo : ‖q‖ < ‖v‖
  v_hi : ‖q‖ * ‖v‖ < 1
  mul_lo : ‖q‖ < ‖u * v‖
  mul_hi : ‖q‖ * ‖u * v‖ < 1
  div_lo : ‖q‖ < ‖u * v⁻¹‖
  div_hi : ‖q‖ * ‖u * v⁻¹‖ < 1

end Region

end TateCurve

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TateCurve

open scoped NNReal

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q u v : K}

section Coefficients

variable (u v)

noncomputable def addDefectSumCoeff (N : ℕ) : K :=
  cauchyMul (xCoeffFull (u * v)) (cauchyMul (xCoeffFull u) (xCoeffFull u)) N
    - 2 * cauchyMul (xCoeffFull (u * v)) (cauchyMul (xCoeffFull u) (xCoeffFull v)) N
    + cauchyMul (xCoeffFull (u * v)) (cauchyMul (xCoeffFull v) (xCoeffFull v)) N
    + cauchyMul (xCoeffFull (u * v⁻¹)) (cauchyMul (xCoeffFull u) (xCoeffFull u)) N
    - 2 * cauchyMul (xCoeffFull (u * v⁻¹)) (cauchyMul (xCoeffFull u) (xCoeffFull v)) N
    + cauchyMul (xCoeffFull (u * v⁻¹)) (cauchyMul (xCoeffFull v) (xCoeffFull v)) N
    - 2 * cauchyMul (xCoeffFull u) (cauchyMul (xCoeffFull u) (xCoeffFull v)) N
    - 2 * cauchyMul (xCoeffFull u) (cauchyMul (xCoeffFull v) (xCoeffFull v)) N
    - cauchyMul (xCoeffFull u) (xCoeffFull v) N
    - 2 * cauchyMul a₄Coeff (xCoeffFull u) N
    - 2 * cauchyMul a₄Coeff (xCoeffFull v) N
    - 4 * a₆Coeff N

variable {u v}

end Coefficients

end TateCurve

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section TripleSplit

noncomputable def cauchyMulIntTriple (c d e : ℕ → K) (N : ℕ) : K :=
  ∑ i ∈ Finset.Ico 1 N, c i * cauchyMulInt d e (N - i)

end TripleSplit

end TateCurve

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TateCurve

open scoped NNReal

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q u v : K}

section PsiCoeff

variable (u) in

noncomputable def psiCoeffFull (N : ℕ) : K := 2 * yCoeffFull u N + xCoeffFull u N

end PsiCoeff

section Coefficients

variable (u v) in

noncomputable def addDefectDiffCoeff (N : ℕ) : K :=
  cauchyMul (xCoeffFull (u * v)) (cauchyMul (xCoeffFull u) (xCoeffFull u)) N
    - 2 * cauchyMul (xCoeffFull (u * v)) (cauchyMul (xCoeffFull u) (xCoeffFull v)) N
    + cauchyMul (xCoeffFull (u * v)) (cauchyMul (xCoeffFull v) (xCoeffFull v)) N
    - cauchyMul (xCoeffFull (u * v⁻¹)) (cauchyMul (xCoeffFull u) (xCoeffFull u)) N
    + 2 * cauchyMul (xCoeffFull (u * v⁻¹)) (cauchyMul (xCoeffFull u) (xCoeffFull v)) N
    - cauchyMul (xCoeffFull (u * v⁻¹)) (cauchyMul (xCoeffFull v) (xCoeffFull v)) N
    + cauchyMul (psiCoeffFull u) (psiCoeffFull v) N

end Coefficients

end TateCurve

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v w : K}

section Psifun

variable (w) in

noncomputable def psifun : K := 2 * yfun w + xfun w

end Psifun

end TateCurve

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {u v : K}

section AbsorbedNormalForm

variable (u v) in

noncomputable def svComplex (M : ℕ) : K :=
  2 * ((xfun (u * v) - xfun (u * v⁻¹)) * ((xfun u - xfun v) * (xCoeff u M - xCoeff v M)))
    + (∑ d ∈ M.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ))) * (xfun u - xfun v) ^ 2
    + (∑ a ∈ Finset.Ico 1 M, (∑ d ∈ a.divisors, (d : K) * (Gz u (d : ℤ) * Gz v (d : ℤ)))
        * (2 * ((xfun u - xfun v) * (xCoeff u (M - a) - xCoeff v (M - a)))))
    + (psifun u * psiCoeffFull v M + psiCoeffFull u M * psifun v)

end AbsorbedNormalForm

end TateCurve

open scoped NNReal

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q u v w : K}

def LatticeRep (q w w' : K) : Prop :=
  ∃ m : ℤ, w' = q ^ m * w ∨ w' = q ^ m * w⁻¹

def OnHalfLattice (q w : K) : Prop :=
  ∃ m : ℤ, ‖q ^ m * w‖ * ‖q ^ m * w‖ = ‖q‖

end TateCurve

namespace TateCurve

open WeierstrassCurve.Affine

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] [DecidableEq K]

def MuTranslation (q ζ : K) (p : ℕ) : Prop :=
  ∀ a : ℕ, 1 ≤ a → a < p → ∀ u : K, u ≠ 0 → OffLattice q u → OffLattice q (ζ ^ a * u) →
    ∀ (h₁ : (curve q).toAffine.Nonsingular (pointX q (ζ ^ a * u)) (pointY q (ζ ^ a * u)))
      (h₂ : (curve q).toAffine.Nonsingular (pointX q (ζ ^ a)) (pointY q (ζ ^ a)))
      (h₃ : (curve q).toAffine.Nonsingular (pointX q u) (pointY q u)),
      (Point.some (pointX q (ζ ^ a * u)) (pointY q (ζ ^ a * u)) h₁ :
          (curve q).toAffine.Point)
        = Point.some (pointX q (ζ ^ a)) (pointY q (ζ ^ a)) h₂
            + Point.some (pointX q u) (pointY q u) h₃

end TateCurve


