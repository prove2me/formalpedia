-- Prove2me | Definitions.Def_PhilipponMultiplicity_GenericMixedSections
-- name    : PhilipponMultiplicity_GenericMixedSections
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-08T21:37:36.745992+00:00
-- url     : https://prove2.me/theorems/c747376b-5ece-4f0a-9bd6-00ec548379ae
-- title:
--   Universal normalized mixed sections and their Jacobian obstruction ideals
-- statement:
--   For a commutative coefficient ring $R$ and a finite set of $N$ ambient variables, associate to any ideal $I\subseteq R[X_v]$ its full Jacobian obstruction ideal
--   $$
--   \mathcal J(I)=I+\left(\det\!\left(\frac{\partial Q_u}{\partial X_v}\right)_{u,v}:Q_1,\ldots,Q_N\in I\right).
--   $$
--   The tuples range over the actual ideal and are not required to generate it. This definition retains the original equations as well as the determinants.
--
--   For a multiprojective space $M=\prod_i\mathbf P^{n_i}$ over a field $K$ and an ordered cutting list $l$, set $R=K[T_{j,v}]$ with independent coefficient variables. The universal ambient ring is $A=R[X_v]$. The universal row $j$ is $\sum_tT_{j,(l_j,t)}X_{l_j,t}$. For any subset $S\subseteq M$ and pivot choice $b$, define
--   $$
--   J_b(S)=I(S)A+(P_j:j<|l|)+(X_{i,b_i}-1:i).
--   $$
--   Finally, the generic coefficient map $A\to\operatorname{Frac}(R)[X_v]$ extends coefficients and fixes every ambient variable. Derivatives in $\mathcal J$ treat coefficient variables as constants. These definitions give a concrete interface for generic-fibre transversality and boundary certificates. No existence, smoothness, or radicality claim is built into them.
-- source:
--   Auxiliary definitions for Philippon mixed sections, Bull. SMF 114 (1986), pp.363–364, https://numdam.org/articles/10.24033/bsmf.2060/ . The Jacobian construction uses coordinate differentials and the conormal presentation from Stacks Project Lemmas 10.131.9 and 10.131.14, https://stacks.math.columbia.edu/tag/00RM . Universal coefficient and normalization formulas are explicitly defined here; this file states no geometric theorem.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.GenericMixedSections
open MvPolynomial

/-- The equations of an affine scheme together with all full square Jacobian minors.
The tuples are taken from the actual ideal, without a chosen generating set. -/
def jacobianIdeal {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]
    (I : Ideal (MvPolynomial σ R)) : Ideal (MvPolynomial σ R) :=
  I ⊔ Ideal.span {d | ∃ Q : σ → MvPolynomial σ R,
    (∀ i, Q i ∈ I) ∧ d = (Matrix.of (fun i j => pderiv j (Q i))).det}

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K) (l : List M.FactorIndex)

/-- Independent coefficient variables for every row and every ambient coordinate. -/
abbrev CoeffRing := MvPolynomial (Fin l.length × M.Variable) K

/-- Polynomial functions of ambient coordinates with universal coefficient polynomials. -/
abbrev UniversalRing := MvPolynomial M.Variable (CoeffRing M l)

/-- The universal block-linear equation of a specified cutting row. -/
def universalRow (j : Fin l.length) : UniversalRing M l :=
  ∑ t : Fin (M.ambientDimension l[j] + 1),
    C (X (j, (⟨l[j],t⟩ : M.Variable))) * X (⟨l[j],t⟩ : M.Variable)

/-- The actual normalized mixed-section ideal over the coefficient ring. -/
def normalizedIdeal (S : Set M.Point)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1)) :
    Ideal (UniversalRing M l) :=
  (M.vanishingIdeal S).map (map C) ⊔
    (⨆ j : Fin l.length, Ideal.span {universalRow M l j}) ⊔
    Ideal.span (Set.range (fun i : M.FactorIndex =>
      (X (⟨i,b i⟩ : M.Variable) : UniversalRing M l) - 1))

/-- Extend only the coefficient ring to its fraction field. -/
def genericMap : UniversalRing M l →+*
    MvPolynomial M.Variable (FractionRing (CoeffRing M l)) :=
  map (algebraMap (CoeffRing M l) (FractionRing (CoeffRing M l)))

end PhilipponMultiplicity.GenericMixedSections


