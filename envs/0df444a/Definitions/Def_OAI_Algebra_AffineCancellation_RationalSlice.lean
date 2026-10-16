-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_RationalSlice
-- name    : OAI_Algebra_AffineCancellation_RationalSlice
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:45:23.496793+00:00
-- url     : https://prove2.me/theorems/431b4e81-2cdb-4f9c-8dd7-eaeacc348f44
-- title:
--   Elements of a domain are polynomials in a rational slice of a locally nilpotent derivation
-- statement:
--   Let $k$ be a field and $R$ a commutative $k$-algebra with fraction field $K$ (so $R$ is an integral domain and $R\subseteq K$), and assume that $K$ has characteristic zero. Let $D\colon R\to R$ be a $k$-linear derivation that is *locally nilpotent*: for every $r\in R$ there is $n\ge0$ with $D^n(r)=0$, where $D^n$ is the $n$-fold iterate of $D$. Let $\tilde D\colon K\to K$ be the extension of $D$ to a derivation of $K$, given by the quotient rule $\tilde D(a/b)=\bigl(b\,D(a)-a\,D(b)\bigr)/b^2$, and let
--   $$K^{\tilde D}=\{\,c\in K:\tilde D(c)=0\,\}$$
--   be its field of constants.
--
--   **Statement.** If $t\in K$ satisfies $\tilde D(t)=1$ (a *rational slice* of $D$), then every element of $R$ is a polynomial in $t$ with coefficients in $K^{\tilde D}$: for each $r\in R$ there exists $p\in K^{\tilde D}[X]$ with
--   $$p(t)=r\qquad\text{in } K.$$
--
--   A nonzero locally nilpotent derivation need not have a slice inside $R$, but rational slices are easy to produce: if $s\in R$ satisfies $D(s)\neq0$ and $D^2(s)=0$, then $t=s/D(s)$ satisfies $\tilde D(t)=1$. The statement therefore places $R$ inside the polynomial ring $K^{\tilde D}[t]$ in one variable over a field, which is the starting point for a polynomial model of $R$.
--
--   **Formalization Note** The extension is `FractionDerivation.extend D`, local nilpotence is `LND.LocallyNilpotent D`, and the fraction field is any field `K` with `IsFractionRing R K` and compatible `k`-algebra structures; the lemma `image_is_polynomial` compares `Polynomial.aeval t p` with `algebraMap R K r`. It omits the section hypotheses that `k` has characteristic zero and that `R` is a domain (the latter is implied by the existence of the fraction field).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/RationalSlice.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/RationalSlice.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ComplexCancellation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
import Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
import Definitions.Def_OAI_Algebra_AffineCancellation_Rees
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DegenerationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveInvariant
import Definitions.Def_OAI_Algebra_AffineCancellation_RelativeClearing
import Definitions.Def_OAI_Algebra_AffineCancellation_FractionDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DifferentialSlice

namespace OAI

noncomputable section

namespace ComplexCancellation.RationalSlice
open DifferentialSlice FractionDerivation
variable {k R K : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R]
  [Algebra k R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
  [Algebra k K] [IsScalarTower k R K]

omit [CharZero k] [IsDomain R] in
lemma image_is_polynomial (D : Derivation k R R) (hD : LND.LocallyNilpotent D)
    {t : K} (ht : extend D t = 1) (r : R) :
    ∃ p : Polynomial (constants (extend (K := K) D)), Polynomial.aeval t p = algebraMap R K r := by
  apply nilpotent_is_polynomial _ ht
  obtain ⟨n, hn⟩ := hD r
  exact ⟨n, by rw [iterate_algebraMap, hn, map_zero]⟩

end ComplexCancellation.RationalSlice

end

end OAI


