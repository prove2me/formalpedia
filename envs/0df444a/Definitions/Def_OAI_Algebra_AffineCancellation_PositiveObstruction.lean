-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_PositiveObstruction
-- name    : OAI_Algebra_AffineCancellation_PositiveObstruction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:14:19.232576+00:00
-- url     : https://prove2.me/theorems/858797dd-f200-400f-93f6-ed47dc15cbdf
-- title:
--   The valuation grading and the fiber Euler derivation on the modified ring $B$
-- statement:
--   Let $T=\mathbb{C}[a,b,c,d,u]/(ac-bd-1)$ be the coordinate ring of $\mathrm{SL}_2\times\mathbb{A}^1$ and $v=a^3b-a^2u^3-d^2\in T$. Let $\delta$ and $\eta$ be the $\mathbb{C}$-derivations of $T$ with
--   $$\delta(a)=\delta(d)=\delta(u)=0,\ \ \delta(b)=a,\ \ \delta(c)=d,\qquad \eta(b)=\eta(c)=\eta(u)=0,\ \ \eta(a)=b,\ \ \eta(d)=c,$$
--   and let $E=[\delta,\eta]=\delta\eta-\eta\delta$ be their commutator, so that $E(a)=a$, $E(d)=d$, $E(b)=-b$, $E(c)=-c$ and $E(u)=0$. Let $B=T[X_0,X_1]/(X_0^2X_1-v)$, with structure map $j\colon T\to B$ and $\tau$, $V$ the classes of $X_0$, $X_1$.
--
--   1. **Weight of $v$.** In $T$,
--   $$E(v)=2v.$$
--   2. **The valuation grading.** $B=\bigoplus_{e\in\mathbb{Z}}B_e$ is a $\mathbb{Z}$-graded $\mathbb{C}$-algebra, where $B_e$ is the image in $B$ of the $T$-linear span of the monomials $X_0^iX_1^l$ with $-i+2l=e$; thus $j(T)\subseteq B_0$, $\tau\in B_{-1}$ and $V\in B_2$.
--   3. **The fiber Euler derivation.** By item 1, the derivation of $T[X_0,X_1]$ that acts as $E$ on the coefficients, kills $X_0$ and sends $X_1$ to $2X_1$ preserves the ideal $(X_0^2X_1-v)$, and it induces a $\mathbb{C}$-derivation $E_B$ of $B$ with
--   $$E_B(j(t))=j(E(t))\quad(t\in T),\qquad E_B(\tau)=0,\qquad E_B(V)=2V.$$
--
--   The ring $B$ contains the degenerate hypersurface ring of the construction through an injective pullback homomorphism. The grading of item 2 and the derivation $E_B$ are the two structures on $B$ with respect to which locally nilpotent derivations of $B$ commuting with $E_B$, and their homogeneous invariants of positive degree, are analysed in the proof that the hypersurface ring is not a polynomial ring. The name of the grading reflects that, under the embedding of $B$ into $\operatorname{Frac}(T)(X)$ with $\tau\mapsto X$ and $V\mapsto v/X^2$, the elements of $B_e$ go to elements $c\,X^{-e}$ with $c\in T$.
--
--   **Formalization Note** Item 1 is `Determinant.Euler_v`, where `Euler` is the commutator of the derivations `δ` and `η` of `Determinant.T`. `valuationPieces e` is `AffineModification.pieces T v e` with scalars restricted from `T` to the complex numbers, `valuationGrading` is the corresponding `GradedAlgebra` instance, and `fiberEuler` is `AffineModification.euler v Euler Euler_v`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/PositiveObstruction.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/PositiveObstruction.lean by skeleton subtraction
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
import Definitions.Def_OAI_Algebra_AffineCancellation_RationalSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_Modification
import Definitions.Def_OAI_Algebra_AffineCancellation_Bundle
import Definitions.Def_OAI_Algebra_AffineCancellation_ModificationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Extraction

namespace OAI

noncomputable section

namespace ComplexCancellation.Determinant
lemma Euler_v : Euler v=2*v := by
  simp only [v,map_sub,Derivation.leibniz,Derivation.leibniz_pow,
    Euler_a,Euler_b,Euler_d,Euler_u,smul_eq_mul]
  ring
end ComplexCancellation.Determinant
namespace ComplexCancellation.Bundle
open Determinant
abbrev valuationPieces (e : ℤ) : Submodule ℂ B :=
  (AffineModification.pieces T v e).restrictScalars ℂ
instance valuationGrading : GradedAlgebra valuationPieces :=
  { (AffineModification.grading T v) with }
def fiberEuler : Derivation ℂ B B := AffineModification.euler v Euler Euler_v
end ComplexCancellation.Bundle

end

end OAI


