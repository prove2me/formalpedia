-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation
-- name    : OAI_Algebra_AffineCancellation_ReesDerivation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:24:07.113991+00:00
-- url     : https://prove2.me/theorems/9924676d-a05f-4a10-9a72-5367c139fca8
-- title:
--   Lifting the generators of the degeneration to the Rees deformation
-- statement:
--   Let $\hat x=s^2+u^3+p^2F$. Let $P=\mathbb{C}[p,s,u,F,J]$ be the polynomial ring presenting the degeneration $G=P/\bigl(\hat x^2F-(1+2s\hat x)J-p^2J^2\bigr)$, and let
--   $$B=\mathbb{C}[q,p,s,u,F,J]\big/\bigl(\hat x^2F-(1+2s\hat x)J-p^2J^2-q^3pu\bigr)$$
--   be the Rees deformation, with letters denoting the classes of variables. The file defines the $\mathbb{C}$-algebra homomorphism
--   $$\mathrm{up}:P\to B,\qquad p\mapsto p,\quad s\mapsto s,\quad u\mapsto u,\quad F\mapsto F,\quad J\mapsto J,$$
--   which sends each variable of $P$ to the class in $B$ of the variable with the same name; the deformation parameter $q$ is not involved.
--
--   Composing $\mathrm{up}$ with the reduction map $B\to G$ (which sends $q$ to $0$ and fixes $p,s,u,F,J$) gives the quotient map $P\to G$; in particular the reduction map is surjective. Surjectivity is what allows a locally nilpotent derivation of $B$ that annihilates $q$ to descend to a derivation of $G$.
--
--   **Formalization Note** `up = aeval ![π (X 1),π (X 2),π (X 3),π (X 4),π (X 5)]`, a map `Degeneration.P →ₐ[ℂ] B`, where `X 0` of the six-variable ring is the parameter q. The identity `red.comp up = Degeneration.π` and the surjectivity of `red` are proved from this definition in the results built on it.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/ReesDerivation.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/ReesDerivation.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace ComplexCancellation.Rees
open MvPolynomial LaurentPolynomial
def up : Degeneration.P →ₐ[ℂ] B := aeval ![π (X 1),π (X 2),π (X 3),π (X 4),π (X 5)]
end ComplexCancellation.Rees

end

end OAI


