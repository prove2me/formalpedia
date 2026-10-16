-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_Order
-- name    : OAI_Algebra_AffineCancellation_Order
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:54:46.811592+00:00
-- url     : https://prove2.me/theorems/89b1be7f-a0cc-4263-b2f6-5a1e4aa62b46
-- title:
--   Degree of an element with respect to a locally nilpotent derivation
-- statement:
--   Let $k$ be a field of characteristic zero and let $R$ be an integral domain that is a $k$-algebra. Let $D$ be a locally nilpotent $k$-linear derivation of $R$, meaning that every $r\in R$ satisfies $D^n(r)=0$ for some $n\ge0$. For $r\in R$ consider its orbit polynomial
--   $$\mathrm{orb}_D(r)=\sum_{n\ge0}\frac{1}{n!}\,D^n(r)\,T^n\in R[T].$$
--
--   **Definition.** The order (or $D$-degree) of $r$ is the degree of its orbit polynomial in $T$:
--   $$\mathrm{ord}_D(r)=\deg_T\,\mathrm{orb}_D(r).$$
--
--   Since $1/n!\neq0$ in $k$, the $n$-th coefficient vanishes exactly when $D^n(r)=0$. Hence for $r\neq0$ the order is the largest $n$ with $D^n(r)\neq0$, and the nonzero elements of $\ker D$ have order $0$. This is the standard degree function attached to a locally nilpotent derivation. It measures how many applications of $D$ are needed to annihilate $r$, and it is the bookkeeping device in later arguments that cancel a common factor from a locally nilpotent derivation.
--
--   **Formalization Note** `order D hD r` is the `natDegree` of `orbit D hD r`. Because the `natDegree` of the zero polynomial is $0$, Lean gives $\mathrm{ord}_D(0)=0$ rather than the classical value $-\infty$. The ambient assumptions are `[Field k] [CharZero k] [CommRing R] [IsDomain R] [Algebra k R]`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/Order.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/Order.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace ComplexCancellation.LND
open Polynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R] [Algebra k R]

def order (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) : ℕ :=
  (orbit D hD r).natDegree

end ComplexCancellation.LND

namespace ComplexCancellation.LND
variable {k R S : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R]
  [CommRing S] [Algebra k S] [Algebra k R]
end ComplexCancellation.LND

end

end OAI


