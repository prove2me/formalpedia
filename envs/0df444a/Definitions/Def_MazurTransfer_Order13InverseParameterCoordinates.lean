-- Prove2me | Definitions.Def_MazurTransfer_Order13InverseParameterCoordinates
-- name    : MazurTransfer_Order13InverseParameterCoordinates
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-10T08:51:21.21007+00:00
-- url     : https://prove2.me/theorems/e1f8fe75-1c83-4594-b796-0207d58cf540
-- title:
--   Actual order-13 inverse-parameter coordinate rings
-- statement:
--   Let $R$ be a commutative ring and let $A$ and $C$ be the ordinary and reciprocal coordinate rings of the literal order-$13$ curve. Put $t=y+x^3+x^2+1$, $p=xt$, $q=x(p+2)$, and define
--   $$s=1/t,\qquad a=p/t^2,\qquad b=q/t^2,\qquad B=R[S][a,b]\subseteq A[1/t].$$
--   Here $S$ acts by $s$, and the structural $R$-action on $B$ is the composition through $R[S]$. In $C$, put $f=w+1+z+z^3$ and $g=f+2z^4$. The reciprocal patch is $P=C[1/(fg)]$, with regular functions
--   $$s_P=z^3/f,\qquad a_P=z^2/f,\qquad b_P=z/f+2z^5/f^2.$$
--   These are literal coordinate definitions, without any supplied finiteness or chart-isomorphism hypotheses. Their named downstream consumer is the construction of inverse-parameter localization charts and single-section finite-map data.
-- source:
--   MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Complete owned recovered reciprocal-coordinate, unit, universal-property and surjectivity proofs using Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Attribution retained. The unchanged public actual-curve geometric-integrality and flatness/smoothness results supply the coordinate-domain proofs; the actual overlap equivalence and faithful localizations prove injectivity.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: literal inverse-parameter coordinate definitions for the
actual order-13 ordinary and reciprocal rings, with their coefficient actions.
Named downstream consumer: actual inverse-parameter localization charts and
single-section FiniteMapData. This interface assumes no chart isomorphisms.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve

noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterPublicCoordinates
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
variable (R : Type u) [CommRing R]

def t : CoordinateRing R := yCoordinate R + (xCoordinate R ^ 3 + xCoordinate R ^ 2 + 1)
def p : CoordinateRing R := xCoordinate R * t R
def q : CoordinateRing R := xCoordinate R * (p R + 2)
abbrev OrdinaryLocalization := Localization.Away (t R)
def s : OrdinaryLocalization R := IsLocalization.Away.invSelf (t R)
def a : OrdinaryLocalization R := algebraMap (CoordinateRing R) (OrdinaryLocalization R) (p R) * s R ^ 2
def b : OrdinaryLocalization R := algebraMap (CoordinateRing R) (OrdinaryLocalization R) (q R) * s R ^ 2
def parameterMap : Polynomial R →+* OrdinaryLocalization R := (aeval (s R)).toRingHom
scoped instance parameterAlgebra : Algebra (Polynomial R) (OrdinaryLocalization R) := (parameterMap R).toAlgebra
scoped instance parameterSMul : SMul (Polynomial R) (OrdinaryLocalization R) := (parameterAlgebra R).toSMul
scoped instance parameterModule : Module (Polynomial R) (OrdinaryLocalization R) :=
  @Algebra.toModule (Polynomial R) (OrdinaryLocalization R) _ _ (parameterAlgebra R)
def candidateAlgebra : Subalgebra (Polynomial R) (OrdinaryLocalization R) :=
  Algebra.adjoin (Polynomial R) ({a R,b R} : Set (OrdinaryLocalization R))
scoped instance candidateBaseAlgebra : Algebra R (candidateAlgebra R) :=
  ((algebraMap (Polynomial R) (candidateAlgebra R)).comp Polynomial.C).toAlgebra

def f : ReciprocalRing R := wCoordinate R + (1 + zCoordinate R + zCoordinate R ^ 3)
def g : ReciprocalRing R := f R + 2 * zCoordinate R ^ 4
abbrev PatchRing := Localization.Away (f R * g R)
def z : PatchRing R := algebraMap (ReciprocalRing R) (PatchRing R) (zCoordinate R)
def r : PatchRing R := algebraMap (ReciprocalRing R) (PatchRing R) (g R) * IsLocalization.Away.invSelf (f R * g R)
def patchS : PatchRing R := z R ^ 3 * r R
def patchA : PatchRing R := z R ^ 2 * r R
def patchB : PatchRing R := z R * r R + 2 * z R ^ 5 * r R ^ 2

end MazurTransfer.Order13InverseParameterPublicCoordinates
end
#print axioms MazurTransfer.Order13InverseParameterPublicCoordinates.candidateAlgebra
#print axioms MazurTransfer.Order13InverseParameterPublicCoordinates.patchB


