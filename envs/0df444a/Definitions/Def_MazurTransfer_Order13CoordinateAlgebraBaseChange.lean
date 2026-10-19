-- Prove2me | Definitions.Def_MazurTransfer_Order13CoordinateAlgebraBaseChange
-- name    : MazurTransfer_Order13CoordinateAlgebraBaseChange
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T02:55:55.823157+00:00
-- url     : https://prove2.me/theorems/6377a94b-ef87-42ae-9075-2286a8800a00
-- title:
--   Scalar extension of the actual quadratic coordinate algebras
-- statement:
--   Let $R$ and $S$ be commutative rings with a fixed $R$-algebra structure on $S$. For $f\in R[X]$, scalar extension gives an $S$-algebra isomorphism
--   $$S\otimes_R R[X][Y]/(Y^2-f(X))\;\cong\;S[X][Y]/(Y^2-f_S(X)),$$
--   where $f_S$ is obtained by applying $R\to S$ to the coefficients of $f$.
--
--   The interface specializes this construction to both actual hyperelliptic coordinate rings of the order-thirteen curve. These concrete algebra isomorphisms supply the chart maps in the Cartesian base-change proof for the glued curve.
-- source:
--   Exact byte-for-byte checked MazurTheorem source Order13CoordinateAlgebraBaseChange.lean, including its constructor proofs, polynomial coefficient identities, unchanged imports, and original statement types. Literal curve provenance: MazurTheorem commit 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Vas and contributors, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Literal curve: MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
Design boundary: actual base-change algebra isomorphisms for both quadratic
coordinate charts. No identification of the glued scheme is assumed.
Named downstream consumer: constructing and identifying the rational and
finite-field fibres of the actual integral order-thirteen curve.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve

noncomputable section
namespace MazurTransfer.Order13CoordinateBaseChange
open Polynomial Algebra TensorProduct
universe u v
variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

def quadraticCoordinateRingEquiv (f : Polynomial R) :
    S ⊗[R] AdjoinRoot (X ^ 2 - C f) ≃ₐ[S]
      AdjoinRoot (X ^ 2 - C (f.map (algebraMap R S))) := by
  let p : Polynomial (Polynomial R) := X ^ 2 - C f
  let q : Polynomial (S ⊗[R] Polynomial R) :=
    p.map Algebra.TensorProduct.includeRight.toRingHom
  let e : S ⊗[R] Polynomial R ≃ₐ[S] Polynomial S :=
    (polyEquivTensor' R S).symm
  have hq : q.map e = X ^ 2 - C (f.map (algebraMap R S)) := by
    simp [q, p, e, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C,
      polyEquivTensor_symm_apply_tmul_eq_smul]
  exact (AdjoinRoot.tensorAlgEquiv p q rfl).trans
    (AdjoinRoot.mapAlgEquiv e q _ (hq ▸ Associated.refl _))

theorem sexticPolynomial_map :
    (MazurTorsion.XOneThirteenAffineCurve.sexticPolynomial R).map (algebraMap R S) =
      MazurTorsion.XOneThirteenAffineCurve.sexticPolynomial S := by
  simp [MazurTorsion.XOneThirteenAffineCurve.sexticPolynomial]

theorem reciprocalPolynomial_map :
    (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalPolynomial R).map (algebraMap R S) =
      MazurTorsion.XOneThirteenProjectiveCurve.reciprocalPolynomial S := by
  simp [MazurTorsion.XOneThirteenProjectiveCurve.reciprocalPolynomial]

def ordinaryCoordinateRingEquiv :
    S ⊗[R] MazurTorsion.XOneThirteenAffineCurve.CoordinateRing R ≃ₐ[S]
      MazurTorsion.XOneThirteenAffineCurve.CoordinateRing S := by
  exact (quadraticCoordinateRingEquiv R S
      (MazurTorsion.XOneThirteenAffineCurve.sexticPolynomial R)).trans
    (AdjoinRoot.algEquivOfEq S _ (MazurTorsion.XOneThirteenAffineCurve.affineEquation S)
      (by rw [sexticPolynomial_map R S]; rfl))

def reciprocalCoordinateRingEquiv :
    S ⊗[R] MazurTorsion.XOneThirteenProjectiveCurve.ReciprocalRing R ≃ₐ[S]
      MazurTorsion.XOneThirteenProjectiveCurve.ReciprocalRing S := by
  exact (quadraticCoordinateRingEquiv R S
      (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalPolynomial R)).trans
    (AdjoinRoot.algEquivOfEq S _ (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalEquation S)
      (by rw [reciprocalPolynomial_map R S]; rfl))

end MazurTransfer.Order13CoordinateBaseChange

#print axioms MazurTransfer.Order13CoordinateBaseChange.quadraticCoordinateRingEquiv
#print axioms MazurTransfer.Order13CoordinateBaseChange.ordinaryCoordinateRingEquiv
#print axioms MazurTransfer.Order13CoordinateBaseChange.reciprocalCoordinateRingEquiv


