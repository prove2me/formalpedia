-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UnitriMonomialOfLowerTri
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_UnitriMonomialOfLowerTri
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:42.391094+00:00
-- url     : https://prove2.me/theorems/69d57da4-15c6-4192-a49e-dca41c1d4736
-- title:
--   Unitri Monomial Of Lower Tri
-- statement:
--   Definitions and structural lemmas for Unitri Monomial Of Lower Tri, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/UnitriMonomialOfLowerTri.lean

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
namespace GlobalTheory.CoeffWord
variable {R : Type} [CommRing R] {r n : ℕ}
def unitri (R : Type) [CommRing R] (L : List (Fin r × Fin n)) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Fin r × Fin n) R :=
  aeval fun v => if v.1.val = v.2.val then 1 else if v ∈ L then X v else 0
def single (R : Type) [CommRing R] (p : Fin r × Fin n) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] Polynomial (MvPolynomial (Fin r × Fin n) R) :=
  aeval fun v => if v = p then Polynomial.X else Polynomial.C (X v)
def letter (e : Fin r × Fin n →₀ ℕ) (p : Fin r × Fin n) : Fin r × Fin r × ℕ :=
  (if h : p.2.val < r then ⟨p.2.val, h⟩ else p.1, p.1, e p)
def positions (r n : ℕ) : List (Fin r × Fin n) :=
  (List.finRange n).reverse.flatMap fun s =>
    ((List.finRange r).filter fun a => s.val < a.val).map fun a => (a, s)
end GlobalTheory.CoeffWord


