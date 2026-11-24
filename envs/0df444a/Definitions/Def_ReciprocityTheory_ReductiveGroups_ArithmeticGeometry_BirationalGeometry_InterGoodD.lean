-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodD
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:47.997863+00:00
-- url     : https://prove2.me/theorems/7b86f575-f43c-42b6-ae37-eadfacfce365
-- title:
--   Inter Good D
-- statement:
--   Definitions and structural lemmas for Inter Good D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodD.lean

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactMore_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaA_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {k : Type*} [Field k]
def substFun {r : ℕ} (lam : Fin r → k) : Fin (r + 1) → Polynomial (MvPolynomial (Fin r) k) :=
  Fin.cons Polynomial.X (fun i => Polynomial.C (C (lam i)) * Polynomial.X + Polynomial.C (X i))
def subst {r : ℕ} (lam : Fin r → k) :
    MvPolynomial (Fin (r + 1)) k →ₐ[k] Polynomial (MvPolynomial (Fin r) k) :=
  aeval (substFun lam)
def IntOver (k : Type*) [Field k] {R : Type*} [CommRing R] [Algebra k R] {r : ℕ} (ℓ : Fin r → R)
    (x : R) : Prop :=
  ((aeval ℓ : MvPolynomial (Fin r) k →ₐ[k] R) : MvPolynomial (Fin r) k →+* R).IsIntegralElem x
end
end ReciprocityTheory.ChartRestriction.G.Geo


