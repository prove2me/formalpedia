-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:08.921945+00:00
-- url     : https://prove2.me/theorems/44f041cb-c898-409c-977d-58810c9126f0
-- title:
--   Cast Add Ne Nat Add
-- statement:
--   Definitions and structural lemmas for Cast Add Ne Nat Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CastAddNeNatAdd.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0.NPB
open MvPolynomial MeasureTheory ReciprocityTheory.MultiplicativeHeights
section MH
variable {R : Type*} [CommSemiring R] {B n : ℕ}
end MH
variable {K : Type} [Field K] {D N : ℕ}
noncomputable def hImg (p : Fin (D + 1) × Fin (N + 1)) :
    MvPolynomial (Fin (N + 1 + D)) (MvPolynomial (Fin D × Fin (N + 1)) K) :=
  Fin.cases (motive := fun _ => Fin (N + 1) → MvPolynomial (Fin (N + 1 + D))
      (MvPolynomial (Fin D × Fin (N + 1)) K))
    (fun j => X (Fin.castAdd D j)) (fun i j => X (Fin.natAdd (N + 1) i) * C (X (i, j))) p.1 p.2
noncomputable def homog : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K →ₐ[K]
    MvPolynomial (Fin (N + 1 + D)) (MvPolynomial (Fin D × Fin (N + 1)) K) :=
  aeval hImg
noncomputable def back : MvPolynomial (Fin (N + 1 + D)) (MvPolynomial (Fin D × Fin (N + 1)) K) →+*
    MvPolynomial (Fin (D + 1) × Fin (N + 1)) K :=
  eval₂Hom (rename fun p : Fin D × Fin (N + 1) => (p.1.succ, p.2)).toRingHom
    (Fin.addCases (fun j => X (0, j)) (fun _ => 1))
noncomputable def psi (sg : K →+* ℂ) (tt : Fin D × Fin (N + 1) → ℂ) :
    MvPolynomial (Fin (D + 1) × Fin (N + 1)) K →+* MvPolynomial (Fin (N + 1 + D)) ℂ :=
  (MvPolynomial.map (eval₂Hom sg tt)).comp (homog (K := K)).toRingHom
noncomputable def gpt (tt : Fin D × Fin (N + 1) → ℂ) (y : Fin (N + 1 + D) → ℂ) :
    Fin (D + 1) × Fin (N + 1) → ℂ :=
  fun p => Fin.cases (motive := fun _ => Fin (N + 1) → ℂ) (fun j => y (Fin.castAdd D j))
    (fun i j => y (Fin.natAdd (N + 1) i) * tt (i, j)) p.1 p.2
end ReciprocityTheory.ChartRestriction.G.T0.NPB


