-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:01.09465+00:00
-- url     : https://prove2.me/theorems/fa152b5e-1051-420f-b7cf-a0cbdb4e55d1
-- title:
--   Fibre St C
-- statement:
--   Definitions and structural lemmas for Fibre St C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStC.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
def psumQ (δ k : ℕ) : MvPolynomial (Fin δ) ℤ :=
  (esymmAlgHom_fin_surjective ℤ (le_refl δ)
    ⟨psum (Fin δ) ℤ k, psum_isSymmetric _ _ _⟩).choose
def psumC {R : Type*} [CommRing R] (p : Polynomial R) (n k : ℕ) : R :=
  aeval (fun i : Fin n => (-1) ^ (i.val + 1) * p.coeff (n - (i.val + 1))) (psumQ n k)
variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω} {e : Fin (D + 1) → ι}
def Gen.S (G : Gen x e) (j : ℕ) : MvPolynomial (Fin (D + 1)) ℤ :=
  psumC G.P G.P.natDegree j
def Gen.TrP (G : Gen x e) (H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)) :
    MvPolynomial (Fin (D + 1)) ℤ :=
  ∑ j ∈ Finset.range (H.natDegree + 1), H.coeff j * G.S j
variable [DecidableEq ι] (G : Gen x e)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open Polynomial IntermediateField
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib


