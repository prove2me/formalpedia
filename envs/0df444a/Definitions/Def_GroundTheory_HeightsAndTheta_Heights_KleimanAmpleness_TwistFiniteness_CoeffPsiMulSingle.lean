-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_CoeffPsiMulSingle
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_CoeffPsiMulSingle
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:10.337876+00:00
-- url     : https://prove2.me/theorems/fc4594d7-ea6d-54a8-9535-e256ffda0871
-- title:
--   Coeff Psi Mul Single
-- statement:
--   Definitions and structural lemmas for Coeff Psi Mul Single, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistFiniteness/CoeffPsiMulSingle.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_IsUnitPhiOfMemMonos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial AddMonoidAlgebra
noncomputable section
universe u w
namespace TwistFin
variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω) (S : Type u) [CommRing S] [Algebra S Ω]
variable (n0 : ℕ) (d0 : Fin n0 → ℤ) (g0 : Fin n0 → Ω)
def toChart (I : StdCell N) (hI : ∀ i ∈ I.1, x i ≠ 0) : Chart x :=
  ⟨I.1, I.2.1, fun i hi => (mem_support x).mpr (hI i hi)⟩
variable (M0 : FinGradedSub (S := S) (x := x) Ω)
def genSet (I : Chart x) (b : ℕ) : Set Ω :=
  {ω | ∃ (f : Poly S N) (e : ℕ) (h : MvPolynomial (Fin (r + 1)) S) (m : Ω) (a : ℤ) (t : Poly S N) (e' : ℕ),
    f.IsHomogeneous e ∧ h.IsHomogeneous b ∧ m ∈ M0.piece a ∧ t ∈ monos (S := S) I.1 ∧
    t.IsHomogeneous e' ∧ (e' : ℤ) = e + a ∧ ω = aeval x f * aeval η h * m / aeval x t}
end TwistFin
end
end GroundTheory.Heights₂.Heights.Kleiman


