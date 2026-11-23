-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtChart
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:11.959808+00:00
-- url     : https://prove2.me/theorems/476540c8-d35b-4d52-9403-a14f6149dfa4
-- title:
--   Et Chart
-- statement:
--   Definitions and structural lemmas for Et Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EtChart.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DenseSec
def EtChart (R A : Type) [CommRing R] [CommRing A] [Algebra R A] {g : ℕ} (t : Fin g → A) (h : A) : Prop :=
  letI : Algebra (MvPolynomial (Fin g) R) (Localization.Away h) :=
    ((algebraMap A (Localization.Away h)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
  Algebra.Etale (MvPolynomial (Fin g) R) (Localization.Away h)
def pt {R A Ω : Type} [CommRing R] [CommRing A] [Algebra R A] [Field Ω] [Algebra R Ω] (a : A →ₐ[R] Ω) :
    TensorProduct R Ω A →ₐ[Ω] Ω :=
  Algebra.TensorProduct.lift (AlgHom.id Ω Ω) a (fun _ _ => Commute.all _ _)
end GlobalTheory.DenseSec


