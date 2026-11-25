-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StComplementLattice
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StComplementLattice
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T02:53:18.963662+00:00
-- url     : https://prove2.me/theorems/82e728a7-ec4c-4479-99e4-921c5b22cb36
-- title:
--   St Complement Lattice
-- statement:
--   Definitions and structural lemmas for St Complement Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StComplementLattice.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section
section Complement
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
def ComplementLattice.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ v₀ w₀ : W, IsHyperbolicPair h v₀ w₀ → ∀ h' : HermitianForm F E (hypComplement h v₀ w₀),
    (∀ x y, h'.toSesq x y = h.toSesq x y) → ∀ D n : ℕ, 0 < n → ∃ D' : ℕ,
      ∀ La : AddSubgroup W, IsDIntegral h D La →
        (∀ x ∈ La, ∃ a ∈ lineCoeffs (E := E) La v₀, ∃ b ∈ lineCoeffs (E := E) La w₀,
          n • x - a • v₀ - b • w₀ ∈ hypComplement h v₀ w₀) →
        IsDIntegral h' D' (La.comap (hypComplement h v₀ w₀).subtype.toAddMonoidHom)
end Complement
section Inhabitants
open GaussianPlane
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


