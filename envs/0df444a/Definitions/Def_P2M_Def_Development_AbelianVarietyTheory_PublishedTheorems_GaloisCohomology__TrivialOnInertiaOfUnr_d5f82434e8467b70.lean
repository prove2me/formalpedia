-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__TrivialOnInertiaOfUnr_d5f82434e8467b70
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__TrivialOnInertiaOfUnr_d5f82434e8467b70
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T18:33:47.395327+00:00
-- url     : https://prove2.me/theorems/5d210b68-b71b-47e4-b9ca-46964c05a772
-- title:
--   Trivial On Inertia Of Unr
-- statement:
--   Definitions and structural lemmas for Trivial On Inertia Of Unr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/TrivialOnInertiaOfUnr.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.GalOfCusp
open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open scoped Matrix
section Polarization
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {k : Type} [Field k] {a : ℕ}
def IsConjDual (c : Ω ≃+* Ω) (r : G E Ω →* GL (Fin a) k) (μ : G E Ω →* kˣ) : Prop :=
  ∃ P : GL (Fin a) k, ∀ g g' : G E Ω, (∀ x, g' x = c (g (c.symm x))) →
    (r g' : Matrix (Fin a) (Fin a) k) =
      (μ g : k) • ((P : Matrix (Fin a) (Fin a) k) * (r g⁻¹ : Matrix (Fin a) (Fin a) k)ᵀ *
        ((P⁻¹ : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
variable (E Ω) in

def cycBar (l : ℕ) [Fact l.Prime] : G E Ω →* (Qbar l)ˣ :=
  (Units.map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom).comp (cycZ E Ω l)
end Polarization
section Record
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N)
def RegAlgShift {a : ℕ} (π : A.CG a) (s : ℝ) : Prop :=
  ∀ τ, (A.infG π τ).Nodup ∧ ∀ z ∈ A.infG π τ, ∃ m : ℤ, z + (s : ℂ) = (m : ℂ) + ((a : ℂ) - 1) / 2
def TrivialOnInertia {w : PlE H} (L : A.LP w) : Prop :=
  ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol L σ = (X - 1) ^ A.lpDim L
structure IsAttached (i : N.Loc) {a : ℕ} (π : A.CG a) (s : ℝ) (r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) :
    Prop where

  cont : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar (N.l i)))

  ss : IsSSRep r

  pol : ∀ c : N.Om ≃+* N.Om, IsCMConjOm H.E N.Om c → ∀ m : ℤ, (m : ℝ) = 2 * s →
    IsConjDual c r (cycBar H.E N.Om (N.l i) ^ (1 - (a : ℤ) + m))

  away : ∀ w, w ∉ placesOver H.E (N.l i) → A.wdOf i r w = A.lpTw (A.locG π w) (s + (1 - (a : ℝ)) / 2)

  pure : ∀ w, w ∉ placesOver H.E (N.l i) → A.tempered (A.lpTw (A.wdOf i r w) (((a : ℝ) - 1) / 2 - s))

  deRham : ∀ w ∈ placesOver H.E (N.l i), A.IsdRW i r w

  jumps : ∀ τ : H.E →+* Qbar (N.l i), (A.jumpsW i r τ).map (fun n : ℤ => (n : ℂ)) =
    (A.infG π ((A.iotaQC i).toRingHom.comp τ)).map fun z => -(z + (s : ℂ)) + ((a : ℂ) - 1) / 2

  iwahori : ∀ w ∈ placesOver H.E (N.l i), TrivialOnInertia A (A.locG π w) →
    A.wdOf i r w = A.lpTw (A.locG π w) (s + (1 - (a : ℝ)) / 2)

  crys : ∀ w ∈ placesOver H.E (N.l i), A.unr (A.locG π w) → A.IsCrysW i r w
def Reading : Prop :=
  ∀ (i : N.Loc) (a : ℕ), 1 ≤ a → ∀ π : A.CG a, A.csd π → ∀ s : ℝ, RegAlgShift A π s →
    ∃ r, IsAttached A i π s r
variable {A}
variable {i : N.Loc} {a : ℕ} {π : A.CG a} {s : ℝ} {r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))}
end Record
end GlobalTheory.GalOfCusp
end


