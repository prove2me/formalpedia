-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvHopfOfTensorLocal
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvHopfOfTensorLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:20:05.194685+00:00
-- url     : https://prove2.me/theorems/0af87da8-17e2-4630-971e-6eee14aba218
-- title:
--   Ev Hopf Of Tensor Local
-- statement:
--   Definitions and structural lemmas for Ev Hopf Of Tensor Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvHopfOfTensorLocal.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvHopfStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
set_option linter.style.haveILetI false
namespace GlobalTheory.EvHopf
def TensorLocal : Prop :=
  ∀ (O A A' : Type) [CommRing O] [CommRing A] [CommRing A'] [IsLocalRing O] [IsLocalRing A]
    [IsLocalRing A'] [Algebra O A] [Algebra O A'] [Module.Finite O A] [Module.Finite O A'],
    (A →ₐ[O] O) → (A' →ₐ[O] O) → IsLocalRing (A ⊗[O] A')
variable {R₀ : Type} [CommRing R₀]
def secAlg {O A : LAlg R₀} (s : LHom O A) (φ : LHom A O) (h : φ.comp s = LHom.id O) :
    letI := algOf s; (A : Type) →ₐ[(O : Type)] (O : Type) :=
  letI := algOf s
  { φ.1.toRingHom with
    commutes' := fun o => congrArg (fun f : LHom O O => f.1 o) h }
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp)
def IsPt (t : Nb p g) (i : D.fin.ι) (φ : LHom (D.fin.AAx i) Tw.O) : Prop :=
  φ.comp (D.fin.sO i) = LHom.id Tw.O ∧ B.map φ (D.fin.y i) = ptOf B D.L.τ t
variable (C : Type) [Field C] [Algebra (Tw.O : Type) C]
end GlobalTheory.EvHopf


