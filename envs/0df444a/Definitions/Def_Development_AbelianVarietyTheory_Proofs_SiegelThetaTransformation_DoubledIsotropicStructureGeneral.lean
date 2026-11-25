-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T13:14:45.528305+00:00
-- url     : https://prove2.me/theorems/4256c646-8b4a-5269-9828-1e714aa5003b
-- title:
--   Doubled Isotropic Structure General
-- statement:
--   Definitions and structural lemmas for Doubled Isotropic Structure General, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledIsotropicStructureGeneral.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianPairingAlgebra_herm_symm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply


set_option autoImplicit false
namespace GlobalTheory
open Module
namespace DoubledSpace
variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W] {σ : E →+* E}
def form (h : W →ₗ[E] W →ₛₗ[σ] E) : (W × W) →ₗ[E] (W × W) →ₛₗ[σ] E :=
  LinearMap.mk₂'ₛₗ (RingHom.id E) σ (fun p q => h p.1 q.1 - h p.2 q.2)
    (fun p p' q => by simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]; ring)
    (fun c p q => by simp [mul_sub])
    (fun p q q' => by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring)
    (fun c p q => by simp [mul_sub])
@[simp] theorem form_apply (h : W →ₗ[E] W →ₛₗ[σ] E) (p q : W × W) :
    form h p q = h p.1 q.1 - h p.2 q.2 := rfl
def left (I : Submodule E (W × W)) : Submodule E W := I.comap (LinearMap.inl E W W)
def right (I : Submodule E (W × W)) : Submodule E W := I.comap (LinearMap.inr E W W)
@[simp] theorem mem_left {I : Submodule E (W × W)} {x : W} : x ∈ left I ↔ (x, 0) ∈ I := Iff.rfl
@[simp] theorem mem_right {I : Submodule E (W × W)} {y : W} : y ∈ right I ↔ (0, y) ∈ I := Iff.rfl
section Isotropic
variable {h : W →ₗ[E] W →ₛₗ[σ] E} {I : Submodule E (W × W)}
variable [FiniteDimensional E W] (hσ : Function.Involutive σ) (hh : ∀ x y, σ (h x y) = h y x)
  (hn : ∀ x, (∀ y, h x y = 0) → x = 0) (hI : ∀ p ∈ I, ∀ q ∈ I, form h p q = 0)
  (hd : finrank E I = finrank E W)
include hσ hh hn hI hd
end Isotropic
abbrev Reduced (h : W →ₗ[E] W →ₛₗ[σ] E) (X : Submodule E W) : Type _ :=
  X.orthogonalBilin h ⧸ X.submoduleOf (X.orthogonalBilin h)
def reducedForm (h : W →ₗ[E] W →ₛₗ[σ] E) (hh : ∀ x y, σ (h x y) = h y x) (X : Submodule E W) :
    Reduced h X →ₗ[E] Reduced h X →ₛₗ[σ] E :=
  (h.domRestrict₁₂ (X.orthogonalBilin h) (X.orthogonalBilin h)).liftQ₂ _ _
    (fun x hx => LinearMap.ext fun y => y.2 x.1 hx)
    (fun y hy => LinearMap.ext fun x => by
      have : h y.1 x.1 = 0 := x.2 y.1 hy
      change h x.1 y.1 = 0
      rw [← hh, this, map_zero])
def glue (h : W →ₗ[E] W →ₛₗ[σ] E) (X X' : Submodule E W) (φ : Reduced h X →ₗ[E] Reduced h X') :
    Submodule E (W × W) :=
  (φ.graph.comap ((Submodule.mkQ _).prodMap (Submodule.mkQ _))).map
    ((X.orthogonalBilin h).subtype.prodMap (X'.orthogonalBilin h).subtype)
section Glue
variable {h : W →ₗ[E] W →ₛₗ[σ] E} {X X' : Submodule E W}
variable [FiniteDimensional E W] (hσ : Function.Involutive σ) (hh : ∀ x y, σ (h x y) = h y x)
  (hn : ∀ x, (∀ y, h x y = 0) → x = 0)
include hσ hh hn
end Glue
end DoubledSpace
open DoubledSpace
section CM
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix LocalLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
theorem hermPairing_conj {G : Matrix (Fin N) (Fin N) E} (hG : ∀ a b, cc (G a b) = G b a)
    (x y : Fin N → E) :
    (IsCMField.complexConj E : E →+* E) (hermPairing G x y) = hermPairing G y x :=
  HermitianPairingAlgebra.herm_symm hG x y
end CM
end GlobalTheory


