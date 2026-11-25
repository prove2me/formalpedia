-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ThetaQSurj
-- name    : ReciprocityTheory_DualLattices_ThetaQSurj
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T17:38:39.715619+00:00
-- url     : https://prove2.me/theorems/a8adab1f-9b6a-4aac-9e00-f3922a5e938d
-- title:
--   Theta QSurj
-- statement:
--   Definitions and structural lemmas for Theta QSurj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ThetaQSurj.lean

import Definitions.Def_ReciprocityTheory_DualLattices_MulVecMemPP
import Theorems.Thm_ReciprocityTheory_PGsh_Up_mem_pP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
section F3c
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp}
def bvec (U : UnramData p g v R O σ cp H) (τ : Fin U.m) (s : Fin (U.r τ)) : Fin g → R :=
  ((U.rank τ).some.symm (Pi.single s 1)).1
def thetaL (U : UnramData p g v R O σ cp H) (τ : Fin U.m) : (Fin g → R) →ₗ[R] (Fin (U.r τ) → R) where
  toFun l s := l ⬝ᵥ bvec U τ s
  map_add' l l' := by funext s; simp [add_dotProduct]
  map_smul' r l := by funext s; simp [smul_dotProduct]
def redP (n : ℕ) : (Fin n → R) →ₗ[R] (Fin n → R ⧸ Ideal.span {(p : R)}) :=
  LinearMap.pi fun s => (Ideal.span {(p : R)}).mkQ ∘ₗ LinearMap.proj s
lemma redP_pP {n : ℕ} {w : Fin n → R}
    (hw : w ∈ Ideal.span {(p : R)} • (⊤ : Submodule R (Fin n → R))) : redP (p := p) n w = 0 := by
  obtain ⟨w', rfl⟩ := (mem_pP w).1 hw
  funext s
  show (Ideal.span {(p : R)}).mkQ (((p : R) • w') s) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Pi.smul_apply, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
def thetaQ (U : UnramData p g v R O σ cp H) (τ : Fin U.m) :
    LieDualModP p R g →ₗ[R] (Fin (U.r τ) → R ⧸ Ideal.span {(p : R)}) :=
  (Ideal.span {(p : R)} • (⊤ : Submodule R (Fin g → R))).liftQ (redP (U.r τ) ∘ₗ thetaL U τ)
    (fun w hw => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      obtain ⟨w', rfl⟩ := (mem_pP w).1 hw
      rw [map_smul]
      exact redP_pP ((mem_pP _).2 ⟨_, rfl⟩))
end F3c
end ReciprocityTheory.PGsh.Up


