-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_DoublingGramFromBlocks
-- name    : Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_DoublingGramFromBlocks
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:12.002169+00:00
-- url     : https://prove2.me/theorems/7fc1d631-541d-4ce3-a331-3694b882691c
-- title:
--   Doubling Gram From Blocks
-- statement:
--   Definitions and structural lemmas for Doubling Gram From Blocks, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/CharacterAdmissibility/DoublingGramFromBlocks.lean

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAlg
import Theorems.Thm_P2M_PositivityTheory_ThK_SiegelT_map_mul__f92fda10766b
import Theorems.Thm_P2M_PositivityTheory_ThK_SiegelT_map_one__a6a1ccb9bfd7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM PositivityTheory.ThK.SiegelT
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {β β₁ μ ν : Type} [Fintype β] [DecidableEq β] [Fintype β₁] [DecidableEq β₁] [Fintype μ] [DecidableEq μ]
  [Fintype ν] [DecidableEq ν]
variable (c) in

structure Fr (J : Matrix β β E) (J₁ : Matrix β₁ β₁ E) (H : Matrix μ μ E) (ι : Matrix β β₁ E) (Z : Matrix β μ E)
    (π : Matrix β₁ β E) (ρ : Matrix μ β E) : Prop where
  one : ι * π + Z * ρ = 1
  pi : π * ι = 1
  pz : π * Z = 0
  ri : ρ * ι = 0
  rz : ρ * Z = 1
  gii : ιᵀ * J * ι.map c = J₁
  giz : ιᵀ * J * Z.map c = 0
  gzi : Zᵀ * J * ι.map c = 0
  gzz : Zᵀ * J * Z.map c = H
abbrev dd2 {a b : Type} (A : Matrix a b E) : Matrix (a ⊕ a) (b ⊕ b) E := fromBlocks A 0 0 A
variable {J : Matrix β β E} {J₁ : Matrix β₁ β₁ E} {H : Matrix μ μ E} {ι : Matrix β β₁ E} {Z : Matrix β μ E}
  {π : Matrix β₁ β E} {ρ : Matrix μ β E}
theorem doubling_gram_fromBlocks {a b : Type} (A : Matrix β a E) (B : Matrix β b E) :
    (dd2 A)ᵀ * dbl J * (dd2 B).map c = fromBlocks (Aᵀ * J * B.map c) 0 0 (-(Aᵀ * J * B.map c)) := by
  simp only [dbl, fromBlocks_transpose, fromBlocks_map, Matrix.map_zero _ (map_zero c), fromBlocks_multiply]
  simp
theorem Fr.dbl (h : Fr c J J₁ H ι Z π ρ) : Fr c (dbl J) (dbl J₁) (dbl H) (dd2 ι) (dd2 Z) (dd2 π) (dd2 ρ) where
  one := by simp [fromBlocks_multiply, fromBlocks_add, h.one]
  pi := by simp [fromBlocks_multiply, h.pi]
  pz := by simp [fromBlocks_multiply, h.pz]
  ri := by simp [fromBlocks_multiply, h.ri]
  rz := by simp [fromBlocks_multiply, h.rz]
  gii := by rw [doubling_gram_fromBlocks, h.gii]; rfl
  giz := by rw [doubling_gram_fromBlocks, h.giz]; simp
  gzi := by rw [doubling_gram_fromBlocks, h.gzi]; simp
  gzz := by rw [doubling_gram_fromBlocks, h.gzz]; rfl
theorem Fr.mul (h : Fr c J J₁ H ι Z π ρ) (g g' : Matrix β₁ β₁ E) (k k' : Matrix μ μ E) :
    (ι * g * π + Z * k * ρ) * (ι * g' * π + Z * k' * ρ) = ι * (g * g') * π + Z * (k * k') * ρ := by
  have e : ∀ {a b a' b' : Type} [Fintype a] [Fintype b] [Fintype a'] [Fintype b'] (A : Matrix β a E) (x : Matrix a b E)
      (B : Matrix b β E) (A' : Matrix β a' E) (x' : Matrix a' b' E) (B' : Matrix b' β E),
      A * x * B * (A' * x' * B') = A * x * (B * A') * x' * B' := fun A x B A' x' B' => by simp only [Matrix.mul_assoc]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e, e, e, e, h.pi, h.pz, h.ri, h.rz]
  simp [Matrix.mul_assoc]
theorem Fr.gram (h : Fr c J J₁ H ι Z π ρ) (g : Matrix β₁ β₁ E) (k : Matrix μ μ E) :
    (ι * g * π + Z * k * ρ)ᵀ * J * (ι * g * π + Z * k * ρ).map c =
      πᵀ * (gᵀ * J₁ * g.map c) * π.map c + ρᵀ * (kᵀ * H * k.map c) * ρ.map c := by
  have e : ∀ {a a' : Type} [Fintype a] [Fintype a'] (A : Matrix β a E) (x : Matrix a a E)
      (B : Matrix a β E) (A' : Matrix β a' E) (x' : Matrix a' a' E) (B' : Matrix a' β E),
      (A * x * B)ᵀ * J * (A' * x' * B').map c = Bᵀ * (xᵀ * (Aᵀ * J * A'.map c) * x'.map c) * B'.map c :=
    fun A x B A' x' B' => by simp only [transpose_mul, map_mul', Matrix.mul_assoc]
  rw [Matrix.map_add _ (map_add c), transpose_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e, e, e, e,
    h.gii, h.giz, h.gzi, h.gzz]
  simp
def Fr.emb (h : Fr c J J₁ H ι Z π ρ) : UG c J₁ × UG c H →* UG c J where
  toFun p := ⟨⟨ι * p.1.1.1 * π + Z * p.2.1.1 * ρ, ι * (p.1.1⁻¹).1 * π + Z * (p.2.1⁻¹).1 * ρ,
    by rw [h.mul, Units.mul_inv, Units.mul_inv, Matrix.mul_one, Matrix.mul_one, h.one],
    by rw [h.mul, Units.inv_mul, Units.inv_mul, Matrix.mul_one, Matrix.mul_one, h.one]⟩, by
      have e := h.gram 1 1
      rw [Matrix.mul_one, Matrix.mul_one, h.one, transpose_one, transpose_one, transpose_one, map_one', map_one', map_one',
        Matrix.mul_one, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul, Matrix.one_mul] at e
      refine (h.gram _ _).trans (Eq.trans ?_ e.symm)
      rw [show p.1.1.1ᵀ * J₁ * p.1.1.1.map c = J₁ from p.1.2, show p.2.1.1ᵀ * H * p.2.1.1.map c = H from p.2.2]⟩
  map_one' := Subtype.ext (Units.ext (by
    show ι * 1 * π + Z * 1 * ρ = 1
    rw [Matrix.mul_one, Matrix.mul_one, h.one]))
  map_mul' p q := Subtype.ext (Units.ext (h.mul _ _ _ _).symm)
abbrev hyp (ν : Type) [DecidableEq ν] (η : ℤˣ) : Matrix (ν ⊕ ν) (ν ⊕ ν) E := fromBlocks 0 1 (((η : ℤ) : E) • 1) 0
end PositivityTheory.ThKF0.Chr


