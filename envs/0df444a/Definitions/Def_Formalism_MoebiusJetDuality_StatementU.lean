-- Prove2me | Definitions.Def_Formalism_MoebiusJetDuality_StatementU
-- name    : Formalism_MoebiusJetDuality_StatementU
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:31.479435+00:00
-- url     : https://prove2.me/theorems/fce89406-6f10-4f4e-a01d-870ebfcf75ac
-- title:
--   Statement U
-- statement:
--   Definitions and structural lemmas for Statement U, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MoebiusJetDuality/StatementU.lean

import Definitions.Def_Formalism_MoebiusJetDuality_StatementV
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MJ
open Matrix
open scoped ComplexOrder
def blk {p q : ℕ} (A : GL (Fin p) ℂ) (D : GL (Fin q) ℂ) : GL (Fin p ⊕ Fin q) ℂ where
  val := fromBlocks (A : Matrix (Fin p) (Fin p) ℂ) 0 0 (D : Matrix (Fin q) (Fin q) ℂ)
  inv := fromBlocks ((A⁻¹ : GL (Fin p) ℂ) : Matrix (Fin p) (Fin p) ℂ) 0 0
    ((D⁻¹ : GL (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ)
  val_inv := by simp [fromBlocks_multiply]
  inv_val := by simp [fromBlocks_multiply]
def moeb {p q : ℕ} (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p) (Fin q) ℂ :=
  (g.toBlocks₁₁ * z + g.toBlocks₁₂) * (g.toBlocks₂₁ * z + g.toBlocks₂₂)⁻¹
def hcDom (p q : ℕ) : Set (Matrix (Fin p) (Fin q) ℂ) :=
  {z | (1 - zᴴ * z).PosDef}
def vecOf {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) : Fin p × Fin q → ℂ := fun x => z x.1 x.2
def moebiusJetDuality : Prop :=
  ∀ (p q : ℕ) (A : GL (Fin p) ℂ) (D : GL (Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ),
    moeb (blk A D : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z =
      (A : Matrix (Fin p) (Fin p) ℂ) * z * ((D⁻¹ : GL (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ)
def moebiusJetDualityReformulated : Prop :=
  ∀ (p q : ℕ) (A : GL (Fin p) ℂ) (D : GL (Fin q) ℂ),
    blk A D ∈ Formalism.UG.Upq p q ↔
      ((A : Matrix (Fin p) (Fin p) ℂ)ᴴ * (A : Matrix (Fin p) (Fin p) ℂ) = 1 ∧
        (D : Matrix (Fin q) (Fin q) ℂ)ᴴ * (D : Matrix (Fin q) (Fin q) ℂ) = 1)
def StabZero : Prop :=
  ∀ (p q : ℕ) (g : GL (Fin p ⊕ Fin q) ℂ), g ∈ Formalism.UG.Upq p q →
    moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0 = 0 → g ∈ Formalism.UG.blockDiag p q
def MoebTangent : Prop :=
  ∀ (p q : ℕ) (A : GL (Fin p) ℂ) (D : GL (Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ),
    vecOf (moeb (blk A D : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) =
      (hcMat (A : Matrix (Fin p) (Fin p) ℂ) ((D⁻¹ : GL (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ)).mulVec
        (vecOf z)
def ActFMoeb : Prop :=
  ∀ (p q r : ℕ) (ρ : (GL (Fin p) ℂ × GL (Fin q) ℂ) →* GL (Fin r) ℂ)
    (k : GL (Fin p) ℂ × GL (Fin q) ℂ) (F : (Fin p × Fin q → ℂ) → (Fin r → ℂ))
    (z : Matrix (Fin p) (Fin q) ℂ),
    actF ρ k F (vecOf z) = ((ρ k : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).mulVec
      (F (vecOf (moeb (((blk k.1 k.2)⁻¹ : GL (Fin p ⊕ Fin q) ℂ) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z)))
def MoebDom : Prop :=
  ∀ (p q : ℕ) (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ),
    g ∈ Formalism.UG.Upq p q → z ∈ hcDom p q →
      IsUnit ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₁ * z +
        (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₂).det ∧
      moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z ∈ hcDom p q
def MoebMul : Prop :=
  ∀ (p q : ℕ) (g h : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ),
    g ∈ Formalism.UG.Upq p q → h ∈ Formalism.UG.Upq p q → z ∈ hcDom p q →
      moeb ((g * h : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z =
        moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
          (moeb (h : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z)
def ZeroMemDom : Prop := ∀ p q : ℕ, (0 : Matrix (Fin p) (Fin q) ℂ) ∈ hcDom p q
end Formalism.MJ


