-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominator
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominator
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:38:36.400749+00:00
-- url     : https://prove2.me/theorems/02a6dcbc-cf42-4586-a7d9-5dc26cb84169
-- title:
--   Embedding Compatible With Weil And Denominator
-- statement:
--   Definitions and structural lemmas for Embedding Compatible With Weil And Denominator, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EmbeddingCompatibleWithWeilAndDenominator.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
namespace GlobalTheory.SW.Emb
noncomputable section
section Corner
variable {R S : Type} [CommRing R] [CommRing S] {N : ℕ}
def cor (c : R) (A : Matrix (Fin N) (Fin N) R) : Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  Matrix.of fun i j => Fin.cases (Fin.cases c (fun _ => 0) j) (fun i' => Fin.cases 0 (A i') j) i
@[simp] theorem corner_embedding_succ_succ (c : R) (A : Matrix (Fin N) (Fin N) R) : cor c A 0 0 = c := rfl
@[simp] theorem cor_zs (c : R) (A : Matrix (Fin N) (Fin N) R) (j : Fin N) :
    cor c A 0 j.succ = 0 := rfl
@[simp] theorem cor_sz (c : R) (A : Matrix (Fin N) (Fin N) R) (i : Fin N) :
    cor c A i.succ 0 = 0 := rfl
@[simp] theorem cor_ss (c : R) (A : Matrix (Fin N) (Fin N) R) (i j : Fin N) :
    cor c A i.succ j.succ = A i j := rfl
end Corner
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
def emb (γ : M2 E N) : M2 E (N + 1) :=
  Matrix.fromBlocks (cor 1 γ.toBlocks₁₁) (cor 0 γ.toBlocks₁₂) (cor 0 γ.toBlocks₂₁)
    (cor 1 γ.toBlocks₂₂)
def corZ (s : ℂ) (Z : CM Ψ N N) : CM Ψ (N + 1) (N + 1) := fun τ => cor s (Z τ)
def corV (z : CM Ψ n N) : CM Ψ n (N + 1) := fun τ => Matrix.of fun k => Fin.cons 0 (z τ k)
abbrev up (N : ℕ) : Fin N ⊕ Fin N → Fin (N + 1) ⊕ Fin (N + 1) := Sum.map Fin.succ Fin.succ
def extV (E : Type) [Field E] (N : ℕ) :
    (Fin N ⊕ Fin N → E) →ₗ[E] (Fin (N + 1) ⊕ Fin (N + 1) → E) where
  toFun v := Sum.elim (Fin.cons 0 fun a => v (Sum.inl a)) (Fin.cons 0 fun a => v (Sum.inr a))
  map_add' v w := by
    ext (i | i) <;> refine Fin.cases ?_ (fun i => ?_) i <;> simp
  map_smul' c v := by
    ext (i | i) <;> refine Fin.cases ?_ (fun i => ?_) i <;> simp
end
end GlobalTheory.SW.Emb


