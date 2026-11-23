-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_GTBranch
-- name    : Formalism_PeriodIntegrals_GTBranch
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:40.673229+00:00
-- url     : https://prove2.me/theorems/b66ae9ee-7c73-4095-995f-d7f0b3e08846
-- title:
--   GTBranch
-- statement:
--   Definitions and structural lemmas for GTBranch, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/GTBranch.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace PI
open Formalism.BasicNotions MvPolynomial
def blkHom (R : Type) [CommRing R] (n : ℕ) :
    Matrix (Fin n) (Fin n) R →* Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R where
  toFun A := Matrix.fromBlocks A 0 0 1
  map_one' := Matrix.fromBlocks_one
  map_mul' A B := by simp [Matrix.fromBlocks_multiply]
def embGL (R : Type) [CommRing R] (n N : ℕ) (h : n + 1 = N) : GL (Fin n) R →* GL (Fin N) R :=
  Units.map (((Matrix.reindexAlgEquiv R R (finSumFinEquiv.trans (finCongr h))).toAlgHom.toRingHom.toMonoidHom).comp
    (blkHom R n))
def Interlace {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : Prop :=
  ∀ i : Fin n, sg.w i ≤ lam.w ⟨i.1, by omega⟩ ∧ lam.w ⟨i.1 + 1, by omega⟩ ≤ sg.w i
def GTBranch : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N),
    (∀ (mu : DomWeight n) (φ φ' : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ),
      (∀ ψ ∈ ({φ, φ'} : Set _), (∀ s ∈ nablaSq ℂ n mu, ψ s ∈ nablaSq ℂ N lam) ∧
        ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n mu,
          ψ (sqAct ℂ n mu g s) = sqAct ℂ N lam (embGL ℂ n N h g) (ψ s)) →
      (∃ s ∈ nablaSq ℂ n mu, φ' s ≠ 0) →
      Interlace h lam mu ∧ ∃ c : ℂ, ∀ s ∈ nablaSq ℂ n mu, φ s = c • φ' s) ∧
    nablaSq ℂ N lam = ⨆ (mu : DomWeight n) (_ : Interlace h lam mu)
      (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
      (_ : (∀ s ∈ nablaSq ℂ n mu, φ s ∈ nablaSq ℂ N lam) ∧
        ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n mu,
          φ (sqAct ℂ n mu g s) = sqAct ℂ N lam (embGL ℂ n N h g) (φ s)), (nablaSq ℂ n mu).map φ
end PI


