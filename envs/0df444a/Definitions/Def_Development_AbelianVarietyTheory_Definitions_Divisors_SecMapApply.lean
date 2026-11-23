-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_SecMapApply
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_SecMapApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:49.818859+00:00
-- url     : https://prove2.me/theorems/48caec96-0f27-4241-8446-69e1bccf595a
-- title:
--   Sec Map Apply
-- statement:
--   Definitions and structural lemmas for Sec Map Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/SecMapApply.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.WeilM
open scoped Matrix
namespace GlobalTheory.LinPair
variable {k : Type} [Field k] [Invertible (2 : k)] {E : Type} [Field E] [Algebra k E] (c : E →ₐ[k] E)
  {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]
  [TopologicalSpace k]
def IsYInv (ψ : AddChar k ℂ) {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} (d : Darboux (symp c ξ JA JB) κ)
    (Cy : Matrix β ν E) (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ z : Matrix α ν E, ∀ φ ∈ SB (κ → k), l (d.rho ψ (z * Cyᵀ) φ) = l φ
def IsYForm (ψ : AddChar k ℂ) {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} (d : Darboux (symp c ξ JA JB) κ)
    (Cy : Matrix β ν E) (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  IsYInv c ψ d Cy l ∧ ∃ φ ∈ SB (κ → k), l φ ≠ 0
structure IsLinPair [IsTopologicalRing k] [LocallyCompactSpace k] [TopologicalSpace E] [IsModuleTopology k E]
    (ψ : AddChar k ℂ) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (d : Darboux (symp c ξ JA JB) κ) (χ : Eˣ →* Circle)
    (Cy : Matrix β ν E) (om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ)) : Prop where
  split : IsUWeilSplit c (sbClass k) ψ ξ JA JB d χ Cy (om.comp (MonoidHom.inr _ _))
  pres : ∀ g : UG c JA, ∀ φ ∈ SB (κ → k), om (g, 1) φ ∈ SB (κ → k)
  impl : ∀ (g : UG c JA) (w : Matrix α β E), ∀ φ ∈ SB (κ → k),
    om (g, 1) (d.rho ψ w φ) = d.rho ψ (((g : GL α E) : Matrix α α E) * w) (om (g, 1) φ)
  lin : ∀ l, IsYInv c ψ d Cy l → ∀ g : UG c JA, ∀ φ ∈ SB (κ → k), l (om (g, 1) φ) = l φ
section Abstract
variable {G H Y : Type} [Group G] [Group H]
def secMap (om : G × H →* Module.End ℂ (Y → ℂ)) (l : (Y → ℂ) →ₗ[ℂ] ℂ) : (Y → ℂ) →ₗ[ℂ] (H → ℂ) :=
  LinearMap.pi fun h => l ∘ₗ om (1, h)
def secSpace [TopologicalSpace Y] (om : G × H →* Module.End ℂ (Y → ℂ)) (l : (Y → ℂ) →ₗ[ℂ] ℂ) : Submodule ℂ (H → ℂ) :=
  (SB Y).map (secMap om l)
def locAug [TopologicalSpace Y] (om : G × H →* Module.End ℂ (Y → ℂ)) : Submodule ℂ (Y → ℂ) :=
  Submodule.span ℂ {z | ∃ g : G, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ}
def IsCoinvQuot {G' Y' : Type} [Group G'] [TopologicalSpace Y] [TopologicalSpace Y'] (om : G × H →* Module.End ℂ (Y → ℂ))
    (om' : G' × H →* Module.End ℂ (Y' → ℂ)) : Prop :=
  locAug om' ≠ SB Y' ∧
  (∀ N : Submodule ℂ (Y' → ℂ), locAug om' ≤ N → N ≤ SB Y' → (∀ h : H, ∀ φ ∈ N, om' (1, h) φ ∈ N) → N = locAug om' ∨ N = SB Y') ∧
  ∃ p : (Y → ℂ) →ₗ[ℂ] ((Y' → ℂ) ⧸ locAug om'), (SB Y).map p = (SB Y').map (locAug om').mkQ ∧ locAug om ≤ LinearMap.ker p ∧
    ∀ h : H, ∀ φ ∈ SB Y, ∀ φ' ∈ SB Y', p φ = (locAug om').mkQ φ' → p (om (1, h) φ) = (locAug om').mkQ (om' (1, h) φ')
end Abstract
def IsWittStep {a a' : ℕ} (r : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JA' : Matrix (Fin a') (Fin a') E) : Prop :=
  a = a' + 2 * r ∧ ∃ P : Matrix (Fin a) (Fin a' ⊕ (Fin r ⊕ Fin r)) E,
    Pᵀ * JA * P.map c = (Matrix.fromBlocks JA' 0 0 (Matrix.fromBlocks 0 1 1 0) :
      Matrix (Fin a' ⊕ (Fin r ⊕ Fin r)) (Fin a' ⊕ (Fin r ⊕ Fin r)) E)
def LocalCompl : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
  ∀ (n a a' r d : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JA' : Matrix (Fin a') (Fin a') E) (JB : Matrix (Fin d) (Fin d) E)
    (Cy : Matrix (Fin d) (Fin n) E), IsHerm c JA → IsHerm c JA' → (∀ i j, c (JB j i) = -JB i j) → IsLagr c JB Cy →
    JB.det ≠ 0 → a + a' = 2 * n → 0 < r → IsWittStep c r JA JA' →
  ∀ χ : Eˣ →* Circle, Continuous χ → ResEtaPow (R := k) ⊥ χ a →
  ∀ (κ κ' : Type) [Fintype κ] [Fintype κ'] (co : Darboux (symp c (-1) JA JB) κ) (co' : Darboux (symp c (-1) JA' JB) κ')
    (om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ)) (om' : UG c JA' × UG c JB →* Module.End ℂ ((κ' → k) → ℂ)),
    IsUWeilPair c (sbClass k) ψ (-1) JA JB co χ 1 om → IsUWeilPair c (sbClass k) ψ (-1) JA' JB co' χ 1 om' →
    IsCoinvQuot om om'
end GlobalTheory.LinPair
end


