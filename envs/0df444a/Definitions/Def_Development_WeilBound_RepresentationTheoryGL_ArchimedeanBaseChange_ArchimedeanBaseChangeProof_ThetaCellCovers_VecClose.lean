-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
-- name    : Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:14.595536+00:00
-- url     : https://prove2.me/theorems/471a60e3-d602-431d-b6c2-b93800187132
-- title:
--   Vec Close
-- statement:
--   Definitions and structural lemmas for Vec Close, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/ThetaCellCovers/VecClose.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
namespace PositivityTheory.Rg.BcB.E1
def Ctx.IsVec (X : Ctx) {ι : Type} (Φ : Matrix ι ι (X.G → ℂ)) (y : X.G) (j : ι) (k : X.Hs ι) : Prop :=
  ∀ l, (k l : X.G → ℂ) =ᵐ[X.ν] fun z => ker X.Γ (Φ l j) z y
def TwoUnif : Prop := ∀ (X : Ctx) (φ : X.G → ℂ) (ε : ℝ), Tst φ → 0 < ε →
  ∃ W ∈ nhds (1 : X.G), ∀ z ∈ W, ∀ w ∈ W, ∀ y, ‖φ (z * y * w) - φ y‖ ≤ ε
def IsBump (X : Ctx) (ψ : X.G → ℂ) : Prop :=
  Tst ψ ∧ (∀ z, ψ z = (‖ψ z‖ : ℝ)) ∧ ∫ z, ‖ψ z⁻¹‖ ∂X.μ = 1
def BumpEx : Prop := ∀ (X : Ctx), ∀ W ∈ nhds (1 : X.G), ∃ ψ, IsBump X ψ ∧ tsupport ψ ⊆ W
def ApproxU : Prop := ∀ (X : Ctx) (φ : X.G → ℂ) (ε : ℝ), Tst φ → 0 < ε → ∃ W ∈ nhds (1 : X.G), ∀ ψ, IsBump X ψ →
  tsupport ψ ⊆ W → ∀ y, ‖cv X.μ φ ψ y - φ y‖ ≤ ε ∧ ‖cv X.μ (adj ψ) (cv X.μ φ ψ) y - φ y‖ ≤ ε
def KerClose : Prop := ∀ (X : Ctx) (Ω : Set X.G) (x y : X.G), IsCompact Ω → ∃ N : ℝ, 0 ≤ N ∧ ∀ (φ φ' : X.G → ℂ) (ε : ℝ),
  Function.support φ ⊆ Ω → Function.support φ' ⊆ Ω → (∀ z, ‖φ z - φ' z‖ ≤ ε) → ‖ker X.Γ φ x y - ker X.Γ φ' x y‖ ≤ N * ε
def VecClose : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (Φ Φ' : Matrix ι ι (X.G → ℂ)) (Ω : Set X.G) (ε : ℝ) (y : X.G) (j : ι)
  (k k' : X.Hs ι), IsCompact Ω → (∀ l, Tst (Φ l j) ∧ Tst (Φ' l j) ∧ Function.support (Φ l j) ⊆ Ω ∧
    Function.support (Φ' l j) ⊆ Ω ∧ ∀ z, ‖Φ l j z - Φ' l j z‖ ≤ ε) → X.IsVec Φ y j k → X.IsVec Φ' y j k' →
  ‖k - k'‖ₑ ^ 2 ≤ Fintype.card ι * (ENNReal.ofReal ε ^ 2 * X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y)
def VecNorm : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (Φ : Matrix ι ι (X.G → ℂ)), (∀ i j, Tst (Φ i j)) →
  ∃ (C : ℝ≥0∞) (Ω : Set X.G), C ≠ ⊤ ∧ IsCompact Ω ∧ ∀ y j k, X.IsVec Φ y j k → ‖k‖ₑ ^ 2 ≤ C * cnt X.Γ Ω y
def VecEx : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (Φ : Matrix ι ι (X.G → ℂ)), (∀ i j, Tst (Φ i j)) →
  ∃ k : X.G → ι → X.Hs ι, (∀ j, Continuous fun y => k y j) ∧ ∀ y j, X.IsVec Φ y j (k y j)
def VecInner : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (Φ : Matrix ι ι (X.G → ℂ)) (y : X.G) (j : ι) (k u : X.Hs ι),
  (∀ i j, Tst (Φ i j)) →
  (X.IsVec Φ y j k → inner ℂ u k = ∑ l, ∫ z, starRingEnd ℂ ((u l : X.G → ℂ) z) * ker X.Γ (Φ l j) z y ∂X.ν) ∧
  (X.IsVec (fun i j => adj (Φ j i)) y j k → inner ℂ k u = ∑ l, ∫ z, ker X.Γ (Φ j l) y z * (u l : X.G → ℂ) z ∂X.ν)
def VecLim : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (Φ : Matrix ι ι (X.G → ℂ)) (T : X.Hs ι →L[ℂ] X.Hs ι) (y : X.G) (j : ι)
  (k : X.Hs ι) (ε : ℝ), (∀ i j, Tst (Φ i j)) → X.IsOp Φ T → X.IsVec Φ y j k → 0 < ε →
  ∃ W ∈ nhds (1 : X.G), ∀ ψ, IsBump X ψ → tsupport ψ ⊆ W → ∀ u, X.IsCol ψ y j u → ‖T u - k‖ ≤ ε
def PtEq : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (Φ₁ Φ₂ Φ : Matrix ι ι (X.G → ℂ)) (T₁ T₂ U : X.Hs ι →L[ℂ] X.Hs ι),
  (∀ i j, Tst (Φ₁ i j)) → (∀ i j, Tst (Φ₂ i j)) → (∀ i j, Tst (Φ i j)) → X.IsOp Φ₁ T₁ → X.IsOp Φ₂ T₂ →
  X.IsOp Φ (T₁ * U * T₂) → ∀ x y i j k₁ k₂, X.IsVec (fun i j => adj (Φ₁ j i)) x i k₁ → X.IsVec Φ₂ y j k₂ →
    ker X.Γ (Φ i j) x y = inner ℂ k₁ (U k₂)
end PositivityTheory.Rg.BcB.E1
end


