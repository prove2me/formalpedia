-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:08.856+00:00
-- url     : https://prove2.me/theorems/f7cd2655-0381-4e4d-a450-f92da80ea6c6
-- title:
--   Sum Rho Eq Trace
-- statement:
--   Definitions and structural lemmas for Sum Rho Eq Trace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SumRhoEqTrace.lean

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.ThW
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
def toA (x : ι → F) : ι → A F := fun j => algebraMap F (A F) (x j)
theorem oh_add {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x + y ∈ Oh F :=
  fun v => add_mem (hx v) (hy v)
theorem oh_zero : (0 : A F) ∈ Oh F := fun _ => zero_mem _
theorem oh_neg {x : A F} (hx : x ∈ Oh F) : -x ∈ Oh F := fun v => neg_mem (hx v)
variable (ι F) in

def latN (N : ℕ) : AddSubgroup (ι → A F) where
  carrier := {x | ∀ i, ∃ y ∈ Oh F, x i = (N : A F) * y}
  add_mem' := by
    intro a b ha hb i
    obtain ⟨y, hy, e⟩ := ha i
    obtain ⟨z, hz, e'⟩ := hb i
    exact ⟨y + z, oh_add hy hz, by simp [e, e', mul_add]⟩
  zero_mem' := fun i => ⟨0, oh_zero, by simp⟩
  neg_mem' := by
    intro a ha i
    obtain ⟨y, hy, e⟩ := ha i
    exact ⟨-y, oh_neg hy, by simp [e]⟩
def indC (N : ℕ) (a : ι → F) : (ι → A F) → ℂ :=
  Set.indicator {x | x - toA a ∈ latN F ι N} fun _ => 1
def emb (ρ : InfinitePlace F → (F →+* ℝ)) (x : ι → F) : ι × InfinitePlace F → ℝ :=
  fun p => ρ p.2 (x p.1)
def cur (x : ι × InfinitePlace F → ℝ) : InfinitePlace F → ι → ℝ := fun w i => x (i, w)
def DM [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) :
    Matrix (ι × InfinitePlace F) (ι × InfinitePlace F) ℝ :=
  blockDiagonal fun w => B.map (ρ w)
def ZM [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (τ : InfinitePlace F → ℂ) :
    Matrix (ι × InfinitePlace F) (ι × InfinitePlace F) ℂ :=
  blockDiagonal fun w => fun i j =>
    ((τ w).re : ℂ) * ((ρ w (B i j) : ℝ) : ℂ) + Complex.I * ((τ w).im : ℂ) * ((P w i j : ℝ) : ℂ)
def EM (ρ : InfinitePlace F → (F →+* ℝ)) (b : InfinitePlace F → 𝓞 F) :
    Matrix (InfinitePlace F) (InfinitePlace F) ℝ :=
  fun w v => ρ w (b v : F)
def gM [DecidableEq (InfinitePlace F)] (ρ : InfinitePlace F → (F →+* ℝ))
    (b : InfinitePlace F → 𝓞 F) (N : ℕ) :
    Matrix (ι × InfinitePlace F) (ι × InfinitePlace F) ℝ :=
  (N : ℝ) • ((1 : Matrix ι ι ℝ) ⊗ₖ EM ρ b)
end GlobalTheory.CompanionTheory.SW.ThW


