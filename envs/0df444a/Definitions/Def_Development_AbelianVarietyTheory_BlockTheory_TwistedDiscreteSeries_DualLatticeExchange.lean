-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLatticeExchange
-- name    : Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLatticeExchange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:57.822808+00:00
-- url     : https://prove2.me/theorems/27e318f8-26c2-4f00-ab80-d6122142ed97
-- title:
--   Dual Lattice Exchange
-- statement:
--   Definitions and structural lemmas for Dual Lattice Exchange, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/DualLatticeExchange.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.DualLatticeExchange
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair
section Defs
variable {k : Type} [Field k] [ValuativeRel k] {n : Type} [Fintype n]
def dualLat (L : Submodule 𝒪[k] (n → k)) : Submodule 𝒪[k] (n → k) where
  carrier := {u | ∀ x ∈ L, u ⬝ᵥ x ∈ 𝒪[k]}
  add_mem' hu hv x hx := by
    rw [add_dotProduct]
    exact add_mem (hu x hx) (hv x hx)
  zero_mem' x _ := by
    rw [zero_dotProduct]
    exact zero_mem _
  smul_mem' s u hu x hx := by
    have : (s • u) ⬝ᵥ x = (s : k) * (u ⬝ᵥ x) := smul_dotProduct (s : k) u x
    rw [this]
    exact mul_mem s.2 (hu x hx)
def intPart (L : Submodule 𝒪[k] (n → k)) (u : n → k) : Submodule 𝒪[k] (n → k) where
  carrier := {x | x ∈ L ∧ u ⬝ᵥ x ∈ 𝒪[k]}
  add_mem' hx hy := ⟨add_mem hx.1 hy.1, by
    rw [dotProduct_add]
    exact add_mem hx.2 hy.2⟩
  zero_mem' := ⟨zero_mem _, by
    rw [dotProduct_zero]
    exact zero_mem _⟩
  smul_mem' s x hx := ⟨L.smul_mem s hx.1, by
    have : u ⬝ᵥ (s • x) = (s : k) * (u ⬝ᵥ x) := dotProduct_smul (s : k) u x
    rw [this]
    exact mul_mem s.2 hx.2⟩
end Defs
section Statements
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def GluedPrimitive : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (q : Unif k) (L : Submodule 𝒪[k] (n → k)) (f : n → k),
    IsGlue L f → 1 ≤ p → p ≤ c → ∀ i j : Fin c, j.val = i.val + 1 →
      (fun g : GL (n ⊕ Fin c) k => g.val (Sum.inr i) (Sum.inr j)) ''
        ((N k n c p ⊓ latStab (gluedLat q c p L f) : Subgroup (GL (n ⊕ Fin c) k)) : Set (GL (n ⊕ Fin c) k)) =
        (𝒪[k] : Set k)
def GluedExchange : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (q : Unif k) (ψ : AddChar k Circle)
    (L : Submodule 𝒪[k] (n → k)) (f : n → k), IsGlue L f → 2 ≤ p → p ≤ c →
    ∀ u₁ ∈ dualLat L, q.inv • u₁ ∉ dualLat L → ∀ l₀ ∈ L, q.inv * (u₁ ⬝ᵥ l₀ - 1) ∈ 𝒪[k] →
      IsGlue (intPart L (q.inv • u₁)) l₀ ∧
      ∃ g ∈ N k n c (p - 1),
        g.val *ᵥ avec k n c p =
          avec k n c p + inX k n c (q.1 • f) + ((q.inv • u₁) ⬝ᵥ (q.1 • f)) • avec k n c (p - 1) ∧
        (∀ i, 1 ≤ i → i ≤ c → i ≠ p → g.val *ᵥ avec k n c i = avec k n c i) ∧
        (∀ x : n → k, g.val *ᵥ inX k n c x = inX k n c x) ∧
        ψ (simpleSum g) = ψ ((q.inv • u₁) ⬝ᵥ (q.1 • f)) ∧
        rowE c (p - 1) (q.inv • u₁) • gluedLat q c p L f =
          g • gluedLat q c (p - 1) (intPart L (q.inv • u₁)) l₀
def FunctionalExchange [MeasurableSpace k] [BorelSpace k] : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (q : Unif k) (ψ : AddChar k Circle) (hψ : HasConductor ψ 1)
    (ν : Measure k), ν.IsAddHaarMeasure →
  ∀ (V A : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A]
    (π : Representation ℂ (GL n k) V) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (M₀ : Submodule 𝒪[k] (n ⊕ Fin c → k)) [M₀.IsLattice k] (v : sphVecs σ M₀)
    (b : V →ₗ[ℂ] A →ₗ[ℂ] ℂ), 2 ≤ p → p ≤ c → IsPos ψ (p - 1) π σ b →
    (∀ (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (f : n → k), IsGlue L f →
      (∀ φ : V,
        (∀ u : n → k, b φ (σ (rowE c (p - 1) u) (vecAt σ v (gluedLat q c p L f))) ≠ 0 → q.1 • u ∈ dualLat L) ∧
        (∀ u : n → k, ∀ u' ∈ dualLat L, b φ (σ (rowE c (p - 1) (u + u')) (vecAt σ v (gluedLat q c p L f))) =
          b φ (σ (rowE c (p - 1) u) (vecAt σ v (gluedLat q c p L f)))) ∧
        Integrable (fun u : n → k => b φ (σ (rowE c (p - 1) u) (vecAt σ v (gluedLat q c p L f))))
          (Measure.pi fun _ => ν) ∧
        (∀ u ∈ dualLat L, b φ (σ (rowE c (p - 1) u) (vecAt σ v (gluedLat q c p L f))) =
          b φ (vecAt σ v (gluedLat q c p L f)))) ∧
      (∀ Φ ∈ EqForm π, Φ ∈ Mram k n V → ∀ P₀ : Pair k n,
        b (Φ P₀) (vecAt σ v (gluedLat q c p L f)) = 0 ∧
        exUp ν (p - 1) σ (b (Φ P₀)) (vecAt σ v (gluedLat q c p L f)) =
          (((Measure.pi fun _ : n => ν).real (dualLat L : Set (n → k)) : ℝ) : ℂ) *
            ∑ Q ∈ withLat L, resChar ψ hψ q (Q.ev (q.1 • f)) * b (Φ P₀) (vecAt σ v (Q.glued q c (p - 1))))) ∧
    (3 ≤ Fintype.card n → ∀ Φ ∈ EqForm π, Φ ∈ Mram k n V → ∀ P₀ : Pair k n,
      exUp ν (p - 1) σ (b (Φ P₀)) (vecAt σ v (P₀.glued q c p)) =
        (((Measure.pi fun _ : n => ν).real (dualLat P₀.ker : Set (n → k)) : ℝ) : ℂ) *
          (((resCard k : ℝ) ^ ((p : ℝ) - 1 - ((c : ℝ) + 1) / 2) : ℝ) : ℂ) *
          b (dia (-1 : 𝓀[k]ˣ) (FFStar q (resChar ψ hψ q) Φ) P₀) (vecAt σ v (P₀.glued q c (p - 1))))
end Statements
def LevelPrimeExchange : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k], GluedPrimitive k ∧ GluedExchange k ∧ FunctionalExchange k
section Examples
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
example (c p : ℕ) (u x : n → k) :
    (rowE c p u).val *ᵥ inX k n c x = inX k n c x + (u ⬝ᵥ x) • avec k n c p := by
  ext (i | i)
  · simp [rowE, lowU, inX, avec, fromBlocks_mulVec]
  · by_cases h : i.val + 1 = p <;> simp [rowE, lowU, inX, avec, fromBlocks_mulVec, mulVec, dotProduct, h]
example : dualLat (stdLat k n) = stdLat k n := by
  ext u
  refine ⟨fun h => mem_stdLat.2 fun i => ?_, fun h x hx => ?_⟩
  · have := h (Pi.single i 1) (mem_stdLat.2 fun j => by
      rw [Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _])
    simpa using this
  · exact sum_mem fun i _ => mul_mem (mem_stdLat.1 h i) (mem_stdLat.1 hx i)
end Examples
end GlobalTheory.IndefiniteRowSideFullHecke.DualLatticeExchange


