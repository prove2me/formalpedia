-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:01:07.27323+00:00
-- url     : https://prove2.me/theorems/e5bd2695-4928-4305-aa6d-bfb526c7d7d2
-- title:
--   Has Level Std
-- statement:
--   Definitions and structural lemmas for Has Level Std, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HasLevelStd.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_DefiningCoordinates
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField UpperHalfPlane
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD)
open scoped Classical
namespace GlobalTheory.HilbFam
variable {F : Type} [Field F] [NumberField F]
abbrev Lat (F : Type) [Field F] [NumberField F] : Type := Submodule (𝓞 F) (Fin 2 → F)
def stdLat (F : Type) [Field F] [NumberField F] : Lat F :=
  Submodule.pi Set.univ fun _ ↦ (1 : Submodule (𝓞 F) F)
def HasLevel (N : ℕ) (L : Lat F) : Prop := (∀ x ∈ stdLat F, (N : 𝓞 F) • x ∈ L) ∧ L ≤ stdLat F
def mulMat (L : Lat F) (A : Matrix (Fin 2) (Fin 2) ℤ) : Lat F :=
  L.map ((Matrix.vecMulLinear (A.map (Int.cast : ℤ → F))).restrictScalars (𝓞 F))
def twist (N : ℕ) (L : Lat F) (α : Matrix (Fin 2) (Fin 2) (ZMod N)) : Lat F :=
  mulMat L (α.map (ZMod.cast : ZMod N → ℤ)) ⊔ mulMat (stdLat F) ((N : ℤ) • 1)
def split (𝔞 𝔟 : Frac F) (x : F) : Lat F where
  carrier := {v | v 0 ∈ (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ∧ v 1 - v 0 * x ∈ latM 𝔞}
  add_mem' := fun {v w} hv hw ↦ ⟨Submodule.add_mem _ hv.1 hw.1, by
    have : (v + w) 1 - (v + w) 0 * x = (v 1 - v 0 * x) + (w 1 - w 0 * x) := by simp only [Pi.add_apply]; ring
    rw [this]; exact Submodule.add_mem (latM 𝔞 : Submodule (𝓞 F) F) hv.2 hw.2⟩
  zero_mem' := ⟨Submodule.zero_mem _, by
    have : (0 : Fin 2 → F) 1 - (0 : Fin 2 → F) 0 * x = 0 := by simp
    rw [this]; exact Submodule.zero_mem (latM 𝔞 : Submodule (𝓞 F) F)⟩
  smul_mem' := fun c v hv ↦ ⟨Submodule.smul_mem _ c hv.1, by
    have : (c • v) 1 - (c • v) 0 * x = c • (v 1 - v 0 * x) := by simp only [Pi.smul_apply, smul_sub, smul_mul_assoc]
    rw [this]; exact Submodule.smul_mem (latM 𝔞 : Submodule (𝓞 F) F) c hv.2⟩
def cls (L : Lat F) : Set (Quotient (MulAction.orbitRel (𝓞 F)ˣ (Fin 2 → F))) := {q | q.out ∈ L ∧ q.out ≠ 0}
def coord (b a : Emb F → ℂ) (x : Fin 2 → F) (i : Emb F) : ℂ := (i (x 0) : ℂ) * b i + (i (x 1) : ℂ) * a i
def gTerm (k : ℕ) (σ : ℂ) (b a : Emb F → ℂ) (x : Fin 2 → F) : ℂ :=
  (∏ i, coord b a x i)⁻¹ ^ k * ((‖∏ i, coord b a x i‖ : ℝ) : ℂ) ^ (-2 * σ)
def IsGVal (k : ℕ) (L : Lat F) (b a : Emb F → ℂ) (G : ℂ) : Prop :=
  (k ≠ 2 → HasSum (fun q : cls L ↦ gTerm k 0 b a q.1.out) G) ∧
  (k = 2 → ∃ H : ℂ → ℂ, DifferentiableOn ℂ H {σ : ℂ | -1 / 2 < σ.re} ∧
    (∀ σ : ℂ, 0 < σ.re → HasSum (fun q : cls L ↦ gTerm 2 σ b a q.1.out) (H σ)) ∧ G = H 0)
def gval (k : ℕ) (L : Lat F) (b a : Emb F → ℂ) : ℂ := if h : ∃ G, IsGVal k L b a G then h.choose else 0
def word {I : Type} [Fintype I] (κ : I → ℕ) : List I := Finset.univ.toList.flatMap fun i ↦ List.replicate (κ i) i
def jet (k : ℕ) (L : Lat F) (κ : Emb F → ℕ) (τ c t : ℂ) : ℂ :=
  iterD (word κ) (fun z ↦ (cK F k : ℂ) * gval k L (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c)) 0
def wt (k : ℕ) (κ : Emb F → ℕ) : ℕ := k * Module.finrank ℚ F + 2 * ∑ i, κ i
def hfun (k : ℕ) (L : Lat F) (κ : Emb F → ℕ) (Ch : ℍ → ℂ) (τ : ℍ) : ℂ :=
  jet k L κ τ ((2 * Real.pi * Complex.I) ^ 2 * Ch τ) (-(2 * Real.pi * Complex.I)) / (2 * Real.pi * Complex.I) ^ wt k κ
def rco (k n m : ℕ) : ℤ := (-1) ^ (n - m) * (n.choose m : ℤ) * ((k + m).ascFactorial (n - m) : ℤ)
def lag (k n : ℕ) (c y : ℂ) : ℂ := ∑ m ∈ Finset.range (n + 1), (rco k n m : ℂ) * c ^ (n - m) * y ^ m
def IsCoef (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) : Prop :=
  a 0 = a₀ ∧ (∀ ξ, ξ ≠ 0 → ∃ n : ℤ, a ξ = n) ∧
  (∀ ξ, ξ ≠ 0 → a ξ ≠ 0 → ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ∧ ∀ i : Emb F, 0 < i ξ) ∧
  ∀ w ∈ upperHalf F, HasSum (fun ξ : F ↦ a ξ * qPow ξ w)
    ((cK F k : ℂ) * gval k (split 𝔞 𝔟 0) w 1 / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k)
def eTr (y : F) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F y : ℚ) : ℂ))
def ecoef (N : ℕ) (a : F → ℂ) (x : F) (μ : Emb F → ℕ) (n : ℕ) : ℂ :=
  ∑ᶠ ξ ∈ {ξ : F | (N : ℚ) * Algebra.trace ℚ F ξ = n}, a ξ * eTr (ξ * x) * ∏ i : Emb F, (i ξ : ℂ) ^ μ i
def hser (k N : ℕ) (𝔞 : Frac F) (a : F → ℂ) (x : F) (κ : Emb F → ℕ) (c : ℕ → ℂ) : PowerSeries ℂ :=
  ((omegaFactor 𝔞 : ℂ) ^ k) • ∑ μ ∈ Finset.Iic κ, ((∏ i, rco k (κ i) (μ i) * (-1) ^ μ i : ℤ) : ℂ) •
    (PowerSeries.mk c ^ (∑ i, (κ i - μ i)) * PowerSeries.mk (ecoef N a x μ))
def ZetaVals (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ) : Prop :=
  ∀ C, ∃ Z : ℂ → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C Z ∧ Z (1 - (k : ℂ)) = (z C : ℂ)
end GlobalTheory.HilbFam


