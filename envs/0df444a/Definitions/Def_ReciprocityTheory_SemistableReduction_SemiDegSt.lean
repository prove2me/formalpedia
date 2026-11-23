-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
-- name    : ReciprocityTheory_SemistableReduction_SemiDegSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:14.821606+00:00
-- url     : https://prove2.me/theorems/cba36dc2-669f-4273-bb9c-2b61fa0c9639
-- title:
--   Semi Deg St
-- statement:
--   Definitions and structural lemmas for Semi Deg St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegSt.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CutSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
def wittMat {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) : Matrix (Fin r) (Fin r) K :=
  Matrix.of fun i j =>
    if (i : ℕ) + j + 1 = r ∧ ((i : ℕ) < m ∨ (j : ℕ) < m) then 1
    else if i = j ∧ m ≤ (i : ℕ) ∧ (i : ℕ) + m < r then g i else 0
def WittBasisStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (S : HermForm K r), S.G.det ≠ 0 →
    ∃ (P : Matrix (Fin r) (Fin r) K) (m : ℕ) (g : Fin r → K), P.det ≠ 0 ∧ 2 * m ≤ r ∧
      (P.map S.c)ᵀ * S.G * P = wittMat r m g ∧
      ∀ t : Fin r → K, (∀ i : Fin r, (i : ℕ) < m ∨ r ≤ (i : ℕ) + m → t i = 0) →
        ∑ i, S.c (t i) * g i * t i = 0 → t = 0
def spanIdx {K : Type} [Field K] [NumberField K] {r k : ℕ} (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) : ℕ :=
  (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup
def hGram {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) : Matrix (Fin k) (Fin k) K :=
  Matrix.of fun i j => S.h (b i) (b j)
def LatDegBasisStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r k : ℕ) (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (B : Submodule (𝓞 K) (Fin r → K)) (b b' : Fin k → Fin r → K),
    (∀ σ, (H σ).PosDef) → B.FG → IsKBasisIn B b → IsKBasisIn B b' →
    latDeg H B b = latDeg H B b'
def IntegralIndexStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r k : ℕ) (S : HermForm K r)
    (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K),
    B.FG → IsKBasisIn B b → IsIntegralOn S B → (hGram S b).det ≠ 0 →
    ((spanIdx B b : ℕ) : ℝ) ^ 2 ≤ |((Algebra.norm ℚ (hGram S b).det : ℚ) : ℝ)|
def SelfDualIndexStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)) (b : Fin r → Fin r → K),
    IsLattice L → IsSelfDual S L → IsKBasisIn L b →
    |((Algebra.norm ℚ (hGram S b).det : ℚ) : ℝ)| ≤ ((spanIdx L b : ℕ) : ℝ) ^ 2
def cutSub (K : Type) [Field K] [NumberField K] (r e : ℕ) : Submodule (𝓞 K) (Fin r → K) := UpperTheory.Reformulated.B.FirstCoordinatesSubmodule.cutSub K r e
def projGe (K : Type) [Field K] [NumberField K] (r e : ℕ) : (Fin r → K) →ₗ[𝓞 K] (Fin r → K) where
  toFun x i := if e ≤ (i : ℕ) then x i else 0
  map_add' x y := by
    funext i
    by_cases h : e ≤ (i : ℕ) <;> simp [h]
  map_smul' a x := by
    funext i
    by_cases h : e ≤ (i : ℕ) <;> simp [h]
def diagMet {K : Type} [Field K] [NumberField K] {r : ℕ} (δ : (K →+* ℂ) → Fin r → ℝ) :
    (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ :=
  fun σ => Matrix.diagonal fun i => ((δ σ i : ℝ) : ℂ)
def GradedExtStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r e k k₀ k₁ : ℕ) (δ : (K →+* ℂ) → Fin r → ℝ)
    (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) (b₀ : Fin k₀ → Fin r → K)
    (b₁ : Fin k₁ → Fin r → K),
    (∀ σ i, 0 < δ σ i) → B.FG → IsKBasisIn B b → IsKBasisIn (B ⊓ cutSub K r e) b₀ →
    IsKBasisIn (B.map (projGe K r e)) b₁ →
    latDeg (diagMet δ) B b ≤
      latDeg (diagMet δ) (B ⊓ cutSub K r e) b₀ + latDeg (diagMet δ) (B.map (projGe K r e)) b₁
def AbsDetStatement : Prop :=
  ∀ (n : ℕ) (A C : Matrix (Fin n) (Fin n) ℂ), A.PosDef → C.IsHermitian →
    (∀ v : Fin n → ℂ, ‖star v ⬝ᵥ (C *ᵥ v)‖ ≤ (star v ⬝ᵥ (A *ᵥ v)).re) → ‖C.det‖ ≤ A.det.re
end ReciprocityTheory.MultiplicativeHeights


