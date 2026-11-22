-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
-- name    : Formalism_FlagUnipotentLattices_IdealCountLeW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:54.63178+00:00
-- url     : https://prove2.me/theorems/3e3a4629-6012-447a-b947-b6374d310d9a
-- title:
--   Ideal Count Le W
-- statement:
--   Definitions and structural lemmas for Ideal Count Le W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/IdealCountLeW.lean

import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
namespace Formalism.HermitianLatticeCounting.S6
def IotaDual : Prop :=
  ∀ (K U : Type) [Field K] [StarRing K] [AddCommGroup U] [Module K U] (h : U →ₗ[K] U →ₗ⋆[K] K)
    (O : Subring K) (g : K) (L₀ L₀' : AddSubgroup U) (ι' : U → U),
    g ∈ O → star g = g → g ≠ 0 → (∀ x ∈ L₀, ∀ y ∈ L₀, h x y ∈ O) → (∀ x ∈ L₀', ι' x ∈ L₀) →
    (∀ x ∈ L₀', ∀ y ∈ L₀', ∃ t ∈ O, h (ι' x) (ι' y) - h x y = g * t) →
      (∀ l' ∈ L₀', ∀ x ∈ L₀ ⊓ L₀', (∃ l ∈ L₀, ι' x - x = g • l) → h (g⁻¹ • (l' - ι' l')) x ∈ O) ∧
      (∀ l' ∈ L₀ ⊓ L₀', (∃ l ∈ L₀, ι' l' - l' = g • l) → g⁻¹ • (l' - ι' l') ∈ L₀)
def IotaDetermined : Prop :=
  ∀ (K U : Type) [Field K] [AddCommGroup U] [Module K U] (g : K) (L₀ : AddSubgroup U) (ι₁ ι₂ : U → U) (l' : U),
    g ≠ 0 → g⁻¹ • (l' - ι₁ l') - g⁻¹ • (l' - ι₂ l') ∈ L₀ → ∃ l ∈ L₀, ι₁ l' - ι₂ l' = g • l
def hdual {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U] (h : U →ₗ[K] U →ₗ⋆[K] K)
    (O : Subring K) (M : AddSubgroup U) : AddSubgroup U where
  carrier := {x | ∀ y ∈ M, h x y ∈ O}
  add_mem' := by
    intro a b ha hb y hy
    simpa using O.add_mem (ha y hy) (hb y hy)
  zero_mem' := by
    intro y _
    simp
  neg_mem' := by
    intro a ha y hy
    simpa using O.neg_mem (ha y hy)
def DualIndex : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (U : Type) [AddCommGroup U] [Module E U]
    [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U] [FiniteDimensional E U] (h : U →ₗ[E] U →ₗ⋆[E] E)
    (M N : Submodule (𝓞 E) U), (∀ x : U, (∀ y : U, h x y = 0) → x = 0) → N ≤ M → M.FG →
    Submodule.span E (N : Set U) = ⊤ →
      (hdual h (algebraMap (𝓞 E) E).range M.toAddSubgroup).relIndex
          (hdual h (algebraMap (𝓞 E) E).range N.toAddSubgroup) =
        N.toAddSubgroup.relIndex M.toAddSubgroup
def SubGen : Prop :=
  ∀ (R Q : Type) [CommRing R] [IsDedekindDomain R] [AddCommGroup Q] [Module R Q] [Finite Q] (e : ℕ)
    (s : Fin e → Q), Submodule.span R (Set.range s) = ⊤ →
      ∀ N : Submodule R Q, ∃ t : Fin e → Q, Submodule.span R (Set.range t) = N
def ExtGen : Prop :=
  ∀ (R Q : Type) [CommRing R] [AddCommGroup Q] [Module R Q] (N : Submodule R Q) (e₁ e₂ : ℕ)
    (s : Fin e₁ → Q) (t : Fin e₂ → Q ⧸ N), Submodule.span R (Set.range s) = N →
    Submodule.span R (Set.range t) = ⊤ → ∃ u : Fin (e₁ + e₂) → Q, Submodule.span R (Set.range u) = ⊤
def ColonScale : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (U : Type) [AddCommGroup U] [Module E U] (Lam₁ : Set U) (y : U)
    (c : E) (aa aa' : Ideal (𝓞 E)), c ≠ 0 →
    (∀ a : E, a • y ∈ Lam₁ ↔ ∃ a₀ ∈ aa, algebraMap (𝓞 E) E a₀ = a) →
    (∀ a : E, a • (c • y) ∈ Lam₁ ↔ ∃ a₀ ∈ aa', algebraMap (𝓞 E) E a₀ = a) →
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) c *
          (aa' : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) =
        (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
def ColonNorm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (L : Type) [AddCommGroup L] [Module (𝓞 E) L]
    (Lam₁ : Submodule (𝓞 E) L) (y : L),
      Ideal.absNorm (Lam₁.comap (LinearMap.toSpanSingleton (𝓞 E) L y) : Ideal (𝓞 E)) ∣
        Lam₁.toAddSubgroup.index ∧
      (Lam₁.toAddSubgroup.index ≠ 0 →
        1 ≤ Ideal.absNorm (Lam₁.comap (LinearMap.toSpanSingleton (𝓞 E) L y) : Ideal (𝓞 E)) ∧
        Ideal.absNorm (Lam₁.comap (LinearMap.toSpanSingleton (𝓞 E) L y) : Ideal (𝓞 E)) ≤
          Lam₁.toAddSubgroup.index)
def IdealCountEq : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), 1 ≤ n →
    {I : Ideal (𝓞 E) | Ideal.absNorm I = n}.Finite ∧
      {I : Ideal (𝓞 E) | Ideal.absNorm I = n}.ncard ≤
        Module.finrank ℚ E ^ (Nat.primeFactorsList n).length
def IdealCountLe : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (f y : ℕ), Module.finrank ℚ E = 2 * f →
    {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ y}.Finite ∧
      (({I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ y}.ncard : ℕ) : ℝ) ≤
        (y : ℝ) ^ (1 + Real.logb 2 (2 * f))
def TotientBound : Prop := ∀ n : ℕ, n ≤ 2 * Nat.totient n ^ 2
def TorsionBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (f : ℕ), Module.finrank ℚ E = 2 * f →
    Nat.card (NumberField.Units.torsion E) ≤ 8 * f ^ 2
def cSet (E : Type) [Field E] [NumberField E] (D : ℕ) : Set E :=
  {c : E | (∀ w : InfinitePlace E, w c = 1) ∧ ∃ aa aa' : Ideal (𝓞 E),
    1 ≤ Ideal.absNorm aa ∧ Ideal.absNorm aa ≤ D ∧ 1 ≤ Ideal.absNorm aa' ∧ Ideal.absNorm aa' ≤ D ∧
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) c *
        (aa' : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) =
      (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)}
def CCount : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (f D : ℕ), Module.finrank ℚ E = 2 * f →
    (cSet E D).Finite ∧
      (((cSet E D).ncard : ℕ) : ℝ) ≤ 8 * (f : ℝ) ^ 2 * (D : ℝ) ^ (2 * (1 + Real.logb 2 (2 * f)))
def CCountAsm : Prop := IdealCountLe → TorsionBound → CCount
def IdealCountLeW : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (f y : ℕ), Module.finrank ℚ E = 2 * f →
    {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ y}.Finite ∧
      (({I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ y}.ncard : ℕ) : ℝ) ≤
        (y : ℝ) ^ (1 + (1 + Real.logb 2 (2 * f)))
def IdealCountLeW' : Prop := Formalism.SLP.SubmoduleIndexCountO → Formalism.SLP.OmegaPow → IdealCountLeW
def CCountW : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (f D : ℕ), Module.finrank ℚ E = 2 * f →
    (cSet E D).Finite ∧
      (((cSet E D).ncard : ℕ) : ℝ) ≤ 8 * (f : ℝ) ^ 2 * (D : ℝ) ^ (2 + 2 * (1 + Real.logb 2 (2 * f)))
def CCountWAsm : Prop := IdealCountLeW → TorsionBound → CCountW
def TorsionBoundAsm : Prop := TotientBound → TorsionBound
def QuotCard : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M]
    [Module.Finite (𝓞 E) M] [Module.Projective (𝓞 E) M] (I : Ideal (𝓞 E)),
      Nat.card (M ⧸ (I • (⊤ : Submodule (𝓞 E) M))) = Ideal.absNorm I ^ Module.finrank (𝓞 E) M
def CostBound : Prop :=
  ∀ (C C₂ r : ℕ) (Db Del NT Ncc : ℝ), 1 ≤ r → 1 ≤ Del → Del ≤ Db → 1 ≤ NT → 0 ≤ Ncc →
    Ncc ≤ (Db * Del * NT) ^ (C * r) →
      Ncc ^ (2 * (2 * r + 1) ^ 2) * (Del * NT) ^ (2 * (2 * r + 1)) * (Ncc ^ 2) ^ (C₂ * r ^ 2) ≤
        (Db * NT) ^ ((36 * C + 4 * C * C₂ + 6) * r ^ 3)
def HLoss : Prop :=
  ∀ (C C' r f : ℕ) (b : ℝ), 1 ≤ b →
    (b ^ (C * (2 * r + 2) ^ 2 * f)) ^ (C' * r ^ 4) ≤
      Real.exp ((C : ℝ) * C' * ((2 * r + 2 : ℕ) : ℝ) ^ 6 * f * Real.log b)
end Formalism.HermitianLatticeCounting.S6


