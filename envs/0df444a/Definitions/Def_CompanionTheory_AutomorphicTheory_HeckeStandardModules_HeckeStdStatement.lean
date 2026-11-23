-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeStdStatement
-- name    : CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeStdStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:17:57.122613+00:00
-- url     : https://prove2.me/theorems/3cef6e8e-16d0-46e9-9900-bd75352bc46e
-- title:
--   Hecke Std Statement
-- statement:
--   Definitions and structural lemmas for Hecke Std Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/HeckeStdStatement.lean

import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut
noncomputable section
namespace ReciprocityTheory.Aut
def IsUnif {L : Type} [Field L] [NumberField L] [IsCMField L] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (ϖ : v.adicCompletion (maximalRealSubfield L)) : Prop := Formalism.AUTREP.IsUnif L v ϖ
end ReciprocityTheory.Aut
namespace ReciprocityTheory.ChartRestriction.L3H
variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {W : Type} [AddCommGroup W] [Module ℂ W]
abbrev GAf : Type := Formalism.AUTREP.GAf L n
def Cong (N : ℕ) (κ : GAf L n) : Prop := Formalism.L2.NG.Cong L n N κ
def IsAlgWeight (ρ : Representation ℂ (GQ L n) W) : Prop := Formalism.AUTREP.IsAlgWeight L n ρ
variable {L n}
def TypeSp (ρ : Representation ℂ (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) : Submodule ℂ (GAf L n → W) :=
  Formalism.L2.NG.TypeSp ρ J χ
def HypOutside (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) : Prop :=
  Formalism.L2.NG.HypOutside J χ B
def tN (J : Subgroup (GAf L n)) (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (f : GAf L n → W) : GAf L n → W := Formalism.L2.NG.tN J s ϖ k f
def HeckeStdStatement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GQ L n) W), IsAlgWeight L n ρ →
    ∀ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))),
    (∃ N : ℕ, 0 < N ∧ ∀ κ, Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → HypOutside J χ B →
    ∀ (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ),
      s.v ∉ B → IsUnif s.v ϖ → 1 ≤ k → k ≤ n →
      (∀ f ∈ TypeSp ρ J χ, tN J s ϖ k f ∈ TypeSp ρ J χ) ∧
      (∀ f ∈ TypeSp ρ J χ, ∀ f' ∈ TypeSp ρ J χ, ∀ c : ℂ,
        tN J s ϖ k (c • f + f') = c • tN J s ϖ k f + tN J s ϖ k f') ∧
      (∀ (s' : SplitPlace L) (ϖ' : s'.v.adicCompletion (maximalRealSubfield L)) (k' : ℕ),
        s'.v ∉ B → IsUnif s'.v ϖ' → 1 ≤ k' → k' ≤ n → ∀ f ∈ TypeSp ρ J χ,
          tN J s ϖ k (tN J s' ϖ' k' f) = tN J s' ϖ' k' (tN J s ϖ k f)) ∧
      (∀ f ∈ TypeSp ρ J χ, f ≠ 0 → ∀ μ : ℂ, tN J s ϖ k f = μ • f →
        ∀ l : ℕ, l.Prime → ¬ s.Above l → ∃ d : ℕ, ¬ l ∣ d ∧ IsIntegral ℤ ((d : ℂ) * μ))
end ReciprocityTheory.ChartRestriction.L3H


