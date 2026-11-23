-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverStd
-- name    : Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverStd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:17:11.332932+00:00
-- url     : https://prove2.me/theorems/68ffc5eb-43df-4d1c-b895-11a73caa8048
-- title:
--   Cover Std
-- statement:
--   Definitions and structural lemmas for Cover Std, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverStd.lean

import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP
namespace Formalism.L2
def HeckeStdPlain : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n)
    (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))),
    (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → NG.HypOutside J χ B →
    ∀ (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ),
      s.v ∉ B → IsUnif L s.v ϖ → 1 ≤ k → k ≤ n →
      (∀ f ∈ NG.TypeSp a.ρ J χ, NG.tN J s ϖ k f ∈ NG.TypeSp a.ρ J χ) ∧
      (∀ f ∈ NG.TypeSp a.ρ J χ, ∀ f' ∈ NG.TypeSp a.ρ J χ, ∀ c : ℂ,
        NG.tN J s ϖ k (c • f + f') = c • NG.tN J s ϖ k f + NG.tN J s ϖ k f') ∧
      (∀ (s' : SplitPlace L) (ϖ' : s'.v.adicCompletion (maximalRealSubfield L)) (k' : ℕ),
        s'.v ∉ B → IsUnif L s'.v ϖ' → 1 ≤ k' → k' ≤ n → ∀ f ∈ NG.TypeSp a.ρ J χ,
          NG.tN J s ϖ k (NG.tN J s' ϖ' k' f) = NG.tN J s' ϖ' k' (NG.tN J s ϖ k f)) ∧
      (∀ f ∈ NG.TypeSp a.ρ J χ, f ≠ 0 → ∀ μ : ℂ, NG.tN J s ϖ k f = μ • f →
        ∀ l : ℕ, l.Prime → ¬ s.Above l → ∃ d : ℕ, ¬ l ∣ d ∧ IsIntegral ℤ ((d : ℂ) * μ))
end Formalism.L2


