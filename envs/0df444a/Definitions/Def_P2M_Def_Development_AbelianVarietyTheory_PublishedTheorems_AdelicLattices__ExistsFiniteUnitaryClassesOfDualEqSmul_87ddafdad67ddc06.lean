-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteUnitaryClassesOfDualEqSmul_87ddafdad67ddc06
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteUnitaryClassesOfDualEqSmul_87ddafdad67ddc06
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:49.714459+00:00
-- url     : https://prove2.me/theorems/74487db4-2b90-4597-b0ba-e5944b41b63f
-- title:
--   Exists Finite Unitary Classes Of Dual Eq Smul
-- statement:
--   Definitions and structural lemmas for Exists Finite Unitary Classes Of Dual Eq Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AdelicLattices₂/ExistsFiniteUnitaryClassesOfDualEqSmul.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsFiniteRepresentatives_c0b95eec68dc9003
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.MultiplicativeHeights
open scoped nonZeroDivisors
namespace Published
def FinitenessOfHermitianClasses : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E),
    (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 →
    ∀ (c : FractionalIdeal (𝓞 E)⁰ E), c ≠ 0 → ∀ (𝔪 : Ideal (𝓞 E)), 𝔪 ≠ ⊥ →
    ∀ (ι : Type) [Finite ι] (𝓛 : Set (Submodule (𝓞 E) (Fin r → E) × (ι → Fin r → E))),
    (∀ p ∈ 𝓛, IsLattice p.1 ∧
      (∀ x, (∀ y ∈ p.1, IsIntegral ℤ (herm G x y)) ↔ x ∈ (c : Submodule (𝓞 E) E) • p.1) ∧
      ∀ i, p.2 i ∈ p.1) →
    ∃ S ⊆ 𝓛, S.Finite ∧ ∀ p ∈ 𝓛, ∃ q ∈ S, ∃ γ : GL (Fin r) E,
      (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) =
        herm G x y) ∧
      (∀ x, x ∈ p.1 ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ x ∈ q.1) ∧
      ∀ i, (γ : Matrix (Fin r) (Fin r) E) *ᵥ p.2 i - q.2 i ∈ 𝔪 • q.1
end Published
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end GlobalTheory


