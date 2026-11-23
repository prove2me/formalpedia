-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_IntAdelesCompactOpen
-- name    : Formalism_LocalToGlobal_AdelicCompactOpens_IntAdelesCompactOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:58:20.608024+00:00
-- url     : https://prove2.me/theorems/a12047c6-08a1-40fc-85e4-b3ad83cc9241
-- title:
--   Int Adeles Compact Open
-- statement:
--   Definitions and structural lemmas for Int Adeles Compact Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/AdelicCompactOpens/IntAdelesCompactOpen.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.Props
open Filter Topology IsDedekindDomain NumberField
def LogCycConv : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]ˣ), ∃ L : ℚ_[l],
    Tendsto (fun k : ℕ => ((((u : ℤ_[l]) : ℚ_[l]) ^ ((l - 1) * l ^ k) - 1) / (((l - 1) * l ^ k : ℕ) : ℚ_[l])))
      atTop (𝓝 L)
def PlaceEmbExists : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω),
    (∀ x : F, algebraMap F Ω x ∈ A ↔ v.valuation F x ≤ 1) →
    ∃ i : Ω →ₐ[F] AlgebraicClosure (v.adicCompletion F), ∀ x : Ω, x ∈ A ↔
      ∃ q : Polynomial (v.adicCompletion F), q.Monic ∧ (∀ k, q.coeff k ∈ v.adicCompletionIntegers F) ∧
        Polynomial.aeval (i x) q = 0
def IntAdelesCompactOpen : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    IsOpen {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F} ∧
    IsCompact {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}
def TameTrivOnZ : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (g : ℕ), g.Prime →
    Nat.card (𝓞 E ⧸ v.asIdeal) = g →
    ∀ ξ : (v.adicCompletion E)ˣ →* ℂˣ,
      (∀ u : (v.adicCompletion E)ˣ, Valued.v ((u : v.adicCompletion E) - 1) < 1 → ξ u = 1) →
      (∀ (m : ℤ) (u : (v.adicCompletion E)ˣ), ¬ (g : ℤ) ∣ m → (u : v.adicCompletion E) = (m : v.adicCompletion E) → ξ u = 1) →
      ∀ u : (v.adicCompletion E)ˣ, Valued.v (u : v.adicCompletion E) = 1 → ξ u = 1
end Formalism.L2.Props


