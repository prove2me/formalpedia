-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:33:09.542971+00:00
-- url     : https://prove2.me/theorems/9c19209b-746f-498a-8085-88a789778d2e
-- title:
--   Quot St
-- statement:
--   Definitions and structural lemmas for Quot St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/QuotSt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
noncomputable def ordAt {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F]
    [Algebra R F] [IsFractionRing R F] (v : IsDedekindDomain.HeightOneSpectrum R) (x : F) : ℤ :=
  -WithZero.log (v.valuation F x)
def QuotLocalStatement : Prop :=
  ∀ (O Q : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup Q] [Module O Q] (ρ : ℕ), Nonempty (Module.Basis (Fin ρ) O Q) →
    ∀ (c : Fin ρ → (Q →ₗ[O] O)) (th : Fin ρ → Q),
      (Matrix.of fun i j => c i (th j)).det ≠ 0 →
      Module.length O (Q ⧸ Submodule.span O (Set.range th)) ≤
        IsDiscreteValuationRing.addVal O (Matrix.of fun i j => c i (th j)).det
def QuotShiftStatement : Prop :=
  ∀ (R F : Type) [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] (v : IsDedekindDomain.HeightOneSpectrum R)
    (Q : Type) [AddCommGroup Q],
    let Rv := (v.valuationSubringAtPrime F).toSubring
    ∀ [Module Rv Q] (ρ : ℕ), Nonempty (Module.Basis (Fin ρ) Rv Q) →
    ∀ (c : Fin ρ → (Q →ₗ[Rv] F)) (s : Fin ρ → ℝ) (β : ℝ) (th : Fin ρ → Q),
      (∀ i q, c i q ≠ 0 → -β ≤ (ordAt v (c i q) : ℝ) + s i) →
      (Matrix.of fun i j => c i (th j)).det ≠ 0 →
      ∃ n : ℕ, Module.length Rv (Q ⧸ Submodule.span Rv (Set.range th)) = n ∧
        (n : ℝ) ≤ (ordAt v (Matrix.of fun i j => c i (th j)).det : ℝ) + ∑ i, s i + ρ * β
def FreeQuotStatement : Prop :=
  ∀ (R F X : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup X] [Module F X] [Module R X] [IsScalarTower R F X]
    (M₁ : Submodule R X), M₁.FG → ∀ N : Submodule F X,
      Module.Free R (M₁ ⧸ (N.restrictScalars R).comap M₁.subtype) ∧
      Module.finrank R (M₁ ⧸ (N.restrictScalars R).comap M₁.subtype) +
          Module.finrank F ↥(Submodule.span F (M₁ : Set X) ⊓ N) =
        Module.finrank F ↥(Submodule.span F (M₁ : Set X))
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank


