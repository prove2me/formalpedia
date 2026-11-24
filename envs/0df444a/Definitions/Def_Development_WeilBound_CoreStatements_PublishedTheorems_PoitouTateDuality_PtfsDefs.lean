-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsDefs
-- name    : Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:49.029876+00:00
-- url     : https://prove2.me/theorems/2ac49e11-3f18-4ec1-b22a-15c529b53ed8
-- title:
--   Ptfs Defs
-- statement:
--   Definitions and structural lemmas for Ptfs Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/PoitouTateDuality/PtfsDefs.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion
namespace PositivityTheory.Lit1.PTN
section Abstract
variable {R : Type} [CommRing R]
def NineCmp {A0 A1 A2 A3 A4 A5 A6 A7 A8 : Type} [AddCommGroup A0] [Module R A0] [AddCommGroup A1] [Module R A1] [AddCommGroup A2] [Module R A2] [AddCommGroup A3] [Module R A3] [AddCommGroup A4] [Module R A4] [AddCommGroup A5] [Module R A5] [AddCommGroup A6] [Module R A6] [AddCommGroup A7] [Module R A7] [AddCommGroup A8] [Module R A8]
    (f0 : A0 →ₗ[R] A1) (f1 : A1 →ₗ[R] A2) (f3 : A3 →ₗ[R] A4) (f4 : A4 →ₗ[R] A5)
    (f6 : A6 →ₗ[R] A7) (f7 : A7 →ₗ[R] A8) : Prop :=
  ∃ (B0 B1 B2 B3 B4 B5 B6 B7 BetaSesquilinearity : ModuleCat.{0} R)
    (g0 : B0 →ₗ[R] B1) (g1 : B1 →ₗ[R] B2) (g2 : B2 →ₗ[R] B3) (g3 : B3 →ₗ[R] B4)
    (g4 : B4 →ₗ[R] B5) (g5 : B5 →ₗ[R] B6) (g6 : B6 →ₗ[R] B7) (g7 : B7 →ₗ[R] BetaSesquilinearity)
    (e0 : A0 ≃ₗ[R] B0) (e1 : A1 ≃ₗ[R] B1) (e2 : A2 ≃ₗ[R] B2) (e3 : A3 ≃ₗ[R] B3)
    (e4 : A4 ≃ₗ[R] B4) (e5 : A5 ≃ₗ[R] B5) (e6 : A6 ≃ₗ[R] B6) (e7 : A7 ≃ₗ[R] B7)
    (e8 : A8 ≃ₗ[R] BetaSesquilinearity) (u : Fin 6 → Rˣ),
    (∀ a, g0 (e0 a) = u 0 • e1 (f0 a)) ∧ (∀ a, g1 (e1 a) = u 1 • e2 (f1 a)) ∧
    (∀ a, g3 (e3 a) = u 2 • e4 (f3 a)) ∧ (∀ a, g4 (e4 a) = u 3 • e5 (f4 a)) ∧
    (∀ a, g6 (e6 a) = u 4 • e7 (f6 a)) ∧ (∀ a, g7 (e7 a) = u 5 • e8 (f7 a)) ∧
    Function.Injective g0 ∧ Function.Exact g0 g1 ∧ Function.Exact g1 g2 ∧ Function.Exact g2 g3 ∧
    Function.Exact g3 g4 ∧ Function.Exact g4 g5 ∧ Function.Exact g5 g6 ∧ Function.Exact g6 g7 ∧
    Function.Surjective g7
def PerfectPair (X Y : Type) [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] : Prop :=
  Finite X ∧ Finite Y ∧
    ∃ P : X →ₗ[R] Y →ₗ[R] R, Function.Bijective P ∧ Function.Bijective P.flip
end Abstract
def NineCmpFS : Prop :=
  ∀ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsAlgClosure K (AlgebraicClosure ℚ)] (l : ℕ) [Fact l.Prime] (r : ℕ),
  (l ≠ 2 ∨ IsTotallyComplex K) → 0 < r →
  ∀ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ (l ^ r) → ∀ inv : InvFam K (AlgebraicClosure ℚ) l r,
  InvNormalised ζ inv →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), ContainsAbove S l →
  ∀ (Av : S → ValuationSubring (AlgebraicClosure ℚ)), (∀ v, IsPlaceOver (Av v) v.1) →
  ∀ (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod K (AlgebraicClosure ℚ) l r),
  ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) M)
    (hρ : ContAction ρ),
    NineCmp (loc0 S Av ρ) (tr0 S Av μ (invAt S Av μ hμ inv) ρ) (loc1 S Av ρ)
      (tr1 S Av μ (invAt S Av μ hμ inv) ρ hρ) (loc2 S Av ρ) (tr2 S Av μ (invAt S Av μ hμ inv) ρ)
def ShaCmpFS : Prop :=
  ∀ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsAlgClosure K (AlgebraicClosure ℚ)] (l : ℕ) [Fact l.Prime] (r : ℕ),
  (l ≠ 2 ∨ IsTotallyComplex K) → 0 < r →
  ∀ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ (l ^ r) → ∀ inv : InvFam K (AlgebraicClosure ℚ) l r,
  InvNormalised ζ inv →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), ContainsAbove S l →
  ∀ (Av : S → ValuationSubring (AlgebraicClosure ℚ)), (∀ v, IsPlaceOver (Av v) v.1) →
  ∀ (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod K (AlgebraicClosure ℚ) l r),
  ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) M)
    (hρ : ContAction ρ),
    PerfectPair (R := ZMod (l ^ r)) (Sha2 ρ (locFam S Av) (continuous_locFam S Av))
      (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)) ∧
    PerfectPair (R := ZMod (l ^ r)) (Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av))
      (Sha1 ρ (locFam S Av) (continuous_locFam S Av))
end PositivityTheory.Lit1.PTN


