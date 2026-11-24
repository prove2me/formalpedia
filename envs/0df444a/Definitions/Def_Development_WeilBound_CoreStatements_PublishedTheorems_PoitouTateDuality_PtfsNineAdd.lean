-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsNineAdd
-- name    : Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsNineAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:47.106097+00:00
-- url     : https://prove2.me/theorems/e46d6334-0dec-4935-a024-7590476e96ee
-- title:
--   Ptfs Nine Add
-- statement:
--   Definitions and structural lemmas for Ptfs Nine Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/PoitouTateDuality/PtfsNineAdd.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsDefs
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoitouTateDuality_PtfsAddTransfer
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
def NineAdd {N : ℕ} {A0 A1 A2 A3 A4 A5 A6 A7 A8 : Type} [AddCommGroup A0] [Module (ZMod N) A0] [AddCommGroup A1] [Module (ZMod N) A1] [AddCommGroup A2] [Module (ZMod N) A2] [AddCommGroup A3] [Module (ZMod N) A3] [AddCommGroup A4] [Module (ZMod N) A4] [AddCommGroup A5] [Module (ZMod N) A5] [AddCommGroup A6] [Module (ZMod N) A6] [AddCommGroup A7] [Module (ZMod N) A7] [AddCommGroup A8] [Module (ZMod N) A8]
    (f0 : A0 →ₗ[ZMod N] A1) (f1 : A1 →ₗ[ZMod N] A2) (f3 : A3 →ₗ[ZMod N] A4)
    (f4 : A4 →ₗ[ZMod N] A5) (f6 : A6 →ₗ[ZMod N] A7) (f7 : A7 →ₗ[ZMod N] A8) : Prop :=
  ∃ (B0 B1 B2 B3 B4 B5 B6 B7 BetaSesquilinearity : AddCommGrpCat.{0})
    (g0 : B0 →+ B1) (g1 : B1 →+ B2) (g2 : B2 →+ B3) (g3 : B3 →+ B4) (g4 : B4 →+ B5)
    (g5 : B5 →+ B6) (g6 : B6 →+ B7) (g7 : B7 →+ BetaSesquilinearity)
    (e0 : A0 ≃+ B0) (e1 : A1 ≃+ B1) (e2 : A2 ≃+ B2) (e3 : A3 ≃+ B3) (e4 : A4 ≃+ B4)
    (e5 : A5 ≃+ B5) (e6 : A6 ≃+ B6) (e7 : A7 ≃+ B7) (e8 : A8 ≃+ BetaSesquilinearity) (ε : Fin 6 → ℤˣ),
    (∀ a, g0 (e0 a) = (ε 0 : ℤ) • e1 (f0 a)) ∧ (∀ a, g1 (e1 a) = (ε 1 : ℤ) • e2 (f1 a)) ∧
    (∀ a, g3 (e3 a) = (ε 2 : ℤ) • e4 (f3 a)) ∧ (∀ a, g4 (e4 a) = (ε 3 : ℤ) • e5 (f4 a)) ∧
    (∀ a, g6 (e6 a) = (ε 4 : ℤ) • e7 (f6 a)) ∧ (∀ a, g7 (e7 a) = (ε 5 : ℤ) • e8 (f7 a)) ∧
    Function.Injective g0 ∧ Function.Exact g0 g1 ∧ Function.Exact g1 g2 ∧
    Function.Exact g2 g3 ∧ Function.Exact g3 g4 ∧ Function.Exact g4 g5 ∧ Function.Exact g5 g6 ∧
    Function.Exact g6 g7 ∧ Function.Surjective g7
def NineAddFS : Prop :=
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
    NineAdd (loc0 S Av ρ) (tr0 S Av μ (invAt S Av μ hμ inv) ρ) (loc1 S Av ρ)
      (tr1 S Av μ (invAt S Av μ hμ inv) ρ hρ) (loc2 S Av ρ) (tr2 S Av μ (invAt S Av μ hμ inv) ρ)
end PositivityTheory.Lit1.PTN


