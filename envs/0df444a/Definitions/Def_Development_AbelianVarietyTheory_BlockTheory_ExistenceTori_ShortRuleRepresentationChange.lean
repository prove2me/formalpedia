-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ShortRuleRepresentationChange
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ShortRuleRepresentationChange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:24.527341+00:00
-- url     : https://prove2.me/theorems/c8f0caa2-2c46-4c72-afb6-7566d5345593
-- title:
--   Short Rule Representation Change
-- statement:
--   Definitions and structural lemmas for Short Rule Representation Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/ShortRuleRepresentationChange.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_NormFactorThetaValue
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_DeltaDatumCombinedCoefficient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab)
def CoverVal {S : Type} [CommRing S] [Algebra Δ.cov.c₂.F S] (y₂ : FrPt Δ.cov.Xo₂ Δ.cov.c₂ S) {n : ℕ} (Λ : Lat E n)
    (N : ℕ) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (v : S) : Prop :=
  ThVal Δ.cov.Xo₂ Δ.cov.c₂ Δ.nab₂ y₂ Λ N (Δ.cov.incl β) (Δ.combinedCoeff x₀) a (MvPolynomial.map Δ.cov.incl P) v
def IsShortRule {n : ℕ} (Λ : Lat E n) (N : ℕ) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R),
    (∃ (S' : Type) (_ : CommRing S') (_ : Algebra Δ.cov.c₂.F S') (φ : p.R →+* S')
      (y₂ : FrPt Δ.cov.Xo₂ Δ.cov.c₂ S'), φ.FaithfullyFlat ∧ Δ.cov.LiesOver φ y₂ y) ∧
    ∀ (S' : Type) [CommRing S'] [Algebra Δ.cov.c₂.F S'] (φ : p.R →+* S') (y₂ : FrPt Δ.cov.Xo₂ Δ.cov.c₂ S'),
      Δ.cov.LiesOver φ y₂ y → ∃ v, CoverVal Δ y₂ Λ N β x₀ a P v ∧ φ (f p y) = v * Δ.fnVal y₂
def ramPart (E : Type) [Field E] [NumberField E] : ℕ := 2 * (discr E).natAbs
def reps (n : ℕ) (s : ℕ+) : Set (Lat E n) :=
  {Λ | Λ.InGenus ∧ Λ.StdAt (ramPart E * Δ.a.l₂.M * s)}
def IsPairIso {n : ℕ} (γ : (Fin n → E) ≃ₗ[E] (Fin n → E)) (Λ Λ' : Lat E n) : Prop :=
  IsUnitary γ ∧ (Λ.map γ).L = Λ'.L ∧
    ∀ x ∈ Λ.L, ∃ k : ℕ, k.Coprime Δ.a.l₂.M ∧ k • (γ x - x) ∈ mulStd E n Δ.a.l₂.M
def MeetsAllClasses {n : ℕ} (T : Set (Lat E n)) : Prop :=
  T ⊆ reps Δ n 1 ∧ ∀ Λ ∈ reps Δ n 1, ∃ Λ' ∈ T, ∃ γ, IsPairIso Δ γ Λ Λ'
def IsSeriesData {n : ℕ} (Λ : Lat E n) (N : ℕ) (β : c.F) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  Λ ∈ reps Δ n 1 ∧ Λ.Admissible Δ.a.l₂.M N ∧ IsBeLat Dw c Λ β ∧ P ∈ harmLat Dw c a Λ
def genOn (hK : ReflexLe Dw c) {n : ℕ} (T : Set (Lat E n)) (adm : (Fin n → ConjCl Dw l) → Prop)
    (B : Lat E n → Set (MvPolynomial (LtN Dw n) c.F)) (a : (E →+* ℂ) × ℕ → ℕ) : Set (Rul Xo c) :=
  {f | ∃ Λ ∈ T, ∃ (N : ℕ) (x₀ : Fin n → ConjCl Dw l), ∃ P ∈ B Λ,
    IsSeriesData Δ Λ N (be hK Λ) a P ∧ adm x₀ ∧ IsShortRule Δ Λ N (be hK Λ) x₀ a P f}
def shortGen (hK : ReflexLe Dw c) (nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (Rul Xo c) :=
  {f | ∃ (Λ : Lat E n) (N : ℕ) (x₀ : Fin n → ConjCl Dw l) (P : MvPolynomial (LtN Dw n) c.F),
    IsSeriesData Δ Λ N (be hK Λ) a P ∧ LevelSpanSeparation.Admissible nV x₀ ∧ IsShortRule Δ Λ N (be hK Λ) x₀ a P f}
def shortGenAny (nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Set (Rul Xo c) :=
  {f | ∃ (Λ : Lat E n) (N : ℕ) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (P : MvPolynomial (LtN Dw n) c.F),
    IsSeriesData Δ Λ N β a P ∧ LevelSpanSeparation.Admissible nV x₀ ∧ IsShortRule Δ Λ N β x₀ a P f}
def shortSpan (hK : ReflexLe Dw c) (nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule (𝓞 c.F) (Rul Xo c) :=
  Submodule.span (𝓞 c.F) (shortGen Δ hK nV a n)
def CoverTot : Prop :=
  ∀ (n N : ℕ) (Λ : Lat E n) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F), IsSeriesData Δ Λ N β a P →
    ∀ (S : Type) [CommRing S] [Algebra Δ.cov.c₂.F S] (y₂ : FrPt Δ.cov.Xo₂ Δ.cov.c₂ S),
      ∃! v, CoverVal Δ y₂ Λ N β x₀ a P v
def Descends : Prop :=
  ∀ (n N : ℕ) (Λ : Lat E n) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F), IsSeriesData Δ Λ N β a P →
    ∃ f ∈ sec Xo c a n, IsShortRule Δ Λ N β x₀ a P f
def ShortRat : Prop := CoverTot Δ ∧ Descends Δ
def ShortFreeOfN : Prop :=
  ∀ (n N N' : ℕ) (Λ : Lat E n) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c), IsSeriesData Δ Λ N β a P → Λ.Admissible Δ.a.l₂.M N' →
    IsShortRule Δ Λ N β x₀ a P f → IsShortRule Δ Λ N' β x₀ a P f
def OnePos (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : Prop :=
  ∃ τ : E →+* ℂ, InPsi H τ ∧ (0 < Dw.p → 1 ≤ a (τ, Dw.p - 1))
def SeriesInCusp (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → OnePos Dw a →
    ∀ (N : ℕ) (Λ : Lat E n) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c),
      IsSeriesData Δ Λ N β a P → IsShortRule Δ Λ N β x₀ a P f → f ∈ cusp a n
def ShortInCusp (hK : ReflexLe Dw c) (nV : ℕ)
    (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → OnePos Dw a → ∀ f ∈ shortGen Δ hK nV a n, f ∈ cusp a n
def RepChange : Prop :=
  IsGalois ℚ E → Odd (Dw.p + Dw.q) → ∀ (n : ℕ), Even n →
    ∀ (Λ Λ' : Lat E n) (γ : (Fin n → E) ≃ₗ[E] (Fin n → E)) (N N' : ℕ) (β β' : c.F),
      Λ' ∈ reps Δ n 1 → IsPairIso Δ γ Λ Λ' → Λ'.Admissible Δ.a.l₂.M N' → IsBeLat Dw c Λ' β' →
      ∃ ζ : c.F, IsOfFinOrder ζ ∧
        ∀ (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c),
          IsSeriesData Δ Λ N β a P → IsShortRule Δ Λ N β x₀ a P f →
          IsShortRule Δ Λ' N' β' x₀ a (push Dw c γ P) fun p y => algebraMap c.F p.R ζ * f p y
def FiniteReps : Prop :=
  ∀ (n : ℕ) (s : ℕ+), ∃ T : Set (Lat E n), T.Finite ∧ T ⊆ reps Δ n s ∧ MeetsAllClasses Δ T
def SpanOfReps (hK : ReflexLe Dw c) (nV : ℕ) : Prop :=
  IsGalois ℚ E → Odd (Dw.p + Dw.q) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Even n →
    Submodule.span (𝓞 c.F) (shortGenAny Δ nV a n) = shortSpan Δ hK nV a n ∧
    ∀ (T : Set (Lat E n)) (B : Lat E n → Set (MvPolynomial (LtN Dw n) c.F)), MeetsAllClasses Δ T →
      (∀ Λ ∈ T, (Submodule.span (𝓞 c.F) (B Λ) : Set (MvPolynomial (LtN Dw n) c.F)) = harmLat Dw c a Λ) →
      Submodule.span (𝓞 c.F) (genOn Δ hK T (LevelSpanSeparation.Admissible nV) B a) = shortSpan Δ hK nV a n
variable (Xo c) in

def ShortRatCanonical : Prop :=
  ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ Δ : DeltaDatum Xo c nab, ShortRat Δ
variable (Xo c) in

def ShortInCuspCanonical (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (Δ : DeltaDatum Xo c nab) (hK : ReflexLe Dw c) (nV : ℕ),
    ShortInCusp Δ hK nV cusp
end GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism


