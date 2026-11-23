-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_StandardFourierShortSpan
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_StandardFourierShortSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:59:58.240223+00:00
-- url     : https://prove2.me/theorems/360f16e9-c0de-4db0-a845-03b6fb76af6b
-- title:
--   Standard Fourier Short Span
-- statement:
--   Definitions and structural lemmas for Standard Fourier Short Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/StandardFourierShortSpan.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ShortRuleRepresentationChange
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.StandardFourierShortSpan
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {nab : NabV Xo c}
def RankRange (Dw : Datum H) (n : ℕ) : Prop :=
  3 ≤ Dw.p + Dw.q ∧ 8 * (Module.finrank ℚ E / 2) * (Dw.p + Dw.q) + 4 ≤ n
def SpanRange (Dw : Datum H) (l : Level H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  l.A = 1 ∧ Dom a n ∧ RankRange Dw n
section Span
variable (Δ : DeltaDatum Xo c nab) (hK : ReflexLe Dw c) (nV : ℕ)
  (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c))
def shortSpanK (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule c.F (Rul Xo c) :=
  Submodule.span c.F (shortGen Δ hK nV a n)
def CuspLeSpan : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), SpanRange Dw l a n → cusp a n ≤ shortSpanK Δ hK nV a n
def CuspEqSpan : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), SpanRange Dw l a n → OnePos Dw a → cusp a n = shortSpanK Δ hK nV a n
def GenNeZero : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), SpanRange Dw l a n → cusp a n ≠ ⊥ → ∃ f ∈ shortGen Δ hK nV a n, f ≠ 0
end Span
def SpanAtEmb (Δ : DeltaDatum Xo c nab) (hK : ReflexLe Dw c) (nV : ℕ) {σ : c.F →+* ℂ} {r : ℕ}
    (U : Formalism.L2.PjFree.Unf Xo c σ r) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), SpanRange Dw l a n →
    ∀ Q ∈ Formalism.L2.PjFree.holSub U.X (Formalism.L2.PjFree.laU U a n),
      ∃ Q' ∈ Submodule.span ℂ (Formalism.L2.PjFree.rdU U '' shortGen Δ hK nV a n),
        ∀ k, ∀ x ∈ (U.X k).dom, Q k x = Q' k x
section Std
variable (Xo c nab)
def IsTranslateFamily {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) (w : (Fin n → NamedCl Dw l) → Rul Xo c) : Prop :=
  ∀ x : Fin n → Dw.La, IsThRule Xo c nab x P (w fun b => Submodule.Quotient.mk (x b))
def fourierComb {n : ℕ} (x₀ : Fin n → ConjCl Dw l) (w : (Fin n → NamedCl Dw l) → Rul Xo c) : Rul Xo c :=
  fun p y => ∑ t ∈ levelIndex Dw l n, algebraMap c.F p.R (indCoeff c x₀ t) * w t p y
def StdFourier : Prop :=
  ∀ (n N : ℕ) (β : c.F) (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F),
    IsSeriesData (DeltaDatum.triv Xo c nab) (Lat.std E n) N β a P →
    (∃ w, IsTranslateFamily Xo c nab P w) ∧
    ∀ w, IsTranslateFamily Xo c nab P w → ∀ f : Rul Xo c,
      IsShortRule (DeltaDatum.triv Xo c nab) (Lat.std E n) N β x₀ a P f ↔
        f = fun p y => algebraMap c.F p.R β⁻¹ * fourierComb Xo c x₀ w p y
def StdFourierUnit : Prop :=
  ∀ (n N : ℕ) (β : c.F), (Lat.std E n).Admissible l.M N → IsBeLat Dw c (Lat.std E n) β →
    ∃ u : (𝓞 c.F)ˣ, ∀ (x₀ : Fin n → ConjCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F),
      P ∈ harmLat Dw c a (Lat.std E n) →
      (∃ w, IsTranslateFamily Xo c nab P w) ∧
      ∀ w, IsTranslateFamily Xo c nab P w → ∀ f : Rul Xo c,
        IsShortRule (DeltaDatum.triv Xo c nab) (Lat.std E n) N β x₀ a P f ↔
          f = fun p y => algebraMap c.F p.R ((u : 𝓞 c.F) : c.F) * fourierComb Xo c x₀ w p y
end Std
section Canonical
variable (Xo c)
def IsUnfAll {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) : Prop :=
  ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)
def SpanCanonical : Prop :=
  ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab →
    ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), IsUnfAll Xo c U →
    ∀ (Δ : DeltaDatum Xo c nab) (hK : ReflexLe Dw c) (nV : ℕ),
      CuspLeSpan Δ hK nV (Formalism.L2.PjFree.cusp Xo c U) ∧ CuspEqSpan Δ hK nV (Formalism.L2.PjFree.cusp Xo c U)
def NeZeroCanonical : Prop :=
  ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab →
    ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), IsUnfAll Xo c U →
    ∀ (Δ : DeltaDatum Xo c nab) (hK : ReflexLe Dw c) (nV : ℕ), GenNeZero Δ hK nV (Formalism.L2.PjFree.cusp Xo c U)
def StdCanonical : Prop :=
  ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → StdFourier Xo c nab
def SpanAtEmbCanonical : Prop :=
  ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab →
    ∀ (σ : c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb c σ → ∀ (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r),
    Formalism.L2.PjFree.IsUnf U → ∀ (Δ : DeltaDatum Xo c nab) (hK : ReflexLe Dw c) (nV : ℕ), SpanAtEmb Δ hK nV U
def ShortSpanClaims : Prop := SpanCanonical Xo c ∧ NeZeroCanonical Xo c ∧ StdCanonical Xo c
end Canonical
section Basic₂
variable {Δ : DeltaDatum Xo c nab} {hK : ReflexLe Dw c} {nV : ℕ}
  {cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)}
end Basic₂
end GlobalTheory.IndefiniteRowSideFullHecke.StandardFourierShortSpan


