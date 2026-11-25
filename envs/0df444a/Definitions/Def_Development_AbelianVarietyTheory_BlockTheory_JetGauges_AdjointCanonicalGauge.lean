-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_AdjointCanonicalGauge
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_AdjointCanonicalGauge
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:06.125102+00:00
-- url     : https://prove2.me/theorems/6147198d-0f02-4a75-9f60-6068b11905e7
-- title:
--   Adjoint Canonical Gauge
-- statement:
--   Definitions and structural lemmas for Adjoint Canonical Gauge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/AdjointCanonicalGauge.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory.IndefiniteRowSideFullHecke.AdjointCanonicalGauge
abbrev Ints (C : Type) [NormedField C] [IsUltrametricDist C] : Type :=
  (NormedField.valuation (K := C)).integer
def IsOddResChar (C : Type) [NormedField C] (g : ℕ) : Prop :=
  g.Prime ∧ Odd g ∧ ‖(g : C)‖ < 1
def SplitsCompletely (E : Type) [Field E] [NumberField E] (O : Type) [CommRing O] (g : ℕ) : Prop :=
  ((Ideal.span {(g : ℤ)}).primesOver O).ncard = Module.finrank ℚ E
def StarIsConj (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (O : Type) [CommRing O]
    [StarRing O] [Algebra O E] : Prop :=
  ∀ a : O, algebraMap O E (star a) = NumberField.IsCMField.complexConj E (algebraMap O E a)
section Defs
variable {R : Type} [CommRing R] {d : ℕ} (k : Type) [CommRing k] [Algebra R k]
def IntBelow {n : ℕ} (g : ℕ) (f : PS k n d) : Prop :=
  ∀ m : Fin n × Fin d →₀ ℕ, ∑ p, m p < g → coeff m f ∈ (algebraMap R k).range
def IntBelowBi (g : ℕ) (f : PS k 2 d) : Prop :=
  ∀ m : Fin 2 × Fin d →₀ ℕ, ∑ i, m (0, i) < g → ∑ j, m (1, j) < g → coeff m f ∈ (algebraMap R k).range
def IntBilin (f : PS k 2 d) : Prop :=
  ∀ i j, bilinPart k f i j ∈ (algebraMap R k).range
def IsAdditive (G : FGLaw R d) (ℓ : Pt k 1 d) : Prop :=
  (∀ i, constantCoeff (ℓ i) = 0) ∧
    comp1 ℓ (addOf (G.mapF (algebraMap R k)) (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1)
def IsLogExp (G : FGLaw R d) (ℓ ex : Pt k 1 d) : Prop :=
  IsAdditive k G ℓ ∧ dLin ℓ = 1 ∧ IsInvPair ℓ ex
def inLetters {n : ℕ} (ex : Pt k 1 d) (f : PS k n d) : PS k n d :=
  ev (n := n) (fun i => comp1 ex (pt k (n := n) d i)) f
variable [Algebra ℚ k] {O : Type} [CommRing O] [StarRing O]
def IsBiaddGauge (B : FB R d O) (h : PS k 2 d) : Prop :=
  ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0 ∧
    FB.toK k B.ph1 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h -
      ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] h) ∧
    FB.toK k B.ph2 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h -
      ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] h)
def IsAdjGauge (B : FB R d O) (h : PS k 2 d) : Prop :=
  IsBiaddGauge k B h ∧ ∀ a : O, FB.toK k (B.ad a) =
    FB.expS k (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
      ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h)
def IsFrameFactor (u : PS R 2 d) : Prop :=
  ev (n := 1) ![0, pt R d 0] u = 1 ∧ ev (n := 1) ![pt R d 0, 0] u = 1
def colProd (B : FB R d O) (w0 : O) (n : ℕ) (u : PS R 2 d) : PS R n d :=
  ∏ i : Fin n, ev (n := n) ![pt R d i, comp1 (B.A.act w0) (pt R d i)] u
def colSum (B : FB R d O) (w0 : O) (n : ℕ) (h : PS k 2 d) : PS k n d :=
  ∑ i : Fin n, ev (n := n) ![pt k d i, comp1 (B.actK k w0) (pt k d i)] h
def IsLetters {E : Type} [Field E] [Algebra O E] (B : FB R d O) (t : Fin d → (E →+* k)) (ℓ ex : Pt k 1 d) : Prop :=
  IsAdditive k B.G ℓ ∧ IsInvPair ℓ ex ∧
    (∃ M : GL (Fin d) R, dLin ℓ = (M : Matrix (Fin d) (Fin d) R).map (algebraMap R k)) ∧
    ∀ (a : O) (i : Fin d), comp1 ℓ (B.actK k a) i = C (t i (algebraMap O E a)) * ℓ i
end Defs
def IsConjType {E k : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [CommRing k]
    (τ τ' : E →+* k) : Prop :=
  ∀ x : E, τ' x = τ (NumberField.IsCMField.complexConj E x)
def LogIntegral : Prop :=
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (g : ℕ),
    IsOddResChar C g → ∀ (d : ℕ) (G : FGLaw (Ints C) d),
      (∃ ℓ ex : Pt C 1 d, IsLogExp C G ℓ ex) ∧
      ∀ ℓ ex : Pt C 1 d, IsLogExp C G ℓ ex →
        (∀ i, IntBelow (R := Ints C) C g (ℓ i)) ∧ ∀ i, IntBelow (R := Ints C) C g (ex i)
def GaugeIntegral : Prop :=
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (g : ℕ),
    IsOddResChar C g → ∀ (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB (Ints C) d O)
      (ℓ ex : Pt C 1 d), IsLogExp C B.G ℓ ex → ∀ h : PS C 2 d, IsBiaddGauge C B h →
      IntBilin (R := Ints C) C (inLetters C ex h) → IntBelowBi (R := Ints C) C g (inLetters C ex h)
def AdjointGauge : Prop :=
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (g : ℕ),
    IsOddResChar C g → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
      (O : Type) [CommRing O] [StarRing O] [Algebra O E] [IsIntegralClosure O ℤ E],
      StarIsConj E O → SplitsCompletely E O g → ∀ (d : ℕ) (B : FB (Ints C) d O),
        ∃ h' : PS C 2 d, IsAdjGauge C B h' ∧ IntBilin (R := Ints C) C h'
def ProductFrame : Prop :=
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (g : ℕ),
    IsOddResChar C g → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
      (O : Type) [CommRing O] [StarRing O] [Algebra O E] [IsIntegralClosure O ℤ E],
      StarIsConj E O → SplitsCompletely E O g → ∀ w0 : O, w0 + star w0 = 1 →
      ∀ (d : ℕ) (B : FB (Ints C) d O),
        (∃ (t : Fin d → (E →+* C)) (ℓ ex : Pt C 1 d), IsLetters C B t ℓ ex) ∧
        ∃ (u : PS (Ints C) 2 d) (h0 : PS C 2 d), IsFrameFactor u ∧ IsAdjGauge C B h0 ∧
          ∀ n : ℕ, ∃ hL : PS C n d, constantCoeff hL = 0 ∧
            FB.toK C (colProd B w0 n u) * FB.expS C (colSum C B w0 n h0) = FB.expS C hL ∧
            ∀ (t : Fin d → (E →+* C)) (ℓ ex : Pt C 1 d), IsLetters C B t ℓ ex →
              IntBelow (R := Ints C) C g (inLetters C ex hL) ∧
              ∀ m : Fin n × Fin d →₀ ℕ, coeff m (inLetters C ex hL) ≠ 0 →
                3 ≤ ∑ p, m p ∧
                ∃ (i : Fin n) (a b : Fin d), (∀ p, m p ≠ 0 → p.1 = i ∧ (t p.2 = t a ∨ t p.2 = t b)) ∧
                  m (i, a) ≠ 0 ∧ m (i, b) ≠ 0 ∧ IsConjType (t a) (t b)
def GaugeBelowResChar : Prop :=
  LogIntegral ∧ GaugeIntegral ∧ AdjointGauge ∧ ProductFrame
example : CompleteSpace ℂ_[3] ∧ IsAlgClosed ℂ_[3] ∧ CharZero ℂ_[3] ∧ IsUltrametricDist ℂ_[3] :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
end GlobalTheory.IndefiniteRowSideFullHecke.AdjointCanonicalGauge


