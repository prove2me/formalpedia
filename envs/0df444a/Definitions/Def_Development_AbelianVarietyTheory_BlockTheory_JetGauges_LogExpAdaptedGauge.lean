-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_LogExpAdaptedGauge
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_LogExpAdaptedGauge
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:44.633531+00:00
-- url     : https://prove2.me/theorems/72430664-e1e1-40b3-9a3b-d63f666394fc
-- title:
--   Log Exp Adapted Gauge
-- statement:
--   Definitions and structural lemmas for Log Exp Adapted Gauge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/LogExpAdaptedGauge.lean

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
open MvPowerSeries NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory.IndefiniteRowSideFullHecke.LogExpAdaptedGauge
abbrev Ints (C : Type) [NormedField C] [IsUltrametricDist C] : Subring C :=
  (NormedField.valuation (K := C)).integer
def SplitsCompletely (g : ℕ) (E : Type) [Field E] [NumberField E] : Prop :=
  (Ideal.primesOver (Ideal.span {(g : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E
def conjType {E : Type} [Field E] [NumberField E] [IsCMField E] {C : Type} [Field C]
    (τ : E →+* C) : E →+* C :=
  τ.comp (IsCMField.complexConj E : E →+* E)
def degAt {n d : ℕ} (m : Fin n × Fin d →₀ ℕ) (j : Fin n) : ℕ := ∑ i : Fin d, m (j, i)
def degTot {n d : ℕ} (m : Fin n × Fin d →₀ ℕ) : ℕ := ∑ p : Fin n × Fin d, m p
section Chart
variable {k : Type} [CommRing k] {d : ℕ}
def inChart {n : ℕ} (φ : Pt k 1 d) (f : PS k n d) : PS k n d :=
  ev (fun j : Fin n => comp1 φ (pt k (n := n) d j)) f
def linMap (U : Matrix (Fin d) (Fin d) k) : Pt k 1 d :=
  fun i => ∑ j : Fin d, MvPowerSeries.C (U i j) * X ((0 : Fin 1), j)
end Chart
section Gauges
variable {R : Type} [CommRing R] {d : ℕ} (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
def IsLogExp (G : FGLaw R d) (ℓ ε : Pt k 1 d) : Prop :=
  dLin ℓ = 1 ∧
  comp1 ℓ (addOf (G.mapF (algebraMap R k)) (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
    comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1) ∧
  IsInvPair ℓ ε
variable {O : Type} [CommRing O] [StarRing O]
def IsBiaddGauge (B : FB R d O) (h : PS k 2 d) : Prop :=
  ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0 ∧
  FB.toK k B.ph1 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h -
    ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] h) ∧
  FB.toK k B.ph2 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h -
    ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] h)
def IsAdjGauge (B : FB R d O) (h : PS k 2 d) : Prop :=
  IsBiaddGauge k B h ∧
  ∀ a : O, FB.toK k (B.ad a) =
    FB.expS k (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
      ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h)
def colSum (B : FB R d O) (h : PS k 2 d) (w0 : O) (n : ℕ) : PS k n d :=
  ∑ i : Fin n, ev (n := n) ![pt k d i] (B.hL k h w0)
def colProd (B : FB R d O) (u : PS R 2 d) (w0 : O) (n : ℕ) : PS R n d :=
  ∏ i : Fin n, ev (n := n) ![pt R d i, comp1 (B.A.act w0) (pt R d i)] u
end Gauges
section Integrality
variable {C : Type} [NormedField C] {d : ℕ}
def IntBelow (g : ℕ) {n : ℕ} (f : PS C n d) : Prop :=
  ∀ m : Fin n × Fin d →₀ ℕ, degTot m < g → ‖coeff m f‖ ≤ 1
def IntBiBelow (g : ℕ) (f : PS C 2 d) : Prop :=
  ∀ m : Fin 2 × Fin d →₀ ℕ, degAt m 0 < g → degAt m 1 < g → ‖coeff m f‖ ≤ 1
def IntBilin (f : PS C 2 d) : Prop :=
  ∀ i j : Fin d, ‖bilinPart C f i j‖ ≤ 1
end Integrality
section Letters
variable {C : Type} [NormedField C] [IsUltrametricDist C] [CharZero C]
  {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {d : ℕ}
def IsAdapted (B : FB (Ints C) d (𝓞 E)) (U : Matrix (Fin d) (Fin d) (Ints C))
    (ty : Fin d → (E →+* C)) : Prop :=
  IsUnit U ∧ ∀ a : 𝓞 E,
    dAct C B a * U.map (algebraMap (Ints C) C) =
      U.map (algebraMap (Ints C) C) * Matrix.diagonal fun j => ty j (a : E)
def letterChart (ε : Pt C 1 d) (U : Matrix (Fin d) (Fin d) (Ints C)) : Pt C 1 d :=
  comp1 ε (linMap (U.map (algebraMap (Ints C) C)))
def ProductFrameFor (g : ℕ) (B : FB (Ints C) d (𝓞 E)) (ε : Pt C 1 d) (h : PS C 2 d) : Prop :=
  ∃ (u : PS (Ints C) 2 d) (h₂ : PS C 2 d),
    ev (n := 1) ![0, pt (Ints C) d 0] u = 1 ∧ ev (n := 1) ![pt (Ints C) d 0, 0] u = 1 ∧
    ev (n := 1) ![0, pt C d 0] h₂ = 0 ∧ ev (n := 1) ![pt C d 0, 0] h₂ = 0 ∧
    FB.toK C u * FB.expS C h = FB.expS C h₂ ∧
    (∀ (U : Matrix (Fin d) (Fin d) (Ints C)) (ty : Fin d → (E →+* C)), IsAdapted B U ty →
      bilinPart C (inChart (letterChart ε U) h₂) = 0 ∧
      ∀ m : Fin 2 × Fin d →₀ ℕ, coeff m (inChart (letterChart ε U) h₂) ≠ 0 →
        ∃ τ : E →+* C, (∀ i, m (0, i) ≠ 0 → ty i = τ) ∧ (∀ j, m (1, j) ≠ 0 → ty j = conjType τ)) ∧
    ∀ w0 : 𝓞 E, w0 + star w0 = 1 → ∀ n : ℕ,
      IsUnit (colProd B u w0 n) ∧
      FB.toK C (colProd B u w0 n) * FB.expS C (colSum C B h w0 n) = FB.expS C (colSum C B h₂ w0 n) ∧
      ∀ (U : Matrix (Fin d) (Fin d) (Ints C)) (ty : Fin d → (E →+* C)), IsAdapted B U ty →
        IntBelow g (inChart (letterChart ε U) (colSum C B h₂ w0 n)) ∧
        ∀ m : Fin n × Fin d →₀ ℕ, coeff m (inChart (letterChart ε U) (colSum C B h₂ w0 n)) ≠ 0 →
          3 ≤ degTot m ∧
          ∃ p q : Fin n × Fin d, m p ≠ 0 ∧ m q ≠ 0 ∧ ty q.2 = conjType (ty p.2)
end Letters
def LogInt : Prop :=
  ∀ (g : ℕ), g.Prime → Odd g →
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C],
    ‖(g : C)‖ < 1 → ∀ (d : ℕ) (G : FGLaw (Ints C) d),
      (∃ ℓ ε : Pt C 1 d, IsLogExp C G ℓ ε) ∧
      ∀ ℓ ε : Pt C 1 d, IsLogExp C G ℓ ε → (∀ i, IntBelow g (ℓ i)) ∧ ∀ i, IntBelow g (ε i)
def GaugeInt : Prop :=
  ∀ (g : ℕ), g.Prime → Odd g →
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C],
    ‖(g : C)‖ < 1 →
  ∀ (O : Type) [CommRing O] [StarRing O] (d : ℕ) (B : FB (Ints C) d O) (ℓ ε : Pt C 1 d),
    IsLogExp C B.G ℓ ε → ∀ h : PS C 2 d, IsBiaddGauge C B h →
      IntBilin (inChart ε h) → IntBiBelow g (inChart ε h)
def Adjoint : Prop :=
  ∀ (g : ℕ), g.Prime → Odd g →
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C],
    ‖(g : C)‖ < 1 →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)],
    (∀ a : 𝓞 E, ((star a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → SplitsCompletely g E →
  ∀ (d : ℕ) (B : FB (Ints C) d (𝓞 E)) (ℓ ε : Pt C 1 d), IsLogExp C B.G ℓ ε →
    ∃ h' : PS C 2 d, IsAdjGauge C B h' ∧ IntBilin (inChart ε h')
def ProductFrame : Prop :=
  ∀ (g : ℕ), g.Prime → Odd g →
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C],
    ‖(g : C)‖ < 1 →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)],
    (∀ a : 𝓞 E, ((star a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → SplitsCompletely g E →
  ∀ (d : ℕ) (B : FB (Ints C) d (𝓞 E)) (ℓ ε : Pt C 1 d), IsLogExp C B.G ℓ ε →
    ∃ h : PS C 2 d, IsAdjGauge C B h ∧ ProductFrameFor g B ε h
def Statement : Prop := LogInt ∧ GaugeInt ∧ Adjoint ∧ ProductFrame
def AdjointSym : Prop :=
  ∀ (g : ℕ), g.Prime → Odd g →
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C],
    ‖(g : C)‖ < 1 →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)],
    (∀ a : 𝓞 E, ((star a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → SplitsCompletely g E →
  ∀ (d : ℕ) (B : FB (Ints C) d (𝓞 E)) (ℓ ε : Pt C 1 d), IsLogExp C B.G ℓ ε →
    ∃ h' : PS C 2 d, B.IsCanonGauge C h' ∧ IntBilin (inChart ε h')
def ProductFrameSym : Prop :=
  ∀ (g : ℕ), g.Prime → Odd g →
  ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C],
    ‖(g : C)‖ < 1 →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)],
    (∀ a : 𝓞 E, ((star a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → SplitsCompletely g E →
  ∀ (d : ℕ) (B : FB (Ints C) d (𝓞 E)) (ℓ ε : Pt C 1 d), IsLogExp C B.G ℓ ε →
    ∃ h : PS C 2 d, B.IsCanonGauge C h ∧ ProductFrameFor g B ε h
example (p : ℕ) [Fact p.Prime] : CompleteSpace ℂ_[p] ∧ IsAlgClosed ℂ_[p] ∧ CharZero ℂ_[p] ∧
    IsUltrametricDist ℂ_[p] :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
end GlobalTheory.IndefiniteRowSideFullHecke.LogExpAdaptedGauge


