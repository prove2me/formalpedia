-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_CutDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_CutDefs
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T06:00:31.475903+00:00
-- url     : https://prove2.me/theorems/88129ce9-6424-408d-88bb-e6d200846a4c
-- title:
--   Cut Defs
-- statement:
--   Definitions and structural lemmas for Cut Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianCommutation/CutDefs.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace PI.UnitaryGroupMassFormula.JCC
def kap {k r : ℕ} (p : B.SS k r) : ℝ :=
  max 1 (((2 * r + k + 1 : ℕ) : ℝ) * B.gN (JF.sR p) * B.gN (JF.sR p)⁻¹)
def RhoRw : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (p : B.SS k r), D.inSS p →
    ∀ (f : B.Mat k r → (Wq →L[ℂ] Wp)) (v : List (B.Mat k r)) (g : B.Mat k r),
      B.Rw v (B.rho D p f) g = B.rho D p (B.Rw (v.map (JF.AdR p)) f) g
def RwScale : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℝ) (v : List (B.Mat k r))
    (f : B.Mat k r → E),
    B.Rw (v.map fun X => (c : ℂ) • X) f = (c ^ v.length : ℝ) • B.Rw v f
def AdUnit : Prop :=
  ∀ (k r : ℕ) (p : B.SS k r), Matrix.of p.2.1 ∈ B.GV k r → Matrix.of p.2.2 ∈ B.GV k r →
    ∀ X : B.Mat k r, B.unitLie k r X → B.unitLie k r ((((kap p)⁻¹ : ℝ) : ℂ) • JF.AdR p X)
def ExpLie : Prop :=
  ∀ (k r : ℕ) (X : B.Mat k r), B.inLie k r X → ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ B.GV k r
def Transport : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (m : ℕ) (A c : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CCle A m F c →
    ∀ p, D.inSS p → ∀ v : List (B.Mat k r), (∀ X ∈ v, B.unitLie k r X) → v.length ≤ m →
      ∀ g ∈ B.GV k r, ‖B.rho D p (B.Rw (v.map (JF.AdR p)) F) g‖ ≤ kap p ^ m * c * B.gN (B.sgs p g) ^ (-A)
def RwCont : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ) (F : B.Mat k r → E),
    B.CkOn (m : ℕ∞) (B.GV k r) F → ∀ j ≤ m,
      ContinuousOn (fun q : (Fin j → B.Mat k r) × B.Mat k r => B.Rw (List.ofFn q.1) F q.2)
        {q | (∀ i, B.inLie k r (q.1 i)) ∧ q.2 ∈ B.GV k r}
def MeasStep : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn (m : ℕ∞) (B.GV k r) F →
    ∀ v : List (B.Mat k r), (∀ X ∈ v, B.inLie k r X) → v.length ≤ m → ∀ g ∈ B.GV k r,
      AEStronglyMeasurable (fun p => B.rho D p (B.Rw (v.map (JF.AdR p)) F) g) D.μSS
def GrowthN : Prop :=
  ∃ c₀ : ℝ, 1 ≤ c₀ ∧ ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∀ g₀ ∈ bigPos D, ∃ U ∈ 𝓝 g₀, ∃ C : ℝ,
    ∀ g ∈ U, g ∈ B.GV k r → ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r,
      B.gN n * B.gN n' ≤ C * B.gN (n⁻¹ * g * n') ^ (c₀ * ((r : ℝ) + 1) ^ 2)
def VolN : Prop :=
  ∃ c₁ : ℝ, 1 ≤ c₁ ∧ ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (b : ℝ),
    c₁ * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) < b →
      Integrable (fun x : Mt k r => B.gN (Matrix.of x) ^ (-b)) D.μN
def Majorant (c₃ : ℝ) : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (o : ℕ) (A : ℝ), thr c₃ k r o ≤ A →
    ∀ K : Set (B.Mat k r), IsCompact K → K ⊆ bigPos D →
      ∃ Φ : B.SS k r → ℝ, Integrable Φ D.μSS ∧
        ∀ᵐ p ∂D.μSS, ∀ g ∈ K, kap p ^ o * B.gN (B.sgs p g) ^ (-A) ≤ Φ p
def StepDomU (c₃ : ℝ) : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (o : ℕ) (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    thr c₃ k r o ≤ A → B.InCC A (o + 1) F →
    (∀ v : List (B.Mat k r), (∀ X ∈ v, B.unitLie k r X) → v.length ≤ o → ∀ g ∈ bigPos D,
      AEStronglyMeasurable (fun p => B.rho D p (B.Rw (v.map (JF.AdR p)) F) g) D.μSS) ∧
    ∀ K : Set (B.Mat k r), IsCompact K → K ⊆ bigPos D →
      ∃ b : B.SS k r → ℝ, Integrable b D.μSS ∧
        ∀ᵐ p ∂D.μSS, ∀ v : List (B.Mat k r), (∀ X ∈ v, B.unitLie k r X) → v.length ≤ o → ∀ g ∈ K,
          ‖B.rho D p (B.Rw (v.map (JF.AdR p)) F) g‖ ≤ b p
def CurveDeriv : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (f : B.Mat k r → E)
    (g X : B.Mat k r) (t₀ : ℝ), B.CkOn 1 (B.GV k r) f → g ∈ B.GV k r → B.inLie k r X →
      HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X)))
        (RdV X f (g * NormedSpace.exp ((t₀ : ℂ) • X))) t₀
def RwCk : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ) (f : B.Mat k r → E)
    (X : B.Mat k r), B.CkOn ((m + 1 : ℕ) : ℕ∞) (B.GV k r) f → B.inLie k r X →
      B.CkOn (m : ℕ∞) (B.GV k r) (RdV X f)
def RhoCk : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (m : ℕ∞) (p : B.SS k r) (f : B.Mat k r → (Wq →L[ℂ] Wp)), D.inSS p →
    B.CkOn m (B.GV k r) f → B.CkOn m (B.GV k r) (B.rho D p f)
def BigPosOpen : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∃ O : Set (B.Mat k r), IsOpen O ∧ bigPos D = O ∩ B.GV k r
def WordsUnder (c₃ : ℝ) : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (o : ℕ) (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    thr c₃ k r o ≤ A → B.InCC A (o + 1) F →
    ∀ w : List (B.Mat k r), (∀ X ∈ w, B.inLie k r X) → w.length ≤ o → ∀ g ∈ bigPos D,
      Integrable (fun p => B.xiTau D (1, 1) p • B.Rw w (B.rho D p F) g) D.μSS ∧
      B.Rw w (B.JF D F) g = ∫ p, B.xiTau D (1, 1) p • B.Rw w (B.rho D p F) g ∂D.μSS ∧
      (w.length < o → ∀ X : B.Mat k r, B.inLie k r X →
        HasDerivAt (fun t : ℝ => B.Rw w (B.JF D F) (g * NormedSpace.exp ((t : ℂ) • X)))
          (B.Rw (X :: w) (B.JF D F) g) 0)
def WordsCont (c₃ : ℝ) : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (o : ℕ) (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    thr c₃ k r o ≤ A → B.InCC A (o + 1) F → ∀ j ≤ o,
      ContinuousOn (fun q : (Fin j → B.Mat k r) × B.Mat k r => B.Rw (List.ofFn q.1) (B.JF D F) q.2)
        {q | (∀ i, B.inLie k r (q.1 i)) ∧ q.2 ∈ bigPos D}
def CkOfRw : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (m : ℕ)
    (O : Set (B.Mat k r)) (f : B.Mat k r → E), IsOpen O →
    (∀ j ≤ m, ContinuousOn (fun q : (Fin j → B.Mat k r) × B.Mat k r => B.Rw (List.ofFn q.1) f q.2)
      {q | (∀ i, B.inLie k r (q.1 i)) ∧ q.2 ∈ O ∩ B.GV k r}) →
    (∀ w : List (B.Mat k r), (∀ X ∈ w, B.inLie k r X) → w.length < m → ∀ g ∈ O ∩ B.GV k r,
      ∀ X : B.Mat k r, B.inLie k r X →
        HasDerivAt (fun t : ℝ => B.Rw w f (g * NormedSpace.exp ((t : ℂ) • X))) (B.Rw (X :: w) f g) 0) →
    B.CkOn (m : ℕ∞) (O ∩ B.GV k r) f
def TransportOf : Prop := RwScale → AdUnit → Transport
def MeasOf : Prop := RwCont → AdUnit → MeasStep
def MajorantOf : Prop := GrowthN → VolN → ∃ c₃ : ℝ, 0 ≤ c₃ ∧ Majorant c₃
def DomOf : Prop := ∀ c₃ : ℝ, MeasStep → Transport → Majorant c₃ → StepDomU c₃
def WordsUnderOf : Prop :=
  ∀ c₃ : ℝ, StepDomU c₃ → RhoRw → RwScale → ExpLie → CurveDeriv → RwCk → RhoCk → BigPosOpen → WordsUnder c₃
def WordsContOf : Prop :=
  ∀ c₃ : ℝ, StepDomU c₃ → WordsUnder c₃ → RhoRw → RwScale → RwCont → BigPosOpen → WordsCont c₃
def StepWordsOfParts : Prop :=
  ∀ c₃ : ℝ, WordsUnder c₃ → WordsCont c₃ → CkOfRw → BigPosOpen → StepWords c₃
end PI.UnitaryGroupMassFormula.JCC


