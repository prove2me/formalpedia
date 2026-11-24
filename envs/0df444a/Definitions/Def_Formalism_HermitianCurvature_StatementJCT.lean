-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementJCT
-- name    : Formalism_HermitianCurvature_StatementJCT
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:48:52.620148+00:00
-- url     : https://prove2.me/theorems/8b5d2bf0-3b5e-48ad-aecb-0cff6386eb5e
-- title:
--   Statement JCT
-- statement:
--   Definitions and structural lemmas for Statement JCT, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementJCT.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementJC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.JCT
open Finset Filter Topology NumberField MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Classical
section defs
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
def jvModel (S : C.HidaSetting E Wp Wq)
    (j : ∀ v : Fin S.f, M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT) (Cm : Fin S.f → ℝ) :
    Fin S.f → ℝ := fun v =>
  Cm v * (∫ q, ∑ ρ, ‖(j v ρ : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) q‖ ^ 2
      ∂MA.mu0 (D.parOf S v).r (D.parOf S v).TT) /
    D.GamLev S.G.k S.G.r (D.kapG S.g (S6.rd E)) (D.deG S.g (S6.rd E)) 0
variable [∀ x, FiniteDimensional ℂ (Wq x)]
def LevelsActual (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) :
    Prop :=
  ∀ v (j : Fin (S.G.r + 1)),
    ∃ (X : Q.ActualOps (JC.parLev (D.parOf S v) j).k (JC.parLev (D.parOf S v) j).r ((T v).bs j).z ((T v).bs j).z'
        ((T v).bs j).π ((T v).bs j).π')
      (μ : Measure (Formalism.QuantumDeterminants.Mt (JC.parLev (D.parOf S v) j).k (JC.parLev (D.parOf S v) j).r))
      (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev (D.parOf S v) j).k (JC.parLev (D.parOf S v) j).r ((T v).bs j).z
        ((T v).bs j).z' ((T v).bs j).π ((T v).bs j).π')) (JC.parLev (D.parOf S v) j).r)
      (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev (D.parOf S v) j).k (JC.parLev (D.parOf S v) j).r ((T v).bs j).z
        ((T v).bs j).z' ((T v).bs j).π ((T v).bs j).π'))),
      P5.IsData (JC.parLev (D.parOf S v) j) ((T v).bs j).z ((T v).bs j).z' ((T v).bs j).π ((T v).bs j).π' X μ L st (S.l + 1) ∧
      ∀ w, D.AdmAt S v w → P5.WordOK (JC.parLev (D.parOf S v) j) ((T v).bs j).z ((T v).bs j).z' ((T v).bs j).π
        ((T v).bs j).π' st (S.l + 1) (D.positionted w)
def SlicesCC (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) : Prop :=
  ∀ v, ∀ ε, 0 < ε → ∀ (i : ℕ) (hi : i ≤ S.G.r) (w : List C.Letter), D.AdmAt S v w → ∀ (p : C.LPt)
    (hp : D.IsLocPt p i) (a : Wd.Ix (Fin w.length)), ∃ ε' : ℝ, 0 < ε' ∧
      JC.CCCoefM ((T v).bs (⟨i, by omega⟩ : Fin (S.G.r + 1))) (P5.Auser (D.parOf S v) S.Ntop + 1)
        (P5.mmUser (D.parOf S v) S.Ntop) ε'
        (D.castF (by simp [hp.2])
          (D.sliceAt S.G.k S.G.r (T v).base.z (T v).base.z'
            (D.uwG S.G.k S.G.r (T v).base.z (T v).base.z' (D.cutF (T v).base χ (f v) ε) i hi w a) p))
def VtTensor (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : TB.Pt E → H) : Prop :=
  ∀ p q : TB.Pt E, TB.IsPt p (S.G.r + 1) → TB.IsPt q (S.G.r + 1) →
    inner ℂ (Vt q) (Vt p) = ∏ v,
      ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) p)) *
          √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) q)) : ℝ) : ℂ) *
        inner ℂ (JC.vecPlace S T f ν' m₀ v (C.loc (S.σ v) q)) (JC.vecPlace S T f ν' m₀ v (C.loc (S.σ v) p))
def BuiltInputs (C₄ C₆ : ℝ) (S : C.HidaSetting E Wp Wq)
    (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (L : ∀ v : Fin S.f, R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
    (j : ∀ v : Fin S.f, M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT)
    (lam : ∀ v : Fin S.f, Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ) (c : LE.Cut) (Cm σ : Fin S.f → ℝ)
    (Lw : ℕ → Fin S.f → ℝ) (Ll Ll' : ℕ → ℕ → Fin S.f → ℝ)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : TB.Pt E → H) : Prop :=
  1 ≤ S.l ∧ S.l + 2 ≤ S.G.k ∧ LevelsActual S T ∧ SlicesCC S T f χ ∧
  (∀ v, D.TopPSD (T v) (f v) χ (D.AdmAt S v) (top v)) ∧
  C.GridsOK S ∧
  JC.WaveByPlaces S Lw ∧ JC.HidaCurvatureBarriers S Lw ∧
  JC.LiftBelowTop S Ll ∧ JC.LiftTopDiag S Ll' ∧ JC.ThresholdsLift S Ll Ll' ∧
  JC.SumFormConcrete S C₄ ∧
  (∀ v, B.CkOn ⊤ (B.GV S.G.k S.G.r) (f v)) ∧
  (∀ v, C₆ * ((S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2) ≤
    S.cutHi v - S.cutLo v) ∧
  (∀ v, JC.IsModelPlace S T f χ v (L v) (j v) (lam v) c (Cm v) (σ v)) ∧
  VtTensor S T f ν' m₀ Vt
end defs
def RealInputsBuilt : Prop :=
  P5.ThmPActual → JC.RadialModuleForm → JC.PosDensityMM → JC.FormLevSesqMM → JC.ThmPModuleOfActualMM →
  JC.ThmPIntBuilt → D.MuRHaar → MA.LemmaEModel →
  ∃ C₆ : ℝ, 0 < C₆ ∧
  ∀ (C₄ : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ)
    (L : ∀ v : Fin S.f, R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
    (j : ∀ v : Fin S.f, M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT)
    (lam : ∀ v : Fin S.f, Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ) (c : LE.Cut) (Cm σ : Fin S.f → ℝ)
    (Lw : ℕ → Fin S.f → ℝ) (Ll Ll' : ℕ → ℕ → Fin S.f → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : TB.Pt E → H),
    0 < S.G.g1 → 0 < S.G.g2 → S6.Unram E → D.IsBuilt S T f χ ν' m₀ top A₀ →
    BuiltInputs C₄ C₆ S T f χ ν' m₀ top L j lam c Cm σ Lw Ll Ll' Vt →
    ∀ Kr hK0 Th e, PB.RealInputs (S.mkData Kr hK0 Th e) C₄ (∏ v, jvModel S j Cm v) Vt
def TheoremABuilt : Prop :=
  P5.ThmPActual → JC.RadialModuleForm → JC.PosDensityMM → JC.FormLevSesqMM → JC.ThmPModuleOfActualMM →
  JC.ThmPIntBuilt → D.MuRHaar → MA.LemmaEModel →
  ∃ C₆ : ℝ, 0 < C₆ ∧
  ∀ C₁ C₄ : ℝ, 1 ≤ C₁ → 1 ≤ C₄ → ∃ Cst Cst' : ℝ,
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ)
    (L : ∀ v : Fin S.f, R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
    (j : ∀ v : Fin S.f, M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT)
    (lam : ∀ v : Fin S.f, Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ) (c : LE.Cut) (Cm σ : Fin S.f → ℝ)
    (Lw : ℕ → Fin S.f → ℝ) (Ll Ll' : ℕ → ℕ → Fin S.f → ℝ) (cE : Fin S.f → ℝ)
    (Kr : ℕ → TB.Pt E → TB.Pt E → ℂ) (hK0 : Kr 0 [] [] = 1)
    (Th : ℕ → ℕ → E → TB.Pt E → TB.Pt E → ℂ) (e : ℕ → ℝ) (Θ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Vt : TB.Pt E → H)
    (cr : ℕ → TB.Pt E → ℂ),
    1 ≤ S.f → 0 < S.G.g1 → 0 < S.G.g2 → S6.Unram E → D.IsBuilt S T f χ ν' m₀ top A₀ →
    BuiltInputs C₄ C₆ S T f χ ν' m₀ top L j lam c Cm σ Lw Ll Ll' Vt →
    C.EnergyLinkC S (jvModel S j Cm) cE →
    0 < Θ → Cst' ≤ Θ → ((S.G.r : ℝ) + 1) * (Cst / Θ) ^ S.f ≤ 1 →
    (S.mkData Kr hK0 Th e).SizesBelow Θ →
    TC.KrPSD (S.mkData Kr hK0 Th e) → (S.mkData Kr hK0 Th e).KernelSupport → TC.EBounds (S.mkData Kr hK0 Th e) →
    TC.DomAfter (S.mkData Kr hK0 Th e) →
    (S.mkData Kr hK0 Th e).LatticeSums ((C₁ * Θ ^ (-((C.Kst : ℝ) - 5 / 2))) ^ S.f) →
    (S.mkData Kr hK0 Th e).LeadingDomination Vt cr →
    ∀ Rs : Finset ℕ, ∑ ρ ∈ Rs, ‖∑' p, cr ρ p • Vt p‖ ^ 2 ≤
      (1 + Cst * ((S.G.r : ℝ) + 1) * (Cst / Θ) ^ S.f) * (∏ i ∈ Icc 1 (S.G.r + 1), (1 + e i)) * ∏ v, jvModel S j Cm v
section closed
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
def LongCut (Cc : ℝ) (S : C.HidaSetting E Wp Wq) : Prop :=
  ∀ v, Cc * ((S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2 +
    (S.Ntop : ℝ) ^ 3) ≤ S.cutHi v - S.cutLo v
def IsBuiltPlace (Cc : ℝ) (S : C.HidaSetting E Wp Wq)
    (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) : Prop :=
  0 < S.G.g1 ∧ 0 < S.G.g2 ∧ S6.Unram E ∧ D.IsBuilt S T f χ ν' m₀ top A₀ ∧ 1 ≤ S.l ∧ S.l + 2 ≤ S.G.k ∧
    C.GridsOK S ∧ LongCut Cc S ∧ Cc ≤ S.CA ∧ (∀ v, B.CkOn ⊤ (B.GV S.G.k S.G.r) (f v)) ∧ 2 ≤ S.G.k ∧
    Cc * ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) ≤ A₀ ∧
    ∀ v, ∀ Y ∈ Set.Icc (S.cutLo v) (S.cutHi v), I.OnCut (D.parOf S v).u (D.parOf S v).u' (S.l + 1) Y
def SliceBudget (S : C.HidaSetting E Wp Wq) (A₀ : ℝ) : Prop :=
  ∀ v, ∀ i ≤ S.G.r,
    9 * ((i : ℝ) + 1) * (P5.Auser (D.parOf S v) S.Ntop + 1) + (S.Ntop : ℝ) * (1 + 3 * ((S.G.r : ℝ) + 1)) * i +
      (6 * (i : ℝ) + 3 * ((S.G.r : ℝ) + 1)) * (P5.mmUser (D.parOf S v) S.Ntop : ℝ) ≤ A₀
end closed
def LevelsActualBuilt : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → LevelsActual S T
def SlicesCCBuilt : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → SliceBudget S A₀ → SlicesCC S T f χ
def WaveBuilt : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → ∃ Lw : ℕ → Fin S.f → ℝ, JC.WaveByPlaces S Lw ∧ JC.HidaCurvatureBarriers S Lw
def LiftBelowTopBuilt : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → ∃ Ll : ℕ → ℕ → Fin S.f → ℝ, JC.LiftBelowTop S Ll ∧
      ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Ll b s v ∧ Ll b s v ≤ S.base.szL b s v
def LiftTopDiagBuilt : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → ∃ Ll' : ℕ → ℕ → Fin S.f → ℝ, JC.LiftTopDiag S Ll' ∧
      ∀ s, 2 ≤ s → s ≤ S.G.r + 1 → ∀ v,
        0 ≤ Ll' (S.G.r + 2 - s) s v ∧ 2 * Ll' (S.G.r + 2 - s) s v ≤ S.base.szL (S.G.r + 2 - s) s v
def SumFormBuilt : Prop :=
  ∃ Cc C₄ : ℝ, 1 ≤ C₄ ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → JC.SumFormConcrete S C₄
def ModelPlaceBuilt : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → ∀ c : LE.Cut, c.χ = χ → ∀ v : Fin S.f,
      ∃ (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
        (j : M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT)
        (lam : Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ) (Cm σ : ℝ),
        JC.IsModelPlace S T f χ v L j lam c Cm σ
def RealInputsBuiltClosed : Prop :=
  P5.ThmPActual → JC.RadialModuleForm → JC.PosDensityMM → JC.FormLevSesqMM → JC.ThmPModuleOfActualMM →
  JC.ThmPIntBuilt → D.MuRHaar → MA.LemmaEModel →
  LevelsActualBuilt → SlicesCCBuilt → WaveBuilt → LiftBelowTopBuilt → LiftTopDiagBuilt → SumFormBuilt →
  ModelPlaceBuilt →
  ∃ C₆ Cc C₄ : ℝ, 0 < C₆ ∧ 1 ≤ C₄ ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ)
    (c : LE.Cut) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : TB.Pt E → H),
    IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → SliceBudget S A₀ → c.χ = χ →
    (∀ v, C₆ * ((S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2) ≤
      S.cutHi v - S.cutLo v) →
    (∀ v, D.TopPSD (T v) (f v) χ (D.AdmAt S v) (top v)) → VtTensor S T f ν' m₀ Vt →
    ∃ (L : ∀ v : Fin S.f, R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
      (j : ∀ v : Fin S.f, M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT)
      (lam : ∀ v : Fin S.f, Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ) (Cm σ : Fin S.f → ℝ),
      (∀ v, JC.IsModelPlace S T f χ v (L v) (j v) (lam v) c (Cm v) (σ v)) ∧
      ∀ Kr hK0 Th e, PB.RealInputs (S.mkData Kr hK0 Th e) C₄ (∏ v, jvModel S j Cm v) Vt
def BetaCutLimit : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → ∀ v, B.normSq (T v).base (f v) ≠ ⊤ ∧
      Filter.Tendsto (fun ε => B.beta (T v).base (D.cutF (T v).base χ (f v) ε) (D.cutF (T v).base χ (f v) ε))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (((B.normSq (T v).base (f v)).toReal : ℝ) : ℂ))
def EnergyOfLemmaE : Prop :=
  BetaCutLimit →
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) (jv : Fin S.f → ℝ),
    IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → C.LemmaE S jv →
    ∀ v, jv v = (B.normSq (T v).base (f v)).toReal /
      D.GamLev S.G.k S.G.r (D.kapG S.g (S6.rd E)) (D.deG S.g (S6.rd E)) 0
def ModelPlaceBuilt2 : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → (∀ v, (S.G.place (S.pl v)).Ok) →
    Sz.IsWord S.G.k S.de → Sz.IsWord S.G.k S.de' → ∀ c : LE.Cut, c.χ = χ → ∀ v : Fin S.f,
      ∃ (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
        (j : M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT)
        (lam : Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ) (Cm σ : ℝ),
        JC.IsModelPlace S T f χ v L j lam c Cm σ
end
end Formalism.FourierDecayAlt.JCT


