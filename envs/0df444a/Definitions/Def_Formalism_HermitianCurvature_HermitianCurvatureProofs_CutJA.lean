-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJA
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJA
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T03:53:44.334983+00:00
-- url     : https://prove2.me/theorems/63d913b8-6637-5a55-8b17-4142787734e5
-- title:
--   Cut JA
-- statement:
--   Definitions and structural lemmas for Cut JA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJA.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.CutMP.JA
open NumberField Formalism.FourierDecayAlt.P.CutMP
noncomputable section
section defs
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
abbrev GFn (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Type := B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))
def smoothFormsPositiveCone (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) : Set (GFn S v) :=
  Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)
def GfP (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (g : B.Mat S.G.k S.G.r) : ℝ :=
  Formalism.QuantumDeterminants.Gf S.G.k S.G.r (T v).base.z (T v).base.z' g
def mulG (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (ψ : ℝ → ℝ) (J : GFn S v) : GFn S v :=
  fun g => ((ψ (GfP S T v g) : ℝ) : ℂ) • J g
def CCg (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (A Bg : ℝ) (F : GFn S v) : Prop :=
  ∀ m : ℕ, B.InCC (A - Bg * m) m F
def CutCoef (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg : ℝ) : Prop :=
  ∀ Tm ∈ Θ, ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ Cb : ℝ, ∀ u w : List (B.Mat S.G.k S.G.r),
    (∀ X ∈ u, B.unitLie S.G.k S.G.r X) → (∀ X ∈ w, B.unitLie S.G.k S.G.r X) → u.length + w.length ≤ m →
    ∀ g ∈ B.GV S.G.k S.G.r, ε ≤ GfP S T v g →
      ‖B.dLR u w Tm.coef g‖ ≤ Cb * B.gN g ^ (d + Bg * m) ∧ ‖B.dLR u w Tm.coefAdj g‖ ≤ Cb * B.gN g ^ (d + Bg * m)
def IsAAOp (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) : Prop :=
  B.SmoothCoef (B.GPos (T v).base) Θ ∧ B.Commutes (T v).base (B.GPos (T v).base) Θ
def LocCC (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (A Bg : ℝ) (J : GFn S v) : Prop :=
  J ∈ smoothFormsPositiveCone S T v ∧ ∀ δ : ℝ, 0 < δ → ∃ F : GFn S v, B.CkOn ⊤ (B.GV S.G.k S.G.r) F ∧ CCg S v A Bg F ∧
    ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, δ ≤ GfP S T v (B.gq (T v).base x) →
      J (B.gq (T v).base x) = B.JF (T v).base F (B.gq (T v).base x)
def applyL (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (Θs : List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (J : GFn S v) : GFn S v :=
  Θs.foldr (fun Θ J' => B.opApply Θ J') J
def adjL (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (Θs : List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (J : GFn S v) : GFn S v :=
  Θs.foldl (fun J' Θ => B.opAdj Θ J') J
end defs
def JABddOp : Prop :=
  ∃ Cc Cb : ℝ, 0 ≤ Cb ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      ∀ b ∈ MA.bddSet (D.parOf S v) L, ∃ Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))), B.opOrder Θ = 0 ∧ IsAAOp S T v Θ ∧
        CutCoef S T v Θ 0 (Cb * ((S.G.r : ℝ) + 1)) ∧
        ∀ J ∈ smoothFormsPositiveCone S T v, B.opApply Θ J ∈ smoothFormsPositiveCone S T v ∧ B.opAdj Θ J ∈ smoothFormsPositiveCone S T v ∧
          MA.actA (D.parOf S v) b (trJ S T v e J) = trJ S T v e (B.opApply Θ J)
def JABddStar : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ b ∈ Submonoid.closure (MA.bddSet P L), star b ∈ Submonoid.closure (MA.bddSet P L) ∧
      ∀ (ε : ℝ) (U V : M.Ty P → MA.SmQ P.r P.TT), 0 < ε →
        (∀ π q, MA.Gq P q < ε → MA.evQ P (U π) q = 0) →
        (∀ π, MeasureTheory.IntegrableOn (fun q => ‖MA.evQ P (U π) q‖ ^ 2) {q | ε ≤ MA.Gq P q} (MA.mu0 P.r P.TT)) →
        (∀ π, MeasureTheory.IntegrableOn (fun q => ‖MA.evQ P (V π) q‖ ^ 2) {q | ε ≤ MA.Gq P q} (MA.mu0 P.r P.TT)) →
        MA.ipA P U (MA.actA P b V) = MA.ipA P (MA.actA P (star b) U) V
def JAIsAdj : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ a ∈ Submonoid.closure (MA.hatSet P L ∪ MA.bddSet P L), MA.IsAdjA P a
def JAPhiOp : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e → ∀ φ : ℝ → ℝ, LE.SmoothLog φ →
      ∀ J ∈ smoothFormsPositiveCone S T v, mulG S T v φ J ∈ smoothFormsPositiveCone S T v ∧
        trJ S T v e (mulG S T v φ J) =
          fun π => MA.toSm (D.parOf S v) (fun q => (φ (MA.Gq (D.parOf S v) q) : ℂ)) * trJ S T v e J π
def JAStarOp : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      ∀ a ∈ Submonoid.closure (MA.hatSet (D.parOf S v) L ∪ MA.bddSet (D.parOf S v) L), ∀ ts : List (ℂ × List (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))), (∀ t ∈ ts, ∀ Θ ∈ t.2, IsAAOp S T v Θ) →
        (∀ J ∈ smoothFormsPositiveCone S T v, (∀ t ∈ ts, applyL S v t.2 J ∈ smoothFormsPositiveCone S T v ∧ adjL S v t.2 J ∈ smoothFormsPositiveCone S T v) ∧
          MA.actA (D.parOf S v) a (trJ S T v e J) = (ts.map fun t => t.1 • trJ S T v e (applyL S v t.2 J)).sum) →
        ∀ J ∈ smoothFormsPositiveCone S T v,
          MA.actA (D.parOf S v) (star a) (trJ S T v e J) = (ts.map fun t => (starRingEnd ℂ t.1) • trJ S T v e (adjL S v t.2 J)).sum
def JAGroupAdj : Prop :=
  ∃ Cc Cg : ℝ, 0 ≤ Cg ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg : ℝ), 0 ≤ d → Cg * ((S.G.r : ℝ) + 1) ≤ Bg → IsAAOp S T v Θ → CutCoef S T v Θ d Bg →
      ∀ ε : ℝ, 0 < ε → ∀ J₁ J₂ : GFn S v,
        LocCC S T v (B.AB S.G.k S.G.r + Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 +
          6 * (S.G.r : ℝ) * ((B.opOrder Θ : ℝ) + 5) + d + 2 * Bg * ((B.opOrder Θ : ℝ) + 5)) Bg J₁ →
        LocCC S T v (B.AB S.G.k S.G.r + Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 +
          6 * (S.G.r : ℝ) * ((B.opOrder Θ : ℝ) + 5) + d + 2 * Bg * ((B.opOrder Θ : ℝ) + 5)) Bg J₂ →
        (∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, GfP S T v (B.gq (T v).base x) < ε → J₁ (B.gq (T v).base x) = 0) →
        B.opApply Θ J₁ ∈ smoothFormsPositiveCone S T v → B.opAdj Θ J₂ ∈ smoothFormsPositiveCone S T v →
        MA.ipA (D.parOf S v) (trJ S T v e (B.opApply Θ J₁)) (trJ S T v e J₂) =
          MA.ipA (D.parOf S v) (trJ S T v e J₁) (trJ S T v e (B.opAdj Θ J₂))
def JALocCC : Prop :=
  ∃ Cc Cg : ℝ, 0 ≤ Cg ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v,
      (∀ (F : GFn S v) (A Bg : ℝ), B.CkOn ⊤ (B.GV S.G.k S.G.r) F → (∀ m : ℕ, B.InCC A m F) →
        B.JF (T v).base F ∈ smoothFormsPositiveCone S T v → 0 ≤ Bg → LocCC S T v A Bg (B.JF (T v).base F)) ∧
      (∀ (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg A : ℝ) (J : GFn S v), 0 ≤ d → Cg * ((S.G.r : ℝ) + 1) ≤ Bg → IsAAOp S T v Θ →
        CutCoef S T v Θ d Bg →
        Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d +
          2 * Bg * ((B.opOrder Θ : ℝ) + 1) ≤ A →
        LocCC S T v A Bg J → B.opApply Θ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v (A - d - 2 * Bg * (B.opOrder Θ : ℝ)) Bg (B.opApply Θ J)) ∧
      (∀ (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))) (d Bg A : ℝ) (J : GFn S v), 0 ≤ d → Cg * ((S.G.r : ℝ) + 1) ≤ Bg → IsAAOp S T v Θ →
        CutCoef S T v Θ d Bg →
        Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d +
          2 * Bg * ((B.opOrder Θ : ℝ) + 1) ≤ A →
        LocCC S T v A Bg J → B.opAdj Θ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v (A - d - 2 * Bg * (B.opOrder Θ : ℝ)) Bg (B.opAdj Θ J)) ∧
      (∀ (φ : ℝ → ℝ) (Bg A : ℝ) (J : GFn S v), LE.SmoothLog φ → (∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C) →
        Cg * ((S.G.r : ℝ) + 1) ≤ Bg → LocCC S T v A Bg J → mulG S T v φ J ∈ smoothFormsPositiveCone S T v →
          LocCC S T v A Bg (mulG S T v φ J)) ∧
      (∀ (Bg A : ℝ) (J J' : GFn S v), 0 ≤ Bg → Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 ≤ A →
        LocCC S T v A Bg J → LocCC S T v A Bg J' → LocCC S T v A Bg (J + J')) ∧
      (∀ (Bg A : ℝ) (c : ℂ) (J : GFn S v), LocCC S T v A Bg J → LocCC S T v A Bg (c • J)) ∧
      (∀ (Bg A A' : ℝ) (J : GFn S v), A' ≤ A → LocCC S T v A Bg J → LocCC S T v A' Bg J) ∧
      (∀ (Bg A ε : ℝ) (J : GFn S v) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e → 0 ≤ Bg → 0 < ε →
        Cc * ((S.G.r : ℝ) + 1) ^ 2 * nDim S.G.k S.G.r + 5 * Bg ≤ A → LocCC S T v A Bg J →
        ∀ π, MeasureTheory.IntegrableOn (fun q => ‖MA.evQ (D.parOf S v) (trJ S T v e J π) q‖ ^ 2)
          {q | ε ≤ MA.Gq (D.parOf S v) q} (MA.mu0 (D.parOf S v).r (D.parOf S v).TT))
def JAFFStable : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (Θ : (B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))), IsAAOp S T v Θ → ∀ J ∈ smoothFormsPositiveCone S T v, B.opApply Θ J ∈ smoothFormsPositiveCone S T v ∧ B.opAdj Θ J ∈ smoothFormsPositiveCone S T v
def JAAssemble : Prop :=
  JDHatOp → JDHatBdd → JDJComm → JDCCLower → TransferSquareIntegrable → BoundedOperatorsSquareIntegrable → JABddOp → JABddStar → JAIsAdj → JAPhiOp →
    JAStarOp → JAGroupAdj → JALocCC → JAFFStable → JAdjTr
end
end Formalism.FourierDecayAlt.P.CutMP.JA


