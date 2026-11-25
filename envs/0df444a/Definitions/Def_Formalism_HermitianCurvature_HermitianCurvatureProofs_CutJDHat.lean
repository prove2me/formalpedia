-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHat
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHat
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T03:51:25.191888+00:00
-- url     : https://prove2.me/theorems/b3a38bf4-3fe4-5fa8-8b82-3f61b449d432
-- title:
--   Cut JDHat
-- statement:
--   Definitions and structural lemmas for Cut JDHat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJDHat.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.CutMP
open NumberField
noncomputable section
section model
variable (P : M.Par)
def RhM (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (y : ℂ) : MA.A P (MA.DQ P) :=
  L.Drb * (MA.t21 P (MA.DQ P) y * L.Ar y + MA.t22 P (MA.DQ P) y * L.Br y)
def RhvM (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (y : ℂ) : MA.A P (MA.DQ P) :=
  L.Dr * (MA.t12 P (MA.DQ P) y * L.Avr y + MA.t22 P (MA.DQ P) y * L.Bvr y)
def xInvM (y : ℂ) : MA.A P (MA.DQ P) := MA.kap P (MA.DQ P) fun π => (M.xC P π y)⁻¹
def SSn (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (l : ℕ) : MA.A P (MA.DQ P) :=
  L.Drb * L.Dri * MA.SS P (MA.DQ P) l
def RegY (y : ℂ) : Prop := ∀ π : M.Ty P, M.xC P π y ≠ 0
end model
def lagC {m : ℕ} (ν : Fin m → ℝ) (j : Fin m) (y : ℂ) : ℂ :=
  ∏ i ∈ Finset.univ.erase j, (y - (ν i : ℂ)) / ((ν j : ℂ) - (ν i : ℂ))
section defs
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
def HatOK (Cc : ℝ) (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) : Prop :=
  B.SmoothCoef (B.GPos (T v).base) Θ ∧ B.Commutes (T v).base (B.GPos (T v).base) Θ ∧
    GlobCoef Θ (Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) ∧ (B.opOrder Θ : ℝ) ≤ Cc * nDim S.G.k S.G.r
def IsGaugeQQ (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) : Prop :=
  ∀ (Dc : (Fin (D.parOf S v).r → ℂ) → Set (Q.Mx (D.parOf S v).k (D.parOf S v).r))
    (Φ : Q.Fn (D.parOf S v).k (D.parOf S v).r (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
    Gauge.FamR (D.parOf S v) (T v).base Dc Φ →
    ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty (D.parOf S v)),
      MA.toSm (D.parOf S v) (Gauge.rawR (D.parOf S v) (T v).base.μsec e
          (Q.QL (D.parOf S v).k (D.parOf S v).r (T v).base.z (T v).base.z' (Fin.last (D.parOf S v).r) (Y : ℂ) a b Φ) ρ) =
        MA.actA (D.parOf S v) (MA.QQr (D.parOf S v) (MA.DQ (D.parOf S v)) (Y : ℂ) a b)
          (fun ρ' => MA.toSm (D.parOf S v) (Gauge.rawR (D.parOf S v) (T v).base.μsec e Φ ρ')) ρ
end defs
def ResidueSplittingModelAlgebra : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), MA.IsModelLevel P (MA.DQ P) L → ∀ y : ℂ, RegY P y →
    L.R0 y = xInvM P y * RhM P L y -
      ∑ l ∈ Finset.Icc 1 (P.k - 1),
        xInvM P y * SSn P L l * MA.kap P (MA.DQ P) (fun π => M.xEx P {l} π y) * L.Ahat y
def MirrorResidueSplittingModelAlgebra : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), MA.IsModelLevel P (MA.DQ P) L → ∀ y : ℂ, RegY P y →
    L.R0v y = xInvM P y * RhvM P L y -
      ∑ l ∈ Finset.Icc 1 (P.k - 1),
        xInvM P y * MA.kap P (MA.DQ P) (fun π => M.xEx P {l} π y) * star (SSn P L l) * L.Ahatv y
def JDHatLagrange : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (ν : Fin (P.r + 2) → ℝ), Function.Injective ν → ∀ y : ℂ,
    L.R0 y = ∑ j, lagC ν j y • L.R0 (ν j) ∧ L.R0v y = ∑ j, lagC ν j y • L.R0v (ν j)
def JDHatNodes : Prop :=
  ∀ P : M.Par, ∃ ν : Fin (P.r + 2) → ℝ, Function.Injective ν ∧ ∀ j, RegY P (ν j)
def JDOpA : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ Cc : ℝ, K ≤ Cc → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L → ∀ y : ℂ,
      ∃ Θ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)), HatOK Cc S T v Θ ∧ HatOK Cc S T v Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          trJ S T v e (B.opApply Θ J) = MA.actA (D.parOf S v) (L.Ahat y) (trJ S T v e J) ∧
          trJ S T v e (B.opApply Θv J) = MA.actA (D.parOf S v) (L.Ahatv y) (trJ S T v e J)
def JDOpR : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ Cc : ℝ, K ≤ Cc → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGaugeQQ S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L → ∀ y : ℝ,
      ∃ Θ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)), HatOK Cc S T v Θ ∧ HatOK Cc S T v Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          trJ S T v e (B.opApply Θ J) = MA.actA (D.parOf S v) (RhM (D.parOf S v) L y) (trJ S T v e J) ∧
          trJ S T v e (B.opApply Θv J) = MA.actA (D.parOf S v) (RhvM (D.parOf S v) L y) (trJ S T v e J)
def JDGaugeQQ : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
      IsFrame S T v e → IsGauge S T v e → IsGaugeQQ S T v e
section gen
variable (P : M.Par)
end gen
section realise
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cc : ℝ} {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
  {v : Fin S.f} {e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))}
  {L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r}
variable (Cc S T v e L) in

def HReal (X : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) : Prop :=
  ∃ ts : List (MA.A (D.parOf S v) (MA.DQ (D.parOf S v)) × B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))),
    (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) ∧ HatOK Cc S T v t.2) ∧
    ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
      MA.actA (D.parOf S v) X (trJ S T v e J) =
        (ts.map fun t => MA.actA (D.parOf S v) t.1 (trJ S T v e (B.opApply t.2 J))).sum
end realise
end
end Formalism.FourierDecayAlt.P.CutMP


