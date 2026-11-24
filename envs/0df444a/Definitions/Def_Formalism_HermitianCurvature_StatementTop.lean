-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementTop
-- name    : Formalism_HermitianCurvature_StatementTop
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T16:11:20.459169+00:00
-- url     : https://prove2.me/theorems/b4bd37b6-2986-4ceb-ae1c-1f425561e83b
-- title:
--   Statement Top
-- statement:
--   Definitions and structural lemmas for Statement Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementTop.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementJCT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.Top
open Finset MeasureTheory NumberField
open scoped ComplexConjugate Matrix
noncomputable section
open Classical Formalism.REAL Formalism.QuantumDeterminants
structure TypeProj (P : M.Par) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (π : B.Mat P.k P.r → (Wp →L[ℂ] Wp)) (z e : Fin (2 * P.r + P.k + 1) → ℂ) where

  E : M.Ty P → (Wp →L[ℂ] Wp)
  idem : ∀ ρ, (E ρ).comp (E ρ) = E ρ
  orth : ∀ ρ ρ', ρ ≠ ρ' → (E ρ).comp (E ρ') = 0
  selfAdj : ∀ ρ (v v' : Wp), inner ℂ (E ρ v) v' = inner ℂ v (E ρ v')
  eigen : ∀ Bs : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [z, e] Bs →
    ∀ ρ (w : ℂ) (v : Wp), Q.capRep P.k P.r π Bs w (E ρ v) = M.xC P ρ (w - ((P.k : ℂ) - 2) / 2) • E ρ v
  full : ∀ Bs : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [z, e] Bs →
    ∀ ρ (v : Wp), (∀ w : ℂ, Q.capRep P.k P.r π Bs w v = M.xC P ρ (w - ((P.k : ℂ) - 2) / 2) • v) → E ρ v = v
def wPt (TT : ℝ) (r : ℕ) (p : C.LPt) : ℝ := Complex.normSq (D.ptMatN p (r + 1)).det / D.ptG TT r p
def cW (P : M.Par) (l0 : ℕ) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (ρ : M.Ty P) : ℂ :=
  Fr.cs (fun Y => M.sgn P l0 * M.xC P ρ Y) (M.qC P) (D.positionted w) e
def dH (P : M.Par) (l0 : ℕ) (TT : ℝ) (w : List C.Letter) (p : C.LPt) (e : Wd.Ix (Fin w.length)) (ρ : M.Ty P) : ℝ :=
  Real.sqrt (wPt TT P.r p ^ w.length * (cW P l0 w e ρ).re)
structure TopLift (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] where

  Θ : (w : List C.Letter) → Wd.Ix (Fin w.length) → (B.Mat k r → (Wq →L[ℂ] Wp)) → B.Mat k r → (Wq →L[ℂ] Wp)
  nil : ∀ e F, Θ [] e F = F
section lift
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
def IsRadOf (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
    (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = Q.resG P.k P.r (Fin.last P.r) (B.JF Bs F) x.1 x.2
def firstStateVector {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : B.Mat k r → (Wp →L[ℂ] Wp)} {π' : B.Mat k r → (Wq →L[ℂ] Wq)}
    {S : Type} (Φ : Q.RadSp k r z z' π π') : Wd.Ix S → Q.RadSp k r z z' π π' :=
  fun e => if e = (fun _ => 0) then Φ else 0
def InTopClass (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (A ε : ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) : Prop :=
  0 < ε ∧ B.CkOn ⊤ (B.GV P.k P.r) F ∧ (∀ m : ℕ, B.InCC A m F) ∧
    ∀ g ∈ B.GV P.k P.r, F g ≠ 0 → ε ≤ Gf P.k P.r Bs.z Bs.z' g
def IsTopLift (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (Θ : TopLift P.k P.r Wp Wq) : Prop :=
  ∀ (w : List C.Letter) (A ε : ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), P5.Auser P w.length ≤ A →
    InTopClass P Bs A ε F → ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', IsRadOf P Bs Φ F →
    ∀ e : Wd.Ix (Fin w.length), IsRadOf P Bs
      (P5.act ((Fr.ofWord L st (D.positionted w)).F * P5.bTall L (D.positionted w)) (firstStateVector Φ) e) (Θ.Θ w e F)
def InDDplus [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (Cb : ℝ)
    (Θ : TopLift P.k P.r Wp Wq) : Prop :=
  ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), ∃ (nf : ℕ) (fib : Fin nf → B.Mat P.k P.r → C6.EndH Wp Wq)
    (o κ : ℕ) (Dop : B.DiffOp P.k P.r Wp Wq),
    (∀ j, C6.FibBound Bs (fib j)) ∧ C6.InDDPlus Bs fib ∅ o κ Dop ∧
    (o : ℝ) ≤ Cb * (w.length : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) ∧ (κ : ℝ) ≤ Cb * ((P.r : ℝ) + 1) * (o : ℝ) ∧
    ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), ∀ g ∈ C6.domL Bs ∅, Θ.Θ w e F g = B.opApply Dop F g
end lift
section top
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def topOf (P : M.Par) (l0 : ℕ) (T : D.LevTower P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ)
    (m₀ : B.Mat P.k P.r) (Θ : TopLift P.k P.r Wp Wq) (TP : TypeProj P T.base.π T.base.z (m₀ *ᵥ ν'))
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (p q : C.LPt) : ℂ :=
  ∑ e : Wd.Ix (Fin w.length), ∑ ρ : M.Ty P,
    ((dH P l0 (Tz P.k P.r T.base.z * Tz P.k P.r T.base.z') w p e ρ *
        dH P l0 (Tz P.k P.r T.base.z * Tz P.k P.r T.base.z') w q e ρ : ℝ) : ℂ) *
      B.hsInner ((TP.E ρ).comp (D.vecV T.base ν' m₀ (Θ.Θ w e F) p))
        ((TP.E ρ).comp (D.vecV T.base ν' m₀ (Θ.Θ w e F) q))
def placeDataOfLeadingForm (P : M.Par) (l0 : ℕ) (T : D.LevTower P.k P.r Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (χ : ℝ → ℝ) (s : ℂ) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r) (Θ : TopLift P.k P.r Wp Wq)
    (TP : TypeProj P T.base.π T.base.z (m₀ *ᵥ ν')) (g rd a₀ : ℝ) : C.PlaceData P.k P.r Wp Wq :=
  D.componentFamilySetting_ofSetting T f χ s ν' m₀ (topOf P l0 T ν' m₀ Θ TP) g rd a₀
end top
def VecVTypes : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r)
    (TP : TypeProj P Bs.π Bs.z (m₀ *ᵥ ν')) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (p : C.LPt),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → D.IsBaseFrame Bs ν' m₀ → D.IsLocPt p (P.r + 1) →
      ∑ ρ : M.Ty P, (TP.E ρ).comp (D.vecV Bs ν' m₀ F p) = D.vecV Bs ν' m₀ F p
def TopOfEmpty : Prop :=
  VecVTypes →
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (l0 : ℕ)
    (T : D.LevTower P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r)
    (Θ : TopLift P.k P.r Wp Wq) (TP : TypeProj P T.base.π T.base.z (m₀ *ᵥ ν'))
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (p q : C.LPt),
    Q.IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.IsBaseFrame T.base ν' m₀ →
    D.IsLocPt p (P.r + 1) → D.IsLocPt q (P.r + 1) →
    0 < D.ptG (Tz P.k P.r T.base.z * Tz P.k P.r T.base.z') P.r p →
    0 < D.ptG (Tz P.k P.r T.base.z * Tz P.k P.r T.base.z') P.r q →
      topOf P l0 T ν' m₀ Θ TP F [] p q = B.hsInner (D.vecV T.base ν' m₀ F p) (D.vecV T.base ν' m₀ F q)
def TopOfRadial : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (l0 : ℕ)
    (T : D.LevTower P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r)
    (Θ : TopLift P.k P.r Wp Wq) (TP : TypeProj P T.base.π T.base.z (m₀ *ᵥ ν'))
    (X : Q.ActualOps P.k P.r T.base.z T.base.z' T.base.π T.base.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π'))),
    P5.IsData P T.base.z T.base.z' T.base.π T.base.π' X μ L st l0 → IsTopLift P T.base L st Θ →
    ∀ (w : List C.Letter) (A ε : ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), P5.Auser P w.length ≤ A →
      InTopClass P T.base A ε F →
    ∀ Φ : Q.RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π', IsRadOf P T.base Φ F →
    ∀ (p : C.LPt) (c : Fin P.r → ℂ) (g : B.Mat P.k P.r) (e' : Fin (2 * P.r + P.k + 1) → ℂ)
      (TP' : TypeProj P T.base.π T.base.z e') (τ : (Wq →L[ℂ] Wp) → (Wq →L[ℂ] Wp)),
      D.IsLocPt p (P.r + 1) → (c, g) ∈ Q.DomR P.k P.r T.base.z T.base.z' →
      (∀ U V, B.hsInner (τ U) (τ V) = B.hsInner U V) →
      (∀ ρ U, (TP.E ρ).comp (τ U) = τ ((TP'.E ρ).comp U)) →
      (∀ e, D.vecV T.base ν' m₀ (Θ.Θ w e F) p =
        τ ((P5.act ((Fr.ofWord L st (D.positionted w)).F * P5.bTall L (D.positionted w)) (firstStateVector Φ) e :
          Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g)) →
      (∀ (y : Wd.Ix (Fin w.length) → Q.RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π') e,
        ∑ ρ : M.Ty P, (TP'.E ρ).comp ((y e : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g) = (y e : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g) →
      (∀ (y : Wd.Ix (Fin w.length) → Q.RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π') e,
        (P5.act ((Fr.ofWord L st (D.positionted w)).d L) y e : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
          ∑ ρ : M.Ty P, ((dH P l0 (Tz P.k P.r T.base.z * Tz P.k P.r T.base.z') w p e ρ ^ 2 : ℝ) : ℂ) •
            (TP'.E ρ).comp ((y e : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g)) →
      topOf P l0 T ν' m₀ Θ TP F w p p =
        P5.topDens L st (D.positionted w) (P5.act (P5.bTall L (D.positionted w)) (firstStateVector Φ))
          (P5.act (P5.bTall L (D.positionted w)) (firstStateVector Φ)) c g
def TopPSDT : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P : M.Par) (l0 : ℕ)
    (T : D.LevTower P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r)
    (Θ : TopLift P.k P.r Wp Wq) (TP : TypeProj P T.base.π T.base.z (m₀ *ᵥ ν'))
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (admitted : List C.Letter → Prop),
    D.TopPSD T f χ admitted (topOf P l0 T ν' m₀ Θ TP)
def TopLiftExists : Prop :=
  ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (l0 : ℕ),
    P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 →
      ∃ Θ : TopLift P.k P.r Wp Wq, IsTopLift P Bs L st Θ ∧ InDDplus P Bs Cb Θ
def TopLiftVanishing : Prop :=
  ∀ Cb : ℝ, 0 ≤ Cb → ∃ C₀ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r)
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (Θ Θ' : TopLift P.k P.r Wp Wq),
    1 ≤ P.r → Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → D.IsBaseFrame Bs ν' m₀ →
    IsTopLift P Bs L st Θ → IsTopLift P Bs L st Θ' → InDDplus P Bs Cb Θ → InDDplus P Bs Cb Θ' →
    ∀ (w : List C.Letter) (As : ℕ) (A ε : ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
      w.length * (2 * P.r + P.k + 1) ^ 2 ≤ As → (2 * P.r + P.k + 1) ^ 3 ≤ As →
      P5.Auser P w.length ≤ A → C₀ * ((P.r : ℝ) + 1) ^ 4 * (As : ℝ) ≤ A → InTopClass P Bs A ε F →
      ∀ (e : Wd.Ix (Fin w.length)) (p : C.LPt), D.IsLocPt p (P.r + 1) →
        D.vecV Bs ν' m₀ (Θ.Θ w e F) p = D.vecV Bs ν' m₀ (Θ'.Θ w e F) p
def TypeProjExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : B.Mat P.k P.r → (Wp →L[ℂ] Wp)) (π' : B.Mat P.k P.r → (Wq →L[ℂ] Wq))
    (e : Fin (2 * P.r + P.k + 1) → ℂ), Q.IsPlace P z z' π π' → inWb P.k P.r e →
    herm (Hpk P.k P.r) e z = 0 → herm (Hpk P.k P.r) e e = 1 → Nonempty (TypeProj P π z e)
section hermitianSpaces
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
def topsOf (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (Θ : ∀ v : Fin S.f, TopLift S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (TP : ∀ v : Fin S.f, TypeProj (D.parOf S v) (T v).base.π (T v).base.z (m₀ v *ᵥ ν' v)) (v : Fin S.f) :
    (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ :=
  topOf (D.parOf S v) (S.l + 1) (T v) (ν' v) (m₀ v) (Θ v) (TP v)
def IsBuiltT (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (Θ : ∀ v : Fin S.f, TopLift S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (TP : ∀ v : Fin S.f, TypeProj (D.parOf S v) (T v).base.π (T v).base.z (m₀ v *ᵥ ν' v)) (A₀ : ℝ) : Prop :=
  D.IsBuilt S T f χ ν' m₀ (topsOf S T ν' m₀ Θ TP) A₀ ∧
  ∀ v, ∃ (X : Q.ActualOps S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π')
    (μ : Measure (Mt S.G.k S.G.r))
    (L : R.LevelData (Q.Pr (Q.RadSp S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π')) S.G.r)
    (st : Fr.Start (Q.Pr (Q.RadSp S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π'))),
    P5.IsData (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' X μ L st (S.l + 1) ∧
      IsTopLift (D.parOf S v) (T v).base L st (Θ v) ∧ ∃ Cb : ℝ, InDDplus (D.parOf S v) (T v).base Cb (Θ v)
def IsBuiltPlaceT (Cc : ℝ) (S : C.HidaSetting E Wp Wq)
    (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (Θ : ∀ v : Fin S.f, TopLift S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (TP : ∀ v : Fin S.f, TypeProj (D.parOf S v) (T v).base.π (T v).base.z (m₀ v *ᵥ ν' v)) (A₀ : ℝ) : Prop :=
  JCT.IsBuiltPlace Cc S T f χ ν' m₀ (topsOf S T ν' m₀ Θ TP) A₀ ∧ IsBuiltT S T f χ ν' m₀ Θ TP A₀
end hermitianSpaces
def WaveBuiltT : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (Θ : ∀ v : Fin S.f, TopLift S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (TP : ∀ v : Fin S.f, TypeProj (D.parOf S v) (T v).base.π (T v).base.z (m₀ v *ᵥ ν' v))
    (A₀ : ℝ),
    IsBuiltPlaceT Cc S T f χ ν' m₀ Θ TP A₀ → ∃ Lw : ℕ → Fin S.f → ℝ, JC.WaveByPlaces S Lw ∧ JC.HidaCurvatureBarriers S Lw
def LiftTopDiagBuiltT : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (Θ : ∀ v : Fin S.f, TopLift S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (TP : ∀ v : Fin S.f, TypeProj (D.parOf S v) (T v).base.π (T v).base.z (m₀ v *ᵥ ν' v))
    (A₀ : ℝ),
    IsBuiltPlaceT Cc S T f χ ν' m₀ Θ TP A₀ → ∃ Ll' : ℕ → ℕ → Fin S.f → ℝ, JC.LiftTopDiag S Ll' ∧
      ∀ s, 2 ≤ s → s ≤ S.G.r + 1 → ∀ v,
        0 ≤ Ll' (S.G.r + 2 - s) s v ∧ 2 * Ll' (S.G.r + 2 - s) s v ≤ S.base.szL (S.G.r + 2 - s) s v
def SumFormBuiltT : Prop :=
  ∃ Cc C₄ : ℝ, 1 ≤ C₄ ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (Θ : ∀ v : Fin S.f, TopLift S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (TP : ∀ v : Fin S.f, TypeProj (D.parOf S v) (T v).base.π (T v).base.z (m₀ v *ᵥ ν' v))
    (A₀ : ℝ),
    IsBuiltPlaceT Cc S T f χ ν' m₀ Θ TP A₀ → JC.SumFormConcrete S C₄
def ThmPIntBuiltT : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (Θ : ∀ v : Fin S.f, TopLift S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (TP : ∀ v : Fin S.f, TypeProj (D.parOf S v) (T v).base.π (T v).base.z (m₀ v *ᵥ ν' v))
    (A₀ : ℝ),
    0 < S.G.g1 → 0 < S.G.g2 → S6.Unram E → IsBuiltT S T f χ ν' m₀ Θ TP A₀ →
    ∃ dl : ℕ → Fin S.f → ℝ,
      (∀ i, 1 ≤ i → i ≤ S.G.r + 1 →
        ∏ v, dl i v = ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1)) ∧
      ∀ v, JC.ThmPIntPlace S v fun i => dl i v
def RealInputsBuiltClosedT : Prop :=
  P5.ThmPActual → JC.RadialModuleForm → JC.PosDensityMM → JC.FormLevSesqMM → JC.ThmPModuleOfActualMM →
  ThmPIntBuiltT → D.MuRHaar → MA.LemmaEModel →
  JCT.LevelsActualBuilt → JCT.SlicesCCBuilt → WaveBuiltT → JCT.LiftBelowTopBuilt → LiftTopDiagBuiltT → SumFormBuiltT →
  JCT.ModelPlaceBuilt → TopPSDT →
  ∃ C₆ Cc C₄ : ℝ, 0 < C₆ ∧ 1 ≤ C₄ ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (Θ : ∀ v : Fin S.f, TopLift S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (TP : ∀ v : Fin S.f, TypeProj (D.parOf S v) (T v).base.π (T v).base.z (m₀ v *ᵥ ν' v))
    (A₀ : ℝ)
    (c : LE.Cut) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : TB.Pt E → H),
    IsBuiltPlaceT Cc S T f χ ν' m₀ Θ TP A₀ → JCT.SliceBudget S A₀ → c.χ = χ →
    (∀ v, C₆ * ((S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2) ≤
      S.cutHi v - S.cutLo v) →
    JCT.VtTensor S T f ν' m₀ Vt →
    ∃ (L : ∀ v : Fin S.f, R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
      (j : ∀ v : Fin S.f, M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT)
      (lam : ∀ v : Fin S.f, Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ) (Cm σ : Fin S.f → ℝ),
      (∀ v, JC.IsModelPlace S T f χ v (L v) (j v) (lam v) c (Cm v) (σ v)) ∧
      ∀ Kr hK0 Th e, PB.RealInputs (S.mkData Kr hK0 Th e) C₄ (∏ v, JCT.jvModel S j Cm v) Vt
def InputsTOfInputs : Prop :=
  WaveBuiltT → LiftTopDiagBuiltT → SumFormBuiltT → TopPSDT → ThmPIntBuiltT →
  ∃ Cc C₄ : ℝ, 1 ≤ C₄ ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (Θ : ∀ v : Fin S.f, TopLift S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (TP : ∀ v : Fin S.f, TypeProj (D.parOf S v) (T v).base.π (T v).base.z (m₀ v *ᵥ ν' v))
    (A₀ : ℝ),
    IsBuiltPlaceT Cc S T f χ ν' m₀ Θ TP A₀ →
      (∃ Lw : ℕ → Fin S.f → ℝ, JC.WaveByPlaces S Lw ∧ JC.HidaCurvatureBarriers S Lw) ∧
      (∃ Ll' : ℕ → ℕ → Fin S.f → ℝ, JC.LiftTopDiag S Ll' ∧
        ∀ s, 2 ≤ s → s ≤ S.G.r + 1 → ∀ v,
          0 ≤ Ll' (S.G.r + 2 - s) s v ∧ 2 * Ll' (S.G.r + 2 - s) s v ≤ S.base.szL (S.G.r + 2 - s) s v) ∧
      JC.SumFormConcrete S C₄ ∧
      (∀ v, D.TopPSD (T v) (f v) χ (D.AdmAt S v) (topsOf S T ν' m₀ Θ TP v)) ∧
      ∃ dl : ℕ → Fin S.f → ℝ,
        (∀ i, 1 ≤ i → i ≤ S.G.r + 1 →
          ∏ v, dl i v = ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1)) ∧
        ∀ v, JC.ThmPIntPlace S v fun i => dl i v
end
end Formalism.FourierDecayAlt.Top


