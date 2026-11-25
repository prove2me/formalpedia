-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementTL
-- name    : Formalism_HermitianCurvature_StatementTL
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:58:36.591486+00:00
-- url     : https://prove2.me/theorems/44bcdbe2-f1f2-4217-aa15-7c7c6233adc1
-- title:
--   Statement TL
-- statement:
--   Definitions and structural lemmas for Statement TL, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementTL.lean

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_Ent_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_Ent_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_Ent_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_Rep_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.TL
open Finset MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open scoped ComplexConjugate
noncomputable section
open Classical
def TopLiftExists3 : Prop :=
  ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (l0 : ℕ), 1 ≤ l0 → l0 ≤ P.k →
    P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 →
      ∃ Θ : Top.TopLift P.k P.r Wp Wq, KB.IsTopLift2 P l0 Bs L st Θ ∧ KB.InDDplus2 P l0 Bs Cb Θ
section algdefs
variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {r : ℕ}
def siteOps (L : LevelData A r) : Set A :=
  Set.range L.p ∪ Set.range L.pb ∪ Set.range L.c ∪ Set.range L.ci ∪ Set.range L.cb ∪ Set.range L.cbi
structure AHyp (L : LevelData A r) (st : Start A) : Prop where
  starLev : IsStarLevel L
  start : IsLevelStart L st
  star_p : ∀ l, star (L.p l) = -L.pb l
  star_c : ∀ l, star (L.c l) = L.cb l
  star_ci : ∀ l, star (L.ci l) = L.cbi l
  qq_site : ∀ Y i j, ∀ x ∈ siteOps L, Commute (st.QQ Y i j) x
def nP (L : LevelData A r) (st : Start A) (Y : ℂ) (i : Fin 2) : A := st.QQ Y i 0 * L.Ar Y + st.QQ Y i 1 * L.Br Y
def cst (L : LevelData A r) (st : Start A) (Y : ℂ) : A := L.Avr Y * nP L st Y 0 + L.Bvr Y * nP L st Y 1
def bP (L : LevelData A r) (st : Start A) (Y : ℂ) : A := L.ζbi * nP L st Y 1
def bM (L : LevelData A r) (st : Start A) (Y : ℂ) : A := L.ζi * (st.QQ Y 0 1 * L.Avr Y + st.QQ Y 1 1 * L.Bvr Y)
def aP (L : LevelData A r) (Y : ℂ) : A := L.ζi * L.Ar Y
def aM (L : LevelData A r) (Y : ℂ) : A := L.ζbi * L.Avr Y
def gI (L : LevelData A r) : A := L.Dri * L.Drbi * L.GGi
def bTA {S : Type} [Fintype S] [DecidableEq S] (L : LevelData A r) (w : List (Letter ℂ S)) : SlopeTestRemainingChoices S A :=
  ((List.finRange r).reverse.map fun l => bT (⟨L.p l, L.c l, L.ci l⟩ : Site A) w).prod
def kAlg (st : Start A) : Subalgebra ℂ A :=
  Algebra.adjoin ℂ ({a | ∃ Y : ℂ, star Y = Y ∧ a = st.x Y} ∪ {a | ∃ Y ∈ st.inv, star Y = Y ∧ a = st.xi Y})
def kMat {S : Type} (st : Start A) (M : SlopeTestRemainingChoices S A) : Prop := ∀ i j, M i j ∈ kAlg st
def dSpan {S : Type} [Fintype S] [DecidableEq S] (st : Start A) (X φ τ : SlopeTestRemainingChoices S A) : Submodule ℂ (SlopeTestRemainingChoices S A) :=
  Submodule.span ℂ ({M | ∃ α β γ, kMat st α ∧ kMat st β ∧ kMat st γ ∧ M = α * (X * β - β * X) * γ} ∪
    {M | ∃ γ, kMat st γ ∧ (M = φ * γ ∨ M = φ * τ * γ)})
structure LiftSys (L : LevelData A r) (st : Start A) (n : ℕ) (Lf : ℕ → ℕ → A → Prop) : Prop where
  mono : ∀ {o o' κ κ' a}, o ≤ o' → κ ≤ κ' → Lf o κ a → Lf o' κ' a
  zero : ∀ o κ, Lf o κ 0
  add : ∀ {o κ a b}, Lf o κ a → Lf o κ b → Lf o κ (a + b)
  smul : ∀ {o κ a} (z : ℂ), Lf o κ a → Lf o κ (z • a)
  one : Lf 0 0 1
  mul : ∀ {o₁ κ₁ o₂ κ₂ a b}, Lf o₁ κ₁ a → Lf o₂ κ₂ b → Lf (o₁ + o₂) (κ₁ + κ₂ + (2 * r + 2) * o₁) (a * b)
  fns : Lf 0 (r + 1) L.D ∧ Lf 0 (r + 1) L.Db ∧ Lf 0 r L.Dr ∧ Lf 0 r L.Drb ∧ Lf 0 0 L.Di ∧ Lf 0 0 L.Dbi ∧ Lf 0 0 (gI L)
  x : ∀ Y : ℂ, star Y = Y → Lf 0 0 (st.x Y)
  xi : ∀ Y ∈ st.inv, star Y = Y → Lf 0 0 (st.xi Y)
  cap : ∀ Y : ℂ, star Y = Y → Lf n 0 (cst L st Y)
end algdefs
def ZetaQQ : Prop :=
  ∀ (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (r : ℕ) (L : LevelData A r) (st : Start A),
    IsStarLevel L → IsLevelStart L st → ∀ Y : ℂ, star Y = Y → Y ∈ st.inv →
    (st.QQ Y 1 0 * L.ζ = L.ζ * st.QQ Y 1 0 - st.QQ Y 1 1 ∧ Commute (st.QQ Y 1 0) L.ζb ∧
      st.QQ Y 0 1 * L.ζb = L.ζb * st.QQ Y 0 1 + st.QQ Y 1 1 ∧ Commute (st.QQ Y 0 1) L.ζ ∧
      Commute (st.QQ Y 1 1) L.ζ ∧ Commute (st.QQ Y 1 1) L.ζb) ∧
    ((Y - 1 ∈ st.inv ∨ Y + 1 ∈ st.inv) →
      st.QQ Y 0 0 * L.ζb = L.ζb * st.QQ Y 0 0 + st.QQ Y 1 0 ∧ st.QQ Y 0 0 * L.ζ = L.ζ * st.QQ Y 0 0 - st.QQ Y 0 1)
def CapConj : Prop :=
  ∀ (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (r : ℕ) (L : LevelData A r) (st : Start A),
    AHyp L st → ∀ Y : ℂ, star Y = Y → Y ∈ st.inv → (Y - 1 ∈ st.inv ∨ Y + 1 ∈ st.inv) → ∀ s : ℕ,
    L.Dbi ^ s * cst L st Y * L.Db ^ s =
      L.Avr (Y - s) * (nP L st Y 0 + (s : ℂ) • bP L st Y) + L.Bvr (Y - s) * nP L st Y 1 ∧
    L.Di ^ s * cst L st Y * L.D ^ s =
      (L.Avr Y * st.QQ Y 0 0 + L.Bvr Y * st.QQ Y 1 0 - (s : ℂ) • bM L st Y) * L.Ar (Y + s) +
        (L.Avr Y * st.QQ Y 0 1 + L.Bvr Y * st.QQ Y 1 1) * L.Br (Y + s)
def BFromCap : Prop :=
  ∀ (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (r : ℕ) (L : LevelData A r) (st : Start A),
    AHyp L st → ∀ Y : ℂ, star Y = Y → Y ∈ st.inv → (Y - 1 ∈ st.inv ∨ Y + 1 ∈ st.inv) →
    bP L st Y = (-1 : ℂ) ^ r • ∑ s : Fin (r + 2), ((F7.lagCo (fun j : Fin (r + 2) => ((j : ℕ) : ℝ)) s : ℝ) : ℂ) •
      (L.Dbi ^ (s : ℕ) * cst L st Y * L.Db ^ (s : ℕ)) ∧
    bM L st Y = -∑ s : Fin (r + 2), ((F7.lagCo (fun j : Fin (r + 2) => ((j : ℕ) : ℝ)) s : ℝ) : ℂ) •
      (L.Di ^ (s : ℕ) * cst L st Y * L.D ^ (s : ℕ))
def AFromB : Prop :=
  ∀ (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (r : ℕ) (L : LevelData A r) (st : Start A),
    AHyp L st → ∀ Y : ℂ, star Y = Y → Y ∈ st.inv →
    aP L (Y + 1) = L.Db * gI L * st.xi Y * (bP L st Y * L.Dr - L.Dr * L.Di * bP L st Y * L.D) ∧
    aM L (Y - 1) = -(L.D * gI L * st.xi Y * (bM L st Y * L.Drb - L.Drb * L.Dbi * bM L st Y * L.Db))
def BasicLift : Prop :=
  ∀ (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (r n : ℕ) (L : LevelData A r) (st : Start A)
    (Lf : ℕ → ℕ → A → Prop), AHyp L st → LiftSys L st n Lf → r + 1 ≤ n →
    ∀ Y : ℂ, star Y = Y → Y - 1 ∈ st.inv → Y ∈ st.inv → Y + 1 ∈ st.inv →
    Lf n (3 * (r + 1) * n) (bP L st Y) ∧ Lf n (3 * (r + 1) * n) (bM L st Y) ∧
      Lf n (8 * (r + 1) * n) (aP L Y) ∧ Lf n (8 * (r + 1) * n) (aM L Y)
def LShape : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)),
    IsStarLevel L → IsLevelStart L st → admitted st w →
    kMat st (ofWord L st w).c ∧ kMat st (ofWord L st w).ci ∧
    ∀ Y ∈ (ofWord L st w).inv, Y + 1 ∈ (ofWord L st w).inv →
      (ofWord L st w).l L Y - (st.frame : FrameData S A).l L Y ∈
        dSpan st ((st.frame : FrameData S A).l L Y) (kapL L) (tz L)
def MShape : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)),
    IsStarLevel L → IsLevelStart L st → admitted st w →
    ∀ Y ∈ (ofWord L st w).inv, star Y = Y → Y - 1 ∈ (ofWord L st w).inv →
      (ofWord L st w).m L Y - (st.frame : FrameData S A).m L Y ∈
        dSpan st ((st.frame : FrameData S A).m L Y) (io (L.ζ * L.ζbi * L.GGi)) (io (L.TT • L.ζi))
def letterCol {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
    (L : LevelData A r) (st : Start A) (l : Letter ℂ S) (w : List (Letter ℂ S)) : Fin 2 → SlopeTestRemainingChoices S A :=
  if l.plus then
    ![io (aP L l.pt), io (L.ζbi * L.GG) * ((ofWord L st w).l L l.pt * io (L.Ar l.pt) + io (L.Br l.pt))]
  else
    ![io (aM L l.pt), io (L.ζi * L.GG) * ((ofWord L st w).m L l.pt * io (L.Avr l.pt) + io (L.Bvr l.pt))]
def WordStep : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (st : Start A) (l : Letter ℂ S) (w : List (Letter ℂ S)),
    AHyp L st → admitted st (l :: w) → ∀ e : Ix S,
      ((ofWord L st (l :: w)).F * bTA L (l :: w)) e e1 =
        ((∑ i : Fin 2, eU l.intersection_update_fsHerm_neg_one i 0 * letterCol L st l w i) * ((ofWord L st w).F * bTA L w)) e e1
def LetterLift : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r n : ℕ) (L : LevelData A r) (st : Start A) (Lf : ℕ → ℕ → A → Prop) (l : Letter ℂ S) (w : List (Letter ℂ S)),
    AHyp L st → LiftSys L st n Lf → r + 1 ≤ n → admitted st (l :: w) →
    ∀ i e e', Lf n (9 * (r + 1) * n) (letterCol L st l w i e e')
def WordLift : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r n : ℕ) (L : LevelData A r) (st : Start A) (Lf : ℕ → ℕ → A → Prop) (w : List (Letter ℂ S)),
    AHyp L st → LiftSys L st n Lf → r + 1 ≤ n → admitted st w →
    ∀ e : Ix S, Lf (w.length * n) (11 * w.length * (r + 1) * n) (((ofWord L st w).F * bTA L w) e e1)
section lifts
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def RadIs (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (Dop : B.DiffOp P.k P.r Wp Wq)
    (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) : Prop :=
  ∀ F, KB.CptCoef Bs F → ∀ Φ, Top.IsRadOf P Bs Φ F → Top.IsRadOf P Bs (T Φ) (B.opApply Dop F)
def Lifts (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (o κ : ℕ)
    (a : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) : Prop :=
  ∃ (nf : ℕ) (fib : Fin nf → B.Mat P.k P.r → C6.EndH Wp Wq) (Dop : B.DiffOp P.k P.r Wp Wq),
    (∀ j, C6.FibBound Bs (fib j)) ∧ C6.InDDPlus Bs fib ∅ o κ Dop ∧ RadIs P Bs Dop a.1
end lifts
def CptFacts : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    KB.CptCoef Bs F → (∃ ε, 0 < ε ∧ JC.NiceCoef Bs ε F) ∧
      ∀ Dop : B.DiffOp k r Wp Wq, B.SmoothCoef (C6.domL Bs ∅) Dop →
        KB.CptCoef Bs (B.opApply Dop F) ∧ ∀ g ∈ B.GV k r, g ∉ C6.domL Bs ∅ → B.opApply Dop F g = 0
def LiftClosed : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq),
    (∀ o o' κ κ' a, o ≤ o' → κ ≤ κ' → Lifts P Bs o κ a → Lifts P Bs o' κ' a) ∧ (∀ o κ, Lifts P Bs o κ 0) ∧
    (∀ o κ a b, Lifts P Bs o κ a → Lifts P Bs o κ b → Lifts P Bs o κ (a + b)) ∧
    (∀ o κ a (z : ℂ), Lifts P Bs o κ a → Lifts P Bs o κ (z • a)) ∧
    ∀ o₁ κ₁ o₂ κ₂ a b, Lifts P Bs o₁ κ₁ a → Lifts P Bs o₂ κ₂ b →
      Lifts P Bs (o₁ + o₂) (κ₁ + κ₂ + (2 * P.r + 2) * o₁) (a * b)
def CellVals : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq), ∀ x ∈ Q.DomR k r Bs.z Bs.z',
    Q.wCell k r (Fin.last r) x.1 * x.2 ∈ C6.bigPos Bs ∧
    Dmin k r Bs.z Bs.z' (Q.wCell k r (Fin.last r) x.1 * x.2) ⟨r, by omega⟩ = ∏ a, x.1 a ∧
    Dmin k r Bs.z Bs.z' (Q.wCell k r (Fin.last r) x.1 * x.2) (Fin.last (r + 1)) =
      (∏ a, x.1 a) * Q.zetaL k r Bs.z Bs.z' (Fin.last r) x.2 ∧
    Gf k r Bs.z Bs.z' (Q.wCell k r (Fin.last r) x.1 * x.2) =
      Complex.normSq (∏ a, x.1 a) * Q.GGl k r Bs.z Bs.z' x.2
def LiftZero : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (κ i j c : ℕ) (Pol : B.Mat P.k P.r → ℂ) (E : B.Mat P.k P.r → C6.EndH Wp Wq)
    (a : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')),
    let cf : B.Mat P.k P.r → C6.EndH Wp Wq := fun g =>
      (Pol g * (Dmin P.k P.r Bs.z Bs.z' g (Fin.last _))⁻¹ ^ i * (star (Dmin P.k P.r Bs.z Bs.z' g (Fin.last _)))⁻¹ ^ j *
        ((Gf P.k P.r Bs.z Bs.z' g : ℝ) : ℂ)⁻¹ ^ c) • E g
    U.IsPolyDeg κ Pol → C6.FibBound Bs E →
    (∀ p, Bs.inSS p → ∀ g ∈ C6.domL Bs ∅, ∀ J : Wq →L[ℂ] Wp,
      cf g ((Bs.π (Matrix.of p.1.1)).comp (J.comp (Bs.π' (Matrix.of p.2.1)⁻¹))) =
        (Bs.π (Matrix.of p.1.1)).comp ((cf (B.sgs p g) J).comp (Bs.π' (Matrix.of p.2.1)⁻¹))) →
    (∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
      (a.1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
        cf (Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2) ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)) →
    Lifts P Bs 0 κ a
def IdOp : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq),
    ∃ Dop : B.DiffOp k r Wp Wq, C6.InDDPlus Bs (fun j : Fin 0 => j.elim0) ∅ 0 0 Dop ∧ ∀ F, B.opApply Dop F = F
def LiftFns : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) P.r), Q.IsActualLevel X L →
    Lifts P Bs 0 0 1 ∧ Lifts P Bs 0 (P.r + 1) L.D ∧ Lifts P Bs 0 (P.r + 1) L.Db ∧ Lifts P Bs 0 P.r L.Dr ∧
      Lifts P Bs 0 P.r L.Drb ∧ Lifts P Bs 0 0 L.Di ∧ Lifts P Bs 0 0 L.Dbi ∧ Lifts P Bs 0 0 (gI L)
def LiftCap : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (l0 : ℕ),
    P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 →
      ∀ Y : ℂ, Lifts P Bs (2 * P.r + P.k + 1) 0 (P5.QQi L st 0 Y 0 0)
def ActualAlg : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq))
    (X : Q.ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r z z' π π'))) (l0 : ℕ),
    P5.IsData P z z' π π' X μ L st l0 →
      AHyp L st ∧ (∀ Y : ℂ, star Y = Y → P5.QQi L st 0 Y 0 0 = cst L st Y) ∧
        ∀ Y ∈ st.inv, ∃ p : Polynomial ℂ, st.xi Y = Polynomial.aeval (st.x Y) p
section fibre
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
def omC (Bs : B.RealPlaceData k r Wp Wq) (B0 : Fin k → Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin k → ℂ :=
  fun j => herm (Hpk k r) ((Hpk k r * gᴴ * Hpk k r) *ᵥ D.cofL Bs g) (B0 j)
def capV [FiniteDimensional ℂ Wq] (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (B0 : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ)
    (ν : Fin k → ℂ) : Wq →L[ℂ] Wq :=
  LinearMap.toContinuousLinearMap (Q.chatA (Qr.EB π' B0) w ν (star ν) : Module.End ℂ Wq)
def xFib [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (B0 : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ)
    (g : B.Mat k r) : C6.EndH Wp Wq :=
  (ContinuousLinearMap.compL ℂ Wq Wq Wp).flip
    (capV Bs.π' B0 w (C6.unitOf (Tz k r Bs.z') (Gf k r Bs.z Bs.z' g) (omC Bs B0 g)))
end fibre
def OmFacts : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (B0 : Fin k → Fin (2 * r + k + 1) → ℂ),
    Q.IsFrameOf k r [Bs.z'] B0 →
    (∀ j, U.IsPolyDeg (r + 1) fun g => omC Bs B0 g j) ∧
    (∀ g ∈ B.GV k r, C6.sq2 (omC Bs B0 g) = Gf k r Bs.z Bs.z' g / Tz k r Bs.z') ∧
    (∀ p, Bs.inSS p → ∀ g ∈ C6.domL Bs ∅,
      ∑ j, omC Bs B0 (B.sgs p g) j • B0 j = (Matrix.of p.2.1)⁻¹ *ᵥ ∑ j, omC Bs B0 g j • B0 j) ∧
    ∀ x ∈ Q.DomR k r Bs.z Bs.z', ∀ j, omC Bs B0 (Q.wCell k r (Fin.last r) x.1 * x.2) j =
      conj (∏ a, x.1 a) * herm (Hpk k r) (x.2⁻¹ *ᵥ Bs.z) (B0 j)
def CapVFrame : Prop :=
  ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (k r : ℕ)
    (z' : Fin (2 * r + k + 1) → ℂ) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (B0 : Fin k → Fin (2 * r + k + 1) → ℂ)
    (Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ) (ν : Fin k → ℂ), 1 ≤ k → inWb k r z' → 0 < Tz k r z' →
    Qr.IsRepW k r z' π' → Q.IsFrameOf k r [z'] B0 → C6.sq2 ν = 1 → Q.IsFrameOf k r [z', ∑ j, ν j • B0 j] Bs →
    ∀ (w : ℂ) (v : Wq), capV π' B0 w ν v = Q.capRep k r π' Bs w v
def CapVEquiv : Prop :=
  ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (k r : ℕ)
    (z' : Fin (2 * r + k + 1) → ℂ) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (B0 : Fin k → Fin (2 * r + k + 1) → ℂ)
    (ν ν' : Fin k → ℂ) (h : Q.Mx k r), 1 ≤ k → inWb k r z' → 0 < Tz k r z' →
    Qr.IsRepW k r z' π' → Q.IsFrameOf k r [z'] B0 → C6.sq2 ν = 1 → h ∈ UWset k r z' →
    ∑ j, ν' j • B0 j = h⁻¹ *ᵥ ∑ j, ν j • B0 j →
    ∀ w : ℂ, (capV π' B0 w ν').comp (π' h⁻¹) = (π' h⁻¹).comp (capV π' B0 w ν)
def XFibFacts : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π'),
    ∃ B0 : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z'] B0 ∧ ∀ Y : ℂ,
      C6.FibBound Bs (xFib Bs B0 (Y + ((P.k : ℂ) - 2) / 2)) ∧
      (∀ p, Bs.inSS p → ∀ g ∈ C6.domL Bs ∅, ∀ J : Wq →L[ℂ] Wp,
        xFib Bs B0 (Y + ((P.k : ℂ) - 2) / 2) g ((Bs.π (Matrix.of p.1.1)).comp (J.comp (Bs.π' (Matrix.of p.2.1)⁻¹))) =
          (Bs.π (Matrix.of p.1.1)).comp
            ((xFib Bs B0 (Y + ((P.k : ℂ) - 2) / 2) (B.sgs p g) J).comp (Bs.π' (Matrix.of p.2.1)⁻¹))) ∧
      ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
        (X.t Y 1 1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = ((Q.GGl P.k P.r Bs.z Bs.z' x.2 : ℝ) : ℂ) •
          xFib Bs B0 (Y + ((P.k : ℂ) - 2) / 2) (Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2)
            ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)
def LiftX : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (l0 : ℕ),
    P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → ∀ Y : ℂ, Lifts P Bs 0 0 (st.x Y)
def LetterLiftOfParts : Prop := BasicLift → LShape → MShape → LetterLift
def WordLiftOfParts : Prop := WordStep → LetterLift → WordLift
def LiftXOfParts : Prop := LiftZero → LiftClosed → XFibFacts → LiftX
def XFibOfParts : Prop := CellVals → OmFacts → CapVFrame → CapVEquiv → XFibFacts
def TopLiftOfParts : Prop := WordLift → LiftClosed → IdOp → LiftFns → LiftCap → ActualAlg → LiftX → TopLiftExists3
end
end Formalism.FourierDecayAlt.TL


