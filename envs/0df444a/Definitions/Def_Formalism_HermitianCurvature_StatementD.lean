-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementD
-- name    : Formalism_HermitianCurvature_StatementD
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T15:05:24.858076+00:00
-- url     : https://prove2.me/theorems/ac9faf2f-7366-4e7e-a467-0d839c2231e9
-- title:
--   Statement D
-- statement:
--   Definitions and structural lemmas for Statement D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementD.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.D
open Finset MeasureTheory NumberField
open scoped ComplexConjugate Matrix
noncomputable section
open Classical Formalism.REAL Formalism.QuantumDeterminants
def castM {k a b : ℕ} (h : a = b) (g : B.Mat k a) : B.Mat k b :=
  Matrix.reindex (finCongr (by rw [h])) (finCongr (by rw [h])) g
def castV {k a b : ℕ} (h : a = b) (v : Fin (2 * a + k + 1) → ℂ) : Fin (2 * b + k + 1) → ℂ :=
  fun i => v (Fin.cast (by rw [h]) i)
def castF {k a b : ℕ} {E : Type*} (h : a = b) (F : B.Mat k b → E) : B.Mat k a → E := fun g => F (castM h g)
def ptSize (p : C.LPt) : ℕ := (p.map Prod.fst).sum
def ptEntry : C.LPt → ℕ → ℕ → ℂ
  | [], _, _ => 0
  | (s, t) :: rest, a, b =>
    if a < s ∧ b < s then (if a + b + 1 = s then t else 0)
    else if s ≤ a ∧ s ≤ b then ptEntry rest (a - s) (b - s) else 0
def ptMatN (p : C.LPt) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := fun a b => ptEntry p a b
def ptMat (p : C.LPt) : Matrix (Fin (ptSize p)) (Fin (ptSize p)) ℂ := ptMatN p (ptSize p)
def ptPartner : C.LPt → ℕ → ℕ
  | [], a => a
  | (s, _) :: rest, a => if a < s then s - 1 - a else s + ptPartner rest (a - s)
def ptScal : C.LPt → ℕ → ℂ
  | [], _ => 0
  | (s, t) :: rest, a => if a < s then t else ptScal rest (a - s)
def ptPartnerF (p : C.LPt) (a : Fin (ptSize p)) : Fin (ptSize p) :=
  if h : ptPartner p a < ptSize p then ⟨ptPartner p a, h⟩ else a
def ptPerm (p : C.LPt) : Equiv.Perm (Fin (ptSize p)) :=
  if h : Function.Bijective (ptPartnerF p) then Equiv.ofBijective _ h else Equiv.refl _
def ptDiag (p : C.LPt) : Fin (ptSize p) → ℂ := fun a => ptScal p a
def IsLocPt (p : C.LPt) (i : ℕ) : Prop := (∀ b ∈ p, 1 ≤ b.1 ∧ b.2 ≠ 0) ∧ ptSize p = i
def ptHead (p : C.LPt) : C.LPt := p.dropLast
def ptLast (p : C.LPt) : ℕ × ℂ := p.getLast?.getD (0, 0)
def ptG (TT : ℝ) (r : ℕ) (p : C.LPt) : ℝ :=
  Complex.normSq (ptMatN p (r + 1)).det - TT * Complex.normSq (ptMatN p r).det
def ptGG (TT : ℝ) (p : C.LPt) : ℝ := Complex.normSq (ptLast p).2 - TT
def toStd (r : ℕ) (g : ℝ) : ℕ → C.LPt → C.LPt
  | _, [] => []
  | b, (s, t) :: rest =>
    (s, (((g / (2 * Real.pi)) ^ S6.nuBlock r b s : ℝ) : ℂ) * Complex.I ^ (s - 1) * t) :: toStd r g (b + s) rest
section orbit
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
def orbIntegrand (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (p : B.SS k r) :
    Wq →L[ℂ] Wp :=
  B.xiTau D (1, 1) p • B.rho D p F γ
def IsNormCut (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (μR : Measure (Mt k r)) (θ : B.SS k r → ℝ) : Prop :=
  Measurable θ ∧ (∀ p, 0 ≤ θ p) ∧ ∀ p, D.inSS p → ∫ x, θ (C6.actR γ (Matrix.of x) p) ∂μR = 1
def orbJ (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (μR : Measure (Mt k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    Wq →L[ℂ] Wp :=
  if h : ∃ θ, IsNormCut D γ μR θ ∧ Integrable (fun p => θ p • orbIntegrand D γ F p) D.μSS then
    ∫ p, h.choose p • orbIntegrand D γ F p ∂D.μSS
  else 0
def rhoOfU (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : B.Mat k r :=
  if h : ∃ ρ ∈ C6.Rset γ, C2.uMap k r D.z ρ = u then h.choose else 1
def muR (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1))) : Measure (Mt k r) :=
  (volume : Measure (C2.Lstidx w → ℂ)).map fun x => Matrix.of.symm (rhoOfU D γ (Matrix.conjTranspose (C2.lowOf (fun q => q.1) x)))
def prW (k r : ℕ) (z v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  let vb : Fin (2 * r + k + 1) → ℂ := fun i => if r ≤ i.val ∧ i.val ≤ r + k then v i else 0
  vb - (herm (Hpk k r) vb z / herm (Hpk k r) z z) • z
def cofR (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  ∑ b, (Zhat k r D.z D.z' γ).adjugate b (Fin.last r) • (γ *ᵥ fvec k r D.z' b)
def cofL (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  ∑ a, conj ((Zhat k r D.z D.z' γ).adjugate (Fin.last r) a) • fvec k r D.z a
def IsBaseFrame (D : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) : Prop :=
  inWb k r ν' ∧ herm (Hpk k r) ν' D.z' = 0 ∧ herm (Hpk k r) ν' ν' = 1 ∧ m₀ ∈ Q.Glev k r (Fin.last r) ∧
    m₀ *ᵥ D.z' = ((√(Tz k r D.z' / Tz k r D.z) : ℝ) : ℂ) • D.z
def IsDFrame (D : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ γ : B.Mat k r) : Prop :=
  (∃ a : ℝ, 0 < a ∧ prW k r D.z (cofR D γ) = ((a : ℂ) * (Zhat k r D.z D.z' γ).det) • (m₀ *ᵥ ν')) ∧
  (∃ a : ℝ, 0 < a ∧ prW k r D.z' (γ⁻¹ *ᵥ cofL D γ) = ((a : ℂ) * conj (Zhat k r D.z D.z' γ).det) • ν') ∧
  ∀ u, (∀ a, herm (Hpk k r) u (fvec k r D.z a) = 0 ∧ herm (Hpk k r) u (γ *ᵥ fvec k r D.z' a) = 0) →
    prW k r D.z u = m₀ *ᵥ prW k r D.z' (γ⁻¹ *ᵥ u)
def vecV (D : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (p : C.LPt) : Wq →L[ℂ] Wp :=
  if h : IsLocPt p (r + 1) ∧ 0 < ptG (Tz k r D.z * Tz k r D.z') r p then
    if h' : ∃ γ ∈ B.GV k r, Zhat k r D.z D.z' γ = ptMatN p (r + 1) ∧ IsDFrame D ν' m₀ γ then
      orbJ D h'.choose (muR D h'.choose (h.1.2 ▸ ptPerm p)) F
    else 0
  else 0
end orbit
def sliceAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (F : B.Mat k r → E) (p : C.LPt) : B.Mat k (r - ptSize p) → E :=
  if h : ptSize p ≤ r then
    U.PhiFun (s := 0) k (r - ptSize p) (ptPerm p) (ptDiag p)
      (castV (by omega) z) (castV (by omega) z') (castF (by omega) F) (fun a => a.elim0)
  else fun _ => 0
def muN (k : ℕ) : (r : ℕ) → Measure (Mt k r)
  | 0 => Measure.dirac (Matrix.of.symm 1)
  | ρ + 1 => ((U.muRC k 1 ρ).prod (muN k ρ)).map fun x =>
      Matrix.of.symm (castM (Nat.add_comm 1 ρ) (U.Rn k 1 ρ x.1 * U.embG k 1 ρ (Matrix.of x.2)))
structure LevTower (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] where

  bs : ∀ j : ℕ, B.RealPlaceData k (r - j) Wp Wq

  z_lev : ∀ j (hj : j ≤ r), castV (by omega) (liftVec k j (r - j) (bs j).z) = (bs 0).z

  z'_lev : ∀ j (hj : j ≤ r), castV (by omega) (liftVec k j (r - j) (bs j).z') = (bs 0).z'

  π_lev : ∀ j (hj : j ≤ r) (y : B.Mat k (r - j)), (bs j).π y = (bs 0).π (castM (by omega) (ιLev k j (r - j) y))

  π'_lev : ∀ j (hj : j ≤ r) (y : B.Mat k (r - j)), (bs j).π' y = (bs 0).π' (castM (by omega) (ιLev k j (r - j) y))
def LevTower.base {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (T : LevTower k r Wp Wq) : B.RealPlaceData k r Wp Wq := T.bs 0
def TowerNormalised {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (T : LevTower k r Wp Wq) : Prop :=
  ∀ j, j ≤ r → (T.bs j).μW Set.univ = 1 ∧ (T.bs j).μW' Set.univ = 1 ∧ (T.bs j).μN = muN k (r - j)
def Op (X : Type) : Type := X → X
section op
variable {X : Type} [AddCommGroup X] [Module ℂ X]
instance : AddCommGroup (Op X) := inferInstanceAs (AddCommGroup (X → X))
instance : Mul (Op X) := ⟨fun f g => fun x => (f : X → X) ((g : X → X) x)⟩
instance : One (Op X) := ⟨fun x => x⟩
def cOp (c : ℂ) : Op X := fun x => c • x
def ap (f : Op X) (x : X) : X := (f : X → X) x
variable {S : Type} [Fintype S] [DecidableEq S]
def scal (M : Wd.M2 (Wd.SlopeTestRemainingChoices S ℂ)) : Wd.M2 (Wd.SlopeTestRemainingChoices S (Op X)) := M.map fun A => A.map cOp
def TTop (QQ : ℂ → Wd.M2 (Op X)) : List (Wd.Letter ℂ S) → ℂ → Wd.M2 (Wd.SlopeTestRemainingChoices S (Op X))
  | [], Y => (QQ Y).map fun x => Matrix.diagonal fun _ => x
  | l :: w, Y =>
    if l.plus then TTop QQ w Y * scal (Wd.Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt))
    else scal (Wd.Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y)) * TTop QQ w Y
def insOp (a : S) (M : Wd.M2 (Wd.SlopeTestRemainingChoices S (Op X))) : Wd.SlopeTestRemainingChoices S (Op X) :=
  ∑ i, ∑ j, (Wd.eU a i j : Wd.SlopeTestRemainingChoices S ℂ).map cOp * M i j
def RRop (QQ : ℂ → Wd.M2 (Op X)) : List (Wd.Letter ℂ S) → Wd.SlopeTestRemainingChoices S (Op X)
  | [] => 1
  | l :: w => RRop QQ w * insOp l.intersection_update_fsHerm_neg_one (if l.plus then TTop QQ w l.pt else (TTop QQ w l.pt).transpose)
def actOp (M : Wd.SlopeTestRemainingChoices S (Op X)) (x : Wd.Ix S → X) : Wd.Ix S → X := fun a => ∑ b, ap (M a b) (x b)
end op
def positionted (w : List C.Letter) : List (Wd.Letter ℂ (Fin w.length)) :=
  List.ofFn fun a : Fin w.length => ⟨(w.get a).1, a, ((w.get a).2 : ℂ)⟩
section levels
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
def QQlev (T : LevTower k r Wp Wq) (s : ℂ) (j : Fin (r + 1)) (Y : ℂ) :
    Wd.M2 (Op (B.Mat k (r - j) → (Wq →L[ℂ] Wp))) :=
  Matrix.of fun a b => (fun f => s • Q.tL k (r - j) (T.bs j).z (T.bs j).z' 0 Y a b f :
    Op (B.Mat k (r - j) → (Wq →L[ℂ] Wp)))
def RRlev (T : LevTower k r Wp Wq) (s : ℂ) (j : Fin (r + 1)) (w : List C.Letter) :
    Wd.SlopeTestRemainingChoices (Fin w.length) (Op (B.Mat k (r - j) → (Wq →L[ℂ] Wp))) :=
  RRop (QQlev T s j) (positionted w)
variable [FiniteDimensional ℂ Wq]
def formLev (T : LevTower k r Wp Wq) (s : ℂ) (j : Fin (r + 1)) (w : List C.Letter)
    (x x' : Wd.Ix (Fin w.length) → B.Mat k (r - j) → (Wq →L[ℂ] Wp)) : ℂ :=
  ∑ a, B.beta (T.bs j) (actOp (RRlev T s j w) x a) (x' a)
end levels
section letters
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
def vLet (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (l : C.Letter) (e : Fin 2)
    (f : B.Mat k r → E) : B.Mat k r → E := fun g =>
  if e = 1 ∧ j = 0 then 0 else
  if l.1 then
    (Dmin k r z z' g ⟨j, by omega⟩)⁻¹ •
      C3.AAop k r (j - e) (by omega) ((l.2 : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) f g
  else
    (conj (Dmin k r z z' g ⟨j, by omega⟩))⁻¹ •
      C3.AAvop k r (j - e) (by omega) ((l.2 : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) f g
def uwG (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (j : ℕ) (hj : j ≤ r) :
    (w : List C.Letter) → Wd.Ix (Fin w.length) → B.Mat k r → E
  | [], _ => F
  | l :: w, e => vLet k r z z' j hj l (e (0 : Fin (w.length + 1))) (uwG k r z z' F j hj w fun a => e a.succ)
end letters
def kapG (g rd : ℝ) : ℝ := 2 * Real.pi / (g * rd)
def deG (g rd : ℝ) : ℝ := 2 / (rd * g ^ 3)
def bSt (κ : ℝ) (p : C.LPt) : ℝ :=
  (p.map fun a => ∏ m ∈ Finset.Ico 1 a.1, (κ ^ (1 - 2 * (m : ℤ)) / Real.pi) ^ (a.1 - m)).prod
def GamLev (k r : ℕ) (κ de : ℝ) (i : ℕ) : ℝ :=
  ∏ l ∈ Finset.Ioc i (r + 1), κ ^ (-(4 * ((r : ℤ) + 1 - l) * (C.Mlev k r l - 1))) / de
def cutF {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (χ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (ε : ℝ) :
    B.Mat k r → (Wq →L[ℂ] Wp) :=
  fun g => (χ (Gf k r D.z D.z' g / ε) : ℂ) • f g
section place
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def RRplace (T : LevTower k r Wp Wq) (s : ℂ) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (top : (B.Mat k r → (Wq →L[ℂ] Wp)) → List C.Letter → C.LPt → C.LPt → ℂ)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (i : ℕ) (w : List C.Letter) (p q : C.LPt) : ℂ :=
  if h : IsLocPt p i ∧ IsLocPt q i then
    if hi : i ≤ r then
      formLev T s ⟨i, by omega⟩ w
        (fun a => castF (by simp [h.1.2]) (sliceAt k r T.base.z T.base.z' (uwG k r T.base.z T.base.z' F i hi w a) p))
        (fun a => castF (by simp [h.2.2]) (sliceAt k r T.base.z T.base.z' (uwG k r T.base.z T.base.z' F i hi w a) q))
    else if i = r + 1 then
      (if w = [] then B.hsInner (vecV T.base ν' m₀ F p) (vecV T.base ν' m₀ F q) else top F w p q)
    else 0
  else 0
def componentFamilySetting_ofSetting (T : LevTower k r Wp Wq) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (s : ℂ)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (top : (B.Mat k r → (Wq →L[ℂ] Wp)) → List C.Letter → C.LPt → C.LPt → ℂ) (g rd a₀ : ℝ) :
    C.PlaceData k r Wp Wq where
  bs := T.base
  f0 := f
  G := ptGG (Tz k r T.base.z * Tz k r T.base.z')
  RR ε i w p q :=
    ((a₀ ^ 2 / (bSt (kapG g rd) p * bSt (kapG g rd) q * GamLev k r (kapG g rd) (deG g rd) i) : ℝ) : ℂ) *
      RRplace T s ν' m₀ top (cutF T.base χ f ε) i w (toStd r g 1 p) (toStd r g 1 q)
end place
section props
def PtPermSpec : Prop :=
  ∀ (p : C.LPt) (i : ℕ), IsLocPt p i →
    (∀ a : Fin (ptSize p), ((ptPerm p a : Fin (ptSize p)) : ℕ) = ptPartner p a) ∧
    ptMat p = C2.monoP (ptPerm p) (ptDiag p) ∧ ptMat p = U.hMat (ptPerm p) (ptDiag p)
def PtGSpec : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (p : C.LPt) (γ : B.Mat k r), IsLocPt p (r + 1) →
    Zhat k r z z' γ = ptMatN p (r + 1) → ptG (Tz k r z * Tz k r z') r p = Gf k r z z' γ
def OrbJOfData : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (O : C6.OrbData D γ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    (∃ θ, IsNormCut D γ O.μR θ ∧ Integrable (fun p => θ p • orbIntegrand D γ F p) D.μSS) →
      O.J F = orbJ D γ O.μR F
def OrbJIndep : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (μR : Measure (Mt k r)),
    C6.IsRelevant D γ → B.IsHaarOn (C6.Rset γ) μR → ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (θ θ' : B.SS k r → ℝ),
      IsNormCut D γ μR θ → IsNormCut D γ μR θ' →
      Integrable (fun p => θ p • orbIntegrand D γ F p) D.μSS →
      Integrable (fun p => θ' p • orbIntegrand D γ F p) D.μSS →
      ∫ p, θ p • orbIntegrand D γ F p ∂D.μSS = ∫ p, θ' p • orbIntegrand D γ F p ∂D.μSS
def MuRHaar : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1)))
    (d : Fin (r + 1) → ℂ), γ ∈ B.GV k r → (∀ a, d a ≠ 0) → Zhat k r D.z D.z' γ = C2.monoP w d →
      B.IsHaarOn (C6.Rset γ) (muR D γ w)
def OrbDataOfParts : Prop :=
  MuRHaar → OrbJIndep →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (w : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ), C6.IsRelevant D γ → (∀ a, d a ≠ 0) →
    Zhat k r D.z D.z' γ = C2.monoP w d →
    ∃ O : C6.OrbData D γ, O.μR = muR D γ w ∧
      ∀ F, (∃ θ, IsNormCut D γ O.μR θ ∧ Integrable (fun p => θ p • orbIntegrand D γ F p) D.μSS) →
        O.J F = orbJ D γ (muR D γ w) F
def PtRelevant : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (p : C.LPt) (γ : B.Mat k r), IsLocPt p (r + 1) →
    γ ∈ B.GV k r → Zhat k r D.z D.z' γ = ptMatN p (r + 1) → C6.IsRelevant D γ
def OrbJConv : Prop :=
  ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1)))
    (d : Fin (r + 1) → ℂ) (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    γ ∈ B.GV k r → C6.IsRelevant D γ → (∀ a, d a ≠ 0) → Zhat k r D.z D.z' γ = C2.monoP w d →
    0 < Gf k r D.z D.z' γ → c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    B.InCC A 1 F →
    ∃ θ, IsNormCut D γ (muR D γ w) θ ∧ Integrable (fun p => θ p • orbIntegrand D γ F p) D.μSS
def VecVIndep : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (p : C.LPt) (hp : IsLocPt p (r + 1)) (γ : B.Mat k r),
    IsBaseFrame D ν' m₀ → 0 < ptG (Tz k r D.z * Tz k r D.z') r p →
    γ ∈ B.GV k r → Zhat k r D.z D.z' γ = ptMatN p (r + 1) → IsDFrame D ν' m₀ γ →
      vecV D ν' m₀ F p = orbJ D γ (muR D γ (hp.2 ▸ ptPerm p)) F
def DFrameExists : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (p : C.LPt), IsBaseFrame D ν' m₀ → IsLocPt p (r + 1) → 0 < ptG (Tz k r D.z * Tz k r D.z') r p →
      ∃ γ ∈ B.GV k r, Zhat k r D.z D.z' γ = ptMatN p (r + 1) ∧ IsDFrame D ν' m₀ γ
def SliceOm : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (h p : C.LPt) (n : ℕ) (t : ℂ)
    (hp : p = h ++ [(n + 1, t)]) (hle : ptSize p ≤ r) (γ : B.Mat k (r - ptSize p)),
    IsLocPt p (ptSize p) →
    Integrable (fun ξ : U.Xi k (ptSize p) 0 (r - ptSize p) (ptPerm p) =>
        U.psiStar k (r - ptSize p) (ptPerm p) (castV (by omega) z) (castV (by omega) z') ξ •
          castF (by omega) F (U.gaXi k (r - ptSize p) (ptPerm p) (ptDiag p) ξ (fun a => a.elim0) γ))
      (U.muXi k (ptSize p) 0 (r - ptSize p) (ptPerm p)) →
    sliceAt k r z z' F p γ =
      ((Real.pi ^ ((n + 1) * n / 2) : ℝ) : ℂ) •
        G.OmLong U.betaU n (fun Z => U.PhiFun k (r - ptSize p) (ptPerm h) (ptDiag h)
          (castV (by subst hp; simp only [ptSize, List.map_append, List.sum_append, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil] at hle ⊢; omega) z)
          (castV (by subst hp; simp only [ptSize, List.map_append, List.sum_append, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil] at hle ⊢; omega) z')
          (castF (by subst hp; simp only [ptSize, List.map_append, List.sum_append, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil] at hle ⊢; omega) F) Z γ) t
def MuNHaar : Prop := ∀ k r : ℕ, B.IsHaarOn (Nset k r) (muN k r)
def MuNSplit : Prop :=
  ∀ (k r j : ℕ) (hj : j ≤ r),
    muN k r =
      ((U.muRC k j (r - j)).prod ((volume : Measure (G.UT j → ℂ)).prod (muN k (r - j)))).map fun x =>
        Matrix.of.symm (castM (by omega : j + (r - j) = r)
          (U.Rn k j (r - j) x.1 * U.muP k j (r - j) (G.upper x.2.1) * U.embG k j (r - j) (Matrix.of x.2.2)))
def NhatCovol : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], S6.Unram E →
    ∀ (g : ℕ) (ν : ℤ) (s : ℕ), 0 < g →
      ZLattice.covolume (J.eLat E (S6.perLat E g ν s) 1) =
        S6.rd E ^ (2 * ν * (S6.deg E : ℤ)) * (S6.rd E / 2) ^ S6.deg E * (g : ℝ) ^ (3 * S6.deg E)
def TowerExists : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq), D.μW Set.univ = 1 → D.μW' Set.univ = 1 →
    D.μN = muN k r → ∃ T : LevTower k r Wp Wq, T.base = D ∧ TowerNormalised T
def ModuleOfWdOn : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (K : Submodule ℂ X) (Y : Type) [AddCommGroup Y] [Module ℂ Y]
    (res : X →ₗ[ℂ] Y) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (S : Type) [Fintype S] [DecidableEq S]
    (φ : A →ₐ[ℂ] Module.End ℂ Y) (Qop : ℂ → Wd.M2 (Op X)) (QQ : ℂ → Wd.M2 A),
    (∀ y a b, ∀ x ∈ K, ap (Qop y a b) x ∈ K ∧ res (ap (Qop y a b) x) = φ (QQ y a b) (res x)) →
    ∀ (w : List (Wd.Letter ℂ S)) (x : Wd.Ix S → X), (∀ a, x a ∈ K) → ∀ a,
      actOp (RRop Qop w) x a ∈ K ∧ res (actOp (RRop Qop w) x a) = ∑ b, φ (Wd.RRw QQ w a b) (res (x b))
def LevelZero : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (T : LevTower k r Wp Wq) (s : ℂ)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (top : (B.Mat k r → (Wq →L[ℂ] Wp)) → List C.Letter → C.LPt → C.LPt → ℂ)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (w : List C.Letter), B.CkOn ⊤ (B.GV k r) F → Wd.Good (positionted w) →
    RRplace T s ν' m₀ top F 0 w [] [] = C7.principalHermitianLattice T.base s w F
def GoodOfAdm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type) [∀ x, NormedAddCommGroup (Wp x)]
    [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
    (w : S.W) (v : Fin S.f), Wd.Good (positionted (w.1 v))
section hermitianSpaces
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]
abbrev parOf (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : M.Par :=
  ⟨S.G.k, S.G.r, S.T, S.T', (S.G.place (S.pl v)).u S.de, (S.G.place (S.pl v)).u S.de'⟩
def AdmAt (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) : Prop := ∃ w : S.W, w.1 v = a
variable [∀ x, FiniteDimensional ℂ (Wq x)]
def IsBuilt (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ) (A₀ : ℝ) :
    Prop :=
  C6.IsCut0 χ ∧ ∀ v,
    S.pd v = componentFamilySetting_ofSetting (T v) (f v) χ (M.sgn (parOf S v) (S.l + 1)) (ν' v) (m₀ v) (top v) (S.g : ℝ) (S6.rd E) 1 ∧
    TowerNormalised (T v) ∧ IsBaseFrame (T v).base (ν' v) (m₀ v) ∧
    Q.IsPlace (parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' ∧
    (∀ m : ℕ, B.InCC A₀ m (f v)) ∧
    ∀ Y : ℝ, ∀ g ∈ B.GV S.G.k S.G.r, Q.CV S.G.k S.G.r (Y : ℂ) (f v) g = ((S.P v Y : ℝ) : ℂ) • f v g
end hermitianSpaces
def LemmaEOfRR0 : Prop :=
  LevelZero → GoodOfAdm →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type) [∀ x, NormedAddCommGroup (Wp x)]
    [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
    (T : ∀ v : Fin S.f, LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ) (A₀ : ℝ)
    (jv : Fin S.f → ℝ), IsBuilt S T f χ ν' m₀ top A₀ →
    (∀ v ε, 0 < ε → B.CkOn ⊤ (B.GV S.G.k S.G.r) (cutF (T v).base χ (f v) ε)) →
    (∀ w : S.W, ∀ v, Filter.Tendsto
      (fun ε => C7.principalHermitianLattice (T v).base (M.sgn (parOf S v) (S.l + 1)) (w.1 v) (cutF (T v).base χ (f v) ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((S.sizeAt v (w.1 v) * jv v : ℝ) : ℂ))) →
    C.LemmaE S fun v => jv v / GamLev S.G.k S.G.r (kapG S.g (S6.rd E)) (deG S.g (S6.rd E)) 0
def ThmPPosOfForms : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type) [∀ x, NormedAddCommGroup (Wp x)]
    [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq),
    (∀ v, ∀ ε, 0 < ε → ∀ i, i ≤ S.G.r + 1 → ∀ w : S.W, ∀ Y : Finset C.LPt,
      TB.PSDOn Y ((S.pd v).RR ε i (w.1 v))) → C.ThmPPos S
section module
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def ThmPModule (T : LevTower k r Wp Wq) (s : ℂ) (admitted : List C.Letter → Prop)
    (KK : ∀ j : Fin (r + 1), Submodule ℂ (B.Mat k (r - j) → (Wq →L[ℂ] Wp))) : Prop :=
  ∀ j w, admitted w → P5.SesqOn (Submodule.pi Set.univ fun _ => KK j) (formLev T s j w) ∧
    P5.NonnegOn (Submodule.pi Set.univ fun _ => KK j) (formLev T s j w)
def SliceInClass (T : LevTower k r Wp Wq) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (admitted : List C.Letter → Prop)
    (KK : ∀ j : Fin (r + 1), Submodule ℂ (B.Mat k (r - j) → (Wq →L[ℂ] Wp))) : Prop :=
  ∀ ε, 0 < ε → ∀ (i : ℕ) (hi : i ≤ r) (w : List C.Letter), admitted w → ∀ (p : C.LPt) (hp : IsLocPt p i)
    (a : Wd.Ix (Fin w.length)),
    castF (by simp [hp.2]) (sliceAt k r T.base.z T.base.z' (uwG k r T.base.z T.base.z' (cutF T.base χ f ε) i hi w a) p)
      ∈ KK ⟨i, by omega⟩
def TopPSD (T : LevTower k r Wp Wq) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (admitted : List C.Letter → Prop)
    (top : (B.Mat k r → (Wq →L[ℂ] Wp)) → List C.Letter → C.LPt → C.LPt → ℂ) : Prop :=
  ∀ ε, 0 < ε → ∀ w, admitted w → w ≠ [] → ∀ Y : Finset C.LPt, TB.PSDOn Y (top (cutF T.base χ f ε) w)
end module
def ThmPPosOfModule : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type) [∀ x, NormedAddCommGroup (Wp x)]
    [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
    (T : ∀ v : Fin S.f, LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ) (A₀ : ℝ),
    IsBuilt S T f χ ν' m₀ top A₀ →
    (∀ v, ∃ KK : ∀ j : Fin (S.G.r + 1), Submodule ℂ (B.Mat S.G.k (S.G.r - j) → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
      ThmPModule (T v) (M.sgn (parOf S v) (S.l + 1)) (AdmAt S v) KK ∧ SliceInClass (T v) (f v) χ (AdmAt S v) KK) →
    (∀ v, TopPSD (T v) (f v) χ (AdmAt S v) (top v)) →
    C.ThmPPos S
end props
end
end Formalism.FourierDecayAlt.D


