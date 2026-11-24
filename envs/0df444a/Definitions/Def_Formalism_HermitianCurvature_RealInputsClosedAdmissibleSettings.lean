-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
-- name    : Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:53:59.72081+00:00
-- url     : https://prove2.me/theorems/eb415e7e-c834-44a5-82a8-fe397ed170e4
-- title:
--   Real Inputs Closed Admissible Settings
-- statement:
--   Definitions and structural lemmas for Real Inputs Closed Admissible Settings, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/RealInputsClosedAdmissibleSettings.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.KB
open Finset Filter Topology NumberField MeasureTheory Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Classical
def CutWord (P : M.Par) (l0 : ℕ) (w : List C.Letter) : Prop :=
  (∀ a : Fin w.length, I.OnCut P.u P.u' l0 (w.get a).2) ∧
    ∀ a b : Fin w.length, a ≠ b → 2 < |(w.get a).2 - (w.get b).2|
def plusW : List ℝ → List C.Letter → List C.Letter
  | [], w => w
  | y :: ys, w => (true, y) :: plusW ys w
def minusW : List ℝ → List C.Letter → List C.Letter
  | [], w => w
  | y :: ys, w => (false, y + 1) :: minusW ys w
def pairJ {X : Type} {w : List C.Letter} (Ξ : (Wd.Ix (Fin w.length) → X) → (Wd.Ix (Fin w.length) → X) → ℂ) :
    (ys : List ℝ) → (Wd.Ix (Fin (plusW ys w).length) → X) → (Wd.Ix (Fin (minusW ys w).length) → X) → ℂ
  | [], x, x' => Ξ x x'
  | _ :: ys, x, x' =>
    pairJ Ξ ys (fun e => x (Fin.cons (1 : Fin 2) e)) (fun e => x' (Fin.cons (0 : Fin 2) e)) -
      pairJ Ξ ys (fun e => x (Fin.cons (0 : Fin 2) e)) (fun e => x' (Fin.cons (1 : Fin 2) e))
def firstSt {w : List C.Letter} : (ys : List ℝ) → Wd.Ix (Fin w.length) → Wd.Ix (Fin (plusW ys w).length)
  | [], e => e
  | _ :: ys, e => Fin.cons (0 : Fin 2) (firstSt ys e)
def uInv {X : Type} [AddCommGroup X] [Module ℂ X] (s : ℂ) :
    (w : List C.Letter) → (Wd.Ix (Fin w.length) → X) → Wd.Ix (Fin w.length) → X
  | [], x => x
  | l :: w, x => fun e =>
    if e (0 : Fin (w.length + 1)) = 0 then uInv s w (fun e' => x (Fin.cons (0 : Fin 2) e')) fun a => e a.succ
    else uInv s w (fun e' => x (Fin.cons (1 : Fin 2) e')) (fun a => e a.succ) +
      (if l.1 then s else conj s) • uInv s w (fun e' => x (Fin.cons (0 : Fin 2) e')) fun a => e a.succ
def onOld {X : Type} {w : List C.Letter} (M : (Wd.Ix (Fin w.length) → X) → Wd.Ix (Fin w.length) → X) :
    (ys : List ℝ) → (Wd.Ix (Fin (plusW ys w).length) → X) → Wd.Ix (Fin (plusW ys w).length) → X
  | [], x => M x
  | _ :: ys, x => fun e =>
    onOld M ys (fun e' => x (Fin.cons (e (0 : Fin ((plusW ys w).length + 1))) e')) fun a => e a.succ
section place
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
def CptCoef (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  B.CkOn ⊤ (B.GV k r) F ∧ (∃ R : ℝ, ∀ g ∈ B.GV k r, F g ≠ 0 → B.gN g ≤ R) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ B.GV k r, F g ≠ 0 → ε ≤ Gf k r Bs.z Bs.z' g
def waveG (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)) : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp) :=
  fun e g => P5.fsv s (Dmin k r Bs.z Bs.z' g ⟨1, by omega⟩) • uInv s w x e g
def slv (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (i : ℕ) (hi : i ≤ r) (w : List C.Letter)
    (p : C.LPt) (hp : D.ptSize p = i) : Wd.Ix (Fin w.length) → B.Mat k (r - i) → (Wq →L[ℂ] Wp) :=
  fun a => D.castF (by simp [hp]) (D.sliceAt k r T.base.z T.base.z' (D.uwG k r T.base.z T.base.z' F i hi w a) p)
def ZetaNorm (Bs : B.RealPlaceData k r Wp Wq) (μ : Measure (Mt k r)) : Prop :=
  B.IsHaarOn (Q.Glev k r (Fin.last r)) μ ∧ ∀ ψ : ℂ → ENNReal, Measurable ψ →
    ∫⁻ g, ψ (Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g)) ∂μ =
      ∫⁻ ζ, ENNReal.ofReal (B2.zWeight k (Tz k r Bs.z) (Tz k r Bs.z') ζ) * ψ ζ
end place
def levW (P : M.Par) (i : ℕ) (c : ℂ) : ℝ :=
  if i = P.r + 1 then B2.zWeight P.k P.T P.T' c else ‖c‖ ^ (2 * (C.Mlev P.k P.r i - 2))
section lift
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def IsTopLift2 (P : M.Par) (l0 : ℕ) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (Θ : Top.TopLift P.k P.r Wp Wq) : Prop :=
  ∀ w, CutWord P l0 w → ∀ F, CptCoef Bs F → ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', Top.IsRadOf P Bs Φ F →
    ∀ e : Wd.Ix (Fin w.length), Top.IsRadOf P Bs
      (P5.act ((Fr.ofWord L st (D.positionted w)).F * P5.bTall L (D.positionted w)) (Top.firstStateVector Φ) e) (Θ.Θ w e F)
def InDDplus2 (P : M.Par) (l0 : ℕ) (Bs : B.RealPlaceData P.k P.r Wp Wq) (Cb : ℝ) (Θ : Top.TopLift P.k P.r Wp Wq) : Prop :=
  ∀ w, CutWord P l0 w → ∀ e : Wd.Ix (Fin w.length), ∃ (nf : ℕ) (fib : Fin nf → B.Mat P.k P.r → C6.EndH Wp Wq)
    (o κ : ℕ) (Dop : B.DiffOp P.k P.r Wp Wq),
    (∀ j, C6.FibBound Bs (fib j)) ∧ C6.InDDPlus Bs fib ∅ o κ Dop ∧
    (o : ℝ) ≤ Cb * (w.length : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) ∧ (κ : ℝ) ≤ Cb * ((P.r : ℝ) + 1) * (o : ℝ) ∧
    ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), ∀ g ∈ C6.domL Bs ∅, Θ.Θ w e F g = B.opApply Dop F g
structure Pl (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] where
  l0 : ℕ
  T : D.LevTower P.k P.r Wp Wq
  ν' : Fin (2 * P.r + P.k + 1) → ℂ
  m₀ : B.Mat P.k P.r
  Θ : Top.TopLift P.k P.r Wp Wq
  TP : Top.TypeProj P T.base.π T.base.z (m₀ *ᵥ ν')
  hl : 1 ≤ l0 ∧ l0 ≤ P.k ∧ 2 ≤ P.k
  hT : D.TowerNormalised T
  hF : D.IsBaseFrame T.base ν' m₀
  hP : Q.IsPlace P T.base.z T.base.z' T.base.π T.base.π'
  hΘ : ∃ X μ L st, P5.IsData P T.base.z T.base.z' T.base.π T.base.π' X μ L st l0 ∧ IsTopLift2 P l0 T.base L st Θ
variable [FiniteDimensional ℂ Wp] {P : M.Par}
def Pl.RR (p : Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ) (w : List C.Letter) (a b : C.LPt) : ℂ :=
  D.RRplace p.T (M.sgn P p.l0) p.ν' p.m₀ (Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP) F i w a b
def Pl.form (p : Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter)
    (x x' : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) : ℂ :=
  D.formLev p.T (M.sgn P p.l0) ⟨j, by omega⟩ w x x'
def Pl.V (p : Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (a : C.LPt) : Wq →L[ℂ] Wp :=
  D.vecV p.T.base p.ν' p.m₀ F a
end lift
def TopLiftExists2 : Prop :=
  ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (l0 : ℕ),
    P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 →
      ∃ Θ : Top.TopLift P.k P.r Wp Wq, IsTopLift2 P l0 Bs L st Θ ∧ InDDplus2 P l0 Bs Cb Θ
def SliceCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq) (F) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (a : C.LPt) (ha : D.IsLocPt a j),
    CptCoef p.T.base F → ∀ e, CptCoef (p.T.bs j) (slv p.T F j hj w a ha.2 e)
def SizeStd : Prop :=
  P5.ThmPActual → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (ys : List ℝ),
    CutWord P p.l0 (plusW ys w) → CutWord P p.l0 (minusW ys w) → ys.Pairwise (fun y y' => 2 < |y - y'|) →
    (∀ y ∈ ys, 0 < (Wd.qw (M.qC P) (D.positionted w) y).re) ∧
    ∀ x x' ε, 0 < ε → (∀ e, JC.NiceCoef (p.T.bs j) ε (x e)) → (∀ e, JC.NiceCoef (p.T.bs j) ε (x' e)) →
      ‖pairJ (p.form j hj w) ys x x'‖ ^ 2 * (ys.map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) y).re).prod ≤
        (p.form j hj (plusW ys w) x x).re * (p.form j hj (minusW ys w) x' x').re
def VIso : Prop :=
  P5.ThmPActual → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter), CutWord P p.l0 w →
    ∀ (s : ℂ) x x' ε, 0 < ε → (∀ e, JC.NiceCoef (p.T.bs j) ε (x e)) → (∀ e, JC.NiceCoef (p.T.bs j) ε (x' e)) →
      (∀ e, JC.NiceCoef (p.T.bs j) ε (waveG (p.T.bs j) s w x e)) ∧
      p.form j hj w (waveG (p.T.bs j) s w x) (waveG (p.T.bs j) s w x') = p.form j hj w x x'
def DegWave : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq) (F) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h h' : C.LPt)
    (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j) (K : ℕ) (grid : Fin K → Fin (2 * j + 1) → ℝ) (s : ℂ)
    (Mo : (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) →ₗ[ℂ]
      (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))),
    (∀ ε x, (∀ e, JC.NiceCoef (p.T.bs j) ε (x e)) → ∀ e, JC.NiceCoef (p.T.bs j) ε (Mo x e)) →
    CptCoef p.T.base F → (∀ a, Function.Injective (grid a)) →
    s ^ K * p.form j hj w (waveG (p.T.bs j) s w (Mo (slv p.T F j hj w h hh.2))) (slv p.T F j hj w h' hh'.2) =
      ∑ n : Fin K → Fin (2 * j + 1), ((∏ a, F7.lagCo (grid a) (n a) : ℝ) : ℂ) *
        pairJ (p.form j hj w) (List.ofFn fun a => grid a (n a))
          (waveG (p.T.bs j) s _ (onOld Mo _ (slv p.T F j hj (plusW (List.ofFn fun a => grid a (n a)) w) h hh.2)))
          (slv p.T F j hj (minusW (List.ofFn fun a => grid a (n a)) w) h' hh'.2)
def DegLift : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq) (F) (j s : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h h' : C.LPt) (t t' : ℂ)
    (ha : D.IsLocPt (h ++ [(s, t)]) j) (ha' : D.IsLocPt (h' ++ [(s, t')]) j)
    (K : ℕ) (grid : Fin K → Fin (2 * (j - s) + s + 1) → ℝ), CptCoef p.T.base F → (∀ a, Function.Injective (grid a)) →
    ((-1) ^ (s - 1) * (t⁻¹ - t'⁻¹)) ^ K * p.RR F j w (h ++ [(s, t)]) (h' ++ [(s, t')]) =
      ∑ n : Fin K → Fin (2 * (j - s) + s + 1), ((∏ a, F7.lagCo (grid a) (n a) : ℝ) : ℂ) *
        pairJ (p.form j hj w) (List.ofFn fun a => grid a (n a))
          (slv p.T F j hj (plusW (List.ofFn fun a => grid a (n a)) w) _ ha.2)
          (slv p.T F j hj (minusW (List.ofFn fun a => grid a (n a)) w) _ ha'.2)
def PStd : Prop :=
  P5.ThmPActual → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq) (F) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h h' : C.LPt)
    (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j) (Cb : ℝ), InDDplus2 P p.l0 p.T.base Cb p.Θ → CptCoef p.T.base F → CutWord P p.l0 w →
    ∃ φ : ℂ → ℂ, Continuous φ ∧ Integrable φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = (levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      ∀ s : ℂ, ∫ c, P5.fsv s c * φ c =
        p.form j hj w (waveG (p.T.bs j) s w (slv p.T F j hj w h hh.2)) (slv p.T F j hj w h' hh'.2)
def SliceStep : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq) (F) (j : ℕ) (hj : j + 1 ≤ P.r) (h : C.LPt) (c : ℂ) (hh : D.IsLocPt h j) (hc : D.IsLocPt (h ++ [(1, c)]) (j + 1)),
    CptCoef p.T.base F → ∀ γ ∈ B.GV P.k (P.r - (j + 1)),
    γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    B.JF (p.T.bs (j + 1)) (slv p.T F (j + 1) hj [] _ hc.2 fun a => a.elim0) γ =
      B.JF (p.T.bs j) (slv p.T F j (by omega) [] h hh.2 fun a => a.elim0)
        (D.castM (by omega : 1 + (P.r - (j + 1)) = P.r - j) (U.mMap P.k 1 (P.r - (j + 1)) (Matrix.of fun _ _ => c) γ))
def HeadAlg : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (M : Type) [AddCommGroup M] [Module ℂ M] (k r m : ℕ) (hm : m + 2 ≤ r)
    (z' : Fin (2 * r + k + 1) → ℂ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (c u : ℂ),
    Formalism.REAL.GlRel E → C3.RightRuleFn k r z' E La → Z.det ≠ 0 → c ≠ 0 →
    (∀ (b : Fin (m + 1)) (x : A), La (E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨b, by omega⟩) * x) =
      (c * Z⁻¹ b (Fin.last m)) • La x) →
    (∀ (a : Fin (m + 1)) (q : Fin (2 * r + k + 1)), xi ⟨a, by omega⟩ q = if h : q.val < m + 1 then Z a ⟨q, h⟩ else 0) →
    (∀ q : Fin (2 * r + k + 1), xi ⟨m + 1, by omega⟩ q = if q.val = m + 1 then c else 0) →
    (Z.det * c)⁻¹ • La (C3.AAx k r E xi (m + 2) hm u) =
      Z.det⁻¹ • La (C3.AAx k r E xi (m + 1) (by omega) u *
          (algebraMap ℂ A (u - ((m + 1 : ℕ) : ℂ)) + E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩))) -
        (c * Z.det⁻¹) • La (C3.AAx k r E xi m (by omega) u)
def RadHead : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq) (F) (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h h' : C.LPt)
    (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j)
    (X : Q.ActualOps (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π')
    (μ : Measure (Mt P.k (P.r - j))) (L) (st)
    (Φ Φ' : Wd.Ix (Fin w.length) →
      Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π'),
    P5.IsData (JC.parLev P j) (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π' X μ L st p.l0 →
    ZetaNorm (p.T.bs j) μ → CptCoef p.T.base F → CutWord P p.l0 w →
    (∀ e, Top.IsRadOf (JC.parLev P j) (p.T.bs j) (Φ e) (slv p.T F j (by omega) w h hh.2 e)) →
    (∀ e, Top.IsRadOf (JC.parLev P j) (p.T.bs j) (Φ' e) (slv p.T F j (by omega) w h' hh'.2 e)) →
    ∀ t : ℂ, t ≠ 0 →
      P5.ph L st μ (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) (D.positionted w) Φ Φ' (fun _ => 1) t =
        (levW P (j + 1) t : ℂ) * p.RR F (j + 1) w (h ++ [(1, t)]) (h' ++ [(1, t)])
def HeadTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq) (F) (w : List C.Letter) (h h' : C.LPt)
    (hh : D.IsLocPt h P.r) (hh' : D.IsLocPt h' P.r)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r))) (L) (st)
    (Cb : ℝ) (Φ Φ' : Wd.Ix (Fin w.length) →
      Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π'),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    InDDplus2 P p.l0 p.T.base Cb p.Θ → CptCoef p.T.base F → CutWord P p.l0 w →
    (∀ e, Top.IsRadOf (JC.parLev P P.r) (p.T.bs P.r) (Φ e) (slv p.T F P.r le_rfl w h hh.2 e)) →
    (∀ e, Top.IsRadOf (JC.parLev P P.r) (p.T.bs P.r) (Φ' e) (slv p.T F P.r le_rfl w h' hh'.2 e)) →
    ∀ x ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z',
      P5.topDens L st (D.positionted w) Φ Φ' x.1 x.2 =
        p.RR F (P.r + 1) w (h ++ [(1, Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)])
          (h' ++ [(1, Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)])
def PhiZero : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq) (F), CptCoef p.T.base F →
    ∃ Φ0 : G.Mat (P.r + 1) → (Wq →L[ℂ] Wp), ContDiff ℝ (⊤ : ℕ∞) Φ0 ∧ HasCompactSupport Φ0 ∧
      (∀ Z ∈ tsupport Φ0, G.detM Z ≠ 0) ∧
      ∀ (a : C.LPt) (σ : Equiv.Perm (Fin (P.r + 1))) (d : Fin (P.r + 1) → ℂ), D.IsLocPt a (P.r + 1) →
        U.hMat σ d = D.ptMatN a (P.r + 1) →
        p.V F a = U.PhiTop (p := P.r + 1) (s := 0) U.betaU σ d Φ0 fun x => x.elim0
def KloostDens : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (Ψ : G.Mat n → V),
    ContDiff ℝ (⊤ : ℕ∞) Ψ → HasCompactSupport Ψ → (∀ Z ∈ tsupport Ψ, G.detM Z ≠ 0) →
    (∀ d : Fin n → ℂ, (∀ a, d a ≠ 0) → U.PhiTop (p := n) (s := 0) U.betaU 1 d Ψ (fun x => x.elim0) = 0) →
    ∀ (a : C.LPt) (σ : Equiv.Perm (Fin n)) (d : Fin n → ℂ), D.IsLocPt a n → U.hMat σ d = D.ptMatN a n →
      U.PhiTop (p := n) (s := 0) U.betaU σ d Ψ (fun x => x.elim0) = 0
def DensC : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq) (F), CptCoef p.T.base F → Top.IsRadOf P p.T.base 0 F → ∀ a, p.V F a = 0
def ThetaCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq) (F) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (Cb : ℝ), InDDplus2 P p.l0 p.T.base Cb p.Θ → CptCoef p.T.base F →
    CutWord P p.l0 w →
    ∃ F', CptCoef p.T.base F' ∧ (∀ g ∈ C6.domL p.T.base ∅, p.Θ.Θ w e F g = F' g) ∧
      ∀ a, p.V (p.Θ.Θ w e F) a = p.V F' a
def TopFirst : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq) (F F') (w : List C.Letter) (y : ℝ) (e : Wd.Ix (Fin w.length)) (Cb : ℝ), InDDplus2 P p.l0 p.T.base Cb p.Θ → CptCoef p.T.base F →
    CutWord P p.l0 ((true, y) :: w) → CptCoef p.T.base F' → (∀ g ∈ C6.domL p.T.base ∅, p.Θ.Θ w e F g = F' g) →
    ∀ a, p.V (p.Θ.Θ ((true, y) :: w) (Fin.cons (0 : Fin 2) e) F) a =
      p.V (fun g => (Dmin P.k P.r p.T.base.z p.T.base.z' g (Fin.last _))⁻¹ •
        C3.AAop P.k P.r P.r le_rfl ((y : ℂ) + ((2 * P.r + P.k : ℕ) : ℂ) / 2) F' g) a
def DegTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq) (F) (s : ℕ) (w : List C.Letter) (h : C.LPt) (t : ℂ) (K : ℕ) (grid : Fin K → Fin (D.ptSize h + 1) → ℝ)
    (e : Wd.Ix (Fin w.length)) (Cb : ℝ), InDDplus2 P p.l0 p.T.base Cb p.Θ → 2 ≤ s → D.IsLocPt (h ++ [(s, t)]) (P.r + 1) → CptCoef p.T.base F →
    (∀ a, Function.Injective (grid a)) → (∀ n : Fin K → Fin (D.ptSize h + 1),
      CutWord P p.l0 (plusW (List.ofFn fun a => grid a (n a)) w)) →
    ((-1) ^ (s - 1) / t) ^ K • p.V (p.Θ.Θ w e F) (h ++ [(s, t)]) =
      ∑ n : Fin K → Fin (D.ptSize h + 1), ((∏ a, F7.lagCo (grid a) (n a) : ℝ) : ℂ) •
        p.V (p.Θ.Θ (plusW (List.ofFn fun a => grid a (n a)) w) (firstSt _ e) F) (h ++ [(s, t)])
def FormLimit : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ) (cut : ℕ → B.Mat P.k P.r → ℂ),
    InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    (∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) →
    (∀ n, CptCoef p.T.base fun g => cut n g • D.cutF p.T.base χ f ε g) ∧
    ∀ i w, CutWord P p.l0 w → w.length ≤ N → ∀ a b,
      Tendsto (fun n => p.RR (fun g => cut n g • D.cutF p.T.base χ f ε g) i w a b) atTop
        (𝓝 (p.RR (D.cutF p.T.base χ f ε) i w a b))
section hermitianSpaces
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
def IsLeadingFormSetting (Cb Cc : ℝ) (S : C.HidaSetting E Wp Wq) (p : ∀ v, Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ) : Prop :=
  0 < S.G.g1 ∧ 0 < S.G.g2 ∧ S6.Unram E ∧ C6.IsCut0 χ ∧ (∀ v, (S.G.place (S.pl v)).Ok) ∧
  Sz.IsWord S.G.k S.de ∧ Sz.IsWord S.G.k S.de' ∧ 1 ≤ S.l ∧ S.l + 2 ≤ S.G.k ∧ S.de S.l ≠ S.de' S.l ∧
  C.GridsOK S ∧ GridsRich S ∧ JCT.LongCut Cc S ∧ Cc ≤ S.CA ∧
  Cc * ((S.G.r : ℝ) + 1) ^ 4 *
    ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) ≤ A₀ ∧
  ∀ v, (p v).l0 = S.l + 1 ∧ InDDplus2 (D.parOf S v) (S.l + 1) (p v).T.base Cb (p v).Θ ∧
    S.pd v = D.componentFamilySetting_ofSetting (p v).T (f v) χ (M.sgn (D.parOf S v) (S.l + 1)) (p v).ν' (p v).m₀
      (Top.topOf (D.parOf S v) (S.l + 1) (p v).T (p v).ν' (p v).m₀ (p v).Θ (p v).TP) (S.g : ℝ) (S6.rd E) 1 ∧
    B.CkOn ⊤ (B.GV S.G.k S.G.r) (f v) ∧ ∀ m : ℕ, B.InCC A₀ m (f v)
def EigenF (S : C.HidaSetting E Wp Wq) (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) : Prop :=
  ∀ v, ∀ Y : ℝ, ∀ g ∈ B.GV S.G.k S.G.r, Q.CV S.G.k S.G.r (Y : ℂ) (f v) g = ((S.P v Y : ℝ) : ℂ) • f v g
def CutInside (S : C.HidaSetting E Wp Wq) : Prop :=
  ∀ v, ∀ Y ∈ Set.Icc (S.cutLo v) (S.cutHi v), I.OnCut (D.parOf S v).u (D.parOf S v).u' (S.l + 1) Y
def plT (S : C.HidaSetting E Wp Wq) (p : ∀ v, Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))) :
    ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) := fun v => (p v).T
def plν (S : C.HidaSetting E Wp Wq) (p : ∀ v, Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))) :
    Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ := fun v => (p v).ν'
def plm (S : C.HidaSetting E Wp Wq) (p : ∀ v, Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))) :
    Fin S.f → B.Mat S.G.k S.G.r := fun v => (p v).m₀
def plTop (S : C.HidaSetting E Wp Wq) (p : ∀ v, Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f) :
    (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ :=
  Top.topOf (D.parOf S v) (S.l + 1) (p v).T (p v).ν' (p v).m₀ (p v).Θ (p v).TP
def IsLeadingFormPlace (Cb Cc : ℝ) (S : C.HidaSetting E Wp Wq) (p : ∀ v, Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ) : Prop :=
  IsLeadingFormSetting Cb Cc S p f χ A₀ ∧ EigenF S f ∧ CutInside S
end hermitianSpaces
def BuiltBounds2 : Prop :=
  P5.ThmPActual → ∀ Cb : ℝ, ∃ Cc C₄ : ℝ, 1 ≤ C₄ ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    IsLeadingFormSetting Cb Cc S p f χ A₀ →
      C.ThmPPos S ∧ IntAll S ∧ (∃ Lw, JC.WaveByPlaces S Lw ∧ JC.HidaCurvatureBarriers S Lw) ∧
      (∃ Ll Ll', JC.LiftBelowTop S Ll ∧ JC.LiftTopDiag S Ll' ∧ JC.ThresholdsLift S Ll Ll') ∧
      JC.SumFormConcrete S C₄
def RealInputsClosedLeadingForm : Prop :=
  P5.ThmPActual → JC.RadialModuleForm → JC.PosDensityMM → JC.FormLevSesqMM → JC.ThmPModuleOfActualMM →
  D.MuRHaar → MA.LemmaEModel → JCT.LevelsActualBuilt → JCT.SlicesCCBuilt → JCT.ModelPlaceBuilt → Top.TopPSDT →
  BuiltBounds2 →
  ∀ Cb : ℝ, ∃ C₆ Cc C₄ : ℝ, 0 < C₆ ∧ 1 ≤ C₄ ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ)
    (c : LE.Cut) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : TB.Pt E → H),
    IsLeadingFormPlace Cb Cc S p f χ A₀ → JCT.SliceBudget S A₀ → c.χ = χ →
    (∀ v, C₆ * ((S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2) ≤
      S.cutHi v - S.cutLo v) →
    JCT.VtTensor S (plT S p) f (plν S p) (plm S p) Vt →
    ∃ (L : ∀ v : Fin S.f, R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
      (j : ∀ v : Fin S.f, M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT)
      (lam : ∀ v : Fin S.f, Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ) (Cm σ : Fin S.f → ℝ),
      (∀ v, JC.IsModelPlace S (plT S p) f χ v (L v) (j v) (lam v) c (Cm v) (σ v)) ∧
      ∀ Kr hK0 Th e, PB.RealInputs (S.mkData Kr hK0 Th e) C₄ (∏ v, JCT.jvModel S j Cm v) Vt
def RealInputsClosedAdmissibleSettings : Prop :=
  P5.ThmPActual → JC.RadialModuleForm → JC.PosDensityMM → JC.FormLevSesqMM → JC.ThmPModuleOfActualMM →
  D.MuRHaar → MA.LemmaEModel → JCT.LevelsActualBuilt → JCT.SlicesCCBuilt → JCT.ModelPlaceBuilt2 → Top.TopPSDT →
  BuiltBounds2 →
  ∀ Cb : ℝ, ∃ C₆ Cc C₄ : ℝ, 0 < C₆ ∧ 1 ≤ C₄ ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ)
    (c : LE.Cut) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : TB.Pt E → H),
    IsLeadingFormPlace Cb Cc S p f χ A₀ → JCT.SliceBudget S A₀ → c.χ = χ →
    (∀ v, C₆ * ((S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2) ≤
      S.cutHi v - S.cutLo v) →
    JCT.VtTensor S (plT S p) f (plν S p) (plm S p) Vt →
    ∃ (L : ∀ v : Fin S.f, R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
      (j : ∀ v : Fin S.f, M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT)
      (lam : ∀ v : Fin S.f, Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ) (Cm σ : Fin S.f → ℝ),
      (∀ v, JC.IsModelPlace S (plT S p) f χ v (L v) (j v) (lam v) c (Cm v) (σ v)) ∧
      ∀ Kr hK0 Th e, PB.RealInputs (S.mkData Kr hK0 Th e) C₄ (∏ v, JCT.jvModel S j Cm v) Vt
end
end Formalism.FourierDecayAlt.KB


