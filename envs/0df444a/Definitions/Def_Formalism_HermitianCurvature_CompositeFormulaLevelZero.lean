-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
-- name    : Formalism_HermitianCurvature_CompositeFormulaLevelZero
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:41:37.733435+00:00
-- url     : https://prove2.me/theorems/c8d30d2a-4266-46ee-a139-2e785a4b7fe9
-- title:
--   Composite Formula Level Zero
-- statement:
--   Definitions and structural lemmas for Composite Formula Level Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/CompositeFormulaLevelZero.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_StatementLE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ComplexOrder
noncomputable section
namespace Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T
def SesqOn {V : Type*} [AddCommGroup V] [Module ℂ V] (U : Submodule ℂ V) (β : V → V → ℂ) : Prop :=
  ∀ x ∈ U, ∀ x' ∈ U, ∀ y ∈ U, ∀ a : ℂ,
    β (x + a • x') y = β x y + a * β x' y ∧ β y (x + a • x') = β y x + conj a * β y x'
def NonnegOn {V : Type*} [AddCommGroup V] [Module ℂ V] (U : Submodule ℂ V) (β : V → V → ℂ) : Prop :=
  ∀ x ∈ U, 0 ≤ β x x
def GramOfForm : Prop :=
  ∀ (V α : Type) [AddCommGroup V] [Module ℂ V] (U : Submodule ℂ V) (β : V → V → ℂ) (v : α → V),
    SesqOn U β → NonnegOn U β → (∀ p, v p ∈ U) → ∀ Y : Finset α, TB.PSDOn Y (fun p q => β (v p) (v q))
def GramPSDOfForms : Prop :=
  ∀ (E W : Type) [Field E] (D : TB.Data E W),
    (∀ ε : ℝ, 0 < ε → ∀ (i : ℕ) (w : W), ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (U : Submodule ℂ V)
      (β : V → V → ℂ) (v : TB.Pt E → V), SesqOn U β ∧ NonnegOn U β ∧ (∀ p, v p ∈ U) ∧
        ∀ p q, D.gram ε i w p q = β (v p) (v q)) → D.GramPSD
section Objects
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
def fsv (s t : ℂ) : ℂ := Complex.exp (s * t - conj s * conj t)
def multiplicationOperator (W : Module.End ℂ (RadSp k r z z' π π')) (m : (Fin r → ℂ) → Mx k r → ℂ) : Prop :=
  ∀ (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) (g : Mx k r),
    (W Φ : Fn k r (Wq →L[ℂ] Wp)) c g = m c g • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g
def site (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (l : Fin r) : Site (Pr (RadSp k r z z' π π')) :=
  ⟨L.p l, L.c l, L.ci l⟩
def tprod (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Y : ℂ) (i : ℕ) : M2 (Pr (RadSp k r z z' π π')) :=
  if h : i < r then tprod L Y (i + 1) * Ts (site L ⟨i, h⟩) Y else 1
termination_by r - i
def QQi (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π'))) (i : Fin (r + 1))
    (Y : ℂ) : M2 (Pr (RadSp k r z z' π π')) :=
  (tprod L (star Y) i.val)ᴴ * st.QQ Y * tprod L Y i.val
def RRi (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π'))) (i : Fin (r + 1))
    (w : List (Letter ℂ S)) : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π')) :=
  RRw (QQi L st i) w
def bTl (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (l : Fin r) (w : List (Letter ℂ S)) :
    SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π')) :=
  bT (site L l) w
def act (M : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (x : Ix S → RadSp k r z z' π π') : Ix S → RadSp k r z z' π π' :=
  fun a => ∑ b, (M a b).1 (x b)
def InK (K : Submodule ℂ (RadSp k r z z' π π')) (x : Ix S → RadSp k r z z' π π') : Prop := ∀ a, x a ∈ K
def pairAt (μ : Measure (Mt k r)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) : ℂ :=
  ∫ x : Mt k r, B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) ∂μ
abbrev Cf (r : ℕ) (i : Fin (r + 1)) : Type := {l : Fin r // i.val ≤ l.val} → ℂ
def glue (i : Fin (r + 1)) (c : Fin r → ℂ) (c' : Cf r i) : Fin r → ℂ :=
  fun l => if h : i.val ≤ l.val then c' ⟨l, h⟩ else c l
def form (μ : Measure (Mt k r)) (i : Fin (r + 1)) (x y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) : ℂ :=
  ∫ c' : Cf r i, ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ a, pairAt μ (x a) (y a) (glue i c c')
def RRform (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (μ : Measure (Mt k r)) (i : Fin (r + 1)) (w : List (Letter ℂ S)) (x y : Ix S → RadSp k r z z' π π')
    (c : Fin r → ℂ) : ℂ :=
  form μ i (act (RRi L st i w) x) y c
def ph (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (μ : Measure (Mt k r)) (l : Fin r) (w : List (Letter ℂ S)) (x y : Ix S → RadSp k r z z' π π')
    (c : Fin r → ℂ) (t : ℂ) : ℂ :=
  ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * RRform L st μ l.succ w (act (bTl L l w) x) (act (bTl L l w) y) (Function.update c l t)
def zeta (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) : ℂ := zetaL k r z z' (Fin.last r) g
def topDens (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (w : List (Letter ℂ S)) (x y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) (g : Mx k r) : ℂ :=
  ∑ e, B.hsInner ((act ((Fr.ofWord L st w).d L * (Fr.ofWord L st w).F) x e : Fn k r (Wq →L[ℂ] Wp)) c g)
    ((act (Fr.ofWord L st w).F y e : Fn k r (Wq →L[ℂ] Wp)) c g)
end Objects
section Data
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
def IsData (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) :
    Prop :=
  IsPlace P z z' π π' ∧ B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ ∧ IsActualLevel X L ∧
    (∀ Y, st.QQ Y = M.sgn P l0 • X.QQ Y) ∧ st.q = M.qC P ∧ st.inv = {Y | ∀ ρ : M.Ty P, M.xC P ρ Y ≠ 0} ∧
    Fr.IsStarLevel L ∧ Fr.IsLevelStart L st
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
  (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
  (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π'))
def WordOK (l0 : ℕ) (w : List (Letter ℂ S)) : Prop :=
  Fr.admitted st w ∧ (∀ a ∈ w, a.pt.im = 0 ∧ I.OnCut P.u P.u' l0 a.pt.re) ∧
    w.Pairwise fun a a' => 2 < |a.pt.re - a'.pt.re|
def TopP (w : List (Letter ℂ S)) : Prop :=
  ∀ x y : Ix S → RadSp P.k P.r z z' π π', InK (K (Fin.last P.r)) x → InK (K (Fin.last P.r)) y →
    ∀ c ∈ OmX P.r,
      Integrable (fun g : Mt P.k P.r => topDens L st w x y c (Matrix.of g)) μ ∧
      (∀ (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π')),
        multiplicationOperator Wv (fun _ g => fsv s (zeta P.k P.r z z' g)) → multiplicationOperator Wv' (fun _ g => fsv (-s) (zeta P.k P.r z z' g)) →
        ∫ g : Mt P.k P.r, fsv s (zeta P.k P.r z z' (Matrix.of g)) * topDens L st w x y c (Matrix.of g) ∂μ =
          RRform L st μ (Fin.last P.r) w (act (Vw (mkP Wv Wv') s w) x) y c) ∧
      0 ≤ RRform L st μ (Fin.last P.r) w x x c
def StepP (w : List (Letter ℂ S)) (l : Fin P.r) : Prop :=
  ∀ x y : Ix S → RadSp P.k P.r z z' π π', InK (K l.castSucc) x → InK (K l.castSucc) y → ∀ c ∈ OmX P.r,
    ∃ φ : ℂ → ℂ, Continuous φ ∧ (∀ t, t ≠ 0 → φ t = ph L st μ l w x y c t) ∧
      (∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C * (1 + ‖t‖) ^ (-4 : ℤ)) ∧
      ∀ (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π')),
        multiplicationOperator Wv (fun c' _ => fsv s (c' l)) → multiplicationOperator Wv' (fun c' _ => fsv (-s) (c' l)) →
        ∫ t : ℂ, fsv s t * φ t = RRform L st μ l.castSucc w (act (Vw (mkP Wv Wv') s w) x) y c
def PosP (w : List (Letter ℂ S)) : Prop :=
  ∀ (i : Fin (P.r + 1)) (c : Fin P.r → ℂ), c ∈ OmX P.r →
    SesqOn (Submodule.pi Set.univ fun _ : Ix S => K i) (fun x y => RRform L st μ i w x y c) ∧
      NonnegOn (Submodule.pi Set.univ fun _ : Ix S => K i) (fun x y => RRform L st μ i w x y c)
def ThmPOn (l0 : ℕ) : Prop :=
  ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → TopP P z z' π π' μ L st K w ∧ (∀ l, StepP P z z' π π' μ L st K w l) ∧
    PosP P z z' π π' μ L st K w
end Data
section Steps
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
  (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
  (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
def TopIdent : Prop :=
  ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w →
  ∀ x y : Ix S → RadSp P.k P.r z z' π π', InK (K (Fin.last P.r)) x → InK (K (Fin.last P.r)) y → ∀ c ∈ OmX P.r,
    Integrable (fun g : Mt P.k P.r => topDens L st w x y c (Matrix.of g)) μ ∧
      RRform L st μ (Fin.last P.r) w x y c = ∫ g : Mt P.k P.r, topDens L st w x y c (Matrix.of g) ∂μ
def TopDensNonneg : Prop :=
  ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w →
  ∀ x : Ix S → RadSp P.k P.r z z' π π', InK (K (Fin.last P.r)) x → ∀ c ∈ OmX P.r, ∀ g : Mx P.k P.r,
    0 ≤ topDens L st w x x c g
def TopTwist : Prop :=
  ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w →
  ∀ (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π')),
    multiplicationOperator Wv (fun _ g => fsv s (zeta P.k P.r z z' g)) → multiplicationOperator Wv' (fun _ g => fsv (-s) (zeta P.k P.r z z' g)) →
    ∀ x y : Ix S → RadSp P.k P.r z z' π π', InK (K (Fin.last P.r)) x → InK (K (Fin.last P.r)) y → ∀ c ∈ OmX P.r,
      InK (K (Fin.last P.r)) (act (Vw (mkP Wv Wv') s w) x) ∧
      ∀ g, topDens L st w (act (Vw (mkP Wv Wv') s w) x) y c g = fsv s (zeta P.k P.r z z' g) * topDens L st w x y c g
def SliceIn : Prop :=
  ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (l : Fin P.r) (x : Ix S → RadSp P.k P.r z z' π π'),
    InK (K l.castSucc) x → InK (K l.succ) (act (bTl L l w) x)
def StepDens : Prop :=
  ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (l : Fin P.r) (x y : Ix S → RadSp P.k P.r z z' π π'),
    InK (K l.castSucc) x → InK (K l.castSucc) y → ∀ c ∈ OmX P.r,
    ∃ φ : ℂ → ℂ, Continuous φ ∧ (∀ t, t ≠ 0 → φ t = ph L st μ l w x y c t) ∧
      (∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C * (1 + ‖t‖) ^ (-4 : ℤ)) ∧ ∫ t : ℂ, φ t = RRform L st μ l.castSucc w x y c
def StepTwist : Prop :=
  ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (l : Fin P.r) (s : ℂ)
    (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π')),
    multiplicationOperator Wv (fun c' _ => fsv s (c' l)) → multiplicationOperator Wv' (fun c' _ => fsv (-s) (c' l)) →
    ∀ x y : Ix S → RadSp P.k P.r z z' π π', InK (K l.castSucc) x → InK (K l.castSucc) y → ∀ c ∈ OmX P.r,
      InK (K l.castSucc) (act (Vw (mkP Wv Wv') s w) x) ∧
      ∀ t, t ≠ 0 → ph L st μ l w (act (Vw (mkP Wv Wv') s w) x) y c t = fsv s t * ph L st μ l w x y c t
def FormSesq : Prop :=
  ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (i : Fin (P.r + 1)) (c : Fin P.r → ℂ), c ∈ OmX P.r →
    SesqOn (Submodule.pi Set.univ fun _ : Ix S => K i) (fun x y => RRform L st μ i w x y c)
def ThmPFromSteps : Prop :=
  TopIdent (S := S) P z z' π π' μ L st K l0 → TopDensNonneg (S := S) P z z' π π' L st K l0 →
    TopTwist (S := S) P z z' π π' L st K l0 → SliceIn (S := S) P z z' π π' L st K l0 →
    StepDens (S := S) P z z' π π' μ L st K l0 → StepTwist (S := S) P z z' π π' μ L st K l0 →
    FormSesq (S := S) P z z' π π' μ L st K l0 → ThmPOn (S := S) P z z' π π' μ L st K l0
end Steps
def ThmPFromStepsAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ),
    ThmPFromSteps (S := S) P z z' π π' μ L st K l0
def GramPSDOfThmP : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ) (E W : Type) [Field E] (D : TB.Data E W),
    ThmPOn (S := S) P z z' π π' μ L st K l0 →
    (∀ ε : ℝ, 0 < ε → ∀ (i : ℕ) (w : W), ∃ (i' : Fin (P.r + 1)) (w' : List (Letter ℂ S)) (c : Fin P.r → ℂ)
      (v : TB.Pt E → Ix S → RadSp P.k P.r z z' π π'), WordOK P z z' π π' st l0 w' ∧ c ∈ OmX P.r ∧
        (∀ p, InK (K i') (v p)) ∧ ∀ p q, D.gram ε i w p q = RRform L st μ i' w' (v p) (v q) c) →
    D.GramPSD
def bTall {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
    (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (w : List (Letter ℂ S)) : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π')) :=
  ((List.finRange r).reverse.map fun l => bTl L l w).prod
def CompositeFormulaLevelZero {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ) : Prop :=
  ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w →
  ∀ x y : Ix S → RadSp P.k P.r z z' π π', InK (K 0) x → InK (K 0) y → ∀ c ∈ OmX P.r,
    Integrable (fun q : Cf P.r 0 × Mt P.k P.r => ((∏ l, ‖q.1 l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      topDens L st w (act (bTall L w) x) (act (bTall L w) y) (glue 0 c q.1) (Matrix.of q.2)) (volume.prod μ) ∧
    RRform L st μ 0 w x y c = ∫ q : Cf P.r 0 × Mt P.k P.r, ((∏ l, ‖q.1 l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      topDens L st w (act (bTall L w) x) (act (bTall L w) y) (glue 0 c q.1) (Matrix.of q.2) ∂(volume.prod μ)
def ThmPLEOfCor : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Sl : Type) [Fintype Sl] [DecidableEq Sl]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ) (S : LE.Sys),
    CompositeFormulaLevelZero (S := Sl) P z z' π π' μ L st K l0 →
    (∀ (N : ℕ) (Y : Fin N → ℝ), N ≤ S.Ntot → S.OnBoxes (List.ofFn Y) → ∀ ε : ℝ, 0 < ε →
      ∃ (w : List (Letter ℂ Sl)) (x : Ix Sl → RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ),
        WordOK P z z' π π' st l0 w ∧ InK (K 0) x ∧ c ∈ OmX P.r ∧
        (S.principalHermitianLattice ε (LE.plus (List.ofFn Y)) : ℂ) = RRform L st μ 0 w x x c ∧
        ((∫ ω, LE.sq S.B ((S.fam N).dw Y) ((S.fam N).gw Y (LE.mulF S.B (S.c.sc ε 1) (S.fam N).u)) ω ∂S.B.μ : ℝ) : ℂ) =
          ∫ q : Cf P.r 0 × Mt P.k P.r, ((∏ l, ‖q.1 l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
            topDens L st w (act (bTall L w) x) (act (bTall L w) x) (glue 0 c q.1) (Matrix.of q.2) ∂(volume.prod μ)) →
    S.ThmP
def WaveCExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (π' : Mx k r → (Wq →L[ℂ] Wq)) (l : Fin r) (s : ℂ),
    ∃ Wv : Module.End ℂ (RadSp k r z z' π π'), multiplicationOperator Wv (fun c _ => fsv s (c l))
def WaveZExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (π' : Mx k r → (Wq →L[ℂ] Wq)) (s : ℂ),
    ∃ Wv : Module.End ℂ (RadSp k r z z' π π'), multiplicationOperator Wv (fun _ g => fsv s (zeta k r z z' g))
def OfWordRR : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] (r : ℕ) (L : R.LevelData A r)
    (st : Fr.Start A) (w : List (Letter ℂ S)),
    (Fr.ofWord L st w).RR = RRw st.QQ w ∧ ∀ Y, (Fr.ofWord L st w).TT Y = TTw st.QQ w Y
section TopParts
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
  (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
  (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
def AdjTop : Prop :=
  ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w →
  ∀ x y : Ix S → RadSp P.k P.r z z' π π', InK (K (Fin.last P.r)) x → InK (K (Fin.last P.r)) y → ∀ c ∈ OmX P.r,
    Integrable (fun g : Mt P.k P.r => topDens L st w x y c (Matrix.of g)) μ ∧
      form μ (Fin.last P.r)
        (act (star (Fr.ofWord L st w).F * (Fr.ofWord L st w).d L * (Fr.ofWord L st w).F) x) y c =
        ∫ g : Mt P.k P.r, topDens L st w x y c (Matrix.of g) ∂μ
def TopIdentFromParts : Prop :=
  IsData P z z' π π' X μ L st l0 → Fr.FrameAll → OfWordRR → AdjTop (S := S) P z z' π π' μ L st K l0 →
    TopIdent (S := S) P z z' π π' μ L st K l0
end TopParts
section StepParts
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
  (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
  (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
def WaveSite : Prop :=
  IsActualLevel X L → ∀ (l : Fin P.r) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π')),
    multiplicationOperator Wv (fun c _ => fsv s (c l)) → multiplicationOperator Wv' (fun c _ => fsv (-s) (c l)) →
    IsWave (mkP Wv Wv') (mkP Wv' Wv) ∧ mkP Wv Wv' * (site L l).c = (site L l).c * mkP Wv Wv' ∧
      mkP Wv Wv' * (site L l).ci = (site L l).ci * mkP Wv Wv' ∧
      (site L l).p * mkP Wv Wv' = mkP Wv Wv' * (site L l).p + algebraMap ℂ _ s * mkP Wv Wv' * (site L l).c
def WaveCommQQ : Prop :=
  ∀ (l : Fin P.r) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π')),
    multiplicationOperator Wv (fun c _ => fsv s (c l)) → multiplicationOperator Wv' (fun c _ => fsv (-s) (c l)) →
    ∀ (Y : ℂ) (a b : Fin 2), Commute (mkP Wv Wv') (QQi L st l.succ Y a b)
def WaveK : Prop :=
  ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (l : Fin P.r) (s : ℂ)
    (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π')),
    multiplicationOperator Wv (fun c' _ => fsv s (c' l)) → multiplicationOperator Wv' (fun c' _ => fsv (-s) (c' l)) →
    ∀ x : Ix S → RadSp P.k P.r z z' π π', InK (K l.castSucc) x → InK (K l.castSucc) (act (Vw (mkP Wv Wv') s w) x)
def StepTwistFromParts : Prop :=
  IsData P z z' π π' X μ L st l0 → PlaneWaveVec → WaveSite P z z' π π' X L → WaveCommQQ P z z' π π' L st →
    WaveK (S := S) P z z' π π' st K l0 → StepTwist (S := S) P z z' π π' μ L st K l0
end StepParts
def nV (P : M.Par) : ℕ := 2 * P.r + P.k + 1
def Auser (P : M.Par) (N : ℕ) : ℝ := 127 * ((P.r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nV P : ℝ) ^ 2 + (nV P : ℝ) ^ 3)
def mmUser (P : M.Par) (N : ℕ) : ℕ := 5 + 3 * (P.r + 1) * (N + 2) * nV P + N * P.r
def HerClasses : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (A : ℝ) (mm : ℕ),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    Auser P (Fintype.card S) ≤ A → mmUser P (Fintype.card S) ≤ mm →
    ∃ K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π'),
      AdjTop (S := S) P z z' π π' μ L st K l0 ∧ TopDensNonneg (S := S) P z z' π π' L st K l0 ∧
      TopTwist (S := S) P z z' π π' L st K l0 ∧ SliceIn (S := S) P z z' π π' L st K l0 ∧
      StepDens (S := S) P z z' π π' μ L st K l0 ∧ WaveK (S := S) P z z' π π' st K l0 ∧
      FormSesq (S := S) P z z' π π' μ L st K l0 ∧ CompositeFormulaLevelZero (S := S) P z z' π π' μ L st K l0 ∧
      ∀ (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (ε : ℝ), 0 < ε → (∀ (A' : ℝ) (m' : ℕ), B.InCC A' m' F) →
        (∀ g ∈ B.GV P.k P.r, F g ≠ 0 → ε ≤ Gf P.k P.r z z' g) →
        ∃ Φ ∈ K 0, ∀ x ∈ DomR P.k P.r z z',
          (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = resG P.k P.r (Fin.last P.r) (B.JF D F) x.1 x.2
def WaveCommQQAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ),
    IsData P z z' π π' X μ L st l0 → WaveCommQQ P z z' π π' L st
def WaveSiteAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π')
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r), WaveSite P z z' π π' X L
def ThmPActual : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (A : ℝ) (mm : ℕ),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    Auser P (Fintype.card S) ≤ A → mmUser P (Fintype.card S) ≤ mm →
    ∃ K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π'),
      ThmPOn (S := S) P z z' π π' μ L st K l0 ∧ SliceIn (S := S) P z z' π π' L st K l0 ∧
      CompositeFormulaLevelZero (S := S) P z z' π π' μ L st K l0 ∧
      ∀ (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (ε : ℝ), 0 < ε → (∀ (A' : ℝ) (m' : ℕ), B.InCC A' m' F) →
        (∀ g ∈ B.GV P.k P.r, F g ≠ 0 → ε ≤ Gf P.k P.r z z' g) →
        ∃ Φ ∈ K 0, ∀ x ∈ DomR P.k P.r z z',
          (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = resG P.k P.r (Fin.last P.r) (B.JF D F) x.1 x.2
def ThmPActualFromInputs : Prop :=
  HerClasses → WaveCommQQAll → WaveSiteAll → Fr.FrameAll → OfWordRR → PlaneWaveVec → ThmPActual
def ThmPActualFromHer : Prop := HerClasses → WaveCommQQAll → ThmPActual
end Formalism.FourierDecayAlt.P5


