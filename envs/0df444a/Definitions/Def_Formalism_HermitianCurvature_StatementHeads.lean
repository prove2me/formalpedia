-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementHeads
-- name    : Formalism_HermitianCurvature_StatementHeads
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T02:10:09.040341+00:00
-- url     : https://prove2.me/theorems/84559afa-5b8c-5213-872f-9ed759cf463d
-- title:
--   Statement Heads
-- statement:
--   Definitions and structural lemmas for Statement Heads, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementHeads.lean

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_StatementTL
import Definitions.Def_Formalism_HermitianCurvature_StatementTop
import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
section
open Matrix Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants
section lift
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
def cLift (s : ℕ) (τ : ℂ) (b : Bool) : ℂ := (-1 : ℂ) ^ (s - 1) * (if b then τ⁻¹ else (conj τ)⁻¹)
def LiftDeg {k r : ℕ} (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (j s : ℕ) (hj : j ≤ r)
    (h : C.LPt) (τ : ℂ) (ha : D.ptSize (h ++ [(s, τ)]) = j) : Prop :=
  ∀ (w' : List C.Letter) (a' : Wd.Ix (Fin w'.length)) (b : Bool) (δ : ℝ),
    ∀ g ∈ JF.Om k (r - j) (T.bs j).z (T.bs j).z', ∃ c : Fin (j - s + 1) → (Wq →L[ℂ] Wp),
      c (Fin.last (j - s)) = cLift s τ b • B.JF (T.bs j) (KB.slv T F j hj w' (h ++ [(s, τ)]) ha a') g ∧
      ∀ y : ℝ, B.JF (T.bs j) (KB.slv T F j hj ((b, y + δ) :: w') (h ++ [(s, τ)]) ha (Fin.cons 1 a')) g =
        ∑ l : Fin (j - s + 1), ((y : ℂ) ^ (l : ℕ)) • c l
end lift
section final
def LiftDegAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base F → ∀ (j s : ℕ) (hj : j ≤ P.r) (h : C.LPt) (τ : ℂ)
    (ha : D.IsLocPt (h ++ [(s, τ)]) j), LiftDeg p.T F j s hj h τ ha.2
end final
end Formalism.FourierDecayAlt.P.PBG
end
section
open MeasureTheory Matrix Filter Topology
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.PBN
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section defs
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
def aaTop (Bs : B.RealPlaceData k r Wp Wq) (y : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) : B.Mat k r → (Wq →L[ℂ] Wp) :=
  fun g => (Dmin k r Bs.z Bs.z' g (Fin.last _))⁻¹ •
    C3.AAop k r r le_rfl ((y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) F g
end defs
def RadAATop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (l0 : ℕ) (y : ℝ),
    P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → ∀ F, KB.CptCoef Bs F →
      KB.CptCoef Bs (aaTop Bs y F) ∧
        ∀ Φ, Top.IsRadOf P Bs Φ F → Top.IsRadOf P Bs ((TL.aP L (y : ℂ)).1 Φ) (aaTop Bs y F)
def PolyTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (s : ℕ) (h : C.LPt) (t : ℂ), 2 ≤ s →
    D.IsLocPt (h ++ [(s, t)]) (P.r + 1) → KB.CptCoef p.T.base G →
    ∃ c : Fin (D.ptSize h + 1) → (Wq →L[ℂ] Wp), c (Fin.last _) = ((-1) ^ (s - 1) / t) • p.V G (h ++ [(s, t)]) ∧
      ∀ y : ℝ, p.V (aaTop p.T.base y G) (h ++ [(s, t)]) = ∑ n : Fin (D.ptSize h + 1), ((y : ℂ) ^ (n : ℕ)) • c n
end Formalism.FourierDecayAlt.P.PBN
end
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff
namespace Formalism.FourierDecayAlt.P.PBH
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k ρ : ℕ}
def consC (t : ℂ) (c : Fin ρ → ℂ) : Fin (1 + ρ) → ℂ :=
  fun l => if h : l.val = 0 then t else c ⟨l.val - 1, by omega⟩
end Formalism.FourierDecayAlt.P.PBH
end
section
open Matrix MeasureTheory
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.PBP
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5
def HeadPic : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (X : Q.ActualOps (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π')
    (μ : Measure (Mt P.k (P.r - j))) (L) (st)
    (Φ : Wd.Ix (Fin w.length) →
      Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π'),
    P5.IsData (JC.parLev P j) (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π' X μ L st p.l0 →
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    (∀ e, Top.IsRadOf (JC.parLev P j) (p.T.bs j) (Φ e) (KB.slv p.T F j (by omega) w h hh.2 e)) →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length)),
    ∀ y ∈ Q.DomR P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z',
      (P5.act (P5.bTl L (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) (D.positionted w)) Φ e :
          Q.Fn (JC.parLev P j).k (JC.parLev P j).r (Wq →L[ℂ] Wp))
        (fun l => PBH.consC t y.1 (Fin.cast (by change P.r - j = 1 + (P.r - (j + 1)); omega) l))
          (D.castM (by change 1 + (P.r - (j + 1)) = P.r - j; omega) (ιLev P.k 1 (P.r - (j + 1)) y.2)) =
        ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) •
          Q.resG P.k (P.r - (j + 1)) (Fin.last _)
            (B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e)) y.1 y.2
end Formalism.FourierDecayAlt.P.PBP
end


