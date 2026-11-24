-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementJC
-- name    : Formalism_HermitianCurvature_StatementJC
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:27:47.267448+00:00
-- url     : https://prove2.me/theorems/56527c9c-879d-46e4-ab63-2f8446680a80
-- title:
--   Statement JC
-- statement:
--   Definitions and structural lemmas for Statement JC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementJC.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementMA
import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
section Positivity
open Matrix MeasureTheory Filter Topology NumberField
noncomputable section
namespace Formalism.FourierDecayAlt.JC
open Formalism.FourierDecayAlt
def parLev (P : M.Par) (j : ℕ) : M.Par := ⟨P.k, P.r - j, P.T, P.T', P.u, P.u'⟩
def NiceCoef {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (ε : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  B.CkOn ⊤ (B.GV k r) F ∧ (∀ (A' : ℝ) (m' : ℕ), B.InCC A' m' F) ∧
    ∀ g ∈ B.GV k r, F g ≠ 0 → ε ≤ Formalism.QuantumDeterminants.Gf k r Bs.z Bs.z' g
def RadialModuleAct : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (j : Fin (P0.r + 1))
    (X : Q.ActualOps (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (μ : Measure (Formalism.QuantumDeterminants.Mt (parLev P0 j).k (parLev P0 j).r))
    (L : R.LevelData (Q.Pr (Q.RadSp (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))
      (parLev P0 j).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')))
    (l0 : ℕ),
    P5.IsData (parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' X μ L st l0 →
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
      (Φ : Wd.Ix (Fin w.length) →
        Q.RadSp (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'),
      (∀ a, x a ∈ Q.FFl (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' 0
        (Q.OmPlus (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z')) →
      (∀ a, ∀ y ∈ Q.DomR (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z',
        (Φ a : Q.Fn (parLev P0 j).k (parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          Q.resG (parLev P0 j).k (parLev P0 j).r (Fin.last _) (x a) y.1 y.2) →
      ∀ a, ∀ y ∈ Q.DomR (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z',
        (P5.act (P5.RRi L st 0 (D.positionted w)) Φ a : Q.Fn (parLev P0 j).k (parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          Q.resG (parLev P0 j).k (parLev P0 j).r (Fin.last _)
            (D.actOp (D.RRlev T (M.sgn P0 l0) j w) x a) y.1 y.2
def RadialBetaPos : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (j : Fin (P0.r + 1)) (μ : Measure (Formalism.QuantumDeterminants.Mt (parLev P0 j).k (parLev P0 j).r)),
    B.IsHaarOn (Q.Glev (parLev P0 j).k (parLev P0 j).r (Fin.last _)) μ →
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (x x' : Wd.Ix (Fin n) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
      (Φ Φ' : Wd.Ix (Fin n) →
        Q.RadSp (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π') (ε : ℝ),
      0 < ε → (∀ a, NiceCoef (T.bs j) ε (x a)) → (∀ a, NiceCoef (T.bs j) ε (x' a)) →
      (∀ a, ∀ y ∈ Q.DomR (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z',
        (Φ a : Q.Fn (parLev P0 j).k (parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          Q.resG (parLev P0 j).k (parLev P0 j).r (Fin.last _) (B.JF (T.bs j) (x a)) y.1 y.2) →
      (∀ a, ∀ y ∈ Q.DomR (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z',
        (Φ' a : Q.Fn (parLev P0 j).k (parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          Q.resG (parLev P0 j).k (parLev P0 j).r (Fin.last _) (B.JF (T.bs j) (x' a)) y.1 y.2) →
      ∑ a, B.beta (T.bs j) (x a) (x' a) = (C : ℂ) * P5.form μ 0 Φ Φ' 0
def JFInFF : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (ε : ℝ), 0 < ε → NiceCoef Bs ε F →
    B.JF Bs F ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 (Q.OmPlus k r Bs.z Bs.z')
def ModuleNice : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter)
    (F : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (ε : ℝ),
    0 < ε → (∀ a, NiceCoef (T.bs j) ε (F a)) → ∀ a, NiceCoef (T.bs j) ε (D.actOp (D.RRlev T s j w) F a)
def BesselModule : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter)
    (F : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (ε : ℝ),
    0 < ε → (∀ a, NiceCoef (T.bs j) ε (F a)) →
    ∀ a, ∀ y ∈ Q.DomR (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z',
      Q.resG (parLev P0 j).k (parLev P0 j).r (Fin.last _) (B.JF (T.bs j) (D.actOp (D.RRlev T s j w) F a)) y.1 y.2 =
        Q.resG (parLev P0 j).k (parLev P0 j).r (Fin.last _)
          (D.actOp (D.RRlev T s j w) (fun b => B.JF (T.bs j) (F b)) a) y.1 y.2
def RadialModuleForm : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (j : Fin (P0.r + 1))
    (X : Q.ActualOps (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (μ : Measure (Formalism.QuantumDeterminants.Mt (parLev P0 j).k (parLev P0 j).r))
    (L : R.LevelData (Q.Pr (Q.RadSp (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')) (parLev P0 j).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))) (l0 : ℕ),
    P5.IsData (parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' X μ L st l0 →
    ∃ Cst : ℝ, 0 < Cst ∧ ∀ (w : List C.Letter) (F F' : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
      (Φ Φ' : Wd.Ix (Fin w.length) → Q.RadSp (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π') (ε : ℝ),
      0 < ε → (∀ a, NiceCoef (T.bs j) ε (F a)) → (∀ a, NiceCoef (T.bs j) ε (F' a)) →
      (∀ a, ∀ y ∈ Q.DomR (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z',
        (Φ a : Q.Fn (parLev P0 j).k (parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG (parLev P0 j).k (parLev P0 j).r (Fin.last _) (B.JF (T.bs j) (F a)) y.1 y.2) →
      (∀ a, ∀ y ∈ Q.DomR (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z',
        (Φ' a : Q.Fn (parLev P0 j).k (parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG (parLev P0 j).k (parLev P0 j).r (Fin.last _) (B.JF (T.bs j) (F' a)) y.1 y.2) →
      D.formLev T (M.sgn P0 l0) j w F F' = (Cst : ℂ) * P5.form μ 0 (P5.act (P5.RRi L st 0 (D.positionted w)) Φ) Φ' 0
def RadialModuleFormOfParts : Prop :=
  RadialBetaPos → RadialModuleAct → JFInFF → BesselModule → ModuleNice → RadialModuleForm
section model
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : NumberField.InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
def IsModelPlace (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (v : Fin S.f)
    (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
    (j : M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT)
    (lam : Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ) (c : LE.Cut) (Cm σ : ℝ) : Prop :=
  c.χ = χ ∧ 0 < Cm ∧ 0 < σ ∧
  MA.HidaSetting (D.parOf S v) (S.l + 1) L lam (S.cutLo v) (S.cutHi v) ∧
  MA.JDecay (D.parOf S v) L j (2 * S.Ntop + 2) ∧ MA.JAdj (D.parOf S v) L j (2 * S.Ntop + 2) ∧
  MA.JEigen (D.parOf S v) j lam ∧
  (∀ ε, 0 < ε → ∀ a : List C.Letter, D.AdmAt S v a →
    C7.principalHermitianLattice (T v).base (M.sgn (D.parOf S v) (S.l + 1)) a (D.cutF (T v).base χ (f v) ε) =
      ((Cm * MA.cutoffEnergyForm (D.parOf S v) (S.l + 1) j c (σ * ε) a : ℝ) : ℂ)) ∧
  ∀ Lb : ℝ, ∀ a : List C.Letter, D.AdmAt S v a →
    (MA.sysQ (D.parOf S v) (S.l + 1) L j lam (S.cutLo v) (S.cutHi v) Lb c S.Ntop).admitted a ∧
    (MA.sysQ (D.parOf S v) (S.l + 1) L j lam (S.cutLo v) (S.cutHi v) Lb c S.Ntop).size a = S.sizeAt v a
end model
def LemmaEOfModel : Prop :=
  D.LemmaEOfRR0 → D.LevelZero → D.GoodOfAdm → MA.LemmaEModel →
  ∃ C₆ : ℝ, 0 < C₆ ∧
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : NumberField.InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ)
    (L : ∀ v : Fin S.f, R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
    (j : ∀ v : Fin S.f, M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT)
    (lam : ∀ v : Fin S.f, Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ) (c : LE.Cut) (Cm σ : Fin S.f → ℝ),
    D.IsBuilt S T f χ ν' m₀ top A₀ →
    (∀ v ε, 0 < ε → B.CkOn ⊤ (B.GV S.G.k S.G.r) (D.cutF (T v).base χ (f v) ε)) →
    (∀ v, C₆ * ((S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2) ≤
      S.cutHi v - S.cutLo v) →
    (∀ v, IsModelPlace S T f χ v (L v) (j v) (lam v) c (Cm v) (σ v)) →
    C.LemmaE S fun v =>
      Cm v * (∫ q, ∑ ρ, ‖(j v ρ : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) q‖ ^ 2
          ∂MA.mu0 (D.parOf S v).r (D.parOf S v).TT) /
        D.GamLev S.G.k S.G.r (D.kapG S.g (S6.rd E)) (D.deG S.g (S6.rd E)) 0
end Formalism.FourierDecayAlt.JC
end
end Positivity
namespace Formalism.FourierDecayAlt.JC
def CutFSmooth : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (χ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (ε : ℝ),
    C6.IsCut0 χ → B.CkOn ⊤ (B.GV k r) f → 0 < ε → B.CkOn ⊤ (B.GV k r) (D.cutF Bs χ f ε)
section density
open scoped ComplexOrder
def PosDensityCC : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (A : ℝ) (mm : ℕ) (ε : ℝ),
    0 < ε → P5.Auser P0 w.length + 1 ≤ A → P5.mmUser P0 w.length ≤ mm →
    (∀ x : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp),
      (∀ a, ∃ F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV P0.k (P0.r - j)) F ∧
        (∀ (A' : ℝ) (m' : ℕ), B.InCC A' m' F) ∧
        (∀ g ∈ B.GV P0.k (P0.r - j), F g ≠ 0 → ε ≤ Formalism.QuantumDeterminants.Gf P0.k (P0.r - j) (T.bs j).z (T.bs j).z' g) ∧
        x a = F) →
      0 ≤ D.formLev T s j w x x) →
    ∀ x : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp),
      (∀ a, ∃ F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV P0.k (P0.r - j)) F ∧ B.InCC A mm F ∧
        (∀ g ∈ B.GV P0.k (P0.r - j), F g ≠ 0 → ε ≤ Formalism.QuantumDeterminants.Gf P0.k (P0.r - j) (T.bs j).z (T.bs j).z' g) ∧
        x a = F) →
      0 ≤ D.formLev T s j w x x
def CCCoef {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (A : ℝ) (mm : ℕ) (ε : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    Prop :=
  B.CkOn ⊤ (B.GV k r) F ∧ B.InCC A mm F ∧ ∀ g ∈ B.GV k r, F g ≠ 0 → ε ≤ Formalism.QuantumDeterminants.Gf k r Bs.z Bs.z' g
def FormLevSesqCC : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (A : ℝ) (mm : ℕ) (ε : ℝ),
    0 < ε → P5.Auser P0 w.length + 1 ≤ A → P5.mmUser P0 w.length ≤ mm →
    ∀ (x x' y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ),
      (∀ a, CCCoef (T.bs j) A mm ε (x a)) → (∀ a, CCCoef (T.bs j) A mm ε (x' a)) →
      (∀ a, CCCoef (T.bs j) A mm ε (y a)) →
      D.formLev T s j w (x + c • x') y = D.formLev T s j w x y + c * D.formLev T s j w x' y ∧
        D.formLev T s j w y (x + c • x') = D.formLev T s j w y x + starRingEnd ℂ c * D.formLev T s j w y x'
def ThmPModuleOfActual : Prop :=
  P5.ThmPActual → RadialModuleForm → PosDensityCC → FormLevSesqCC →
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (l0 N : ℕ) (admitted : List C.Letter → Prop) (A : ℝ) (mm : ℕ),
    1 ≤ l0 → l0 ≤ P0.k → (∀ w, admitted w → w.length ≤ N) → P5.Auser P0 N + 1 ≤ A → P5.mmUser P0 N ≤ mm →
    (∀ j : Fin (P0.r + 1),
      ∃ (X : Q.ActualOps (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
        (μ : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt (parLev P0 j).k (parLev P0 j).r))
        (L : R.LevelData (Q.Pr (Q.RadSp (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
          (T.bs j).π')) (parLev P0 j).r)
        (st : Fr.Start (Q.Pr (Q.RadSp (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
          (T.bs j).π'))),
        P5.IsData (parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' X μ L st l0 ∧
        ∀ w, admitted w → P5.WordOK (parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' st l0 (D.positionted w)) →
    ∃ KK : ∀ j : Fin (P0.r + 1), Submodule ℂ (B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)),
      D.ThmPModule T (M.sgn P0 l0) admitted KK ∧
      ∀ (j : Fin (P0.r + 1)) (F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (ε : ℝ), 0 < ε → B.InCC A mm F →
        B.CkOn ⊤ (B.GV P0.k (P0.r - j)) F →
        (∀ g ∈ B.GV P0.k (P0.r - j), F g ≠ 0 → ε ≤ Formalism.QuantumDeterminants.Gf P0.k (P0.r - j) (T.bs j).z (T.bs j).z' g) →
        F ∈ KK j
def CCCoefM {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (A : ℝ) (mm : ℕ) (ε : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    Prop :=
  B.CkOn (mm : ℕ∞) (B.GV k r) F ∧ B.InCC A mm F ∧ ∀ g ∈ B.GV k r, F g ≠ 0 → ε ≤ Formalism.QuantumDeterminants.Gf k r Bs.z Bs.z' g
def FormLevSesqMM : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (A : ℝ) (mm : ℕ) (ε : ℝ),
    0 < ε → P5.Auser P0 w.length + 1 ≤ A → P5.mmUser P0 w.length ≤ mm →
    ∀ (x x' y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ),
      (∀ a, CCCoefM (T.bs j) A mm ε (x a)) → (∀ a, CCCoefM (T.bs j) A mm ε (x' a)) →
      (∀ a, CCCoefM (T.bs j) A mm ε (y a)) →
      D.formLev T s j w (x + c • x') y = D.formLev T s j w x y + c * D.formLev T s j w x' y ∧
        D.formLev T s j w y (x + c • x') = D.formLev T s j w y x + starRingEnd ℂ c * D.formLev T s j w y x'
def PosDensityMM : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (A : ℝ) (mm : ℕ) (ε : ℝ),
    0 < ε → P5.Auser P0 w.length + 1 ≤ A → P5.mmUser P0 w.length ≤ mm →
    (∀ ε' : ℝ, 0 < ε' → ∀ x : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp),
      (∀ a, NiceCoef (T.bs j) ε' (x a)) → 0 ≤ D.formLev T s j w x x) →
    ∀ x : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp),
      (∀ a, CCCoefM (T.bs j) A mm ε (x a)) → 0 ≤ D.formLev T s j w x x
def ThmPModuleOfActualMM : Prop :=
  P5.ThmPActual → RadialModuleForm → PosDensityMM → FormLevSesqMM →
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (l0 N : ℕ) (admitted : List C.Letter → Prop) (A : ℝ) (mm : ℕ),
    1 ≤ l0 → l0 ≤ P0.k → (∀ w, admitted w → w.length ≤ N) → P5.Auser P0 N + 1 ≤ A → P5.mmUser P0 N ≤ mm →
    (∀ j : Fin (P0.r + 1),
      ∃ (X : Q.ActualOps (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
        (μ : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt (parLev P0 j).k (parLev P0 j).r))
        (L : R.LevelData (Q.Pr (Q.RadSp (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
          (T.bs j).π')) (parLev P0 j).r)
        (st : Fr.Start (Q.Pr (Q.RadSp (parLev P0 j).k (parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
          (T.bs j).π'))),
        P5.IsData (parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' X μ L st l0 ∧
        ∀ w, admitted w → P5.WordOK (parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' st l0 (D.positionted w)) →
    ∃ KK : ∀ j : Fin (P0.r + 1), Submodule ℂ (B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)),
      D.ThmPModule T (M.sgn P0 l0) admitted KK ∧
      ∀ (j : Fin (P0.r + 1)) (F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (ε : ℝ), 0 < ε → B.InCC A mm F →
        B.CkOn (mm : ℕ∞) (B.GV P0.k (P0.r - j)) F →
        (∀ g ∈ B.GV P0.k (P0.r - j), F g ≠ 0 → ε ≤ Formalism.QuantumDeterminants.Gf P0.k (P0.r - j) (T.bs j).z (T.bs j).z' g) →
        F ∈ KK j
end density
end Formalism.FourierDecayAlt.JC
section Decay
namespace Formalism.FourierDecayAlt.JC
open Finset Filter Topology NumberField
noncomputable section
open Classical
section hyps
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
def WaveByPlaces (S : C.HidaSetting E Wp Wq) (abelian₂ : ℕ → Fin S.f → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ w ∈ S.base.Wall, S.base.cnt w + C.Kst ≤ S.Ntop →
    ∃ θ : Finset (Fin S.f) → S.W → ℝ, (∀ A, TB.IsProb (S.base.Wb (S.base.cnt w + C.Kst)) (θ A)) ∧
      ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - 1) → ∀ κ, TB.PSDOn Y κ →
        ∀ l ∈ S.base.Lad i, l ≠ 0 → ∀ A : Finset (Fin S.f),
          (∏ v ∈ A, S.base.av v l ^ C.Kst) * ‖S.Nhat ε i w.1 Y κ l‖ ≤
            (∏ v ∈ A, abelian₂ i v ^ C.Kst) *
              ∑ w' ∈ S.base.Wb (S.base.cnt w + C.Kst), θ A w' * S.base.N0 ε (i - 1) w' Y κ
def HidaCurvatureBarriers (S : C.HidaSetting E Wp Wq) (abelian₂ : ℕ → Fin S.f → ℝ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ v, 0 ≤ abelian₂ i v ∧ abelian₂ i v ≤ S.base.szD i v
def LiftBelowTop (S : C.HidaSetting E Wp Wq) (abelian₂ : ℕ → ℕ → Fin S.f → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∀ i s, 1 ≤ s → s ≤ i → i ≤ S.G.r → ∀ w ∈ S.base.Wall, S.base.cnt w + S.base.K ≤ S.base.Ntop →
    ∃ θ : Finset (Fin S.f) → S.W × S.W → ℝ,
      (∀ A, TB.IsProb (S.base.Wb (S.base.cnt w + S.base.K) ×ˢ S.base.Wb (S.base.cnt w + S.base.K)) (θ A)) ∧
      ∀ (Y : Finset (TB.Pt E)) (T : Finset E) (κ : TB.Pt E → TB.Pt E → ℂ),
        (∀ h ∈ Y, TB.level h = i - s) → TB.PSDOn (TB.pts Y s T) κ →
        ∀ t ∈ T, ∀ t' ∈ T, t ≠ 0 → t' ≠ 0 → t⁻¹ - t'⁻¹ ≠ 0 → ∀ A : Finset (Fin S.f),
          (∏ v ∈ A, S.base.av v (t⁻¹ - t'⁻¹) ^ S.base.K) *
              ‖S.base.Nst ε i s w Y (TB.blk κ s t t') t t'‖ ≤
            (∏ v ∈ A, abelian₂ (i - s + 1) s v ^ S.base.K) *
              ∑ x ∈ S.base.Wb (S.base.cnt w + S.base.K) ×ˢ S.base.Wb (S.base.cnt w + S.base.K), θ A x *
                (((S.base.Nst ε i s x.1 Y (TB.blk κ s t t) t t).re +
                  (S.base.Nst ε i s x.2 Y (TB.blk κ s t' t') t' t').re) / 2)
def LiftTopDiag (S : C.HidaSetting E Wp Wq) (Lam' : ℕ → ℕ → Fin S.f → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∀ s, 2 ≤ s → s ≤ S.G.r + 1 → ∀ w ∈ S.base.Wall, S.base.cnt w + S.base.K ≤ S.base.Ntop →
    ∃ θ : Finset (Fin S.f) → S.W → ℝ, (∀ B, TB.IsProb (S.base.Wb (S.base.cnt w + S.base.K)) (θ B)) ∧
      ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = S.G.r + 1 - s) → ∀ κ, TB.PSDOn Y κ →
        ∀ t : E, t ≠ 0 → ∀ B : Finset (Fin S.f),
          (S.base.Nst ε (S.G.r + 1) s w Y κ t t).re ≤
            (∏ v ∈ B, (S.base.av v t * Lam' (S.G.r + 2 - s) s v) ^ (2 * S.base.K)) *
              ∑ w' ∈ S.base.Wb (S.base.cnt w + S.base.K), θ B w' * (S.base.Nst ε (S.G.r + 1) s w' Y κ t t).re
def ThresholdsLift (S : C.HidaSetting E Wp Wq) (abelian₂ Lam' : ℕ → ℕ → Fin S.f → ℝ) : Prop :=
  (∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ abelian₂ b s v ∧ abelian₂ b s v ≤ S.base.szL b s v) ∧
  (∀ s, 2 ≤ s → s ≤ S.G.r + 1 → ∀ v,
    0 ≤ Lam' (S.G.r + 2 - s) s v ∧ 2 * Lam' (S.G.r + 2 - s) s v ≤ S.base.szL (S.G.r + 2 - s) s v)
def SumFormConcrete (S : C.HidaSetting E Wp Wq) (C₄ : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∀ i s, 2 ≤ s → s ≤ i → i ≤ S.base.r + 1 → ∀ w ∈ S.base.Wall,
    S.base.cnt w + (s + 1) * S.base.K ≤ S.base.Ntop → S.base.vol (i - s + 1) s ≤ 1 →
    ∃ Mv, Mv ≤ C₄ ^ (S.base.f * s) * (∏ s' ∈ Ico 1 s, S.base.vol (i - s + 1) s') ∧
      crystallineComparison.SumForm S.base ε i s w Mv
end hyps
def PlaneExponentialBoundOfPlaces : Prop :=
  C.GramPSDOfParts → C.WordsPosOfParts →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (abelian₂ : ℕ → Fin S.f → ℝ),
    C.ThmPPos S → C.GridsOK S → WaveByPlaces S abelian₂ → HidaCurvatureBarriers S abelian₂ → C.PlaneWaveBoundAllPlaces S
def OffDiagonalLiftBoundOfPlaces : Prop :=
  PairingProductCorollary.LeadingBlockSeveralPlacesBound → C.GramPSDOfParts → C.WordsPosOfParts →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (abelian₂ Lam' : ℕ → ℕ → Fin S.f → ℝ),
    C.ThmPPos S → C.GridsOK S → LiftBelowTop S abelian₂ → LiftTopDiag S Lam' → ThresholdsLift S abelian₂ Lam' →
    C.OffDiagonalLiftBound S
def CorollaryTOfSumForm : Prop :=
  crystallineComparison.EstBlockOfSumForm → C.GramPSDOfParts → C.WordsPosOfParts →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (C₄ : ℝ),
    C.ThmPPos S → C.GridsOK S → SumFormConcrete S C₄ → C.CorollaryT S C₄
end
end Formalism.FourierDecayAlt.JC
end Decay
section Data
namespace Formalism.FourierDecayAlt.JC
open Finset NumberField
noncomputable section
def MkDataInst : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
    (Kr : ℕ → TB.Pt E → TB.Pt E → ℂ) (hK0 : Kr 0 [] [] = 1)
    (Th : ℕ → ℕ → E → TB.Pt E → TB.Pt E → ℂ) (e : ℕ → ℝ),
    J.Inst (S.mkData Kr hK0 Th e) S.pl S.G S.CA S.de S.de' S.T S.T' S.l
def ThetaExistence₂ : Prop :=
  ∀ (ι : Type) [Fintype ι] (G : Sz.Glob ι) (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ),
    1 ≤ G.f → (∀ x ∈ G.thrSet C de de' T T' l, 0 < x) →
    ∃ Θ : ℝ, 0 < Θ ∧ IsGreatest (G.thrSet C de de' T T' l) ((Θ ^ G.f)⁻¹)
def SizesConcrete : Prop :=
  ∃ C₁ : ℝ, 1 ≤ C₁ ∧
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
    (Kr : ℕ → TB.Pt E → TB.Pt E → ℂ) (hK0 : Kr 0 [] [] = 1)
    (Th : ℕ → ℕ → E → TB.Pt E → TB.Pt E → ℂ) (e : ℕ → ℝ) (Θ : ℝ),
    S6.Unram E → 0 < S.G.g1 → 0 < S.G.g2 → 0 ≤ S.CA → 0 < S.G.lenI → 4 < Θ →
    IsGreatest (S.G.thrSet S.CA S.de S.de' S.T S.T' S.l) ((Θ ^ S.G.f)⁻¹) →
    (S.mkData Kr hK0 Th e).SizesBelow Θ ∧
      (S.mkData Kr hK0 Th e).LatticeSums ((C₁ * Θ ^ (-((C.Kst : ℝ) - 5 / 2))) ^ S.f)
def SizesConcreteOfParts : Prop :=
  J.LatticeSumsJoint → J.InstSizes → Formalism.SA.C.BoxSum → S6.LatticesGeneral → S6.IdealsMatch → S6.NormIdl →
    S6.DegreeFacts → J.FrameProducts → J.XIsLamOne → J.InstLatticeSums → MkDataInst → SizesConcrete
def AxiomsConcrete : Prop :=
  PB.AxiomsOfLocalModel → PB.LocalCores → (∀ s, 1 ≤ s → A5.A13 s) →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
    (Kr : ℕ → TB.Pt E → TB.Pt E → ℂ) (hK0 : Kr 0 [] [] = 1)
    (Th : ℕ → ℕ → E → TB.Pt E → TB.Pt E → ℂ),
    PB.LocalModel (S.mkData Kr hK0 Th fun _ => 0) →
      TC.KrPSD (S.mkData Kr hK0 Th fun _ => 0) ∧ (S.mkData Kr hK0 Th fun _ => 0).KernelSupport ∧
        TC.EBounds (S.mkData Kr hK0 Th fun _ => 0) ∧ TC.DomAfter (S.mkData Kr hK0 Th fun _ => 0)
def LocalModelExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq),
    S6.Unram E → 0 < S.G.g1 → 0 < S.G.g2 →
    ∃ (Kr : ℕ → TB.Pt E → TB.Pt E → ℂ) (hK0 : Kr 0 [] [] = 1) (Th : ℕ → ℕ → E → TB.Pt E → TB.Pt E → ℂ),
      PB.LocalModel (S.mkData Kr hK0 Th fun _ => 0)
end
end Formalism.FourierDecayAlt.JC
end Data
section Needs
namespace Formalism.FourierDecayAlt.JC
open Finset Filter Topology NumberField MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Classical Formalism.REAL Formalism.QuantumDeterminants
def ThmPIntPlace {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (dl : ℕ → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ w : S.W, ∀ h h' : C.LPt, D.ptSize h = i - 1 →
    D.ptSize h' = i - 1 →
    ∃ φ : ℂ → ℂ, Continuous φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = S.gramLoc v ε i (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      (∃ Cφ : ℝ, ∀ c : ℂ, ‖φ c‖ ≤ Cφ * ((1 + ‖c‖) ^ 3)⁻¹) ∧
      ∫ c : ℂ, φ c = (dl i : ℂ) * S.gramLoc v ε (i - 1) (w.1 v) h h'
def ThmPIntOfPlaces : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
    (dl : ℕ → Fin S.f → ℝ),
    C.ThmPPos S →
    (∀ i, 1 ≤ i → i ≤ S.G.r + 1 →
      ∏ v, dl i v = ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1)) →
    (∀ i, 1 ≤ i → i ≤ S.G.r + 1 →
      ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1) ≠ 0) →
    (∀ v, ThmPIntPlace S v fun i => dl i v) →
    C.ThmPInt S
def ThmPIntBuilt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq)
    (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    0 < S.G.g1 → 0 < S.G.g2 → S6.Unram E → D.IsBuilt S T f χ ν' m₀ top A₀ →
    ∃ dl : ℕ → Fin S.f → ℝ,
      (∀ i, 1 ≤ i → i ≤ S.G.r + 1 →
        ∏ v, dl i v = ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1)) ∧
      ∀ v, ThmPIntPlace S v fun i => dl i v
def GramPlace {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (v : Fin S.f) {Hv : Type} [NormedAddCommGroup Hv] [InnerProductSpace ℂ Hv]
    (V : C.LPt → Hv) : Prop :=
  ∀ Y : Finset C.LPt, (∀ p ∈ Y, D.ptSize p = S.G.r + 1) →
    ∀ᶠ ε in 𝓝[>] 0, ∀ p ∈ Y, ∀ q ∈ Y, (S.pd v).RR ε (S.G.r + 1) [] p q = inner ℂ (V q) (V p)
def PropGramOfPlaces : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
    (Hv : Fin S.f → Type) [∀ v, NormedAddCommGroup (Hv v)] [∀ v, InnerProductSpace ℂ (Hv v)]
    (V : ∀ v, C.LPt → Hv v) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Vt : TB.Pt E → H),
    (∀ p q : TB.Pt E, TB.IsPt p (S.G.r + 1) → TB.IsPt q (S.G.r + 1) →
      inner ℂ (Vt q) (Vt p) = ∏ v,
        ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) p)) *
            √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) q)) : ℝ) : ℂ) *
          inner ℂ (V v (C.loc (S.σ v) q)) (V v (C.loc (S.σ v) p))) →
    (∀ v, GramPlace S v (V v)) →
    C.PropGram S Vt
def OrbJCutScalar : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (μR : Measure (Mt k r))
    (χ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (ε : ℝ),
    C6.IsRelevant Bs γ → B.IsHaarOn (C6.Rset γ) μR → 0 < ε →
    D.orbJ Bs γ μR (D.cutF Bs χ f ε) = ((χ (Gf k r Bs.z Bs.z' γ / ε) : ℝ) : ℂ) • D.orbJ Bs γ μR f
def vecPlace {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r) (v : Fin S.f) (p : C.LPt) :
    PiLp 2 (fun _ : Fin (Module.finrank ℂ (Wq (S.pl v))) => Wp (S.pl v)) :=
  (((D.bSt (D.kapG S.g (S6.rd E)) p)⁻¹ : ℝ) : ℂ) •
    B.hsVec (D.vecV (T v).base (ν' v) (m₀ v) (f v) (D.toStd S.G.r S.g 1 p))
def GramPlaceBuilt : Prop :=
  D.PtPermSpec → D.PtGSpec → D.PtRelevant → D.MuRHaar → OrbJCutScalar →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq)
    (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    0 < S.G.g1 → 0 < S.G.g2 → D.IsBuilt S T f χ ν' m₀ top A₀ →
    ∀ v, GramPlace S v (vecPlace S T f ν' m₀ v)
end
end Formalism.FourierDecayAlt.JC
end Needs


