-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnCut
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnCut
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T03:10:10.177239+00:00
-- url     : https://prove2.me/theorems/5c0d74ae-4918-5f6e-819f-28f19af61ba2
-- title:
--   Cut En Cut
-- statement:
--   Definitions and structural lemmas for Cut En Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutEnCut.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_HermitianCurvature_StatementJF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField
namespace Formalism.FourierDecayAlt.P.CutMP.En
noncomputable section
def foldCV (k r : ℕ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : ℂ) (a : List C.Letter)
    (H : B.Mat k r → E) : B.Mat k r → E :=
  a.foldr (fun x J => s • Q.CV k r (x.2 : ℂ) J) H
def CVLocal : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (U : Set (B.Mat k r)) (f₁ f₂ : B.Mat k r → E)
    (Y : ℂ), IsOpen U → B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (U ∩ B.GV k r) f₁ →
    B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (U ∩ B.GV k r) f₂ → (∀ g ∈ U ∩ B.GV k r, f₁ g = f₂ g) →
    ∀ g ∈ U ∩ B.GV k r, Q.CV k r Y f₁ g = Q.CV k r Y f₂ g
def FoldRev : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (Dm : Set (Q.Mx k r)), IsOpen Dm →
    (∀ J ∈ Q.FFl k r z z' π π' 0 Dm, ∀ (Y : ℝ) (s : ℂ), s • Q.CV k r (Y : ℂ) J ∈ Q.FFl k r z z' π π' 0 Dm) →
    ∀ J ∈ Q.FFl k r z z' π π' 0 Dm, ∀ (s : ℂ) (a : List C.Letter), ∀ g ∈ Q.Glev k r 0 ∩ Dm,
      foldCV k r s a.reverse J g = foldCV k r s a J g
def AdmLen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (v : Fin S.f)
    (a : List C.Letter), D.AdmAt S v a → a.length ≤ S.Ntop
def CVInCC : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (m : ℕ) (F : B.Mat k r → E) (Y s : ℂ),
    B.InCC A (m + (2 * r + k + 1)) F → B.InCC A m (s • Q.CV k r Y F)
def BesselFoldBuilt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW 100 S T f χ ν' m₀ top A₀ →
    ∀ v, (∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v), ∀ (Y : ℝ) (s : ℂ), s • Q.CV S.G.k S.G.r (Y : ℂ) J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)) →
      ∀ ε : ℝ, 0 < ε → B.JF (T v).base (D.cutF (T v).base χ (f v) ε) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
      ∀ a : List C.Letter, a.length ≤ S.Ntop → ∀ g ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z',
        B.JF (T v).base (foldCV S.G.k S.G.r (M.sgn (D.parOf S v) (S.l + 1)) a (D.cutF (T v).base χ (f v) ε)) g =
          foldCV S.G.k S.G.r (M.sgn (D.parOf S v) (S.l + 1)) a (B.JF (T v).base (D.cutF (T v).base χ (f v) ε)) g
def L2BoundAtTowerPlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW 100 S T f χ ν' m₀ top A₀ →
    ∀ v, ∀ ε : ℝ, 0 < ε → ∀ a : List C.Letter, a.length ≤ S.Ntop →
      B.normSq (T v).base (foldCV S.G.k S.G.r (M.sgn (D.parOf S v) (S.l + 1)) a (D.cutF (T v).base χ (f v) ε)) ≠ ⊤
def FibMem : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f), Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' →
    ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
      ∀ q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT,
        J (B.gq (T v).base q) ∈ NF.Fib S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec (T v).base.π (T v).base.π' q.2
def TrSmooth : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f), Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' →
    ∀ (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
    ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v), ∀ ρ,
      (fun q : MA.Qp (D.parOf S v).r (D.parOf S v).TT =>
        ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
          inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq (T v).base q.1)))) ∈ MA.smSub (D.parOf S v).r (D.parOf S v).TT
def BetaFrame : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f), Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' →
    ∀ (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
    ∀ J₁ ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
    ∀ J₂ ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
      jNormSq S.G.k S.G.r (Tz S.G.k S.G.r (T v).base.z) (Tz S.G.k S.G.r (T v).base.z')
          (fun q => B.hsVec (J₁ (B.gq (T v).base q))) ≠ ⊤ →
      jNormSq S.G.k S.G.r (Tz S.G.k S.G.r (T v).base.z) (Tz S.G.k S.G.r (T v).base.z')
          (fun q => B.hsVec (J₂ (B.gq (T v).base q))) ≠ ⊤ →
      betaBig S.G.k S.G.r (Tz S.G.k S.G.r (T v).base.z) (Tz S.G.k S.G.r (T v).base.z') (T v).base.μsec
          (fun g => B.hsVec (J₁ g)) (fun g => B.hsVec (J₂ g)) =
        MA.ipA (D.parOf S v) (trJ S T v e J₁) (trJ S T v e J₂)
end
end Formalism.FourierDecayAlt.P.CutMP.En


