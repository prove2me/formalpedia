-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeNeZeroComplex
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_AeNeZeroComplex
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T03:10:30.067078+00:00
-- url     : https://prove2.me/theorems/d9915b93-74c0-4772-866f-68a57f68a1e8
-- title:
--   Ae Ne Zero Complex
-- statement:
--   Definitions and structural lemmas for Ae Ne Zero Complex, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeNeZeroComplex.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FormPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PBL
open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBD
open scoped ComplexConjugate
noncomputable section
section rr
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
end rr
section frame
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
def nnS (S : C.HidaSetting E Wp Wq) (P : C.LPt) : ℝ := C.nLoc S.G.k S.G.r S.fr (D.ptGG (S.T * S.T')) P
def bS (S : C.HidaSetting E Wp Wq) (P : C.LPt) : ℝ := D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) P
def ΓS (S : C.HidaSetting E Wp Wq) (i : ℕ) : ℝ :=
  D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) i
def stdS (S : C.HidaSetting E Wp Wq) (P : C.LPt) : C.LPt := D.toStd S.G.r (S.g : ℝ) 1 P
def lamS (S : C.HidaSetting E Wp Wq) (j : ℕ) : ℝ :=
  ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock (S.G.r : ℤ) ((j + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ)
def sW (S : C.HidaSetting E Wp Wq) (j : ℕ) (l : ℂ) : ℂ :=
  Complex.I * (((2 * Real.pi / ((S.g : ℝ) * lamS S j)) : ℝ) : ℂ) * l
def dW (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (j : ℕ) (w : List C.Letter) (h h' : C.LPt) : ℝ :=
  √(nnS S h) * √(nnS S h') / (bS S h * bS S h' * ΓS S j) / S.sizeAt v w
theorem tsize_lemma (r : ℕ) (g : ℝ) (P : C.LPt) :
    ∀ x : ℕ, D.ptSize (D.toStd r g x P) = D.ptSize P := by
  induction P with
  | nil => intro x; simp only [D.toStd]
  | cons a l ih =>
    intro x
    simp only [D.toStd, D.ptSize, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
theorem stdS_size (S : C.HidaSetting E Wp Wq) (P : C.LPt) : D.ptSize (stdS S P) = D.ptSize P := by
  unfold stdS
  exact tsize_lemma _ _ P 1
end frame
section main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
end main
section main2
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
def rhoS (S : C.HidaSetting E Wp Wq) (j : ℕ) : ℝ :=
  (S.fr (j + 1) 1 / lamS S j) ^ (2 * (C.Mlev S.G.k S.G.r (j + 1) - 2))
def Kc (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (j : ℕ) (w : List C.Letter) (h h' : C.LPt) : ℝ :=
  √(nnS S h) * √(nnS S h') * (1 / (bS S h * bS S h' * ΓS S (j + 1))) * rhoS S j / S.sizeAt v w
end main2
section main3
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
end main3
section main4
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
end main4
end
end Formalism.FourierDecayAlt.P.PBL


