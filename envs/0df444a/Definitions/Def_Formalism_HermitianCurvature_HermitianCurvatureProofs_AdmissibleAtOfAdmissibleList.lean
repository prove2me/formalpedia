-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleAtOfAdmissibleList
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleAtOfAdmissibleList
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:41:50.456673+00:00
-- url     : https://prove2.me/theorems/64994b0e-1b68-45a5-a1f6-bec0fa01282c
-- title:
--   Admissible At Of Admissible List
-- statement:
--   Definitions and structural lemmas for Admissible At Of Admissible List, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdmissibleAtOfAdmissibleList.lean

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RoomOffGridSymmetric
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField Finset
noncomputable section
def nodeOf (x : C.Letter) : ℝ := if x.1 then x.2 else x.2 - 1
def Sep (x y : C.Letter) : Prop := ∀ δ : ℤ, -2 ≤ δ → δ ≤ 2 → 2 < |x.2 - y.2 + δ|
def pushU {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (mk : List ℝ → List C.Letter) : Finset (List C.Letter) :=
  univ.image fun j : Fin K → Fin (d + 1) => mk (List.ofFn fun b => grid b (j b))
def pushTh {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (mk : List ℝ → List C.Letter) (a : List C.Letter) : ℝ :=
  ∑ j : Fin K → Fin (d + 1), if mk (List.ofFn fun b => grid b (j b)) = a then F7.thGrid grid j else 0
section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
def AdmList (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (L : List C.Letter) : Prop :=
  (∀ j (hj : j < L.length), nodeOf (L[j]'hj) ∈ S.grid v (L.length - j) ∪ S.grid1 v) ∧ L.Pairwise Sep
end
section new
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
end new
end
def NewLetters : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)] (S : C.HidaSetting E Wp Wq),
    C.GridsOK S → KB.GridsRich S → KB.CutInside S →
    ∀ (v : Fin S.f) (a : List C.Letter) (K n : ℕ), D.AdmAt S v a → a.length + K ≤ S.Ntop → n ≤ 2 * S.G.r →
    KB.CutWord (D.parOf S v) (S.l + 1) a ∧
    ∃ grid : Fin K → Fin (n + 1) → ℝ,
      (∀ b, Function.Injective (grid b)) ∧
      (∀ b, ∑ j, |F7.lagCo (grid b) j| ≤ (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ n) ∧
      (∀ (b : Fin K) j, grid b j ∈ S.grid v (a.length + K - (b : ℕ))) ∧
      (∀ j : Fin K → Fin (n + 1),
        D.AdmAt S v (KB.plusW (List.ofFn fun b => grid b (j b)) a) ∧
        D.AdmAt S v (KB.minusW (List.ofFn fun b => grid b (j b)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun b => grid b (j b)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW (List.ofFn fun b => grid b (j b)) a) ∧
        (List.ofFn fun b => grid b (j b)).Pairwise fun y y' => 4 < |y - y'|) ∧
      KB.LocProb S v (a.length + K) (pushU grid fun ys => KB.plusW ys a) (pushTh grid fun ys => KB.plusW ys a) ∧
      KB.LocProb S v (a.length + K) (pushU grid fun ys => KB.minusW ys a) (pushTh grid fun ys => KB.minusW ys a)
def NewLetters1 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)] (S : C.HidaSetting E Wp Wq),
    C.GridsOK S → KB.GridsRich S → KB.CutInside S →
    ∀ (v : Fin S.f) (a : List C.Letter) (K : ℕ), D.AdmAt S v a → a.length + K ≤ S.Ntop →
    ∃ ys : List ℝ, ys.length = K ∧ ys.Nodup ∧ (∀ y ∈ ys, y ∈ S.grid1 v) ∧
      D.AdmAt S v (KB.plusW ys a) ∧ D.AdmAt S v (KB.minusW ys a) ∧
      KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW ys a) ∧ KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW ys a) ∧
      ys.Pairwise fun y y' => 4 < |y - y'|
end Formalism.FourierDecayAlt.P.PBD


