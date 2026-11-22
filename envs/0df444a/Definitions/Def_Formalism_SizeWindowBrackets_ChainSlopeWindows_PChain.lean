-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
-- name    : Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:03:47.0536+00:00
-- url     : https://prove2.me/theorems/6ea6ee22-3521-4263-8243-6c4d66f1b1d1
-- title:
--   PChain
-- statement:
--   Definitions and structural lemmas for PChain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.LFunctionChainParameters.LChain
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
section
variable {U0 : Type} [Fintype U0] {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}
def sLog (D0 : Data U0 W Top m f) (u0 : U0) : ℝ :=
  ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D0.w u0 j ρ)
def compl (D0 : Data U0 W Top m f) (C : Consts) : Data U0 (fun _ => Unit) Top m f where
  x := D0.x
  ε := D0.ε
  a := D0.a
  b := D0.b
  b' := D0.b'
  k := D0.k
  L := D0.L
  La := D0.La
  B0 := D0.B0
  Nc := D0.Nc
  gam := D0.gam
  LpL := D0.LpL
  v := Real.pi
  lg := 0
  logGam := 0
  aT := D0.aT
  w := D0.w
  d := fun _ _ => 1
  T := fun u0 _ => Real.exp (sLog D0 u0)
  muN := fun u0 _ => D0.ASK u0 - D0.LoP C
  muMaxN := fun u0 _ => D0.ASK u0 - D0.LoP C
  h := fun _ _ => 0
  muM := fun _ _ => 0
  muMaxM := fun _ _ => 0
  EeJ := fun _ _ _ => 0
  muCC := fun u0 => D0.ASK u0 - D0.LoP C
  muMinCC := fun u0 => D0.ASK u0 - D0.LoP C
  Fo := fun _ => 0
  Ga := fun u0 => D0.ASK u0 - D0.LoP C
  Ta := fun _ => 0
  ASK := D0.ASK
  IO := fun _ => 0
  HH := fun _ => D0.x ^ C.cHH * D0.b
  del := fun _ => 0
  η := fun _ => 0
  e := fun _ => 0
  delBar := 0
  etaBar := 0
  eBar := 0
end
namespace Model
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
lemma model_sigma_add_self : (sgc0 : E0 × H) + sgc0 = 0 := by
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  simp [sgc0, h11]
def Id : AddSubgroup (E0 × H) where
  carrier := {x | x = 0 ∨ x = sgc0}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · left; simp
    · right; simp
    · right; simp
    · left; exact model_sigma_add_self
  neg_mem' := by
    rintro a (rfl | rfl)
    · left; simp
    · right; exact neg_eq_of_add_eq_zero_left model_sigma_add_self
def DA : ArithData H where
  q1 := 11
  d := 7
  inertia p := if p = 7 then Id else ⊥
  frob _ := 0
def wM : H → Fin 1 → E0 × H → ℝ := fun u0 _ ρ => if IsThickAt univ u0 ρ then 2 ^ 60 else 2 ^ 56
def aM : H → ℝ := fun _ => 65536 * 2 ^ 60
def fM (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] : ℕ := (PhiSet (H := H)).card
def ePM : Fin (fM H) ≃ PhiSet (H := H) := (Finset.equivFin _).symm
def modelData : Data H (fun _ => Unit) (univ : Finset H) 1 (fM H) where
  x := 65536
  ε := 1
  a := 65536 * 2 ^ 60
  b := 2 ^ 60
  b' := 2 ^ 56
  k := 65536
  L := 60
  La := 100
  B0 := 0
  Nc := 0
  gam := Real.eulerMascheroniConstant
  LpL := 0
  v := 1
  lg := 0
  logGam := 0
  aT := fun _ => 65536 * 2 ^ 60
  w := fun u0 j ρ => wM u0 j (ePM ρ)
  d := fun _ _ => 1
  T := fun _ _ => 1
  muN := fun _ _ => 0
  muMaxN := fun _ _ => 0
  h := fun _ _ => 0
  muM := fun _ _ => 0
  muMaxM := fun _ _ => 0
  EeJ := fun _ _ _ => 0
  muCC := fun _ => 0
  muMinCC := fun _ => 0
  Fo := fun _ => 0
  Ga := fun _ => 0
  Ta := fun _ => 0
  ASK := fun u0 => ∑ t ∈ (univ : Finset H), ∑ j : Fin 1, ASK DA 1048576 (aM t) t (wM u0 j)
  IO := fun _ => 0
  HH := fun _ => 1
  del := fun _ => 0
  η := fun _ => 0
  e := fun _ => 0
  delBar := 0
  etaBar := 0
  eBar := 0
def CM : Consts := ⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 1⟩
end
end Model
end Formalism.LFunctionChainParameters.LChain
section Check
open Formalism.LFunctionChainParameters.LChain
end Check
namespace Formalism.LFunctionChainParameters.LChain
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.ConditionalMainTheorem Formalism.LFunctionChainParameters.LErr
namespace ModelEv
open Model
def SizesAt (K cHH eK ε x : ℝ) : Prop :=
  ∃ (H : Type) (_ : AddCommGroup H) (_ : Fintype H) (_ : DecidableEq H)
    (Top : Type) (_ : Fintype Top) (m f : ℕ)
    (D0 : Data H (fun _ => Unit) Top m f) (C : Consts) (Xpp : ℝ)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)) (η X' θ : ℝ),
    D0.x = x ∧ D0.ε = ε ∧ C.eDiv ≤ 1 ∧ C.eLoss ≤ 1 ∧ C.cHH ≤ cHH ∧
    HostFacts D ∧ Ident D0 D N ell TT a w eT eP ∧ ErrWindows D0 C Xpp eK K ∧ BNBounds D0 T2 ∧
    GrowthInequalitySizes TT T2 a w N D0.x D0.b D0.b' η X' θ ∧ 0 < θ ∧ CostWindows D0.x (fPl H) D0.b η θ ∧
    RestSize D0.ε D0.x (Fintype.card H) TT.card T2.card m D0.b D0.k D0.a ∧
    (∀ u0, 0 ≤ ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D0.w u0 j ρ)) ∧
    (∀ u0, ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D0.w u0 j ρ) ≤ C.cCount * (m : ℝ) * D0.L) ∧
    (∀ u0, D0.ASK u0 ≤ D0.Main u0 + C.cDiv * D0.nT * D0.a * D0.La
      + C.cDiv * (m : ℝ) * (D0.B0 + D0.Nc) * D0.x ^ (C.eDiv * D0.ε) + D0.LoP C)
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
def wE (m : ℕ) (b : ℝ) : H → Fin m → E0 × H → ℝ := fun u0 _ ρ => if IsThickAt univ u0 ρ then b else 1
def DE (x ε b : ℝ) (m N : ℕ) : Data H (fun _ => Unit) (univ : Finset H) m (fM H) where
  x := x
  ε := ε
  a := x * b
  b := b
  b' := 1
  k := x * m
  L := Real.log b
  La := Real.log b
  B0 := (2 * (Fintype.card H : ℝ)) * m * b * x ^ ε
  Nc := ((univ : Finset H).card : ℝ) * (x * m) * b * x ^ ε
    / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * x ^ (-ε)))
  gam := Real.eulerMascheroniConstant
  LpL := 0
  v := 1
  lg := 0
  logGam := 0
  aT := fun _ => x * b
  w := fun u0 j ρ => wE m b u0 j (ePM ρ)
  d := fun _ _ => 1
  T := fun _ _ => 1
  muN := fun _ _ => 0
  muMaxN := fun _ _ => 0
  h := fun _ _ => 0
  muM := fun _ _ => 0
  muMaxM := fun _ _ => 0
  EeJ := fun _ _ _ => 0
  muCC := fun _ => 0
  muMinCC := fun _ => 0
  Fo := fun _ => 0
  Ga := fun _ => 0
  Ta := fun _ => 0
  ASK := fun u0 => ∑ t ∈ (univ : Finset H), ∑ j : Fin m, ASK DA N (x * b) t (wE m b u0 j)
  IO := fun _ => 0
  HH := fun _ => 1
  del := fun _ => 0
  η := fun _ => 0
  e := fun _ => 0
  delBar := 0
  etaBar := 0
  eBar := 0
end
end ModelEv
namespace ModelText
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
def kTx (x ε : ℝ) : ℝ := x ^ ((9 : ℝ) / 2 + 10 * ε)
def etaTx (x ε : ℝ) : ℝ := Real.exp (x ^ (ε / 4))
def thTx (x ε : ℝ) : ℝ := Real.exp (-(x ^ (ε / 8)))
def wF (x ε : ℝ) (m : ℕ) (TT T2 : Finset H) : H → Fin m → E0 × H → ℝ := fun u0 _ ρ =>
  if IsThickAt T2 u0 ρ then bTx x ε + etaTx x ε
  else if ρ ∈ TT.image topPl then 2 * bpTx x ε else wppTx x ε (Fintype.card H)
def NF (H : Type) [Fintype H] (x ε : ℝ) : ℕ := ⌈XppTx x ε (Fintype.card H)⌉₊
def textData (x ε : ℝ) (m : ℕ) (TT T2 : Finset H) : Data H (fun _ => Unit) TT m (Model.fM H) where
  x := x
  ε := ε
  a := aTx x ε
  b := bTx x ε
  b' := bpTx x ε
  k := kTx x ε
  L := x ^ ε
  La := Real.log (aTx x ε) + x ^ (ε / 3)
  B0 := (2 * (Fintype.card H : ℝ)) * m * bTx x ε * x ^ ε
  Nc := (T2.card : ℝ) * kTx x ε * bTx x ε * x ^ ε / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * x ^ (-ε)))
  gam := Real.eulerMascheroniConstant
  LpL := 0
  v := 1
  lg := 0
  logGam := 0
  aT := fun _ => aTx x ε
  w := fun u0 j ρ => wF x ε m TT T2 u0 j (Model.ePM ρ)
  d := fun _ _ => 1
  T := fun _ _ => 1
  muN := fun _ _ => 0
  muMaxN := fun _ _ => 0
  h := fun _ _ => 0
  muM := fun _ _ => 0
  muMaxM := fun _ _ => 0
  EeJ := fun _ _ _ => 0
  muCC := fun _ => 0
  muMinCC := fun _ => 0
  Fo := fun _ => 0
  Ga := fun _ => 0
  Ta := fun _ => 0
  ASK := fun u0 => ∑ t ∈ TT, ∑ j : Fin m, ASK Model.DA (NF H x ε) (aTx x ε) t (wF x ε m TT T2 u0 j)
  IO := fun _ => 0
  HH := fun _ => 1
  del := fun _ => 0
  η := fun _ => 0
  e := fun _ => 0
  delBar := 0
  etaBar := x ^ (-1 : ℝ)
  eBar := 0
def CF : Consts := ⟨1, 1, 1, 1, 2, 1, 1, 1, 1, 1⟩
def AllSizes (x ε : ℝ) (m : ℕ) (TT T2 : Finset H) : Prop :=
  HostFacts (Model.DA (H := H)) ∧
  Ident (textData x ε m TT T2) Model.DA (NF H x ε) (fun _ => 0) TT (fun _ => aTx x ε) (wF x ε m TT T2)
    (Equiv.refl _) Model.ePM ∧
  ErrWindows (textData x ε m TT T2) CF (XppTx x ε (Fintype.card H)) 15 2 ∧
  BNBounds (textData x ε m TT T2) T2 ∧
  GrowthInequalitySizes TT T2 (fun _ => aTx x ε) (wF x ε m TT T2) (NF H x ε) x (bTx x ε) (bpTx x ε) (etaTx x ε) (XpTx x ε)
    (thTx x ε) ∧
  CostWindows x (fPl H) (bTx x ε) (etaTx x ε) (thTx x ε) ∧
  RestSize ε x (Fintype.card H) TT.card T2.card m (bTx x ε) (kTx x ε) (aTx x ε) ∧
  (∀ u0, 0 ≤ ∑ j : Fin m, (1 / (Model.fM H : ℝ)) * ∑ ρ : Fin (Model.fM H), Real.log ((textData x ε m TT T2).w u0 j ρ)) ∧
  (∀ u0, ∑ j : Fin m, (1 / (Model.fM H : ℝ)) * ∑ ρ : Fin (Model.fM H), Real.log ((textData x ε m TT T2).w u0 j ρ)
    ≤ CF.cCount * (m : ℝ) * (textData x ε m TT T2).L)
end
def FamAt (ε x : ℝ) : Prop :=
  ∃ (n : ℕ) (_ : NeZero n) (m : ℕ) (TT T2 : Finset (ZMod n)),
    x ^ (2 + 8 * ε) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * x ^ (2 + 8 * ε) ∧
    x ^ ((1 : ℝ) / 2 - ε / 16) ≤ m ∧ (m : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 2 - ε / 16) ∧
    (TT.card : ℝ) < x ^ (-(ε / 8)) * n / 2 + 1 ∧ (T2.card : ℝ) < x ^ (-ε) * n + 1 ∧
    AllSizes x ε m TT T2
end ModelText
end Formalism.LFunctionChainParameters.LChain
section Check2
open Formalism.LFunctionChainParameters.LChain
end Check2


