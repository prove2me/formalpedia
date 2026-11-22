-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementFr
-- name    : Formalism_HermitianCurvature_StatementFr
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:22.410339+00:00
-- url     : https://prove2.me/theorems/74c2d62a-40e1-491b-994e-b606bd163d21
-- title:
--   Statement Fr
-- statement:
--   Definitions and structural lemmas for Statement Fr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementFr.lean

import Definitions.Def_Formalism_YangianSpanCharacter_StatementF
import Definitions.Def_Formalism_YangianSpanCharacter_ModHypYangian
import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_StatementWd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.Fr
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd
noncomputable section
def LShift : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ Y : 𝕜, Y ∈ S → Y + 1 ∈ S → lf t τinv Y = t (Y + 1) 1 0 * τinv (Y + 1)
def QuasiDetT : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ Y : 𝕜, Y ∈ S → Y - 1 ∈ S → t Y 0 0 - t Y 1 0 * τinv Y * t Y 0 1 = q (Y - 1) • τinv (Y - 1)
def GaussMinus : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜), ModHyp t τinv q S →
    ∀ Y : 𝕜, Y ∈ S → Y - 1 ∈ S →
      (t Y)ᵀ = !![1, lf t τinv (Y - 1); 0, 1] * !![q (Y - 1) • τinv (Y - 1), 0; 0, t Y 1 1] *
        !![1, 0; mf t τinv Y, 1]
def AdjL : Prop :=
  ∀ (𝕜 A : Type) [Field 𝕜] [Ring A] [StarRing A] [Algebra 𝕜 A] (t : 𝕜 → Matrix (Fin 2) (Fin 2) A)
    (τinv : 𝕜 → A) (q : 𝕜 → 𝕜) (S : Set 𝕜) (RR : A), ModHyp t τinv q S → star RR = RR →
    ∀ Y : 𝕜, Y ∈ S → Y + 1 ∈ S → (∀ i j, star (RR * t Y i j) = RR * t Y j i) →
      RR * mf t τinv (Y + 1) = star (lf t τinv Y) * RR
def RTTEntries : Prop :=
  ∀ (K B : Type) [Field K] [Ring B] [Algebra K B] (M : K → M2 B) (v u : K), RTTat M v u →
    ∀ i j k l : Fin 2,
      (u - v) • (M u i j * M v k l - M v k l * M u i j) = M u k j * M v i l - M v k j * M u i l
section Defs
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
def zfns (L : LevelData A r) : Set A := {L.ζ, L.ζi, L.ζb, L.ζbi, L.GG, L.GGi}
def IsStarLevel (L : LevelData A r) : Prop :=
  star L.ζ = L.ζb ∧ star L.nab = L.nabs ∧ star L.TT = L.TT
structure FrameData (S A : Type) where

  reg : Set ℂ

  inv : Set ℂ

  RR : SlopeTestRemainingChoices S A

  TT : ℂ → M2 (SlopeTestRemainingChoices S A)

  q : ℂ → ℂ

  N : ℕ

  F : SlopeTestRemainingChoices S A

  Fi : SlopeTestRemainingChoices S A

  x : ℂ → SlopeTestRemainingChoices S A

  xi : ℂ → SlopeTestRemainingChoices S A

  c : SlopeTestRemainingChoices S A

  ci : SlopeTestRemainingChoices S A

  ee : ℂ → SlopeTestRemainingChoices S A
def kapL (L : LevelData A r) : SlopeTestRemainingChoices S A := io (L.ζb * L.ζi * L.GGi)
def wt (L : LevelData A r) : SlopeTestRemainingChoices S A := io (L.ζ * L.ζb * L.GGi)
def wti (L : LevelData A r) : SlopeTestRemainingChoices S A := io (L.GG * L.ζi * L.ζbi)
def tz (L : LevelData A r) : SlopeTestRemainingChoices S A := io (L.TT • L.ζbi)
namespace FrameData
variable (L : LevelData A r) (f : FrameData S A)
def l (Y : ℂ) : SlopeTestRemainingChoices S A := io (L.l0 Y) + kapL L * f.ee Y
def d : SlopeTestRemainingChoices S A := wt L ^ f.N * f.c
def di : SlopeTestRemainingChoices S A := f.ci * wti L ^ f.N
def m (Y : ℂ) : SlopeTestRemainingChoices S A := f.di L * star (f.l L (Y - 1)) * f.d L
def DD (Y Ya : ℂ) : SlopeTestRemainingChoices S A := (Y - Ya)⁻¹ • (f.ee Y - f.ee Ya)
def plus (a : S) (Ya : ℂ) : FrameData S A where
  reg := f.reg ∩ {Y | Y - Ya ≠ 1}
  inv := f.inv ∩ {Y | Y - Ya ≠ 0 ∧ Y - Ya ≠ 1}
  RR := f.RR * ins a (f.TT Ya)
  TT := fun Y => f.TT Y * Rh0 a (Y - Ya)
  q := fun Y => f.q Y * ((Y - Ya + 1) / (Y - Ya))
  N := f.N + 1
  F := ins a (!![io L.ζi, 0; 0, io L.ζbi] * !![1, 0; io L.GG * f.l L Ya, io L.GG]) * f.F
  Fi := f.Fi * ins a (!![1, 0; -f.l L Ya, io L.GGi] * !![io L.ζ, 0; 0, io L.ζb])
  x := fun Y => f.x Y * ins a !![((Y - Ya) / (Y - Ya - 1)) • 1, 0; 0, 1]
  xi := fun Y => f.xi Y * ins a !![((Y - Ya - 1) / (Y - Ya)) • 1, 0; 0, 1]
  c := f.c * ins a !![f.q Ya • f.xi (Ya + 1), 0; 0, f.x Ya]
  ci := f.ci * ins a !![(f.q Ya)⁻¹ • f.x (Ya + 1), 0; 0, f.xi Ya]
  ee := fun Y => ins a !![f.ee Y - f.DD Y Ya + tz L, -((Y - Ya)⁻¹ • 1); 0, f.xi Ya * f.ee Y * f.x Ya]
def minus (b : S) (Yb : ℂ) : FrameData S A where
  reg := f.reg ∩ {Y | Yb - Y ≠ 1}
  inv := f.inv ∩ {Y | Yb - Y ≠ 0 ∧ Yb - Y ≠ 1}
  RR := f.RR * ins b (f.TT Yb)ᵀ
  TT := fun Y => Rht0 b (Yb - Y) * f.TT Y
  q := fun Y => f.q Y * ((Yb - Y) / (Yb - Y - 1))
  N := f.N + 1
  F := ins b (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG]) * f.F
  Fi := f.Fi * ins b (!![1, 0; -f.m L Yb, io L.GGi] * !![io L.ζb, 0; 0, io L.ζ])
  x := fun Y => f.x Y * ins b !![((Yb - Y) / (Yb - Y - 1)) • 1, 0; 0, 1]
  xi := fun Y => f.xi Y * ins b !![((Yb - Y - 1) / (Yb - Y)) • 1, 0; 0, 1]
  c := f.c * ins b !![f.q (Yb - 1) • f.xi (Yb - 1), 0; 0, f.x Yb]
  ci := f.ci * ins b !![(f.q (Yb - 1))⁻¹ • f.x (Yb - 1), 0; 0, f.xi Yb]
  ee := fun Y => ins b !![f.ee Y, 0;
    -((f.q (Yb - 1) / (Yb - Y - 1)) • (f.xi Yb * f.xi (Yb - 1))),
    f.xi Yb * f.ee Y * f.x Yb - f.DD Y Yb + tz L]
def Free (a : S) : Prop :=
  FreeOf a f.RR ∧ (∀ Y, FreeOf2 a (f.TT Y)) ∧ FreeOf a f.F ∧ FreeOf a f.Fi ∧ (∀ Y, FreeOf a (f.x Y)) ∧
    (∀ Y, FreeOf a (f.xi Y)) ∧ FreeOf a f.c ∧ FreeOf a f.ci ∧ ∀ Y, FreeOf a (f.ee Y)
open Classical in

def hatT (Y : ℂ) : M2 (SlopeTestRemainingChoices S A) := if Y ∈ f.reg then (f.TT Y).map (fun b => f.F * b * f.Fi) else 0
open Classical in

def hatQ (Y : ℂ) : ℂ := if Y ∈ f.reg ∧ Y + 1 ∈ f.reg then f.q Y else 0
end FrameData
structure IsFrame (L : LevelData A r) (f : FrameData S A) : Prop where

  module : IsModule f.reg f.RR f.TT f.q

  lowerLeftEntry_commute : ∀ Y ∈ f.reg, ∀ Y' ∈ f.reg, Commute (f.TT Y 1 0) (f.TT Y' 1 0)
  inv_reg : f.inv ⊆ f.reg
  F_Fi : f.F * f.Fi = 1
  Fi_F : f.Fi * f.F = 1
  x_xi : ∀ Y ∈ f.inv, f.x Y * f.xi Y = 1 ∧ f.xi Y * f.x Y = 1
  c_ci : f.c * f.ci = 1 ∧ f.ci * f.c = 1

  x_commute : ∀ Y Y', Commute (f.x Y) (f.x Y')
  x_c : ∀ Y, Commute (f.x Y) f.c
  x_fn : ∀ Y, ∀ g ∈ zfns L, Commute (f.x Y) (io g)
  x_nab : ∀ Y, Commute (f.x Y) (io L.nab)
  c_fn : ∀ g ∈ zfns L, Commute f.c (io g)
  x_star : ∀ Y, star Y = Y → star (f.x Y) = f.x Y
  c_star : star f.c = f.c

  ee_fn : ∀ Y, ∀ g ∈ zfns L, Commute (f.ee Y) (io g)

  form : f.RR = star f.F * f.d L * f.F

  frame_τ : ∀ Y ∈ f.reg, f.F * f.TT Y 1 1 = io L.GG * f.x Y * f.F

  frame_l : ∀ Y ∈ f.inv, Y + 1 ∈ f.inv → f.F * f.TT Y 1 0 = io L.GG * f.x Y * f.l L Y * f.F
def PlusHyp (L : LevelData A r) (f : FrameData S A) (a : S) (Ya : ℂ) : Prop :=
  IsStarLevel L ∧ IsFrame L f ∧ f.Free a ∧ star Ya = Ya ∧ Ya ∈ f.inv ∧ Ya + 1 ∈ f.inv ∧ f.q Ya ≠ 0
def MinusHyp (L : LevelData A r) (f : FrameData S A) (b : S) (Yb : ℂ) : Prop :=
  IsStarLevel L ∧ IsFrame L f ∧ f.Free b ∧ star Yb = Yb ∧ Yb ∈ f.inv ∧ Yb + 1 ∈ f.inv ∧ Yb - 1 ∈ f.inv ∧
    f.q (Yb - 1) ≠ 0
structure Start (A : Type) where
  QQ : ℂ → M2 A
  q : ℂ → ℂ
  x : ℂ → A
  xi : ℂ → A
  ee : ℂ → A
  inv : Set ℂ
structure IsLevelStart (L : LevelData A r) (st : Start A) : Prop where
  start : IsStart st.QQ st.q
  lowerLeftEntry_commute : ∀ Y Y', Commute (st.QQ Y 1 0) (st.QQ Y' 1 0)
  x_xi : ∀ Y ∈ st.inv, st.x Y * st.xi Y = 1 ∧ st.xi Y * st.x Y = 1
  x_commute : ∀ Y Y', Commute (st.x Y) (st.x Y')
  x_fn : ∀ Y, ∀ g ∈ zfns L, Commute (st.x Y) g
  x_nab : ∀ Y, Commute (st.x Y) L.nab
  x_star : ∀ Y, star Y = Y → star (st.x Y) = st.x Y
  ee_fn : ∀ Y, ∀ g ∈ zfns L, Commute (st.ee Y) g
  tau : ∀ Y, st.QQ Y 1 1 = L.GG * st.x Y
  low : ∀ Y ∈ st.inv, st.QQ Y 1 0 = L.GG * st.x Y * (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y)
def Start.frame (st : Start A) : FrameData S A where
  reg := Set.univ
  inv := st.inv
  RR := 1
  TT := fun Y => lift0 (st.QQ Y)
  q := st.q
  N := 0
  F := 1
  Fi := 1
  x := fun Y => io (st.x Y)
  xi := fun Y => io (st.xi Y)
  c := 1
  ci := 1
  ee := fun Y => io (st.ee Y)
def ofWord (L : LevelData A r) (st : Start A) : List (Letter ℂ S) → FrameData S A
  | [] => st.frame
  | l :: w => if l.plus then (ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt else (ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt
def admitted (st : Start A) (w : List (Letter ℂ S)) : Prop :=
  (w.map Letter.intersection_update_fsHerm_neg_one).Nodup ∧ (∀ l ∈ w, star l.pt = l.pt) ∧
    (∀ l ∈ w, l.pt ∈ st.inv ∧ l.pt + 1 ∈ st.inv ∧ l.pt - 1 ∈ st.inv ∧ st.q l.pt ≠ 0 ∧ st.q (l.pt - 1) ≠ 0) ∧
    w.Pairwise fun l l' => ∀ n : ℤ, |n| ≤ 2 → l.pt - l'.pt ≠ (n : ℂ)
def phiL (l : Letter ℂ S) (Y : ℂ) : ℂ :=
  if l.plus then (Y - l.pt) / (Y - l.pt - 1) else (l.pt - Y) / (l.pt - Y - 1)
def xs (x0 : ℂ → ℂ) : List (Letter ℂ S) → Ix S → ℂ → ℂ
  | [], _, Y => x0 Y
  | l :: w, e, Y => xs x0 w e Y * (if e l.intersection_update_fsHerm_neg_one = 0 then phiL l Y else 1)
def cs (x0 q0 : ℂ → ℂ) : List (Letter ℂ S) → Ix S → ℂ
  | [], _ => 1
  | l :: w, e => cs x0 q0 w e *
      (if l.plus then (if e l.intersection_update_fsHerm_neg_one = 0 then qw q0 w l.pt / xs x0 w e (l.pt + 1) else xs x0 w e l.pt)
       else (if e l.intersection_update_fsHerm_neg_one = 0 then qw q0 w (l.pt - 1) / xs x0 w e (l.pt - 1) else xs x0 w e l.pt))
def Pos (z : ℂ) : Prop := 0 < z.re ∧ z.im = 0
def sg (i : Fin 2) : ℂ := if i = 0 then 1 else -1
def mult (v : List (Letter ℂ S)) (γ : ℂ) : SlopeTestRemainingChoices S A :=
  Matrix.diagonal fun e => algebraMap ℂ A ((v.map fun l => 1 + sg (e l.intersection_update_fsHerm_neg_one) / (l.pt - γ)).prod)
def letterSum : List (Letter ℂ S) → List (Letter ℂ S) → ℂ → SlopeTestRemainingChoices S A
  | _, [], _ => 0
  | v, l :: w, Y => (Y - l.pt)⁻¹ • (eU l.intersection_update_fsHerm_neg_one 0 1 * mult v l.pt) + letterSum (v ++ [l]) w Y
def Kw (L : LevelData A r) (w : List (Letter ℂ S)) : SlopeTestRemainingChoices S A :=
  tz L * Matrix.diagonal fun e => algebraMap ℂ A ((w.filter fun l => e l.intersection_update_fsHerm_neg_one = 0).length : ℂ)
end Defs
def CoordinateBlockCondition : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] (a : S) (M : M2 (SlopeTestRemainingChoices S A)) (D : ℂ), FreeOf2 a M → ∀ i j : Fin 2,
    (M * Rh0 a D : M2 (SlopeTestRemainingChoices S A)) i j = ins a (Formalism.YangianSpanCharacter.F.blk (E1 M *
      ((D - 1)⁻¹ • (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A)))) i j)
def TransposedCoordinateBlockCondition : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] (b : S) (M : M2 (SlopeTestRemainingChoices S A)) (d : ℂ), ∀ i j : Fin 2,
    (Rht0 b d * M : M2 (SlopeTestRemainingChoices S A)) i j = ins b (Formalism.YangianSpanCharacter.F.blk
      (((d - 1)⁻¹ • pt1 (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A))) * E1 M) i j)
def FrameModHyp : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (f : FrameData S A), IsFrame L f →
    ModHyp f.hatT (fun Y => io L.GGi * f.xi Y) f.hatQ f.inv ∧
      ∀ Y ∈ f.inv, Y + 1 ∈ f.inv → lf f.hatT (fun Y => io L.GGi * f.xi Y) Y = f.l L Y
def StartEe : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r) (SS : A),
    L.D * L.Dbi * (L.Drb * L.Dri * SS) = L.ζ * L.ζbi * SS
def EtaLevel : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (f : FrameData S A) (Y Ya : ℂ), Y ≠ Ya →
    (Y - Ya)⁻¹ • (f.l L Y - f.l L Ya) = -io (L.ζb * L.GGi) + kapL L * f.DD Y Ya
def ZetaConj : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (f : FrameData S A) (Y : ℂ),
    (∀ g ∈ zfns L, Commute (f.ee Y) (io g)) →
    io L.ζi * f.l L Y * io L.ζ = f.l L Y - io L.ζi ∧ L.ζb * L.GGi - L.ζi = L.TT • (L.ζi * L.GGi)
def EeConj : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (f : FrameData S A) (Y Ya : ℂ), IsFrame L f →
    Y ∈ f.inv → Y + 1 ∈ f.inv → Ya ∈ f.inv → Ya + 1 ∈ f.inv → Y ≠ Ya →
    f.xi Ya * f.ee Y * f.x Ya - f.DD Y Ya = f.ee Y
def FrameM : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (f : FrameData S A) (Y : ℂ), IsStarLevel L → IsFrame L f →
    star Y = Y → Y ∈ f.inv → Y - 1 ∈ f.inv →
    f.F * f.TT Y 0 1 = io L.GG * f.x Y * f.m L Y * f.F
def NewLetterPlus : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (f : FrameData S A) (Y : ℂ),
    (∀ g ∈ zfns L, Commute (f.ee Y) (io g)) →
    (!![io L.ζi, 0; 0, io L.ζbi] * !![1, 0; io L.GG * f.l L Y, io L.GG]) *ᵥ ![io (L.Ar Y), io (L.Br Y)] =
      ![io (L.Di * L.Ahat Y), io (L.Dbi * L.R0 Y) + f.ee Y * io (L.Di * L.Ahat Y)]
def GaussFormPlus : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (f : FrameData S A) (a : S) (Ya : ℂ), PlusHyp L f a Ya →
    f.RR * ins a (f.TT Ya) = star (ins a !![1, 0; f.l L Ya, 1] * f.F) *
      (f.d L * ins a !![f.q Ya • (io L.GGi * f.xi (Ya + 1)), 0; 0, io L.GG * f.x Ya]) *
      (ins a !![1, 0; f.l L Ya, 1] * f.F)
def PlusForm : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (f : FrameData S A) (a : S) (Ya : ℂ), PlusHyp L f a Ya →
    (f.plus L a Ya).RR = star (f.plus L a Ya).F * (f.plus L a Ya).d L * (f.plus L a Ya).F
def PlusTau : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (f : FrameData S A) (a : S) (Ya : ℂ), PlusHyp L f a Ya →
    ∀ Y ∈ (f.plus L a Ya).reg,
      (f.plus L a Ya).F * (f.plus L a Ya).TT Y 1 1 = io L.GG * (f.plus L a Ya).x Y * (f.plus L a Ya).F
def PlusL : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (f : FrameData S A) (a : S) (Ya : ℂ), PlusHyp L f a Ya →
    ∀ Y ∈ (f.plus L a Ya).inv, Y + 1 ∈ (f.plus L a Ya).inv →
      (f.plus L a Ya).F * (f.plus L a Ya).TT Y 1 0 =
        io L.GG * (f.plus L a Ya).x Y * (f.plus L a Ya).l L Y * (f.plus L a Ya).F
def PlusStep : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (f : FrameData S A) (a : S) (Ya : ℂ), PlusHyp L f a Ya → IsFrame L (f.plus L a Ya)
def PlusAssemble : Prop :=
  InsMul → InsStar → InsDiag → InsFree → LetterPlus → RTTEntries → PlusForm → PlusTau → PlusL → PlusStep
def GaussFormMinus : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (f : FrameData S A) (b : S) (Yb : ℂ), MinusHyp L f b Yb →
    f.RR * ins b (f.TT Yb)ᵀ = star (ins b !![1, 0; f.m L Yb, 1] * f.F) *
      (f.d L * ins b !![f.q (Yb - 1) • (io L.GGi * f.xi (Yb - 1)), 0; 0, io L.GG * f.x Yb]) *
      (ins b !![1, 0; f.m L Yb, 1] * f.F)
def MinusForm : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (f : FrameData S A) (b : S) (Yb : ℂ), MinusHyp L f b Yb →
    (f.minus L b Yb).RR = star (f.minus L b Yb).F * (f.minus L b Yb).d L * (f.minus L b Yb).F
def MinusTau : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (f : FrameData S A) (b : S) (Yb : ℂ), MinusHyp L f b Yb →
    ∀ Y ∈ (f.minus L b Yb).reg,
      (f.minus L b Yb).F * (f.minus L b Yb).TT Y 1 1 = io L.GG * (f.minus L b Yb).x Y * (f.minus L b Yb).F
def MinusL : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (f : FrameData S A) (b : S) (Yb : ℂ), MinusHyp L f b Yb →
    ∀ Y ∈ (f.minus L b Yb).inv, Y + 1 ∈ (f.minus L b Yb).inv →
      (f.minus L b Yb).F * (f.minus L b Yb).TT Y 1 0 =
        io L.GG * (f.minus L b Yb).x Y * (f.minus L b Yb).l L Y * (f.minus L b Yb).F
def MinusLast : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (f : FrameData S A) (b : S) (Yb : ℂ), MinusHyp L f b Yb →
    ∀ Y ∈ (f.minus L b Yb).inv, Y + 1 ∈ (f.minus L b Yb).inv →
      (f.minus L b Yb).ee Y = ins b !![f.ee Y, 0;
        -((f.q (Yb - 1) / (Yb - Y - 1)) • (f.xi Yb * f.xi (Yb - 1))), f.ee Y + tz L]
def MinusStep : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (f : FrameData S A) (b : S) (Yb : ℂ), MinusHyp L f b Yb → IsFrame L (f.minus L b Yb)
def MinusAssemble : Prop :=
  InsMul → InsStar → InsDiag → InsFree → LetterMinus → RTTEntries → MinusForm → MinusTau → MinusL → MinusStep
def StartFrame : Prop :=
  StartModule → ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (st : Start A), IsLevelStart L st → IsFrame L (st.frame : FrameData S A)
def WordJoint : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)),
    (ofWord L st w).RR = RRw st.QQ w ∧ (ofWord L st w).TT = TTw st.QQ w ∧ (ofWord L st w).q = qw st.q w ∧
      (ofWord L st w).N = w.length ∧ (ofWord L st w).reg = {Y | Reg w Y}
def FrameFree : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)) (c : S),
    c ∉ w.map Letter.intersection_update_fsHerm_neg_one → (ofWord L st w).Free c
def FrameAll : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)),
    IsStarLevel L → IsLevelStart L st → admitted st w → IsFrame L (ofWord L st w)
def FrameWord : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)),
    IsStarLevel L → IsLevelStart L st → admitted st w →
    (ofWord L st w).F * (ofWord L st w).Fi = 1 ∧ (ofWord L st w).Fi * (ofWord L st w).F = 1 ∧
    RRw st.QQ w = star (ofWord L st w).F * (wt L ^ w.length * (ofWord L st w).c) * (ofWord L st w).F ∧
    (∀ Y, Reg w Y → (ofWord L st w).F * TTw st.QQ w Y 1 1 =
      io L.GG * (ofWord L st w).x Y * (ofWord L st w).F) ∧
    (∀ Y ∈ (ofWord L st w).inv, Y + 1 ∈ (ofWord L st w).inv → (ofWord L st w).F * TTw st.QQ w Y 1 0 =
      io L.GG * (ofWord L st w).x Y * (io (L.l0 Y) + kapL L * (ofWord L st w).ee Y) * (ofWord L st w).F)
def FrameAssemble : Prop :=
  StartFrame → StartModule → PlusStep → MinusStep → FrameFree → WordJoint → FrameAll ∧ FrameWord
def CDiag : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (st : Start A) (P : Type) (κ : (P → ℂ) →ₐ[ℂ] A) (x0 : P → ℂ → ℂ),
    (∀ Y, st.x Y = κ fun ρ => x0 ρ Y) → (∀ Y, st.xi Y = κ fun ρ => (x0 ρ Y)⁻¹) →
    ∀ w : List (Letter ℂ S),
      (∀ Y, (ofWord L st w).x Y = Matrix.diagonal fun e => κ fun ρ => xs (x0 ρ) w e Y) ∧
      (∀ Y, (ofWord L st w).xi Y = Matrix.diagonal fun e => κ fun ρ => (xs (x0 ρ) w e Y)⁻¹) ∧
      (ofWord L st w).c = Matrix.diagonal fun e => κ fun ρ => cs (x0 ρ) st.q w e
def CPos : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (x0 q0 : ℂ → ℂ) (w : List (Letter ℂ S)),
    (∀ l ∈ w, l.pt.im = 0) → (w.Pairwise fun l l' => 2 < |l.pt.re - l'.pt.re|) →
    (∀ l ∈ w, Pos (x0 l.pt) ∧ Pos (x0 (l.pt + 1)) ∧ Pos (x0 (l.pt - 1)) ∧ Pos (q0 l.pt) ∧ Pos (q0 (l.pt - 1))) →
    ∀ e : Ix S, Pos (cs x0 q0 w e)
def QPositiveShift : Prop :=
  ∀ (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y T T' : ℝ), 1 ≤ l → l ≤ k → I.Interlaces k u u' ρ →
    I.OnCut u u' l Y → 0 < T → 0 < T' → 0 < I.qpoly k T T' u u' (Y - 1)
def CPosCut : Prop :=
  I.InterlaceSign → I.QPositive → QPositiveShift → CPos →
  ∀ (S : Type) [Fintype S] [DecidableEq S] (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (T T' : ℝ)
    (w : List (Letter ℂ S)), 1 ≤ l → l ≤ k → I.Interlaces k u u' ρ → 0 < T → 0 < T' →
    (∀ a ∈ w, a.pt.im = 0 ∧ I.OnCut u u' l a.pt.re) →
    (w.Pairwise fun a a' => 2 < |a.pt.re - a'.pt.re|) →
    ∀ e : Ix S, Pos (cs (fun Y => (-1) ^ (k - l) * ∏ i ∈ Finset.Icc 1 (k - 1), (Y + (ρ i : ℂ)))
      (fun Y => -((T : ℂ) * T') * ∏ i ∈ Finset.Icc 1 k, ((Y + 1 / 2 + (u i : ℂ)) * (Y + 1 / 2 + (u' i : ℂ)))) w e)
def ResidueStep : Prop :=
  ∀ (B : Type) [Ring B] [Algebra ℂ B] (Z : B) (γ Ya Y : ℂ), Y ≠ γ → Ya ≠ γ → Y ≠ Ya →
    (Y - γ)⁻¹ • Z - (Y - Ya)⁻¹ • ((Y - γ)⁻¹ • Z - (Ya - γ)⁻¹ • Z) = (1 + 1 / (Ya - γ)) • ((Y - γ)⁻¹ • Z) ∧
    (Y - γ)⁻¹ • Z + (Y - Ya)⁻¹ • ((Y - γ)⁻¹ • Z - (Ya - γ)⁻¹ • Z) = (1 - 1 / (Ya - γ)) • ((Y - γ)⁻¹ • Z)
def ResidueForm : Prop :=
  FrameAll → EeConj →
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (st : Start A) (J : Type) [Fintype J] (Z : J → A) (γ : J → ℂ) (w : List (Letter ℂ S)),
    IsStarLevel L → IsLevelStart L st → admitted st w → (∀ l ∈ w, l.plus = true) →
    (∀ Y, st.ee Y = L.ζ * L.ζbi * ∑ j, (Y - γ j)⁻¹ • Z j) → (∀ l ∈ w, ∀ j, l.pt ≠ γ j) →
    ∀ Y ∈ (ofWord L st w).inv, Y + 1 ∈ (ofWord L st w).inv → (∀ j, Y ≠ γ j) →
      (ofWord L st w).ee Y = Kw L w + (∑ j, (Y - γ j)⁻¹ • (io (L.ζ * L.ζbi * Z j) * mult w (γ j))) -
        letterSum [] w Y
section BaseDefs
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
def AdmRec (L : LevelData A r) (st : Start A) : List (Letter ℂ S) → Prop
  | [] => True
  | l :: w => AdmRec L st w ∧ l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ star l.pt = l.pt ∧
      l.pt ∈ (ofWord L st w).inv ∧ l.pt + 1 ∈ (ofWord L st w).inv ∧
      (if l.plus then (ofWord L st w).q l.pt ≠ 0
       else l.pt - 1 ∈ (ofWord L st w).inv ∧ (ofWord L st w).q (l.pt - 1) ≠ 0)
def AdmBase (st : Start A) (w : List (Letter ℂ S)) : Prop :=
  (w.map Letter.intersection_update_fsHerm_neg_one).Nodup ∧ (∀ l ∈ w, star l.pt = l.pt) ∧
    (∀ l ∈ w, ypt l ∈ st.inv ∧ ypt l + 1 ∈ st.inv ∧ (l.plus = false → ypt l + 2 ∈ st.inv) ∧ st.q (ypt l) ≠ 0) ∧
    w.Pairwise fun l l' => ∀ n : ℤ, |n| ≤ 2 → ypt l - ypt l' ≠ (n : ℂ)
end BaseDefs
def AdmRecOfAdm : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)), admitted st w → AdmRec L st w
def AdmRecOfBase : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)), AdmBase st w → AdmRec L st w
def FrameAllRec : Prop :=
  ∀ (A S : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
    (r : ℕ) (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)),
    IsStarLevel L → IsLevelStart L st → AdmRec L st w → IsFrame L (ofWord L st w)
def FrameRecAssemble : Prop :=
  StartFrame → StartModule → PlusStep → MinusStep → FrameFree → FrameAllRec
def CPosBase : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] (x0 q0 : ℂ → ℂ) (w : List (Letter ℂ S)),
    (∀ l ∈ w, l.pt.im = 0) → (w.Pairwise fun l l' => 2 < |(ypt l).re - (ypt l').re|) →
    (∀ l ∈ w, Pos (x0 (ypt l)) ∧ Pos (x0 (ypt l + 1)) ∧ Pos (q0 (ypt l))) →
    ∀ e : Ix S, Pos (cs x0 q0 w e)
def CPosCutBase : Prop :=
  I.InterlaceSign → I.QPositive → QPositiveShift → CPosBase →
  ∀ (S : Type) [Fintype S] [DecidableEq S] (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (T T' : ℝ)
    (w : List (Letter ℂ S)), 1 ≤ l → l ≤ k → I.Interlaces k u u' ρ → 0 < T → 0 < T' →
    (∀ a ∈ w, a.pt.im = 0 ∧ (I.OnCut u u' l (ypt a).re ∨ I.OnCut u u' l ((ypt a).re + 1))) →
    (w.Pairwise fun a a' => 2 < |(ypt a).re - (ypt a').re|) →
    ∀ e : Ix S, Pos (cs (fun Y => (-1) ^ (k - l) * ∏ i ∈ Finset.Icc 1 (k - 1), (Y + (ρ i : ℂ)))
      (fun Y => -((T : ℂ) * T') * ∏ i ∈ Finset.Icc 1 k, ((Y + 1 / 2 + (u i : ℂ)) * (Y + 1 / 2 + (u' i : ℂ)))) w e)
end
end Formalism.FourierDecayAlt.Fr


