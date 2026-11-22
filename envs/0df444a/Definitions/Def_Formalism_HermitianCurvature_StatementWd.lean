-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementWd
-- name    : Formalism_HermitianCurvature_StatementWd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:26.264204+00:00
-- url     : https://prove2.me/theorems/b54773bc-e85d-430d-b5b6-f52e04e75505
-- title:
--   Statement Wd
-- statement:
--   Definitions and structural lemmas for Statement Wd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementWd.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.Wd
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W
abbrev Ix (S : Type) : Type := S → Fin 2
abbrev SlopeTestRemainingChoices (S A : Type) : Type := Matrix (Ix S) (Ix S) A
abbrev M2 (B : Type) : Type := Matrix (Fin 2) (Fin 2) B
structure Letter (K S : Type) where

  plus : Bool

  intersection_update_fsHerm_neg_one : S

  pt : K
structure Site (A : Type) where

  p : A

  c : A

  ci : A
section Defs
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A]
  [Fintype S] [DecidableEq S]
def eU (a : S) (i j : Fin 2) : SlopeTestRemainingChoices S A :=
  Matrix.of fun x y => if x a = i ∧ y a = j ∧ ∀ b, b ≠ a → x b = y b then 1 else 0
def FreeOf (a : S) (b : SlopeTestRemainingChoices S A) : Prop := ∀ i j, Commute (eU a i j : SlopeTestRemainingChoices S A) b
def FreeOf2 (a : S) (M : M2 (SlopeTestRemainingChoices S A)) : Prop := ∀ i j, FreeOf a (M i j)
def ins (a : S) (M : M2 (SlopeTestRemainingChoices S A)) : SlopeTestRemainingChoices S A := ∑ i, ∑ j, eU a i j * M i j
def io (x : A) : SlopeTestRemainingChoices S A := Matrix.scalar (Ix S) x
def lift0 (M : M2 A) : M2 (SlopeTestRemainingChoices S A) := M.map io
def d0 (b : SlopeTestRemainingChoices S A) : M2 (SlopeTestRemainingChoices S A) := Matrix.diagonal fun _ => b
def P0 (a : S) : M2 (SlopeTestRemainingChoices S A) := Matrix.of fun i j => eU a j i
def Q0 (a : S) : M2 (SlopeTestRemainingChoices S A) := Matrix.of fun i j => eU a i j
def Rh0 (a : S) (D : K) : M2 (SlopeTestRemainingChoices S A) := (D - 1)⁻¹ • (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a)
def Rht0 (b : S) (d : K) : M2 (SlopeTestRemainingChoices S A) := (d - 1)⁻¹ • (d • (1 : M2 (SlopeTestRemainingChoices S A)) - Q0 b)
def e1 : Ix S := fun _ => 0
def RTTat {B : Type} [Ring B] [Algebra K B] (M : K → M2 B) (Y Y' : K) : Prop :=
  ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B) * E1 (M Y') * E2 (M Y) =
    E2 (M Y) * E1 (M Y') * ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B)
def DetAt {B : Type} [Ring B] [Algebra K B] (M : K → M2 B) (q : K → K) (Y : K) : Prop :=
  (M (Y + 1))ᵀ * YangianSpanCharacter.T.J B * M Y = algebraMap K B (q Y) • YangianSpanCharacter.T.J B ∧
    M Y * YangianSpanCharacter.T.J B * (M (Y + 1))ᵀ = algebraMap K B (q Y) • YangianSpanCharacter.T.J B
structure IsModule (Ω : Set K) (RR : SlopeTestRemainingChoices S A) (TT : K → M2 (SlopeTestRemainingChoices S A)) (q : K → K) : Prop where

  form_herm : star RR = RR

  herm : ∀ Y ∈ Ω, star Y = Y → (d0 RR * TT Y)ᴴ = d0 RR * TT Y

  rtt : ∀ Y ∈ Ω, ∀ Y' ∈ Ω, RTTat TT Y Y'

  det : ∀ Y ∈ Ω, Y + 1 ∈ Ω → DetAt TT q Y

  q_real : ∀ Y, star Y = Y → star (q Y) = q Y
structure IsStart (QQ : K → M2 A) (q : K → K) : Prop where

  herm : ∀ Y, star Y = Y → (QQ Y)ᴴ = QQ Y

  rtt : IsRTT QQ

  det : IsDet QQ q

  q_real : ∀ Y, star Y = Y → star (q Y) = q Y
def TTw (QQ : K → M2 A) : List (Letter K S) → K → M2 (SlopeTestRemainingChoices S A)
  | [], Y => lift0 (QQ Y)
  | l :: w, Y =>
    if l.plus then TTw QQ w Y * Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) else Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) * TTw QQ w Y
def RRw (QQ : K → M2 A) : List (Letter K S) → SlopeTestRemainingChoices S A
  | [] => 1
  | l :: w => RRw QQ w * ins l.intersection_update_fsHerm_neg_one (if l.plus then TTw QQ w l.pt else (TTw QQ w l.pt)ᵀ)
def qw (q : K → K) : List (Letter K S) → K → K
  | [], Y => q Y
  | l :: w, Y =>
    if l.plus then qw q w Y * ((Y - l.pt + 1) / (Y - l.pt))
    else qw q w Y * ((l.pt - Y) / (l.pt - Y - 1))
def RegL (l : Letter K S) (Y : K) : Prop := if l.plus then Y - l.pt ≠ 1 else l.pt - Y ≠ 1
def Reg (w : List (Letter K S)) (Y : K) : Prop := ∀ l ∈ w, RegL l Y
def Good (w : List (Letter K S)) : Prop :=
  (w.map Letter.intersection_update_fsHerm_neg_one).Nodup ∧ (∀ l ∈ w, star l.pt = l.pt) ∧ w.Pairwise fun l l' => RegL l' l.pt
def Xp : List (Letter K S) → K → M2 (SlopeTestRemainingChoices S A)
  | [], _ => 1
  | l :: w, Y => if l.plus then Xp w Y * Rh0 l.intersection_update_fsHerm_neg_one (Y - l.pt) else Xp w Y
def Xm : List (Letter K S) → K → M2 (SlopeTestRemainingChoices S A)
  | [], _ => 1
  | l :: w, Y => if l.plus then Xm w Y else Rht0 l.intersection_update_fsHerm_neg_one (l.pt - Y) * Xm w Y
def Ts (σ : Site A) (Y : K) : M2 A := Tm Y σ.p σ.c σ.ci
def hol (σ : Site A) : Set A := {σ.p, σ.c, σ.ci}
def ops (σ : Site A) : Set A := {x | x ∈ hol σ ∨ star x ∈ hol σ}
def IsSite (σ : Site A) : Prop :=
  WeylRel σ.p σ.c σ.ci ∧ ∀ x ∈ hol σ, ∀ y ∈ hol σ, Commute x (star y)
def SitesCommute (σ τ : Site A) : Prop := ∀ x ∈ ops σ, ∀ y ∈ ops τ, Commute x y
def QQCommutes (QQ : K → M2 A) (σ : Site A) : Prop := ∀ Y i j, ∀ x ∈ ops σ, Commute (QQ Y i j) x
def vlet (σ : Site A) (l : Letter K S) : SlopeTestRemainingChoices S A :=
  ins l.intersection_update_fsHerm_neg_one (lift0 (if l.plus then Ts σ l.pt else (Ts σ l.pt).map star))
def bT (σ : Site A) : List (Letter K S) → SlopeTestRemainingChoices S A
  | [] => 1
  | l :: w => vlet σ l * bT σ w
def uw (sites : List (Site A)) (w : List (Letter K S)) : Ix S → A :=
  fun z => (sites.map fun σ => bT σ w).prod z e1
def v0 (sites : List (Site A)) (Y : K) : Fin 2 → A :=
  fun k => (sites.map fun σ => Ts σ Y).prod k 0
def Cw (QQ : K → M2 A) (sites : List (Site A)) (w : List (Letter K S)) (Y : K) : SlopeTestRemainingChoices S A :=
  ∑ k, ∑ l, io (star (v0 sites Y k)) * TTw QQ w Y k l * io (v0 sites Y l)
def C0 (QQ : K → M2 A) (sites : List (Site A)) (Y : K) : A :=
  ∑ k, ∑ l, star (v0 sites Y k) * QQ Y k l * v0 sites Y l
def dl (l : Letter K S) : Letter K S :=
  if l.plus then ⟨false, l.intersection_update_fsHerm_neg_one, l.pt + 1⟩ else ⟨true, l.intersection_update_fsHerm_neg_one, l.pt - 1⟩
def ypt (l : Letter K S) : K := if l.plus then l.pt else l.pt - 1
def PsiP (TT : K → M2 (SlopeTestRemainingChoices S A)) (q : K → K) (a : S) (Y : K) : SlopeTestRemainingChoices S A :=
  ins a (-((q Y)⁻¹ • (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * (TT (Y + 1))ᵀ)))
def PsiM (TT : K → M2 (SlopeTestRemainingChoices S A)) (q : K → K) (a : S) (Yb : K) : SlopeTestRemainingChoices S A :=
  ins a ((q (Yb - 1))⁻¹ • (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * TT (Yb - 1)))
def Ps (QQ : K → M2 A) (q : K → K) (w : List (Letter K S)) : List (Letter K S) → SlopeTestRemainingChoices S A
  | [] => 1
  | l :: L =>
    (if l.plus then PsiP (TTw QQ (L ++ w)) (qw q (L ++ w)) l.intersection_update_fsHerm_neg_one l.pt
      else PsiM (TTw QQ (L ++ w)) (qw q (L ++ w)) l.intersection_update_fsHerm_neg_one l.pt) * Ps QQ q w L
def ph : List (Letter K S) → K → K
  | [], _ => 1
  | l :: L, Y =>
    if l.plus then ph L Y * ((Y - l.pt) / (Y - l.pt - 1)) else ph L Y * ((Y - l.pt) / (Y - l.pt + 1))
def kap (q : K → K) (w : List (Letter K S)) : List (Letter K S) → K
  | [] => 1
  | l :: L => kap q w L * qw q (L ++ w) (ypt l) / ph L (dl l).pt
def JL : List (Letter K S) → SlopeTestRemainingChoices S A
  | [] => 1
  | l :: L => ins l.intersection_update_fsHerm_neg_one (if l.plus then YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) else (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))ᵀ) * JL L
def DualOK (q : K → K) (w : List (Letter K S)) : List (Letter K S) → Prop
  | [] => True
  | l :: L => Reg (L ++ w) (dl l).pt ∧ qw q (L ++ w) (ypt l) ≠ 0 ∧ DualOK q w L
def kapF (q : K → K) (w : List (Letter K S)) : List (Letter K S) → K
  | [] => 1
  | l :: L => kapF q w L * qw q w (ypt l) *
      (L.map fun l' => if l.plus = l'.plus then 1
        else 1 - ((l.pt - l'.pt + (if l.plus then 1 else -1)) ^ 2)⁻¹).prod
def UUw (s : K) : List (Letter K S) → SlopeTestRemainingChoices S A
  | [] => 1
  | l :: w => ins l.intersection_update_fsHerm_neg_one (lift0 (Um (A := A) (if l.plus then s else star s))) * UUw s w
def UUiw (s : K) : List (Letter K S) → SlopeTestRemainingChoices S A
  | [] => 1
  | l :: w => ins l.intersection_update_fsHerm_neg_one (lift0 (Uinv (A := A) (if l.plus then s else star s))) * UUiw s w
def Vw (f : A) (s : K) (w : List (Letter K S)) : SlopeTestRemainingChoices S A := io f * UUiw s w
def Viw (fi : A) (s : K) (w : List (Letter K S)) : SlopeTestRemainingChoices S A := UUw s w * io fi
def IsWave (f fi : A) : Prop := f * fi = 1 ∧ fi * f = 1 ∧ star f = fi
def WaveQQ (QQ : K → M2 A) (f fi : A) (s : K) : Prop :=
  ∀ Y, Matrix.diagonal (fun _ => fi) * QQ Y * Matrix.diagonal (fun _ => f) =
    (Um (A := A) s)ᴴ * QQ Y * Um (A := A) s
end Defs
def InsMul : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (a : S) (M N : M2 (SlopeTestRemainingChoices S A)),
    FreeOf2 a M → ins a (M * N) = ins a M * ins a N
def InsStar : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (a : S) (M : M2 (SlopeTestRemainingChoices S A)),
    FreeOf2 a M → star (ins a M) = ins a Mᴴ
def InsDiag : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (a : S) (b : SlopeTestRemainingChoices S A),
    ins a (1 : M2 (SlopeTestRemainingChoices S A)) = 1 ∧ ins a (d0 b) = b
def InsFree : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (a : S) (M : M2 (SlopeTestRemainingChoices S A)),
    (∀ c, c ≠ a → FreeOf2 c M → FreeOf c (ins a M)) ∧
      ∀ b : SlopeTestRemainingChoices S A, FreeOf a b → (∀ i j, Commute b (M i j)) → Commute b (ins a M)
def PositionRTTPlus : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (a : S) (M N : M2 (SlopeTestRemainingChoices S A)) (D : K),
    FreeOf2 a M → FreeOf2 a N →
    (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A)) * E1 M * E2 N =
      E2 N * E1 M * (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A)) →
    Rh0 a D * M * d0 (ins a N) = d0 (ins a N) * M * Rh0 a D
def PositionRTTMinus : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (b : S) (M N : M2 (SlopeTestRemainingChoices S A)) (d : K),
    FreeOf2 b M → FreeOf2 b N →
    (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A)) * E1 N * E2 M =
      E2 M * E1 N * (d • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A)) →
    d0 (ins b Nᵀ) * Rht0 b d * M = M * Rht0 b d * d0 (ins b Nᵀ)
def StartModule : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (QQ : K → M2 A) (q : K → K),
    IsStart QQ q → IsModule (S := S) Set.univ 1 (fun Y => lift0 (QQ Y)) q
def ExchPlus : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (Ω : Set K) (RR : SlopeTestRemainingChoices S A) (TT : K → M2 (SlopeTestRemainingChoices S A)) (q : K → K) (a : S) (Y Ya : K),
    IsModule Ω RR TT q → (∀ Y, FreeOf2 a (TT Y)) → Y ∈ Ω → Ya ∈ Ω →
    d0 (ins a (TT Ya)) * TT Y * Rh0 a (Y - Ya) = Rh0 a (Y - Ya) * TT Y * d0 (ins a (TT Ya))
def ExchMinus : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (Ω : Set K) (RR : SlopeTestRemainingChoices S A) (TT : K → M2 (SlopeTestRemainingChoices S A)) (q : K → K) (b : S) (Y Yb : K),
    IsModule Ω RR TT q → (∀ Y, FreeOf2 b (TT Y)) → Y ∈ Ω → Yb ∈ Ω →
    d0 (ins b (TT Yb)ᵀ) * Rht0 b (Yb - Y) * TT Y = TT Y * Rht0 b (Yb - Y) * d0 (ins b (TT Yb)ᵀ)
def LetterPlus : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (Ω : Set K) (RR : SlopeTestRemainingChoices S A) (TT : K → M2 (SlopeTestRemainingChoices S A)) (q : K → K) (a : S) (Ya : K),
    IsModule Ω RR TT q → FreeOf a RR → (∀ Y, FreeOf2 a (TT Y)) → Ya ∈ Ω → star Ya = Ya →
    IsModule (Ω ∩ {Y | Y - Ya ≠ 1}) (RR * ins a (TT Ya)) (fun Y => TT Y * Rh0 a (Y - Ya))
      (fun Y => q Y * ((Y - Ya + 1) / (Y - Ya)))
def LetterMinus : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (Ω : Set K) (RR : SlopeTestRemainingChoices S A) (TT : K → M2 (SlopeTestRemainingChoices S A)) (q : K → K) (b : S) (Yb : K),
    IsModule Ω RR TT q → FreeOf b RR → (∀ Y, FreeOf2 b (TT Y)) → Yb ∈ Ω → star Yb = Yb →
    IsModule (Ω ∩ {Y | Yb - Y ≠ 1}) (RR * ins b (TT Yb)ᵀ) (fun Y => Rht0 b (Yb - Y) * TT Y)
      (fun Y => q Y * ((Yb - Y) / (Yb - Y - 1)))
def WordFree : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (QQ : K → M2 A) (w : List (Letter K S)) (c : S),
    c ∉ w.map Letter.intersection_update_fsHerm_neg_one → FreeOf c (RRw QQ w) ∧ ∀ Y, FreeOf2 c (TTw QQ w Y)
def WordModule : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (QQ : K → M2 A) (q : K → K) (w : List (Letter K S)),
    IsStart QQ q → Good w → IsModule {Y | Reg w Y} (RRw QQ w) (TTw QQ w) (qw q w)
def TTFactor : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (QQ : K → M2 A) (w : List (Letter K S)) (Y : K),
    TTw QQ w Y = Xm w Y * lift0 (QQ Y) * Xp w Y
def ExchangePlusFactor : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (σ : Site A) (w : List (Letter K S)) (Y : K),
    IsSite σ → Good w →
    Xp w Y * lift0 (Ts σ Y) * d0 (bT σ w) = d0 (bT σ w) * lift0 (Ts σ Y) * Xp w Y
def ExchangeMinusFactorStar : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (σ : Site A) (w : List (Letter K S)) (Y : K),
    IsSite σ → Good w → star Y = Y →
    lift0 (Ts σ Y)ᴴ * Xm w Y * d0 (bT σ w) = d0 (bT σ w) * Xm w Y * lift0 (Ts σ Y)ᴴ
def ExchangeMinusFactorTranspose : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (σ : Site A) (w : List (Letter K S)) (Y : K),
    IsSite σ → Good w → star Y = Y →
    (Xm w Y)ᵀ * lift0 ((Ts σ Y).map star) * d0 (bT σ w) =
      d0 (bT σ w) * lift0 ((Ts σ Y).map star) * (Xm w Y)ᵀ
def ExchangePlusFactorTranspose : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (σ : Site A) (w : List (Letter K S)) (Y : K),
    IsSite σ → Good w →
    lift0 (Ts σ Y)ᵀ * (Xp w Y)ᵀ * d0 (bT σ w) = d0 (bT σ w) * (Xp w Y)ᵀ * lift0 (Ts σ Y)ᵀ
def SiteStep : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (σ : Site A) (QQ QQ' : K → M2 A) (w : List (Letter K S)),
    IsSite σ → QQCommutes QQ σ →
    (∀ Y, star Y = Y → QQ' Y = (Ts σ Y)ᴴ * QQ Y * Ts σ Y) → Good w →
    star (bT σ w) * RRw QQ w * bT σ w = RRw QQ' w
def XpFix : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (w : List (Letter K S)) (Y : K),
    (w.map Letter.intersection_update_fsHerm_neg_one).Nodup → Reg w Y →
    ∀ (k : Fin 2) (z : Ix S), (Xp w Y k 0 : SlopeTestRemainingChoices S A) z e1 = if k = 0 ∧ z = e1 then 1 else 0
def XmFix : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (w : List (Letter K S)) (Y : K),
    (w.map Letter.intersection_update_fsHerm_neg_one).Nodup → Reg w Y →
    ∀ (k : Fin 2) (z : Ix S), (Xm w Y 0 k : SlopeTestRemainingChoices S A) z e1 = if k = 0 ∧ z = e1 then 1 else 0
def EntryOne : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (QQ : K → M2 A) (w : List (Letter K S)),
    Good w → RRw QQ w e1 e1 = (w.reverse.map fun l => QQ l.pt 0 0).prod
def SitesOK {K A : Type} [Field K] [Ring A] [StarRing A] [Algebra K A]
    (QQ : K → M2 A) (sites : List (Site A)) : Prop :=
  (∀ σ ∈ sites, IsSite σ ∧ QQCommutes QQ σ) ∧ sites.Pairwise SitesCommute
def ExchVecA : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (QQ : K → M2 A) (sites : List (Site A)) (w : List (Letter K S)) (Y : K),
    SitesOK QQ sites → Good w → Reg w Y →
    ∀ (k : Fin 2) (z : Ix S),
      (∑ l, ∑ z', (Xp w Y k l : SlopeTestRemainingChoices S A) z z' * (v0 sites Y l * uw sites w z')) =
        uw sites w z * v0 sites Y k
def ExchVecB : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (QQ : K → M2 A) (sites : List (Site A)) (w : List (Letter K S)) (Y : K),
    SitesOK QQ sites → Good w → Reg w Y → star Y = Y →
    ∀ (l : Fin 2) (z : Ix S),
      (∑ k, ∑ z', star (v0 sites Y k) * (Xm w Y k l : SlopeTestRemainingChoices S A) z z' * uw sites w z') =
        uw sites w z * star (v0 sites Y l)
def CwEigen : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (QQ : K → M2 A) (sites : List (Site A)) (w : List (Letter K S)) (Y : K),
    SitesOK QQ sites → Good w → Reg w Y → star Y = Y →
    ∀ z : Ix S, (∑ z', Cw QQ sites w Y z z' * uw sites w z') = uw sites w z * C0 QQ sites Y
def UwProduct : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (QQ : K → M2 A) (sites : List (Site A)) (w : List (Letter K S)),
    SitesOK QQ sites → Good w →
    ∀ z : Ix S, uw sites w z =
      if ∀ c, c ∉ w.map Letter.intersection_update_fsHerm_neg_one → z c = 0 then
        (w.map fun l => if l.plus then v0 sites l.pt (z l.intersection_update_fsHerm_neg_one)
          else (sites.map fun σ => (Ts σ l.pt).map star).prod (z l.intersection_update_fsHerm_neg_one) 0).prod
      else 0
def DualPlus : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (Ω : Set K) (RR : SlopeTestRemainingChoices S A) (TT : K → M2 (SlopeTestRemainingChoices S A)) (q : K → K) (a : S) (Y : K),
    IsModule Ω RR TT q → FreeOf a RR → (∀ Y, FreeOf2 a (TT Y)) →
    Y ∈ Ω → Y + 1 ∈ Ω → star Y = Y → q Y ≠ 0 →
    ins a (TT Y) * PsiP TT q a Y = ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))ᵀ ∧
    PsiP TT q a Y * ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * TT Y) = 1 ∧
    ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * TT Y) * PsiP TT q a Y = 1 ∧
    star (PsiP TT q a Y) * (RR * ins a (TT Y)) = ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A)) * RR ∧
    star (PsiP TT q a Y) * (RR * ins a (TT Y)) * PsiP TT q a Y =
      (q Y)⁻¹ • (RR * ins a (TT (Y + 1))ᵀ) ∧
    ∀ Y0 ∈ Ω, Y0 - Y ≠ 1 → Y0 - Y ≠ 0 →
      TT Y0 * Rh0 a (Y0 - Y) * d0 (PsiP TT q a Y) =
        ((Y0 - Y) / (Y0 - Y - 1)) • (d0 (PsiP TT q a Y) * (Rht0 a (Y + 1 - Y0) * TT Y0))
def DualMinus : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (Ω : Set K) (RR : SlopeTestRemainingChoices S A) (TT : K → M2 (SlopeTestRemainingChoices S A)) (q : K → K) (a : S) (Yb : K),
    IsModule Ω RR TT q → FreeOf a RR → (∀ Y, FreeOf2 a (TT Y)) →
    Yb ∈ Ω → Yb - 1 ∈ Ω → star Yb = Yb → q (Yb - 1) ≠ 0 →
    IsUnit (PsiM TT q a Yb) ∧
    star (PsiM TT q a Yb) * (RR * ins a (TT Yb)ᵀ) = ins a (YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))ᵀ * RR ∧
    star (PsiM TT q a Yb) * (RR * ins a (TT Yb)ᵀ) * PsiM TT q a Yb =
      (q (Yb - 1))⁻¹ • (RR * ins a (TT (Yb - 1))) ∧
    ∀ Y0 ∈ Ω, Yb - Y0 ≠ 1 → Y0 - Yb ≠ 0 →
      Rht0 a (Yb - Y0) * TT Y0 * d0 (PsiM TT q a Yb) =
        ((Y0 - Yb) / (Y0 - Yb + 1)) • (d0 (PsiM TT q a Yb) * (TT Y0 * Rh0 a (Y0 - Yb + 1)))
def DualityList : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (QQ : K → M2 A) (q : K → K) (w L : List (Letter K S)),
    IsStart QQ q → Good (L ++ w) → Good (L.map dl ++ w) → DualOK q w L →
    IsUnit (Ps QQ q w L) ∧ kap q w L ≠ 0 ∧
    star (Ps QQ q w L) * RRw QQ (L ++ w) = JL L * RRw QQ w ∧
    star (Ps QQ q w L) * RRw QQ (L ++ w) * Ps QQ q w L = (kap q w L)⁻¹ • RRw QQ (L.map dl ++ w) ∧
    ∀ Y, Reg (L ++ w) Y → Reg (L.map dl ++ w) Y →
      TTw QQ (L ++ w) Y * d0 (Ps QQ q w L) =
        ph L Y • (d0 (Ps QQ q w L) * TTw QQ (L.map dl ++ w) Y)
def KapFormula : Prop :=
  ∀ (K S : Type) [Field K] [StarRing K] (q : K → K) (w L : List (Letter K S)),
    Good (L ++ w) → Good (L.map dl ++ w) → DualOK q w L → kap q w L = kapF q w L
def RhUU : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (a : S) (D s : K),
    lift0 (Um (A := A) s) * d0 (ins a (lift0 (Um (A := A) s))) * Rh0 a D =
      Rh0 a D * (lift0 (Um (A := A) s) * d0 (ins a (lift0 (Um (A := A) s))))
def RhtUU : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (b : S) (d s : K),
    d0 (ins b (lift0 (Um (A := A) (star s)))) * Rht0 b d * lift0 (Um (A := A) s)ᴴ =
      lift0 (Um (A := A) s)ᴴ * Rht0 b d * d0 (ins b (lift0 (Um (A := A) (star s))))
def PlaneWaveVec : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (σ : Site A) (f fi : A) (s : K) (w : List (Letter K S)),
    IsWave f fi → f * σ.c = σ.c * f → f * σ.ci = σ.ci * f →
    σ.p * f = f * σ.p + algebraMap K A s * f * σ.c → (w.map Letter.intersection_update_fsHerm_neg_one).Nodup →
    bT σ w * Vw f s w = io f * bT σ w
def PlaneWaveWord : Prop :=
  ∀ (K A S : Type) [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
    [Fintype S] [DecidableEq S] (QQ : K → M2 A) (f fi : A) (s : K) (w : List (Letter K S)),
    IsWave f fi → WaveQQ QQ f fi s → (w.map Letter.intersection_update_fsHerm_neg_one).Nodup →
    Vw f s w * Viw fi s w = 1 ∧ Viw fi s w * Vw f s w = 1 ∧
    star (Vw f s w) * RRw QQ w * Vw f s w = RRw QQ w ∧
    ∀ Y, d0 (Viw fi s w) * TTw QQ w Y * d0 (Vw f s w) =
      lift0 (Um (A := A) s)ᴴ * TTw QQ w Y * lift0 (Um (A := A) s)
def WordsAll : Prop :=
  WordModule ∧ SiteStep ∧ EntryOne ∧ CwEigen ∧ UwProduct ∧ DualityList ∧ KapFormula ∧ PlaneWaveVec ∧
    PlaneWaveWord
def WordsAssemble : Prop :=
  InsMul → InsStar → InsDiag → InsFree → PositionRTTPlus → PositionRTTMinus → StartModule → ExchPlus →
  ExchMinus → LetterPlus → LetterMinus → WordFree → TTFactor → ExchangePlusFactor → ExchangeMinusFactorStar → ExchangeMinusFactorTranspose → ExchangePlusFactorTranspose →
  XpFix → XmFix → ExchVecA → ExchVecB → DualPlus → DualMinus → RhUU → RhtUU → WordsAll
end Formalism.FourierDecayAlt.Wd


