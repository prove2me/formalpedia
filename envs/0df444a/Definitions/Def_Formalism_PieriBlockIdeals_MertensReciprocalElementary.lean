-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
-- name    : Formalism_PieriBlockIdeals_MertensReciprocalElementary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:49.882876+00:00
-- url     : https://prove2.me/theorems/971cea3e-f65f-4f75-8515-5496ce4002ab
-- title:
--   Mertens Reciprocal Elementary
-- statement:
--   Definitions and structural lemmas for Mertens Reciprocal Elementary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/MertensReciprocalElementary.lean

import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_ContentDistanceBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
def pr (y : ℝ) : Finset ℕ := (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime
def ChebyshevThetaUpperBound : Prop := ∀ y : ℝ, 0 < y → ∑ p ∈ pr y, Real.log (p : ℝ) < 1.02 * y
def MertensLogBound : Prop := ∀ y : ℝ, 1 < y → ∑ p ∈ pr y, Real.log (p : ℝ) / (p : ℝ) < Real.log y
def MertensLogLowerBound : Prop := ∀ y : ℝ, 1 < y →
  Real.log y - 1.34 - 1 / (2 * Real.log y) < ∑ p ∈ pr y, Real.log (p : ℝ) / (p : ℝ)
def PrimeCountingBound : Prop := ∀ y : ℝ, 1 < y → ((pr y).card : ℝ) < 1.26 * y / Real.log y
def MertensReciprocalBound : Prop := ∀ y : ℝ, 1 < y →
  ∑ p ∈ pr y, 1 / (p : ℝ) < Real.log (Real.log y) + 0.27 + 1 / (Real.log y) ^ 2
def RSPP : Prop := ∀ y : ℝ, ∑ p ∈ pr y, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) < 0.76
def RS2' : Prop := ∀ y : ℝ, 1 < y →
  ∑ p ∈ pr y, Real.log (p : ℝ) / ((p : ℝ) - 1) < Real.log y + 0.76
def RosserSchoenfeldSecondBound : Prop := MertensLogBound → RSPP → RS2'
structure Par where
  k : ℕ
  m : ℕ
  t : ℕ
  f : ℕ
  n : ℕ

  Nr : ℕ
  L : ℝ
  x : ℝ
  b' : ℝ
  η : ℝ
  S : ℝ
namespace Par
def b (P : Par) : ℝ := Real.exp P.L
def w'' (P : Par) : ℝ := P.b' / (P.x * (P.n : ℝ))
def N (P : Par) : ℝ := (P.k : ℝ) + (P.m : ℝ) * ((P.t : ℝ) + 1)
def lstar (P : Par) : ℝ :=
  (P.m : ℝ) * P.b /
    ((P.n : ℝ) * (P.t : ℝ) ^ 2 * (P.N + (P.t : ℝ)) * P.L ^ 2
      + (P.k : ℝ) * (P.n : ℝ) ^ 2 * (P.S + (P.t : ℝ) + P.L))
def h (P : Par) : ℝ := P.b + P.S + P.η + (P.t : ℝ) + 1
def lJ (P : Par) : ℝ :=
  (P.m : ℝ) * P.b * P.L / ((P.k : ℝ) * ((P.m : ℝ) + (P.t : ℝ)) * Real.log (3 * P.h))
def kmax (P : Par) : ℕ := ⌊2 * P.b / P.lstar⌋₊
def kap (P : Par) (l : ℕ) : ℕ := ⌊P.h / ((l : ℝ) - 1)⌋₊
def Excl (P : Par) (l : ℕ) : Prop :=
  ∃ z : ℤ, P.b - ((P.t : ℝ) - 1) / 2 - (P.kmax : ℝ) ≤ (z : ℝ) ∧
    (z : ℝ) ≤ P.b + P.S + P.η + 1 + ((P.t : ℝ) - 1) / 2 + (P.kmax : ℝ) ∧ (l : ℤ) ∣ z
structure Hyp (P : Par) : Prop where
  x_ge : 1 ≤ P.x
  b'_pos : 0 < P.b'
  m_pos : 1 ≤ P.m
  n_pos : 1 ≤ P.n
  f_pos : 1 ≤ P.f
  t_ge : P.k + P.m + 4 ≤ P.t
  t_gt : 3 * P.m < P.t
  m_le : P.m ≤ P.k
  η_le : P.η ≤ P.b / ((P.t : ℝ) ^ 3 * (P.f : ℝ) * (P.k : ℝ) ^ 3)
  Nr_eq : P.Nr + 1 = P.k + P.m + P.t
  t_le : (P.t : ℝ) ≤ P.η
  S_nonneg : 0 ≤ P.S
  sum_lt : P.b' + P.S + P.η + P.b / P.lstar < P.lstar
  win_lt : 2 * P.η + (P.t : ℝ) + 8 * P.b / P.lstar + 7 < P.lstar
structure Large (P : Par) : Prop where
  L_ge : 4 ≤ P.L
  b_gt : 48 * (P.k : ℝ) ^ 2 * (P.t : ℝ) ^ 2 < P.b
  bb' : 12 * (P.k : ℝ) * (P.t : ℝ) * P.b' < P.b
  w_gt : 2 * (2 * P.b / P.lstar + (P.t : ℝ)) < P.w''
  top_le : P.S + P.b' * (1 + 1 / P.x + 1 / P.x ^ 2) + P.η + ((P.t : ℝ) - 1) / 2 ≤ 2 * P.b'
end Par
def Elem0 : Prop :=
  ∀ P : Par, P.Hyp → P.Large → P.Nr ≤ 2 * P.t ∧ 2 * P.lstar ≤ P.b ∧ P.h ≤ 2 * P.b
def Elem_a : Prop :=
  ∀ P : Par, P.Hyp → P.Large →
    Real.log (3 * P.h) ≤ P.L + Real.log 6 ∧ P.L + Real.log 6 ≤ 2 * P.L ∧ P.lJ ≤ P.b
def Elem_b : Prop :=
  ∀ P : Par, P.Hyp → P.Large → P.L * P.lstar ≤ P.lJ ∧ P.lstar + 1 < P.L * P.lstar
def Elem_c : Prop :=
  ∀ P : Par, P.Hyp → P.Large →
    P.b / (4 * (P.k : ℝ) * (P.t : ℝ)) ≤ P.lJ ∧ 3 * P.b < P.lJ ^ 2 ∧ P.h + (P.Nr : ℝ) ≤ 3 * P.b ∧
      P.b + P.S + P.η + 1 + ((P.t : ℝ) - 1) / 2 + (P.kmax : ℝ) ≤ 3 * P.b
def Elem_d : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ l : ℕ, P.lJ < (l : ℝ) →
    P.lstar ≤ (l : ℝ) - 1 ∧ (P.kap l : ℝ) ≤ 2 * P.b / P.lstar ∧ P.kap l ≤ P.kmax ∧
      P.t + 2 * P.kap l < l ∧ P.η + (P.t : ℝ) + (P.kap l : ℝ) < (l : ℝ) ∧ P.Nr + 1 < l ∧
      P.S + (P.k : ℝ) < (l : ℝ) ∧ P.h + (P.Nr : ℝ) < (l : ℝ) ^ 2
def Elem_e : Prop := ∀ P : Par, P.Hyp → P.Large → 3 * P.b' < P.lJ
def Elem_f : Prop :=
  ∀ P : Par, P.Hyp → P.Large → (P.kmax : ℝ) + (P.t : ℝ) < P.w'' / 2 ∧ P.w'' ≤ P.b'
namespace Par
def Thick (P : Par) (e : ℝ) : Prop := P.b ≤ e ∧ e ≤ P.b + P.η + 1
def Top (P : Par) (e : ℝ) : Prop :=
  ∃ bt : ℝ, P.b' ≤ bt ∧ bt ≤ P.b' * (1 + 1 / P.x ^ 2) ∧ bt + P.b' / P.x ≤ e ∧
    e ≤ bt + P.b' / P.x + P.η
def Thin (P : Par) (e : ℝ) : Prop := P.w'' ≤ e ∧ e ≤ P.w'' + P.η
def Shape (P : Par) (U : Finset ℤ) (bot : ℤ) (c e : ℝ) (σ : ℤ) : Prop :=
  (σ = 1 ∨ σ = -1) ∧ (σ : ℝ) * ((bot : ℝ) + ((P.t : ℝ) - 1) / 2 - c) = -e ∧
    ∀ u ∈ U, u ∉ Finset.Icc bot (bot + (P.t : ℤ) - 1) →
      (0 ≤ (σ : ℝ) * ((u : ℝ) - c) ∧ (σ : ℝ) * ((u : ℝ) - c) ≤ P.S) ∨
      (2 * P.b / P.lstar + (P.t : ℝ) / 2 + 3 ≤ |(σ : ℝ) * ((u : ℝ) - c) + e| ∧
        |(σ : ℝ) * ((u : ℝ) - c) + e| ≤ P.η)
end Par
def NoResidueInWindow : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ l : ℕ, l.Prime → P.lJ < (l : ℝ) →
    ∀ (U : Finset ℤ) (bot : ℤ) (c e : ℝ) (σ : ℤ), P.Shape U bot c e σ →
      ((P.Thick e ∧ ¬ P.Excl l) ∨ P.Top e ∨ P.Thin e) →
      mwCount l bot P.t (P.kap l) U = 0
def ExceptionalRange : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ z : ℤ,
    P.b - ((P.t : ℝ) - 1) / 2 - (P.kmax : ℝ) ≤ (z : ℝ) →
    (z : ℝ) ≤ P.b + P.S + P.η + 1 + ((P.t : ℝ) - 1) / 2 + (P.kmax : ℝ) →
    0 < z ∧ (z : ℝ) < P.lJ ^ 2
def ExceptionalCount : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ Q : Finset ℕ,
    (∀ l ∈ Q, l.Prime ∧ P.lJ < (l : ℝ) ∧ P.Excl l) →
    (Q.card : ℝ) ≤ P.S + P.η + (P.t : ℝ) + 2 * (P.kmax : ℝ) + 1
structure SizeData₂ (ι : Type) where
  T2 : Finset ι
  Sp : Finset ℕ
  J : ℕ → ℕ
  ex : ι → ℕ → ℕ
  ecl : ι → ℕ → ℕ
  mw : ι → ℕ → ℕ
  mwF : ι → ℕ → ℕ
  q : ι → ℕ
  j : ι → ℕ
  xlo : ι → ℤ
  xhi : ι → ℤ
  maxB : ι → ℤ
  hw : ι → ℝ
namespace SizeData₂
variable {ι : Type}
def depth (D : SizeData₂ ι) (P : Par) (τ : ι) (l : ℕ) : ℝ :=
  (D.q τ : ℝ) * P.h
    + ((l : ℝ) * (D.mwF τ l : ℝ) + (D.mw τ l : ℝ)) * ((P.t : ℝ) + 2 * (P.kap l : ℝ))
def cW (D : SizeData₂ ι) (P : Par) (τ : ι) (l : ℕ) : ℝ :=
  ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * ((P.h + (P.Nr : ℝ)) / ((l : ℝ) - 1) + 6)
    + (D.ecl τ l : ℝ)
    + (P.k : ℝ) * (P.S / (l : ℝ) + IlInd l (D.xlo τ) (D.xhi τ) (D.maxB τ))
    + (if ((d0 l (D.xlo τ - D.maxB τ) : ℕ) : ℤ) < D.xlo τ - D.maxB τ then
        min (min (P.k : ℝ) (P.t : ℝ)) (D.depth P τ l / (d0 l (D.xlo τ - D.maxB τ) : ℝ)) else 0)
    + (D.depth P τ l / (l : ℝ)) * (1 + max 0 (Real.log (P.h / (l : ℝ))))
def BoundA [Fintype ι] (D : SizeData₂ ι) (P : Par) : Prop :=
  ∀ l : ℕ, l.Prime → ((l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ D.Sp) → D.J l ≤ ∑ τ, D.ex τ l
def BoundW [Fintype ι] (D : SizeData₂ ι) (P : Par) : Prop :=
  ∀ l : ℕ, l.Prime → P.lJ < (l : ℝ) → ¬ P.Excl l → l ∉ D.Sp →
    P.h + (P.Nr : ℝ) < (l : ℝ) ^ 2 → P.Nr + 1 < l → P.t + 2 * P.kap l < l →
    (D.J l : ℝ) ≤ ∑ τ, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (D.cW P τ l) else (D.ex τ l : ℝ))
def ThinA (D : SizeData₂ ι) (P : Par) : Prop :=
  ∀ τ, τ ∉ D.T2 → ∀ l : ℕ, l.Prime →
    (D.hw τ < (l : ℝ) → D.ex τ l = 0) ∧
    ((l : ℝ) ≤ D.hw τ → (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ (P.Nr.choose 2 : ℝ) * Real.log (D.hw τ))
def ThickA (D : SizeData₂ ι) (P : Par) : Prop :=
  ∀ τ ∈ D.T2, ∀ l : ℕ, l.Prime →
    (P.h < (l : ℝ) → D.ex τ l = 0) ∧
    (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ (P.Nr.choose 2 : ℝ) * Real.log P.h ∧
    (2 * P.η + (P.t : ℝ) ≤ (l : ℝ) → (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤
      (P.k : ℝ) * ((P.m : ℝ) + (P.t : ℝ)) * Real.log (3 * P.h)
        + (P.k : ℝ) ^ 2 * Real.log (P.S + (P.k : ℝ)))
def CloudA (D : SizeData₂ ι) (P : Par) : Prop :=
  ∀ τ ∈ D.T2, ∀ l : ℕ, l.Prime → P.S + (P.k : ℝ) < (l : ℝ) → D.ecl τ l = 0
def ShapeT (D : SizeData₂ ι) (P : Par) : Prop :=
  ∀ τ ∈ D.T2, 0 ≤ D.maxB τ ∧ D.maxB τ < D.xlo τ ∧ D.xlo τ ≤ D.xhi τ ∧ ((D.xhi τ : ℤ) : ℝ) ≤ P.h ∧
    ((D.xhi τ - D.xlo τ : ℤ) : ℝ) ≤ P.S ∧ D.q τ + D.j τ ≤ P.m
def Widths (D : SizeData₂ ι) (P : Par) : Prop :=
  ∀ τ, τ ∉ D.T2 →
    D.hw τ ≤ P.S + P.b' * (1 + 1 / P.x + 1 / P.x ^ 2) + P.η + ((P.t : ℝ) - 1) / 2 ∨
    D.hw τ ≤ P.S + P.w'' + P.η + ((P.t : ℝ) - 1) / 2
def NoWindow (D : SizeData₂ ι) (P : Par) : Prop :=
  ∀ l : ℕ, l.Prime → P.lJ < (l : ℝ) → ¬ P.Excl l → ∀ τ, D.mw τ l = 0 ∧ D.mwF τ l = 0
structure Inputs [Fintype ι] (D : SizeData₂ ι) (P : Par) : Prop where
  card_ι : Fintype.card ι = P.f
  card_Sp : D.Sp.card ≤ 5
  boundA : D.BoundA P
  boundW : D.BoundW P
  thinA : D.ThinA P
  thickA : D.ThickA P
  cloudA : D.CloudA P
  shapeT : D.ShapeT P
  widths : D.Widths P
end SizeData₂
structure Places {ι : Type} (D : SizeData₂ ι) (P : Par) where
  U : ι → Finset ℤ
  bot : ι → ℤ
  c : ι → ℝ
  e : ι → ℝ
  σ : ι → ℤ
  UF : ι → ℕ → Finset ℤ
  botF : ι → ℕ → ℤ
  cF : ι → ℕ → ℝ
  eF : ι → ℕ → ℝ
  σF : ι → ℕ → ℤ
  shape : ∀ τ, P.Shape (U τ) (bot τ) (c τ) (e τ) (σ τ)
  kind : ∀ τ, P.Thick (e τ) ∨ P.Top (e τ) ∨ P.Thin (e τ)
  shapeF : ∀ τ l, P.Shape (UF τ l) (botF τ l) (cF τ l) (eF τ l) (σF τ l)
  kindF : ∀ τ l, P.Thick (eF τ l) ∨ P.Top (eF τ l) ∨ P.Thin (eF τ l)
  mw_eq : ∀ τ l, D.mw τ l = mwCount l (bot τ) P.t (P.kap l) (U τ)
  mwF_eq : ∀ τ l, D.mwF τ l = mwCount l (botF τ l) P.t (P.kap l) (UF τ l)
def NoWindowOf : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) (D : SizeData₂ ι), Places D P → D.NoWindow P
def SumA : Prop :=
  PrimeCountingBound → ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) (D : SizeData₂ ι), D.ThinA P → D.Widths P →
    ∀ τ, τ ∉ D.T2 → ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ 1.3 * (P.Nr : ℝ) ^ 2 * P.b'
def CostB : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] (D : SizeData₂ ι), Fintype.card ι = P.f →
    D.ThinA P → D.ThickA P → D.Widths P → ∀ l : ℕ, l.Prime →
      (∑ τ, (D.ex τ l : ℝ)) * Real.log (l : ℝ) ≤ (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.L
def TermC : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) (D : SizeData₂ ι), D.ThickA P →
    ∀ τ ∈ D.T2, ∀ l : ℕ, l.Prime → (l : ℝ) ≤ P.lJ →
      (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ 2 * (P.m : ℝ) * P.b * P.L / (l : ℝ)
def SumC : Prop :=
  MertensReciprocalBound → ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) (D : SizeData₂ ι), D.ThickA P →
    ∀ τ ∈ D.T2, ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime ∧ (l : ℝ) ≤ P.lJ) →
      ∑ l ∈ Q, (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ 2 * (P.m : ℝ) * P.b * P.L * (Real.log P.L + 1) ∧
      2 * (P.m : ℝ) * P.b * P.L * (Real.log P.L + 1) ≤ 2 * (P.m : ℝ) * P.b * P.L ^ 2
def SumD : Prop :=
  ChebyshevThetaUpperBound → MertensLogBound → RS2' → ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) (D : SizeData₂ ι), D.ThickA P →
    D.CloudA P → D.ShapeT P → D.NoWindow P →
    ∀ τ ∈ D.T2, ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime ∧ P.lJ < (l : ℝ) ∧ ¬ P.Excl l) →
      ∑ l ∈ Q, min (D.ex τ l : ℝ) (D.cW P τ l) * Real.log (l : ℝ) ≤
        (P.m : ℝ) * P.b * (4 * (P.L + 2) ^ 2 + 6 * (P.L + 2) + 37)
          + 2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2) ∧
      (P.m : ℝ) * P.b * (4 * (P.L + 2) ^ 2 + 6 * (P.L + 2) + 37)
          + 2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2) ≤
        14 * (P.m : ℝ) * P.b * P.L ^ 2 + 2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2)
def totalBound (P : Par) (T : ℕ) (X : ℝ) : ℝ :=
  (T : ℝ) * (X + 2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2))
    + 1.3 * (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.b'
    + (P.S + P.η + (P.t : ℝ) + 2 * (P.kmax : ℝ) + 6) * (P.f : ℝ) * (P.Nr : ℝ) ^ 2 * P.L
def TotalPrimeSumBoundConstSixteen : Prop :=
  ChebyshevThetaUpperBound → MertensLogBound → RS2' → PrimeCountingBound → MertensReciprocalBound → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] (D : SizeData₂ ι), D.Inputs P → D.NoWindow P →
    ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (D.J l : ℝ) * Real.log (l : ℝ) ≤ totalBound P D.T2.card (16 * (P.m : ℝ) * P.b * P.L ^ 2)
def TotalWeightBound : Prop :=
  ChebyshevThetaUpperBound → MertensLogBound → RS2' → PrimeCountingBound → MertensReciprocalBound → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] (D : SizeData₂ ι), D.Inputs P → D.NoWindow P →
    ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (D.J l : ℝ) * Real.log (l : ℝ) ≤ totalBound P D.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2)
def Corollary8 : Prop :=
  ChebyshevThetaUpperBound → MertensLogBound → RS2' → PrimeCountingBound → MertensReciprocalBound → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] (D : SizeData₂ ι), D.Inputs P → Places D P →
    ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (D.J l : ℝ) * Real.log (l : ℝ) ≤ totalBound P D.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2)
def ShortPrimeSum : Prop :=
  MertensLogBound → MertensLogLowerBound → ∀ P : Par, P.Hyp → P.Large → ∀ Q : Finset ℕ,
    (∀ l ∈ Q, l.Prime ∧ P.lJ < (l : ℝ) ∧ (l : ℝ) ≤ P.h + (P.Nr : ℝ)) →
    ∑ l ∈ Q, Real.log (l : ℝ) / (l : ℝ) ≤ Real.log ((P.h + (P.Nr : ℝ)) / P.lJ) + 2 ∧
      Real.log ((P.h + (P.Nr : ℝ)) / P.lJ) ≤ Real.log (12 * (P.k : ℝ) * (P.t : ℝ))
def bracketLogBound (L Λ lk : ℝ) : ℝ :=
  2 * L * (Real.log L + 1) + 12 * (Λ + 2) + 37 + 2 * (1 + Λ) * (Λ + 2) + 2 * (1 + lk) * (L + 0.7)
def LargePrimeSumLog : Prop :=
  ChebyshevThetaUpperBound → MertensLogBound → MertensLogLowerBound → ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) (D : SizeData₂ ι), D.ThickA P →
    D.CloudA P → D.ShapeT P → D.NoWindow P →
    ∀ τ ∈ D.T2, ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime ∧ P.lJ < (l : ℝ) ∧ ¬ P.Excl l) →
      ∑ l ∈ Q, min (D.ex τ l : ℝ) (D.cW P τ l) * Real.log (l : ℝ) ≤
        (P.m : ℝ) * P.b * (12 * (Real.log (12 * (P.k : ℝ) * (P.t : ℝ)) + 2) + 37
            + 2 * (1 + Real.log (12 * (P.k : ℝ) * (P.t : ℝ)))
                * (Real.log (12 * (P.k : ℝ) * (P.t : ℝ)) + 2)
            + 2 * (1 + Real.log (P.k : ℝ)) * (P.L + 0.7))
          + 2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2)
def TotalLog : Prop :=
  ChebyshevThetaUpperBound → MertensLogBound → MertensLogLowerBound → PrimeCountingBound → MertensReciprocalBound → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] (D : SizeData₂ ι), D.Inputs P → D.NoWindow P →
    ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (D.J l : ℝ) * Real.log (l : ℝ) ≤
        totalBound P D.T2.card ((P.m : ℝ) * P.b *
          bracketLogBound P.L (Real.log (12 * (P.k : ℝ) * (P.t : ℝ))) (Real.log (P.k : ℝ)))
def BracketSize : Prop :=
  ∀ A L lam Λ lk : ℝ, 0 ≤ A → 4 ≤ L → 1 ≤ lam → lam ≤ L → Real.log L ≤ lam → 0 ≤ Λ → Λ ≤ A * lam →
    0 ≤ lk → lk ≤ A * lam → bracketLogBound L Λ lk ≤ (2 * A ^ 2 + 22 * A + 46) * (L * lam)
def ConvolutionKernelIntegrable : Prop := ∀ y : ℝ, 0 ≤ y → ∑ p ∈ pr y, Real.log (p : ℝ) ≤ Real.log 4 * y
def MertensLogElementary : Prop :=
  ∀ y : ℝ, 1 ≤ y → ∑ p ∈ pr y, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log y + Real.log 4
def MertensReciprocalElementary : Prop := ∀ y : ℝ, 1 ≤ y → ∑ p ∈ pr y, 1 / (p : ℝ) ≤ Real.log y
def SumCE : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) (D : SizeData₂ ι), D.ThickA P →
    ∀ τ ∈ D.T2, ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime ∧ (l : ℝ) ≤ P.lJ) →
      ∑ l ∈ Q, (D.ex τ l : ℝ) * Real.log (l : ℝ) ≤ 2 * (P.m : ℝ) * P.b * P.L ^ 2
def SumDE : Prop :=
  ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) (D : SizeData₂ ι), D.ThickA P →
    D.CloudA P → D.ShapeT P → D.NoWindow P →
    ∀ τ ∈ D.T2, ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime ∧ P.lJ < (l : ℝ) ∧ ¬ P.Excl l) →
      ∑ l ∈ Q, min (D.ex τ l : ℝ) (D.cW P τ l) * Real.log (l : ℝ) ≤
        (P.m : ℝ) * P.b * (12 * (P.L + 2.5) + 51 + 2 * (P.L + 2) ^ 2 + 2 * (P.L + 2) * (P.L + 2.5))
          + 2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2) ∧
      (P.m : ℝ) * P.b * (12 * (P.L + 2.5) + 51 + 2 * (P.L + 2) ^ 2 + 2 * (P.L + 2) * (P.L + 2.5))
          + 2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2) ≤
        18 * (P.m : ℝ) * P.b * P.L ^ 2 + 2 * (P.k : ℝ) * (P.S + 1) * (P.L + 2)
def TotalElementary : Prop :=
  PrimeCountingBound → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] (D : SizeData₂ ι), D.Inputs P → D.NoWindow P →
    ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (D.J l : ℝ) * Real.log (l : ℝ) ≤ totalBound P D.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2)
def Corollary8E : Prop :=
  PrimeCountingBound → ∀ P : Par, P.Hyp → P.Large →
    ∀ (ι : Type) [Fintype ι] (D : SizeData₂ ι), D.Inputs P → Places D P →
    ∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) →
      ∑ l ∈ Q, (D.J l : ℝ) * Real.log (l : ℝ) ≤ totalBound P D.T2.card (30 * (P.m : ℝ) * P.b * P.L ^ 2)
def WeightSpreadBound : Prop :=
  ∀ P : Par, 1 ≤ P.t → P.S + (P.b + P.η + 1) + ((P.t : ℝ) - 1) / 2 ≤ P.h ∧
    P.b + P.S + P.η < P.S + (P.b + P.η + 1) + ((P.t : ℝ) - 1) / 2
end Formalism.CohomologicalDescent.LogSmallConstantBounds


