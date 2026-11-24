-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTieFB
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T10:36:53.321718+00:00
-- url     : https://prove2.me/theorems/428b9610-9561-418f-a84a-6a240c44c46f
-- title:
--   Row Tie FB
-- statement:
--   Definitions and structural lemmas for Row Tie FB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieFB.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
def un1 {dd : ℕ} (f : PS C 1 dd) : MvPowerSeries (Fin dd) C :=
  fun μ => MvPowerSeries.coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) f
def linAct {dd : ℕ} (φ : Pt C 1 dd) (v : Fin dd → C) : Fin dd → C :=
  fun i => ∑ j, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ i) * v j
structure FBChart (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) where
  algClosed : IsAlgClosed C

  cpl : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)
  l_odd : V.l ≠ 2
  B : FB C dd O
  h : PS C 2 dd
  gauge : B.IsCanonGauge C h
  intF : ∀ i, IntS V (B.G.F i)
  intAct : ∀ a i, IntS V (B.A.act a i)
  intPh1 : IntS V B.ph1
  intPh2 : IntS V B.ph2
  intSy : IntS V B.sy
  intAd : ∀ a, IntS V (B.ad a)

  lg : Pt C 1 dd
  lg_lin : ∀ i (μ : Fin 1 × Fin dd →₀ ℕ), μ.degree ≤ 1 →
    MvPowerSeries.coeff μ (lg i) = MvPowerSeries.coeff μ (MvPowerSeries.X ((0 : Fin 1), i) : PS C 1 dd)
  lg_add : ∀ i, ev (n := 2) ![addOf B.G.F (pt C dd 0) (pt C dd 1)] (lg i) =
    ev (n := 2) ![pt C dd 0] (lg i) + ev (n := 2) ![pt C dd 1] (lg i)

  ex : Pt C 1 dd
  ex_const : ∀ i, MvPowerSeries.constantCoeff (ex i) = 0
  lg_ex : comp1 lg ex = pt C dd 0

  ex_lg : comp1 ex lg = pt C dd 0
  w0 : O

  halfIntegralGenerator_add_conj_eq_one : w0 + star w0 = 1
  k : ℕ
  k_unit : V.v (k : C) = 0
structure PairData {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] where

  em : Fin 2 → ZMod d → (O →+* C)
  em_int : ∀ g a x, V.Ge 0 (em g a x)
  em_conj : ∀ a x, em 1 a x = em 0 a (star x)

  em_frob : ∀ g a x, V.MM (em g (a + 1) x - em g a x ^ V.l)

  em_sep : ∀ p p' : Fin 2 × ZMod d, p ≠ p' → ∃ x, V.v (em p.1 p.2 x - em p'.1 p'.2 x) = 0

  em_unr : ∀ g, ∃ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) ∧ (∀ a, V.MM (em g a ε - 1)) ∧
    ∀ x : O, (∀ a, V.MM (em g a x)) → ∃ y, ε * x = (V.l : O) * y
  u : ∀ g, I g → Fin dd → C
  ty : ∀ g, I g → ZMod d
  u_int : ∀ g c i, V.Ge 0 (u g c i)
  u_eig : ∀ g c x, linAct (Y.B.A.act x) (u g c) = em g (ty g c) x • u g c

  u_sat : ∀ g, ∃ w : Fin dd → I g → C, (∀ x c, V.Ge 0 (w x c)) ∧
    ∀ c c' : I g, ∑ x, u g c x * w x c' = if c = c' then 1 else 0

  u_full : ∀ g a (v : Fin dd → C), (∀ x, linAct (Y.B.A.act x) v = em g a x • v) →
    ∃ b : I g → C, (∀ c, ty g c ≠ a → b c = 0) ∧ v = ∑ c, b c • u g c
  n : ℕ
  j : ℕ
  j' : ℕ
  big : Fin 2 → ZMod d → Prop
namespace FBChart
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)]
def raw (Y : FBChart C V O dd) (p : PairData Y d I) : RawChart C d I (Fin dd) where
  lg := fun i => un1 (Y.lg i)
  ex := fun i => un1 (Y.ex i)
  h := Y.h
  k := Y.k
  u := p.u
  ty := p.ty
  n := p.n
  j := p.j
  j' := p.j'
  big := p.big
end FBChart
section Closed
def AllFB (Φ : ∀ (C : Type) [Field C] (_V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (dd : ℕ),
    RawChart C d I (Fin dd) → Prop) : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I),
    Φ C V d I dd (Y.raw p)
def CartFBSt : Prop := AllFB fun _ _ V _ _ _ _ X => ∀ g, X.CartHyp V g
def AxesFBSt : Prop := AllFB fun _ _ _ _ _ _ _ X => X.AxesSt
def IntegralGermIndependentAllCharts : Prop := AllFB fun _ _ V _ _ _ _ X => ∀ H : ∀ g, X.CartHyp V g, RawChart.IntegralGermIndependentOfSystem H
def CEqFBSt : Prop := AllFB fun _ _ V _ _ _ _ X => X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, RawChart.CEqSt H
def IndependenceBoundAllCharts : Prop :=
  AllFB fun _ _ V _ _ _ _ X => X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition H → RawChart.IndependenceBoundCondition H
end Closed
section Steps
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
def FBChart.sgP (Y : FBChart C V O dd) (v : Fin dd → C) : PS C 1 dd :=
  -∑ i, MvPowerSeries.C (v i) * ev (n := 1) ![pt C dd 0, 0] (MvPowerSeries.pderiv C ((1 : Fin 2), i) Y.h)
def GermISt (Y : FBChart C V O dd) : Prop :=
  ∀ v : Fin dd → C, (∀ i, V.Ge 0 (v i)) →
    IntS V (ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] (Y.sgP v) -
      ev (n := 2) ![pt C dd 0] (Y.sgP v) - ev (n := 2) ![pt C dd 1] (Y.sgP v))
def GermIISt (Y : FBChart C V O dd) : Prop :=
  ∀ v : Fin dd → C, (∀ i, V.Ge 0 (v i)) →
    IntS V ((∑ j : Fin dd, (∑ i : Fin dd, MvPowerSeries.C (v i) *
        ev (n := 2) ![pt C dd 1, 0] (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.G.F j))) *
          MvPowerSeries.pderiv C ((1 : Fin 2), j) Y.h) + ev (n := 2) ![pt C dd 0] (Y.sgP v))
def ActCv (Y : FBChart C V O dd) (a : ℕ → O) : Prop :=
  ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (MvPowerSeries.coeff μ (Y.B.A.act (a (n + 1)) i) -
    MvPowerSeries.coeff μ (Y.B.A.act (a n) i))
def EndomorphismLimitIntegral (Y : FBChart C V O dd) : Prop :=
  ∀ a : ℕ → O, ActCv Y a → ActCv Y (fun n => star (a n)) →
    ∃ e eb : Pt C 1 dd, (∀ i, IntS V (e i)) ∧ (∀ i, IntS V (eb i)) ∧
      (∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
        V.Ge N (MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (Y.B.A.act (a n) i))) ∧
      (∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
        V.Ge N (MvPowerSeries.coeff μ (eb i) - MvPowerSeries.coeff μ (Y.B.A.act (star (a n)) i))) ∧
      comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
        addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)) ∧
      IntS V (FB.expS C (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
        ev (n := 2) ![pt C dd 0, comp1 eb (pt C dd 1)] Y.h))
end Steps
section Record
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d] {I : Fin 2 → Type}
  [∀ g, Fintype (I g)]
end Record
end Formalism.L2.FormalSeriesBounds


