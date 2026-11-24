-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T11:06:20.066901+00:00
-- url     : https://prove2.me/theorems/122c1d66-fcc5-4116-927b-5d3e5ede7969
-- title:
--   Row Tie Self
-- statement:
--   Definitions and structural lemmas for Row Tie Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieSelf.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieVal
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
structure SelfData {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) (d : ℕ) (I0 : Type) [Fintype I0] where

  em : ZMod d → (O →+* C)
  em_int : ∀ a x, V.Ge 0 (em a x)
  em_frob : ∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)
  em_sep : ∀ a a' : ZMod d, a ≠ a' → ∃ x, V.v (em a x - em a' x) = 0

  em_unr : ∃ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) ∧ (∀ a, V.MM (em a ε - 1)) ∧
    ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y

  hd : ZMod d
  hd_ne : hd ≠ 0
  hd_two : hd + hd = 0
  em_conj : ∀ a x, em a (star x) = em (a + hd) x

  e : I0 → Fin dd → C
  ty0 : I0 → ZMod d
  e_int : ∀ c i, V.Ge 0 (e c i)
  e_eig : ∀ c x, linAct (Y.B.A.act x) (e c) = em (ty0 c) x • e c
  e_sat : ∃ w : Fin dd → I0 → C, (∀ x c, V.Ge 0 (w x c)) ∧
    ∀ c c' : I0, ∑ x, e c x * w x c' = if c = c' then 1 else 0
  e_full : ∀ a (v : Fin dd → C), (∀ x, linAct (Y.B.A.act x) v = em a x • v) →
    ∃ b : I0 → C, (∀ c, ty0 c ≠ a → b c = 0) ∧ v = ∑ c, b c • e c

  gm : ZMod d → Matrix (Fin 2) (Fin 2) C
  gm_lim : ∀ N : ℕ, ∃ M : Matrix (Fin 2) (Fin 2) O, ∀ a r s, V.Ge N (gm a r s - em a (M r s))

  gm_hyp : ∀ a (s s' : Fin 2), ∑ r, gm (a + hd) r s * gm a r s' = if s = s' then 0 else 1
  n : ℕ
  j : ℕ
  j' : ℕ
  big : Fin 2 → ZMod d → Prop
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
def inCol (col : Fin 2) (f : MvPowerSeries (Fin dd) C) : MvPowerSeries (Fin 2 × Fin dd) C :=
  MvPowerSeries.subst
    (fun x : Fin dd => (MvPowerSeries.X (col, x) : MvPowerSeries (Fin 2 × Fin dd) C)) f
def hCol (col : Fin 2) (h : PS C 2 dd) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C :=
  MvPowerSeries.subst (fun p : Fin 2 × Fin dd =>
    (MvPowerSeries.X (p.1, (col, p.2)) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) h
def FBChart.rawSelf (Y : FBChart C V O dd) {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0) :
    RawChart C d (fun _ => I0) (Fin 2 × Fin dd) where
  lg := fun x => inCol x.1 (un1 (Y.lg x.2))
  ex := fun x => inCol x.1 (un1 (Y.ex x.2))
  h := ∑ col, hCol col Y.h
  k := Y.k
  u := fun g c x => p.gm (p.ty0 c) x.1 g * p.e c x.2
  ty := fun g c => if g = 0 then p.ty0 c else p.ty0 c + p.hd
  n := p.n
  j := p.j
  j' := p.j'
  big := p.big
def AllSelf (Φ : ∀ (C : Type) [Field C] (_V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (dd : ℕ),
    RawChart C d I (Fin 2 × Fin dd) → Prop) : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0),
    Φ C V d (fun _ => I0) dd (Y.rawSelf p)
def CartSelfSt : Prop := AllSelf fun _ _ V _ _ _ _ X => ∀ g, X.CartHyp V g
def AxesSelfSt : Prop := AllSelf fun _ _ _ _ _ _ _ X => X.AxesSt
def GermZeroSelfConjugate : Prop := AllSelf fun _ _ V _ _ _ _ X => ∀ H : ∀ g, X.CartHyp V g, RawChart.IntegralGermIndependentOfSystem H
def CEqSelfSt : Prop := AllSelf fun _ _ V _ _ _ _ X => X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, RawChart.CEqSt H
def IndependenceBoundSelfConjugate : Prop :=
  AllSelf fun _ _ V _ _ _ _ X => X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition H → RawChart.IndependenceBoundCondition H
section Val
variable {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]
def IsImgS (X : ∀ o, RawChart C d (fun _ => I0 o) (Fin 2 × Fin dd)) {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) {ι : Type}
    (cp : ι → Fin n) (uv : ι → Fin dd → C) (P : MvPolynomial ι C)
    (Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => I0 o) C) : Prop :=
  ∃ co : ι → Fin N × (WVO fun o (_ : Fin 2) => I0 o) → C,
    (∀ ℓ ∈ P.vars, ∃ ρ col, pl (ρ, col) = cp ℓ ∧ (∀ ρ' w, ρ' ≠ ρ → co ℓ (ρ', w) = 0) ∧
      (fun x : Fin 2 × Fin dd => if x.1 = col then uv ℓ x.2 else 0) =
        ∑ w : (WVO fun o (_ : Fin 2) => I0 o), co ℓ (ρ, w) • (X w.1).u w.2.1 w.2.2) ∧
    Q = MvPolynomial.aeval (fun ℓ => ∑ x, MvPolynomial.C (co ℓ x) * MvPolynomial.X x) P
variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
  (Ls : LetSys C dd) (n : ℕ)
def SelfSep : Prop :=
  ∀ x x' : Orb × ZMod d, x ≠ x' → ∃ a : O, V.v ((p x.1).em x.2 a - (p x'.1).em x'.2 a) = 0
def ValEqSelfSt : Prop :=
  SelfSep Y p → ∀ (N : ℕ) (pl : Fin N × Fin 2 ↪ Fin n), ∀ P ∈ Ls.FF n,
    ∀ Po : ∀ o, MvPolynomial (Fin N × WV fun _ => I0 o) C,
    IsImgS (fun o => Y.rawSelf (p o)) pl (Ls.cp n) (Ls.uv n) P (∏ o, toAll o (Po o)) →
    ∀ kind : Orb → Fin N → Option (Fin 2 × ZMod d × ZMod d),
    (∀ o, RowsOK ((Y.rawSelf (p o)).rowData (H o)).G ((Y.rawSelf (p o)).rowData (H o)).Alt (Po o) (kind o)) →
    ∀ (S : ∀ o g, Sys (((Y.rawSelf (p o)).rowData (H o)).G g)) (t : ∀ o (_ : Fin 2), I0 o → MvPowerSeries (I0 o) C),
    (∀ o g, (S o g).IsT (t o g)) →
    ∀ gr : ∀ o, Fin N → MvPowerSeries (WV fun _ => I0 o) C, (∀ o ρ, gr o ρ ∈ IntGerm V (t o)) →
      ∃ f : PS C n dd, IntS V f ∧
        Y.nab Ls n f P = ∏ o, ValOf ((Y.rawSelf (p o)).rowData (H o)).hL (Po o) (kind o) (gr o)
end Val
end Formalism.L2.FormalSeriesBounds


