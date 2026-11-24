-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
-- name    : Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T11:34:53.205109+00:00
-- url     : https://prove2.me/theorems/274923a8-3e76-4c83-bf0a-85a3da1119ed
-- title:
--   Has Teich
-- statement:
--   Definitions and structural lemmas for Has Teich, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TeichmullerDepth/HasTeich.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
namespace GlobalTheory.RowLaw
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
def gp (C : Type) [Field C] (κ : Type) {n : ℕ} (j : Fin n) : κ → MvPowerSeries (Fin n × κ) C :=
  fun x => MvPowerSeries.X (j, x)
def addP (X : RawChart C d I κ) {τ : Type} (a b : κ → MvPowerSeries τ C) : κ → MvPowerSeries τ C :=
  fun i => MvPowerSeries.subst (fun x => MvPowerSeries.subst a (X.lg x) + MvPowerSeries.subst b (X.lg x)) (X.ex i)
def endP (X : RawChart C d I κ) (M : Matrix κ κ C) {τ : Type} (a : κ → MvPowerSeries τ C) : κ → MvPowerSeries τ C :=
  fun i => MvPowerSeries.subst (fun x => ∑ y, M x y • MvPowerSeries.subst a (X.lg y)) (X.ex i)
def hAt (X : RawChart C d I κ) {τ : Type} (a b : κ → MvPowerSeries τ C) : MvPowerSeries τ C :=
  MvPowerSeries.subst (fun p : Fin 2 × κ => if p.1 = 0 then a p.2 else b p.2) X.h
structure RLaw (X : RawChart C d I κ) (V : VF C) : Prop where
  charZero : CharZero C
  closed : IsAlgClosed C
  odd : V.l ≠ 2
  lin : ∀ i (μ : κ →₀ ℕ), μ.degree ≤ 1 →
    MvPowerSeries.coeff μ (X.lg i) = MvPowerSeries.coeff μ (MvPowerSeries.X i : MvPowerSeries κ C)
  exc : ∀ i, MvPowerSeries.constantCoeff (X.ex i) = 0
  lgex : ∀ i, MvPowerSeries.subst X.ex (X.lg i) = (MvPowerSeries.X i : MvPowerSeries κ C)
  exlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C)
  axes : ∀ (g : Fin 2) (e : Fin 2 × κ →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → MvPowerSeries.coeff e X.h = 0
  addInt : ∀ i, IntS V (addP X (gp C κ (0 : Fin 2)) (gp C κ 1) i)
  ph1 : IntS V (mvExp (hAt X (gp C κ (0 : Fin 3)) (gp C κ 2) + hAt X (gp C κ 1) (gp C κ 2) -
    hAt X (addP X (gp C κ 0) (gp C κ 1)) (gp C κ 2)))
  ph2 : IntS V (mvExp (hAt X (gp C κ (0 : Fin 3)) (gp C κ 1) + hAt X (gp C κ 0) (gp C κ 2) -
    hAt X (gp C κ 0) (addP X (gp C κ 1) (gp C κ 2))))
  sy : IntS V (mvExp (hAt X (gp C κ (1 : Fin 2)) (gp C κ 0) - X.h))
  kunit : V.v (X.k : C) = 0
  uint : ∀ g c i, V.Ge 0 (X.u g c i)
  sat : ∀ g, ∃ w : κ → I g → C, (∀ x c, V.Ge 0 (w x c)) ∧
    ∀ c c' : I g, (c = c' → ∑ x, X.u g c x * w x c' = 1) ∧ (c ≠ c' → ∑ x, X.u g c x * w x c' = 0)
def IsEnd (X : RawChart C d I κ) (V : VF C) (M M' : Matrix κ κ C) : Prop :=
  (∀ i, IntS V (endP X M (MvPowerSeries.X : κ → MvPowerSeries κ C) i)) ∧
  (∀ i, IntS V (endP X M' (MvPowerSeries.X : κ → MvPowerSeries κ C) i)) ∧
  IntS V (mvExp (hAt X (endP X M (gp C κ (0 : Fin 2))) (gp C κ 1) - hAt X (gp C κ 0) (endP X M' (gp C κ 1))))
def HasProj (X : RawChart C d I κ) (V : VF C) : Prop :=
  ∃ M : Fin 2 → Matrix κ κ C, IsEnd X V (M 0) (M 1) ∧ IsEnd X V (M 1) (M 0) ∧
    (∀ g c, (M g).mulVec (X.u g c) = X.u g c) ∧ (∀ g c, (M g).mulVec (X.u (1 - g) c) = 0) ∧
    ∀ g v, ∃ b : I g → C, (M g).mulVec v = ∑ c, b c • X.u g c
def HasTeich (X : RawChart C d I κ) (V : VF C) (g : Fin 2) : Prop :=
  ∃ (N : ℕ) (ζ : ZMod d → C) (M M' : Matrix κ κ C), V.v (N : C) = 0 ∧ (∀ a, ζ a ^ N = 1) ∧ Function.Injective ζ ∧
    (∀ a, ζ (a + 1) = ζ a ^ V.l) ∧ IsEnd X V M M' ∧
    (∀ c, M.mulVec (X.u g c) = ζ (X.ty g c) • X.u g c) ∧
    ∀ q, M'.mulVec (X.u (1 - g) q) = ζ (X.ty (1 - g) q) • X.u (1 - g) q
def Cv (X : RawChart C d I κ) (V : VF C) (g : Fin 2) : Set ((κ → PowerSeries C) × (JJ I g → PowerSeries C)) :=
  {a | ∃ (γ : κ → PowerSeries C) (lam : JJ I g → PowerSeries C), IsCv V γ ∧ IsCv V lam ∧
    (∀ i, alongCv γ (X.lg i) = a.1 i) ∧ ∀ q, a.2 q = lam q - alongCv γ (X.sg (X.u (1 - g) q))}
def typ (l : ℕ) (f : PowerSeries C) : PowerSeries C := tyS l fun s => PowerSeries.coeff (l ^ s) f
def ExpInt (X : RawChart C d I κ) (V : VF C) : Set (MvPowerSeries (WV I) C) :=
  {F | ∃ f : MvPowerSeries (Fin 2 × κ) C, IntS V f ∧
    F = MvPowerSeries.subst (fun p : Fin 2 × κ => X.expPt p.1 p.2) f}
end GlobalTheory.RowLaw


