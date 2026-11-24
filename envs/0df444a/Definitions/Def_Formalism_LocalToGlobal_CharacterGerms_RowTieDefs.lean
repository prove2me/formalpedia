-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDefs
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTieDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:28.948798+00:00
-- url     : https://prove2.me/theorems/cedb0500-bb44-4eb2-825d-65f0d9c4762a
-- title:
--   Row Tie Defs
-- statement:
--   Definitions and structural lemmas for Row Tie Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieDefs.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IntSubst
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_neg
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero

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
open Formalism.IncomingBounds
variable {C : Type} [Field C]
def tyS (l : ℕ) (a : ℕ → C) : PowerSeries C :=
  PowerSeries.mk fun n => ∑ s ∈ Finset.range (n + 1), if l ^ s = n then a s else 0
def IsCv (V : VF C) {σ : Type} (γ : σ → PowerSeries C) : Prop :=
  ∀ i, PowerSeries.constantCoeff (γ i) = 0 ∧ ∀ n, V.Ge 0 (PowerSeries.coeff n (γ i))
def alongCv {σ : Type} (γ : σ → PowerSeries C) (f : MvPowerSeries σ C) : PowerSeries C :=
  MvPowerSeries.subst γ f
abbrev JJ (I : Fin 2 → Type) : Fin 2 → Type := fun g => I (1 - g)
structure RawChart (C : Type) [Field C] (d : ℕ) (I : Fin 2 → Type) (κ : Type) where

  lg : κ → MvPowerSeries κ C
  ex : κ → MvPowerSeries κ C

  h : MvPowerSeries (Fin 2 × κ) C

  k : ℕ

  u : ∀ g, I g → κ → C
  ty : ∀ g, I g → ZMod d

  n : ℕ
  j : ℕ
  j' : ℕ
  big : Fin 2 → ZMod d → Prop
namespace RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
instance (g : Fin 2) : Fintype (JJ I g) := inferInstanceAs (Fintype (I (1 - g)))
def sg (v : κ → C) : MvPowerSeries κ C :=
  fun μ => -∑ i, v i * MvPowerSeries.coeff
    (μ.mapDomain (fun x : κ => ((0 : Fin 2), x)) + Finsupp.single ((1 : Fin 2), i) 1) X.h
def sg1 (w v : κ → C) : C := ∑ x, w x * MvPowerSeries.coeff (Finsupp.single x 1) (X.sg v)
def tyC (g : Fin 2) : I g ⊕ JJ I g → ZMod d := Sum.elim (X.ty g) (X.ty (1 - g))
def TySet (V : VF C) (g : Fin 2) : Set (ℕ → I g ⊕ JJ I g → C) :=
  {x | ∃ (γ : κ → PowerSeries C) (lam : JJ I g → PowerSeries C), IsCv V γ ∧ IsCv V lam ∧
    (∀ i : κ, alongCv γ (X.lg i) = ∑ c : I g, X.u g c i • tyS V.l (fun s => x s (Sum.inl c))) ∧
    ∀ q : JJ I g, tyS V.l (fun s => x s (Sum.inr q)) =
      lam q - alongCv γ (X.sg (X.u (1 - g) q)) +
        ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c)) else 0}
structure CartHyp (V : VF C) (g : Fin 2) : Prop where

  zero : (0 : ℕ → I g ⊕ JJ I g → C) ∈ X.TySet V g

  add : ∀ x y, x ∈ X.TySet V g → y ∈ X.TySet V g → x + y ∈ X.TySet V g
  neg : ∀ x, x ∈ X.TySet V g → -x ∈ X.TySet V g

  teich : ∀ c, V.Ge 0 c → ∀ x ∈ X.TySet V g, teich V.l c x ∈ X.TySet V g

  Vm : ∀ x ∈ X.TySet V g, Vpow 1 x ∈ X.TySet V g

  Fm : ∀ x ∈ X.TySet V g, Fs V.l x ∈ X.TySet V g

  sumV : ∀ y : ℕ → ℕ → I g ⊕ JJ I g → C, (∀ s, y s ∈ X.TySet V g) → sumV y ∈ X.TySet V g

  t2 : ∀ x ∈ X.TySet V g, ∀ s, (∀ i < s, x i = 0) → ∀ n, V.Ge 0 (x s n)

  t3 : ∀ ζ : JJ I g → C, (∀ q, V.Ge 0 (ζ q)) → const0 (Sum.elim 0 ζ) ∈ X.TySet V g

  t4 : ∀ (a : ZMod d) (w : I g → C), (∀ c, V.Ge 0 (w c)) → (∀ c, X.tyC g (Sum.inl c) ≠ a → w c = 0) →
    ∃ x ∈ X.TySet V g, x 0 = Sum.elim w 0 ∧ ∀ (i : ℕ) n, X.tyC g n ≠ a + i → x i n = 0
variable {X}
def cart {V : VF C} {g : Fin 2} (H : X.CartHyp V g) : Cart V d (I g) (JJ I g) where
  ty := X.tyC g
  Ty :=
    { carrier := X.TySet V g
      zero_mem' := H.zero
      add_mem' := fun {x y} hx hy => H.add x y hx hy
      neg_mem' := fun {x} hx => H.neg x hx }
  teich_mem := H.teich
  V_mem := H.Vm
  F_mem := H.Fm
  sumV_mem := H.sumV
  t2 := H.t2
  t3 := H.t3
  t4 := H.t4
variable (X)
def pairK (g : Fin 2) (q : JJ I g) (c : I (1 - g)) : C := if q = c then -(X.k : C) else 0
def expPt (g : Fin 2) (x : κ) : MvPowerSeries (WV I) C :=
  MvPowerSeries.subst (fun i : κ => ∑ c : I g, X.u g c i • (MvPowerSeries.X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C))
    (X.ex x)
def hRow : MvPowerSeries (WV I) C :=
  (X.k : C) • MvPowerSeries.subst (fun p : Fin 2 × κ => X.expPt p.1 p.2) X.h
def OnLf (g : Fin 2) (a a' : ZMod d) (w : WV I) : Prop :=
  (w.1 = g ∧ X.ty w.1 w.2 = a) ∨ (w.1 = 1 - g ∧ X.ty w.1 w.2 = a')
def hLf (g : Fin 2) (a a' : ZMod d) : MvPowerSeries (WV I) C :=
  fun μ => if ∀ w ∈ μ.support, X.OnLf g a a' w then MvPowerSeries.coeff μ X.hRow else 0
structure RankHyp : Prop where
  big_compl : ∀ g a, X.big (1 - g) a ↔ ¬ X.big g a
  rk_big : ∀ g a, X.big g a → (Finset.univ.filter fun c : I g => X.ty g c = a).card = X.n + X.j
  rk_small : ∀ g a, ¬ X.big g a → (Finset.univ.filter fun c : I g => X.ty g c = a).card = X.j'
def AltC : Prop := Even d ∧ ∀ a : ZMod d, (X.big 0 a ↔ Even a.val)
def AxesSt : Prop :=
  ∀ (μ : WV I →₀ ℕ), ((∀ w ∈ μ.support, w.1 = 0) ∨ (∀ w ∈ μ.support, w.1 = 1)) →
    MvPowerSeries.coeff μ X.hRow = 0
section Geo
variable {X} {V : VF C} (H : ∀ g, X.CartHyp V g)
def IntegralGermIndependentOfSystem : Prop :=
  ∀ (S S₂ : ∀ g, Sys (cart (H g))) (t t₂ : ∀ g, I g → MvPowerSeries (I g) C),
    (∀ g, (S g).IsT (t g)) → (∀ g, (S₂ g).IsT (t₂ g)) → IntGerm V t = IntGerm V t₂
def CEqSt : Prop :=
  X.AltC → ∀ g a a', Odd (a' - a).val →
    ∀ (S : ∀ g, Sys (cart (H g))) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) →
    ∀ k : I (1 - g), X.ty (1 - g) k = a' →
      ∃ K ∈ IntGerm V t,
        dVar (⟨1 - g, k⟩ : WV I) (X.hLf g a a') -
            toLeaf (fun g => cart (H g)) g a a' (∑ q : JJ I g, X.pairK g q k • upG g ((S g).ze (t g) q)) =
          toLeaf (fun g => cart (H g)) g a a' K
def RankMaximalCondition : Prop :=
  X.AltC → ∀ g a, X.big g a →
    ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (cart (H g)).Good a w x →
    (∀ q, V.MM ((cart (H g)).c0' x q)) → ∀ c, V.MM (w c)
def IndependenceBoundCondition : Prop :=
  X.AltC → ∀ g a, X.big g a →
    ∀ (N : ℕ) (w : Fin N → I g → C) (x : Fin N → ℕ → I g ⊕ JJ I g → C),
    (∀ ν, (cart (H g)).Good a (w ν) (x ν)) → (∀ ν c, V.MM ((cart (H g)).V2 (x ν) c)) →
    IndepMod V w → N ≤ X.j'
def CHSt : Prop :=
  ∀ g a, X.big g a → ∀ w : Fin X.n → I g → C, IsSat V w →
    (∀ c x, X.ty g x ≠ a → w c x = 0) →
    ∃ y : Fin X.n → I g → C, (∀ ρ x, V.Ge 0 (y ρ x)) ∧
      (∀ (S : ∀ g, Sys (cart (H g))) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) →
        ∀ ρ, upG g (mvExp (∑ x : I g, y ρ x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
          IntGerm V t) ∧
      (X.AltC →
        V.v (Matrix.of fun ρ c : Fin X.n => ∑ x, y ρ x * w c x).det ≤
          (((X.n : ℝ) * gam V.l + ((X.j : ℝ) + X.j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ)) ∧
      ((∀ a, X.big g a) →
        V.v (Matrix.of fun ρ c : Fin X.n => ∑ x, y ρ x * w c x).det ≤
          ((((X.j : ℝ) + X.j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ))
end Geo
structure Hyps (V : VF C) : Prop where
  charZero : CharZero C
  algClosed : IsAlgClosed C
  l_odd : V.l ≠ 2
  k_unit : V.v (X.k : C) = 0
  cartH : ∀ g, X.CartHyp V g
  rank : X.RankHyp
  axes : X.AxesSt
  G0 : IntegralGermIndependentOfSystem cartH
  CEq : CEqSt cartH
  R1 : IndependenceBoundCondition cartH
  R2 : RankMaximalCondition cartH
  CH : CHSt cartH
end RawChart
end Formalism.L2.FormalSeriesBounds


