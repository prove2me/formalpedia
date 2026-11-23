-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
-- name    : Formalism_LocalToGlobal_CharacterGerms_Interface
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:47.08346+00:00
-- url     : https://prove2.me/theorems/ed020205-3879-4231-b922-7f6f9dc458ad
-- title:
--   Interface
-- statement:
--   Definitions and structural lemmas for Interface, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/Interface.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
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
def VF.MM (V : VF C) (x : C) : Prop := 0 < V.v x
def IsSat (V : VF C) {N : ℕ} {σ : Type} [Fintype σ] (u : Fin N → σ → C) : Prop :=
  (∀ c x, V.Ge 0 (u c x)) ∧
    ∃ w : σ → Fin N → C, (∀ x c, V.Ge 0 (w x c)) ∧
      ∀ c c' : Fin N, ∑ x, u c x * w x c' = if c = c' then 1 else 0
def IndepMod (V : VF C) {N : ℕ} {σ : Type} (u : Fin N → σ → C) : Prop :=
  ∀ c : Fin N → C, (∀ ν, V.Ge 0 (c ν)) → (∀ x, V.MM (∑ ν, c ν * u ν x)) → ∀ ν, V.MM (c ν)
section OneGroup
variable {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
structure Sys (X : Cart V d I J) where
  tan : I → I → C
  cur : I → ℕ → I ⊕ J → C
  curve : ∀ c, X.IsCurve (X.ty (Sum.inl c)) (tan c) (cur c)
  unimod : V.v (Matrix.of tan).det = 0
namespace Sys
variable {X : Cart V d I J} (S : Sys X)
def al (c : I) (i : ℕ) (x : I) : C := S.cur c i (Sum.inl x)
def be (c : I) (i : ℕ) (κ : J) : C := S.cur c i (Sum.inr κ)
def IsT (t : I → MvPowerSeries I C) : Prop :=
  (∀ c, MvPowerSeries.constantCoeff (t c) = 0) ∧
    ∀ (x : I) (μ : I →₀ ℕ),
      (∑ s ∈ Finset.range (μ.degree + 1), ∑ c : I,
        S.al c s x * MvPowerSeries.coeff μ (t c ^ (V.l ^ s))) =
        if μ = Finsupp.single x 1 then 1 else 0
def ze (t : I → MvPowerSeries I C) (κ : J) : MvPowerSeries I C :=
  fun μ => -(∑ s ∈ Finset.Icc 1 μ.degree, ∑ c : I,
    S.be c s κ * MvPowerSeries.coeff μ (t c ^ (V.l ^ s)))
end Sys
end OneGroup
section TwoGroups
variable {V : VF C} {d : ℕ} {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
abbrev WV (I : Fin 2 → Type) := Σ g : Fin 2, I g
def tyW (G : ∀ g, Cart V d (I g) (J g)) (w : WV I) : ZMod d := (G w.1).ty (Sum.inl w.2)
def upG (g : Fin 2) (F : MvPowerSeries (I g) C) : MvPowerSeries (WV I) C :=
  MvPowerSeries.subst (fun x : I g => (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C)) F
def IntGerm (V : VF C) (t : ∀ g, I g → MvPowerSeries (I g) C) : Set (MvPowerSeries (WV I) C) :=
  {F | ∃ γ : MvPowerSeries (WV I) C, (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) ∧
    F = MvPowerSeries.subst (fun w : WV I => upG w.1 (t w.1 w.2)) γ}
def OnLeafV (G : ∀ g, Cart V d (I g) (J g)) (g : Fin 2) (a a' : ZMod d) (w : WV I) : Prop :=
  (w.1 = g ∧ tyW G w = a) ∨ (w.1 = 1 - g ∧ tyW G w = a')
def toLeaf (G : ∀ g, Cart V d (I g) (J g)) (g : Fin 2) (a a' : ZMod d)
    (F : MvPowerSeries (WV I) C) : MvPowerSeries (WV I) C :=
  fun μ => if ∀ w ∈ μ.support, OnLeafV G g a a' w then MvPowerSeries.coeff μ F else 0
def dVar {σ : Type} (w : σ) (F : MvPowerSeries σ C) : MvPowerSeries σ C :=
  fun μ => ((μ w + 1 : ℕ) : C) * MvPowerSeries.coeff (μ + Finsupp.single w 1) F
def rowCopy {N : ℕ} (ρ : Fin N) (F : MvPowerSeries (WV I) C) : MvPowerSeries (Fin N × WV I) C :=
  MvPowerSeries.subst
    (fun w : WV I => (MvPowerSeries.X (ρ, w) : MvPowerSeries (Fin N × WV I) C)) F
def RowsOK (G : ∀ g, Cart V d (I g) (J g)) (alt : Prop) {N : ℕ}
    (P : MvPolynomial (Fin N × WV I) C) (kind : Fin N → Option (Fin 2 × ZMod d × ZMod d)) : Prop :=
  (∀ ρ g a a', kind ρ = some (g, a, a') → alt ∧ Odd (a' - a).val ∧
    ∀ μ ∈ P.support, ∀ w, μ (ρ, w) ≠ 0 → OnLeafV G g a a' w) ∧
  (∀ ρ, kind ρ = none → ∃ g : Fin 2, ∀ μ ∈ P.support, ∀ w : WV I, μ (ρ, w) ≠ 0 → w.1 = g)
def ValOf (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) {N : ℕ}
    (P : MvPolynomial (Fin N × WV I) C) (kind : Fin N → Option (Fin 2 × ZMod d × ZMod d))
    (gr : Fin N → MvPowerSeries (WV I) C) : C :=
  jetAt0 P (∏ ρ, (rowCopy ρ (gr ρ) *
    mvExp (rowCopy ρ (match kind ρ with
      | some (g, a, a') => hL g a a'
      | none => 0))))
end TwoGroups
structure RowData (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type)
    [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] where

  charZero : CharZero C
  algClosed : IsAlgClosed C
  l_odd : V.l ≠ 2

  G : ∀ g, Cart V d (I g) (J g)

  n : ℕ
  j : ℕ
  j' : ℕ
  rh : ℕ
  r : ℕ
  r_eq : r = n + j + j'

  big : Fin 2 → ZMod d → Prop
  big_compl : ∀ g a, big (1 - g) a ↔ ¬ big g a

  rk_big : ∀ g a, big g a → (Finset.univ.filter fun c : I g => (G g).ty (Sum.inl c) = a).card = n + j
  rk_small : ∀ g a, ¬ big g a →
    (Finset.univ.filter fun c : I g => (G g).ty (Sum.inl c) = a).card = j'
  rk_fil : ∀ g a, (Finset.univ.filter fun κ : J g => (G g).ty (Sum.inr κ) = a).card + rh +
    (Finset.univ.filter fun c : I g => (G g).ty (Sum.inl c) = a).card = r

  pair : ∀ g, J g → I (1 - g) → C
  pair_int : ∀ g κ k, V.Ge 0 (pair g κ k)
  pair_type : ∀ g κ k, (G g).ty (Sum.inr κ) ≠ (G (1 - g)).ty (Sum.inl k) → pair g κ k = 0
  pair_onto : ∀ g, ∃ s : I (1 - g) → J g → C, (∀ k κ, V.Ge 0 (s k κ)) ∧
    ∀ κ κ' : J g, ∑ k, pair g κ k * s k κ' = if κ = κ' then 1 else 0

  R2 : (Even d ∧ ∀ a : ZMod d, (big 0 a ↔ Even a.val)) → ∀ g a, big g a →
    ∀ (u : I g → C) (x : ℕ → I g ⊕ J g → C), (G g).Good a u x →
    (∀ κ, V.MM ((G g).c0' x κ)) → ∀ k, V.MM (u k)

  R1 : (Even d ∧ ∀ a : ZMod d, (big 0 a ↔ Even a.val)) → ∀ g a, big g a →
    ∀ (N : ℕ) (u : Fin N → I g → C) (x : Fin N → ℕ → I g ⊕ J g → C),
    (∀ ν, (G g).Good a (u ν) (x ν)) → (∀ ν k, V.MM ((G g).V2 (x ν) k)) →
    IndepMod V u → N + rh ≤ j'

  G0 : ∀ (S S₂ : ∀ g, Sys (G g)) (t t₂ : ∀ g, I g → MvPowerSeries (I g) C),
    (∀ g, (S g).IsT (t g)) → (∀ g, (S₂ g).IsT (t₂ g)) → IntGerm V t = IntGerm V t₂

  hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C
  hL_leaf : ∀ g a a' μ, MvPowerSeries.coeff μ (hL g a a') ≠ 0 → ∀ w ∈ μ.support, OnLeafV G g a a' w

  hL_swap : ∀ a a', hL 1 a' a = hL 0 a a'

  hL_axes : ∀ g a a' (μ : WV I →₀ ℕ), ((∀ w ∈ μ.support, w.1 = g) ∨ (∀ w ∈ μ.support, w.1 = 1 - g)) →
    MvPowerSeries.coeff μ (hL g a a') = 0

  C_eq : (Even d ∧ ∀ a : ZMod d, (big 0 a ↔ Even a.val)) → ∀ g a a', Odd (a' - a).val →
    ∀ (S : ∀ g, Sys (G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) →
    ∀ k : I (1 - g), (G (1 - g)).ty (Sum.inl k) = a' →
      ∃ K ∈ IntGerm V t,
        dVar (⟨1 - g, k⟩ : WV I) (hL g a a') -
            toLeaf G g a a' (∑ κ : J g, pair g κ k • upG g ((S g).ze (t g) κ)) =
          toLeaf G g a a' K

  CH : ∀ g a, big g a → ∀ u : Fin n → I g → C, IsSat V u →
    (∀ c x, (G g).ty (Sum.inl x) ≠ a → u c x = 0) →
    ∃ y : Fin n → I g → C, (∀ ρ x, V.Ge 0 (y ρ x)) ∧
      (∀ (S : ∀ g, Sys (G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) →
        ∀ ρ, upG g (mvExp (∑ x : I g, y ρ x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
          IntGerm V t) ∧
      ((Even d ∧ ∀ a : ZMod d, (big 0 a ↔ Even a.val)) →
        V.v (Matrix.of fun ρ c : Fin n => ∑ x, y ρ x * u c x).det ≤
          (((n : ℝ) * gam V.l + ((j : ℝ) + j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ)) ∧
      ((∀ a, big g a) →
        V.v (Matrix.of fun ρ c : Fin n => ∑ x, y ρ x * u c x).det ≤
          ((((j : ℝ) + j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ))
namespace RowData
variable {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
  [∀ g, Fintype (J g)] (X : RowData C V d I J)
def Alt : Prop := Even d ∧ ∀ a : ZMod d, (X.big 0 a ↔ Even a.val)
def m : ℕ := X.j + X.j'
end RowData
structure RowValue {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) where
  nu : WithTop ℝ
  FF : ∀ N : ℕ, Set (MvPolynomial (Fin N × WV I) C)
  VAL : ∀ (N : ℕ), ∀ P ∈ FF N, ∀ kind : Fin N → Option (Fin 2 × ZMod d × ZMod d),
    RowsOK X.G X.Alt P kind →
    ∀ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) →
    ∀ gr : Fin N → MvPowerSeries (WV I) C, (∀ ρ, gr ρ ∈ IntGerm V t) →
      nu ≤ V.v (ValOf X.hL P kind gr)
end Formalism.L2.FormalSeriesBounds


