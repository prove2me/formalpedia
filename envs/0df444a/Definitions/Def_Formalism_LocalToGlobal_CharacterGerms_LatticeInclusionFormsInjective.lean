-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
-- name    : Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:17.719017+00:00
-- url     : https://prove2.me/theorems/4601bd33-4b8d-49b3-8789-0cfcfa644ad7
-- title:
--   Lattice Inclusion Forms Injective
-- statement:
--   Definitions and structural lemmas for Lattice Inclusion Forms Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LatticeInclusionFormsInjective.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
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
section OneGroup
variable {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
def StructEq (X : Cart V d I J) (S : Sys X) : Prop :=
  ∃ (c : ℕ → I → I → C) (c' : ℕ → I → J → C),
    (∀ s a b, V.Ge 0 (c s a b)) ∧ (∀ s a κ, V.Ge 0 (c' s a κ)) ∧
    (∀ (s : ℕ) a b, X.ty (Sum.inl b) ≠ X.ty (Sum.inl a) + 1 + s → c s a b = 0) ∧
    ∀ (a : I) (i : ℕ) (n : I ⊕ J),
      (V.l : C) * S.cur a (i + 1) n =
        (∑ s ∈ Finset.range (i + 1), ∑ b : I, c s a b ^ (V.l ^ (i - s)) * S.cur b (i - s) n) +
          Sum.elim (fun _ => 0) (c' i a) n
def StructEqAll (X : Cart V d I J) : Prop := ∀ S : Sys X, StructEq X S
def LatticeInclusionFormsInjective (X : Cart V d I J) : Prop :=
  ∀ (S : Sys X) (c : I) (i : ℕ) (n : I ⊕ J), V.Ge (-(i : ℝ)) (S.cur c i n)
def Eq16 (X : Cart V d I J) : Prop :=
  ∀ (a : ZMod d) (u : I → C) (x : ℕ → I ⊕ J → C), X.Good a u x → ∀ i : ℕ, 1 ≤ i →
      (∀ k, V.Ge (-((i : ℝ) - 1)) (x i (Sum.inl k))) ∧
        ∀ κ, V.Ge (-(max 1 ((i : ℝ) - 1))) (x i (Sum.inr κ))
def TExistsUnique (X : Cart V d I J) : Prop := ∀ S : Sys X, ∃! t : I → MvPowerSeries I C, S.IsT t
def SysExists (X : Cart V d I J) : Prop :=
  ∀ u : I → I → C, (∀ c x, V.Ge 0 (u c x)) → (∀ c x, X.ty (Sum.inl x) ≠ X.ty (Sum.inl c) → u c x = 0) →
    V.v (Matrix.of u).det = 0 → ∃ S : Sys X, S.tan = u
end OneGroup
section Rows
variable {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
  [∀ g, Fintype (J g)]
def toW (g : Fin 2) (u : I g → C) : WV I → C := fun w => if h : w.1 = g then u (h ▸ w.2) else 0
def hPullW {ι ι' : Type} [Fintype ι] [Fintype ι'] (H : MvPowerSeries (WV I) C)
    (e : ι → WV I → C) (e' : ι' → WV I → C) : MvPowerSeries (ι ⊕ ι') C :=
  MvPowerSeries.subst (fun w : WV I =>
    (∑ c : ι, e c w • (MvPowerSeries.X (Sum.inl c) : MvPowerSeries (ι ⊕ ι') C)) +
      ∑ b : ι', e' b w • (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') C)) H
def WtGe2 (V : VF C) (i : ℕ) (w : ℝ) {ι ι' : Type} [Fintype ι] [Fintype ι']
    (h : MvPowerSeries (ι ⊕ ι') C) : Prop :=
  ∀ μ : ι ⊕ ι' →₀ ℕ, ((w : ℝ) : WithTop ℝ) ≤ V.v (MvPowerSeries.coeff μ h) +
    ((((∑ c : ι, μ (Sum.inl c) : ℕ) : ℝ) * (r1 V.l i - del V.l i) +
      ((∑ b : ι', μ (Sum.inr b) : ℕ) : ℝ) * (r2 V.l - del V.l i) : ℝ) : WithTop ℝ)
def WtGe1 (V : VF C) (i : ℕ) (w : ℝ) {ι : Type} (h : MvPowerSeries ι C) : Prop :=
  ∀ μ : ι →₀ ℕ, ((w : ℝ) : WithTop ℝ) ≤ V.v (MvPowerSeries.coeff μ h) +
    (((μ.degree : ℝ) * (r1 V.l i - del V.l i) : ℝ) : WithTop ℝ)
def mainM (V : VF C) (i : ℕ) {ι ι' : Type} [Fintype ι] [Fintype ι'] (Φ : ι' → ι → C) :
    MvPowerSeries (ι ⊕ ι') C :=
  ((V.l : C) ^ expE V.l i)⁻¹ • ∑ b : ι', ∑ c : ι,
    Φ b c • (MvPowerSeries.X (Sum.inl c) ^ (V.l ^ i) * MvPowerSeries.X (Sum.inr b))
def hRows (n0 : ℕ) (H : MvPowerSeries (Fin n0 ⊕ Fin n0) C) : MvPowerSeries (PVar n0) C :=
  ∑ ρ : Fin n0, MvPowerSeries.subst
    (Sum.elim (fun c => (MvPowerSeries.X (Sum.inl (ρ, c)) : MvPowerSeries (PVar n0) C))
      (fun b => MvPowerSeries.X (Sum.inr (ρ, b)))) H
namespace RowData
variable (X : RowData C V d I J)
def SatIn (g : Fin 2) (a : ZMod d) {N : ℕ} (u : Fin N → I g → C) : Prop :=
  IsSat V u ∧ ∀ c x, (X.G g).ty (Sum.inl x) ≠ a → u c x = 0
def hM (g : Fin 2) (a : ZMod d) (i : ℕ) {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) : MvPowerSeries (ι ⊕ ι') C :=
  hPullW (X.hL g a (a + (i : ZMod d))) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))
def MConcl (g : Fin 2) (a : ZMod d) (i : ℕ) (U : Fin X.n → I g → C) (U' : Fin X.n → I (1 - g) → C)
    (n0 : ℕ) (e : Fin n0 → I g → C) (v' : Fin X.n → I (1 - g) → C) (Φ : Fin X.n → Fin n0 → C) :
    Prop :=
  (X.n ≤ n0 + (i + 1) * X.j' + X.j ∧ n0 ≤ X.n) ∧
  IsSat V e ∧
  (∃ A : Fin n0 → Fin X.n → C, (∀ c b, V.Ge 0 (A c b)) ∧ ∀ c x, e c x = ∑ b, A c b * U b x) ∧
  (∃ Y : Matrix (Fin X.n) (Fin X.n) C, (∀ b b', V.Ge 0 (Y b b')) ∧ V.v Y.det = 0 ∧
    ∀ b x, v' b x = ∑ b', Y b b' * U' b' x) ∧
  (∀ b c, V.Ge 0 (Φ b c)) ∧
  (∀ (b : Fin X.n) (c : Fin n0), b.val < n0 → Φ b c = if b.val = c.val then -1 else 0) ∧
  WtGe2 V i (1 / ((V.l : ℝ) - 1)) (X.hM g a i e v' - mainM V i Φ) ∧
  (∀ μ : Fin n0 ⊕ Fin X.n →₀ ℕ, (∀ b, μ (Sum.inr b) = 0) →
    MvPowerSeries.coeff μ (X.hM g a i e v' - mainM V i Φ) = 0)
def CurveSystemVanishing (g : Fin 2) (a : ZMod d) (i : ℕ) (n0 : ℕ) (e : Fin n0 → I g → C)
    (v' : Fin X.n → I (1 - g) → C) (Φ : Fin X.n → Fin n0 → C) : Prop :=
  ∃ (S : Sys (X.G g)) (t : I g → MvPowerSeries (I g) C) (em : Fin n0 ↪ I g)
    (Φt : Fin n0 → J g → C),
    S.IsT t ∧ (∀ c, S.tan (em c) = e c) ∧ (∀ c x, S.al (em c) 1 x = 0) ∧
    (∀ c κ, V.Ge 0 (Φt c κ)) ∧
    (∀ b c, Φ b c = ∑ κ : J g, ∑ k : I (1 - g), Φt c κ * X.pair g κ k * v' b k) ∧
    ∀ κ : J g, (X.G g).ty (Sum.inr κ) = a + (i : ZMod d) →
      WtGe1 V i 0
        (MvPowerSeries.subst (fun x : I g =>
            ∑ c : Fin n0, e c x • (MvPowerSeries.X c : MvPowerSeries (Fin n0) C)) (S.ze t κ) -
          ((V.l : C) ^ expE V.l i)⁻¹ • ∑ c : Fin n0,
            Φt c κ • (MvPowerSeries.X c : MvPowerSeries (Fin n0) C) ^ (V.l ^ i))
def MPlusConcl (g : Fin 2) (a : ZMod d) (n0 : ℕ) (e : Fin n0 → I g → C)
    (v' : Fin X.n → I (1 - g) → C) (Φ : Fin X.n → Fin n0 → C) : Prop :=
  ∀ μ : Fin n0 ⊕ Fin X.n →₀ ℕ, (∑ c, μ (Sum.inl c)) < V.l ^ 2 → (∑ b, μ (Sum.inr b)) < V.l →
    V.Ge 0 (MvPowerSeries.coeff μ (X.hM g a 1 e v' - mainM V 1 Φ))
def LemmaM : Prop :=
  X.Alt → 5 ≤ V.l → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ i : ℕ, Odd i → i < d →
    ∀ (U : Fin X.n → I g → C) (U' : Fin X.n → I (1 - g) → C), X.SatIn g a U →
      X.SatIn (1 - g) (a + (i : ZMod d)) U' →
      ∃ (n0 : ℕ) (e : Fin n0 → I g → C) (v' : Fin X.n → I (1 - g) → C) (Φ : Fin X.n → Fin n0 → C),
        X.MConcl g a i U U' n0 e v' Φ ∧ X.CurveSystemVanishing g a i n0 e v' Φ
def LemmaMLeaf : Prop :=
  X.Alt → 5 ≤ V.l → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ i : ℕ, Odd i → i < d →
    ∀ (U : Fin X.n → I g → C) (U' : Fin X.n → I (1 - g) → C), X.SatIn g a U →
      X.SatIn (1 - g) (a + (i : ZMod d)) U' →
      ∃ (N1 : ℕ) (w : Fin N1 → I g → C) (Φ : Fin X.n → Fin N1 → C),
        IsSat V w ∧
        (∃ A : Fin N1 → Fin X.n → C, (∀ c b, V.Ge 0 (A c b)) ∧ ∀ c x, w c x = ∑ b, A c b * U b x) ∧
        X.n ≤ N1 + (Formalism.BaseCaseIdentities.Kn i + 1) * X.j' ∧
        (∀ b c, V.Ge 0 (Φ b c)) ∧
        WtGe2 V i (1 / ((V.l : ℝ) - 1)) (X.hM g a i w U' - mainM V i Φ) ∧
        ∃ (n0 : ℕ) (rr : Fin n0 ↪ Fin X.n) (cc : Fin n0 ↪ Fin N1),
          X.n ≤ n0 + (i + 1) * X.j' + X.j ∧
          V.v (Matrix.of fun b c : Fin n0 => Φ (rr b) (cc c)).det = 0
def LemmaMPlus : Prop :=
  X.Alt → 5 ≤ V.l → 1 < d → ∀ (g : Fin 2) (a : ZMod d), X.big g a →
    ∀ (U : Fin X.n → I g → C) (U' : Fin X.n → I (1 - g) → C), X.SatIn g a U →
      X.SatIn (1 - g) (a + ((1 : ℕ) : ZMod d)) U' →
      ∃ (n0 : ℕ) (e : Fin n0 → I g → C) (v' : Fin X.n → I (1 - g) → C) (Φ : Fin X.n → Fin n0 → C),
        X.MConcl g a 1 U U' n0 e v' Φ ∧ X.CurveSystemVanishing g a 1 n0 e v' Φ ∧ X.MPlusConcl g a n0 e v' Φ
def hGood (g : Fin 2) (a : ZMod d) (i : ℕ) {n0 : ℕ} (hn : n0 ≤ X.n) (e : Fin n0 → I g → C)
    (v' : Fin X.n → I (1 - g) → C) : MvPowerSeries (Fin n0 ⊕ Fin n0) C :=
  X.hM g a i e (fun b : Fin n0 => v' (Fin.castLE hn b))
def restrictedCurveSystemSeries (g : Fin 2) (a : ZMod d) (i : ℕ) {n0 : ℕ} (hn : n0 ≤ X.n) (e : Fin n0 → I g → C)
    (v' : Fin X.n → I (1 - g) → C) : MvPowerSeries (PVar n0) C :=
  hRows n0 (X.hGood g a i hn e v' - mainM V i (fun b c : Fin n0 => if b = c then (-1 : C) else 0))
def MtoHM : Prop :=
  ∀ (g : Fin 2) (a : ZMod d) (i : ℕ) (U : Fin X.n → I g → C) (U' : Fin X.n → I (1 - g) → C)
    (n0 : ℕ) (e : Fin n0 → I g → C) (v' : Fin X.n → I (1 - g) → C) (Φ : Fin X.n → Fin n0 → C),
    X.MConcl g a i U U' n0 e v' Φ → ∀ hn : n0 ≤ X.n,
      hRows n0 (X.hGood g a i hn e v') = hP C V.l i n0 (X.restrictedCurveSystemSeries g a i hn e v') ∧
      HM1 V.v V.l i n0 (X.restrictedCurveSystemSeries g a i hn e v') ∧ HM2 (X.restrictedCurveSystemSeries g a i hn e v') ∧
      (i = 1 → X.MPlusConcl g a n0 e v' Φ → HSeparatedRowSum V.v V.l n0 (X.restrictedCurveSystemSeries g a i hn e v'))
def AdaptedChainData : Prop :=
  X.Alt → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ i : ℕ, Odd i → i < d →
    ∀ U : Fin X.n → I g → C, X.SatIn g a U →
      ∃ (S : Sys (X.G g)) (N1 : ℕ) (D : Formalism.BaseCaseIdentities.Data C (Fin N1) (I g)),
        D.v = V.v ∧ D.l = V.l ∧ D.i = i ∧
        (∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, D.al c k b * S.al b 0 x) ∧
        (∀ c, D.lev c < Formalism.BaseCaseIdentities.Kn i →
          (X.G g).ty (Sum.inl c) = a + ((2 * D.lev c : ℕ) : ZMod d)) ∧
        X.n ≤ N1 + (Formalism.BaseCaseIdentities.Kn i + 1) * X.j' ∧
        ∃ A : Fin N1 → Fin X.n → C, (∀ δ b, V.Ge 0 (A δ b)) ∧
          ∀ δ x, S.al (D.ι δ) 0 x = ∑ b, A δ b * U b x
end RowData
end Rows
end Formalism.L2.FormalSeriesBounds


