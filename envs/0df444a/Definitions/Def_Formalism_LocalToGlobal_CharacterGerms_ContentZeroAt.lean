-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ContentZeroAt
-- name    : Formalism_LocalToGlobal_CharacterGerms_ContentZeroAt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:08.911803+00:00
-- url     : https://prove2.me/theorems/9e9254dd-33bc-4dc4-a455-5d3764c96120
-- title:
--   Content Zero At
-- statement:
--   Definitions and structural lemmas for Content Zero At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ContentZeroAt.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum

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
namespace Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
def blockBd (l n m i y : ℕ) : ℝ :=
  if y = 0 then 0 else bdP l i n n y + ((i : ℝ) + 1) * m * ((l : ℝ) ^ i + 1) * y / ((l : ℝ) - 1)
def chBd (l n m u : ℕ) : ℝ := (u : ℝ) * (n * gam l + m / ((l : ℝ) - 1))
def Windows (S : ℕ) (G : Set ℕ) : Prop := 0 ∈ G ∧ ∀ Y0 : ℕ, ∃ y ∈ G, Y0 ≤ y ∧ y < Y0 + S
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
def _root_.Formalism.L2.FormalSeriesBounds.RowData.rkF (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) : ℕ :=
  (Finset.univ.filter fun c : I g => (X.G g).ty (Sum.inl c) = a).card
structure Flag (X : RowData C V d I J) where
  en : ∀ g a, Fin (X.rkF g a) → I g
  en_inj : ∀ g a, Function.Injective (en g a)
  en_ty : ∀ g a c, (X.G g).ty (Sum.inl (en g a c)) = a
def Flag.letter {X : RowData C V d I J} (F : Flag X) (g : Fin 2) (a : ZMod d) {N : ℕ}
    (x : Fin N × Fin (X.rkF g a)) : Fin N × WV I := (x.1, ⟨g, F.en g a x.2⟩)
def bg (a : ZMod d) : Fin 2 := if Even a.val then 0 else 1
inductive GlobalTheory (d : ℕ) where

  | bi (g : Fin 2) (a : ZMod d) (i y : ℕ)

  | ch (g : Fin 2) (a : ZMod d) (u : ℕ)

  | mon (g : Fin 2) (e : ZMod d → ℕ → ℕ) (N : ℕ)
namespace GlobalTheory
def what₂ (n : ℕ) : GlobalTheory d → ℕ
  | bi _ _ _ _ => n
  | ch _ _ _ => n
  | mon _ _ N => N
variable (X : RowData C V d I J) (F : Flag X)
def poly : (b : GlobalTheory d) → MvPolynomial (Fin (b.what₂ X.n) × WV I) C
  | bi g a i y =>
      MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rkF g a) X.n) ^ (V.l ^ i * y) *
        MvPolynomial.rename (F.letter (1 - g) (a + (i : ZMod d)))
          (minorK C X.n (X.rkF (1 - g) (a + (i : ZMod d))) X.n) ^ y
  | ch g a u => MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rkF g a) X.n) ^ u
  | mon g e N => ∏ a : ZMod d, MvPolynomial.rename (F.letter g a) (monP C N (X.rkF g a) (e a))
def kind (n : ℕ) : (b : GlobalTheory d) → Fin (b.what₂ n) → Option (Fin 2 × ZMod d × ZMod d)
  | bi g a i _ => fun _ => some (g, a, a + (i : ZMod d))
  | ch _ _ _ => fun _ => none
  | mon _ _ _ => fun _ => none
def wt : GlobalTheory d → Fin 2 → ZMod d → ℕ → ℕ
  | bi g a i y => fun g' a' k =>
      (if g' = g ∧ a' = a ∧ k = X.n then V.l ^ i * y else 0) +
        (if g' = 1 - g ∧ a' = a + (i : ZMod d) ∧ k = X.n then y else 0)
  | ch g a u => fun g' a' k => if g' = g ∧ a' = a ∧ k = X.n then u else 0
  | mon g e N => fun g' a' k => if g' = g ∧ 1 ≤ k ∧ k ≤ min N (X.rkF g a') then e a' k else 0
def Attains (b : GlobalTheory d) (c : ℝ) : Prop :=
  ∃ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) ∧
    ∃ gr : Fin (b.what₂ X.n) → MvPowerSeries (WV I) C, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
      V.v (ValOf X.hL (b.poly X F) (b.kind X.n) gr) ≤ ((c : ℝ) : WithTop ℝ)
end GlobalTheory
def BiSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X), X.Alt → 5 ≤ V.l → 1 ≤ X.n →
    ∀ g a, X.big g a → ∀ i : ℕ, Odd i → i < d →
      Windows (S0 V.l i X.n) {y | (GlobalTheory.bi g a i y).Attains X F (blockBd V.l X.n X.m i y)}
def CHSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X), ∀ g a, X.big g a → ∀ u : ℕ,
      (X.Alt → (GlobalTheory.ch g a u).Attains X F (chBd V.l X.n X.m u)) ∧
      ((∀ a, X.big g a) → (GlobalTheory.ch g a u).Attains X F ((u : ℝ) * (X.m / ((V.l : ℝ) - 1))))
def monDegAll (X : RowData C V d I J) (g : Fin 2) (e : ZMod d → ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ a : ZMod d, monDeg N (X.rkF g a) (e a)
def UBSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X), X.Alt → 5 ≤ V.l → 1 ≤ X.n →
    ∀ g a, X.big g a → ∀ y : ℕ, y + X.n ≤ V.l - 1 →
      (GlobalTheory.bi g a 1 y).Attains X F (2 * (X.m : ℝ) * y)
def MONSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X) (g : Fin 2) (e : ZMod d → ℕ → ℕ)
    (N : ℕ),
      (GlobalTheory.mon g e N).Attains X F ((monDegAll X g e N : ℝ) / ((V.l : ℝ) - 1)) ∧
      ((∀ a ρ, monAl N (X.rkF g a) (e a) ρ < V.l) → (GlobalTheory.mon g e N).Attains X F 0)
def ValBlocks {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
    [∀ o g, Fintype (J o g)] (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, Flag (X o))
    (Z : Finset Orb) (nW : ℕ) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (ν : ℝ) : Prop :=
  ∀ L : Orb → List (GlobalTheory d × ℝ),
    (∀ o ∈ Z, ∀ p ∈ L o, p.1.Attains (X o) (F o) p.2) →
    (∑ o ∈ Z, ((L o).map fun p => p.1.what₂ (X o).n).sum) ≤ nW →
    (∀ o ∈ Z, ∀ g a k, ((L o).map fun p => p.1.wt (X o) g a k).sum = ga o g a k) →
    ν ≤ ∑ o ∈ Z, ((L o).map Prod.snd).sum
def restDeg (bgr : ZMod d → Fin 2) (n : ℕ) (ga : Fin 2 → ZMod d → ℕ → ℕ) (K : ℕ) : ℕ :=
  ∑ g : Fin 2, ∑ a : ZMod d, ∑ k ∈ Finset.Icc 1 K, if g = bgr a ∧ k = n then 0 else k * ga g a k
def totDeg (ga : Fin 2 → ZMod d → ℕ → ℕ) (K : ℕ) : ℕ :=
  ∑ g : Fin 2, ∑ a : ZMod d, ∑ k ∈ Finset.Icc 1 K, k * ga g a k
structure WtHyp {Orb : Type} (k K : ℕ) (Z : Finset Orb) (bgr : ZMod d → Fin 2)
    (rk : Orb → Fin 2 → ZMod d → ℕ) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (Wa ea : Orb → ZMod d → ℕ)
    (rest : ℝ) : Prop where
  supp : ∀ z ∈ Z, ∀ g a k', ga z g a k' ≠ 0 → 1 ≤ k' ∧ k' ≤ rk z g a
  main : ∀ z ∈ Z, ∀ a, ga z (bgr a) a (k - 1) = Wa z a + ea z a
  rest_eq : rest = ∑ z ∈ Z, ((restDeg bgr (k - 1) (ga z) K : ℝ) +
    ∑ a, ((k : ℝ) - 1) * ((ea z a : ℕ) : ℝ))
def ValBlocksC {C : Type} [Field C] {V : VF C} {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type}
    [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)] (X : ∀ o, RowData C V 2 (I o) (J o))
    (F : ∀ o, Flag (X o)) (nW : ℕ) (gaC : Orb → ZMod 2 → ℕ → ℕ) (ν : ℝ) : Prop :=
  ∀ L : Orb → List (GlobalTheory 2 × ℝ),
    (∀ o, ∀ p ∈ L o, p.1.Attains (X o) (F o) p.2) →
    (∀ o, ∀ p ∈ L o, ∀ g e N, p.1 = GlobalTheory.mon g e N → ∃ s : ZMod 2, ∀ a k, a ≠ s → e a k = 0) →
    2 * (∑ o, ((L o).map fun p => p.1.what₂ (X o).n).sum) ≤ nW →
    (∀ o s k, ((L o).map fun p => p.1.wt (X o) 0 s k + p.1.wt (X o) 1 (s + 1) k).sum = gaC o s k) →
    ν ≤ ∑ o, ((L o).map Prod.snd).sum
def ContentZeroAt : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (Orb : Type) [Fintype Orb]
    (I J : Orb → Fin 2 → Type) [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, Flag (X o)) (Z : Finset Orb)
    (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (K nW : ℕ) (ν : ℝ),
    (∀ z ∈ Z, ∀ g a k, ga z g a k ≠ 0 → 1 ≤ k ∧ k ≤ (X z).rkF g a ∧ k ≤ K) →
    2 * K * Z.card ≤ nW →
    (∑ z ∈ Z, totDeg (ga z) K) < V.l → ValBlocks X F Z nW ga ν → ν ≤ 0
end Formalism.L2.FormalSeriesBounds.RF


