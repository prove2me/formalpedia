-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_QmDefs
-- name    : Formalism_PeriodIntegrals_QmDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:40:26.700521+00:00
-- url     : https://prove2.me/theorems/62cd52e9-0ac1-46fb-9e18-d853d721216f
-- title:
--   Qm Defs
-- statement:
--   Definitions and structural lemmas for Qm Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/QmDefs.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace PI
open Formalism.REAL
def skip1 {t : ℕ} (i : Fin t) (j : Fin (t - 1)) : Fin t :=
  if j.val < i.val then ⟨j.val, by have := j.isLt; omega⟩ else ⟨j.val + 1, by have := j.isLt; omega⟩
def skip2 {t : ℕ} (i i' : Fin t) (j : Fin (t - 2)) : Fin t :=
  if j.val < i.val then ⟨j.val, by have := j.isLt; omega⟩
  else if j.val + 1 < i'.val then ⟨j.val + 1, by have := j.isLt; omega⟩
  else ⟨j.val + 2, by have := j.isLt; omega⟩
def SkipSucc : Prop := ∀ (t : ℕ) (i : Fin (t + 1)) (j : Fin t), skip1 i j = i.succAbove j
def SkipSucc2 : Prop :=
  ∀ (t : ℕ) (i : Fin (t + 2)) (i' : Fin (t + 1)) (j : Fin t), i.val ≤ i'.val →
    skip2 i (i.succAbove i') j = i.succAbove (i'.succAbove j)
def qminorRow {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (u : ℂ) : A :=
  ∑ σ : Equiv.Perm (Fin t),
    ((Equiv.Perm.sign σ : ℤ) : A) *
      (List.ofFn fun k : Fin t => Tm E (u - (t : ℂ) + 1 + ((k : ℕ) : ℂ)) (a k) (b (σ k))).prod
def RowForm : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (a b : Fin t → Fin n) (u : ℂ), qminor E a b u = qminorRow E a b u
def ExpFirstCol : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (a b : Fin (t + 1) → Fin n) (u : ℂ),
    qminor E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (l : ℕ) : ℤ) : A) *
      (Tm E u (a l) (b 0) * qminor E (a ∘ l.succAbove) (b ∘ Fin.succ) (u - 1))
def ExpLastCol : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (a b : Fin (t + 1) → Fin n) (u : ℂ),
    qminor E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (t + (l : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ l.succAbove) (b ∘ Fin.castSucc) u * Tm E (u - (t : ℂ)) (a l) (b (Fin.last t)))
def ExpFirstRow : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (a b : Fin (t + 1) → Fin n) (u : ℂ),
      qminor E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (l : ℕ) : ℤ) : A) *
        (Tm E (u - (t : ℂ)) (a 0) (b l) * qminor E (a ∘ Fin.succ) (b ∘ l.succAbove) u)
def ExpLastRow : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (a b : Fin (t + 1) → Fin n) (u : ℂ),
      qminor E a b u = ∑ l : Fin (t + 1), (((-1 : ℤ) ^ (t + (l : ℕ)) : ℤ) : A) *
        (qminor E (a ∘ Fin.castSucc) (b ∘ l.succAbove) (u - 1) * Tm E u (a (Fin.last t)) (b l))
def MoveVec : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (y : Fin n → A), GlRel E →
    (∀ a b c, E a b * y c - y c * E a b = if a = c then -y b else 0) → (∀ a b, y a * y b = y b * y a) →
    ∀ (a : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (w : ℂ),
      ∑ j : Fin (t + 1), (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) * (y (b j) * qminor E a (b ∘ j.succAbove) w) =
        ∑ j : Fin (t + 1), (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) * (qminor E a (b ∘ j.succAbove) (w - 1) * y (b j))
def MoveCov : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (η : Fin n → A), GlRel E →
    (∀ a b c, E a b * η c - η c * E a b = if b = c then η a else 0) → (∀ a b, η a * η b = η b * η a) →
    ∀ (a : Fin (t + 1) → Fin n) (b : Fin t → Fin n) (w : ℂ),
      ∑ i : Fin (t + 1), (((-1 : ℤ) ^ (i : ℕ) : ℤ) : A) * (η (a i) * qminor E (a ∘ i.succAbove) b (w - 1)) =
        ∑ i : Fin (t + 1), (((-1 : ℤ) ^ (i : ℕ) : ℤ) : A) * (qminor E (a ∘ i.succAbove) b w * η (a i))
def StarMinor : Prop :=
  ∀ (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (n t : ℕ) (E : Fin n → Fin n → A)
    (ε : Fin n → ℤˣ), GlRel E → (∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a) →
    ∀ (a b : Fin t → Fin n) (w : ℂ),
      star (qminor E a b w) = ((((∏ k, ε (a k)) * ∏ k, ε (b k) : ℤˣ) : ℤ) : A) * qminor E b a (star w)
def bE {n m : ℕ} (e : Fin n) (v : Fin m → Fin n) : Fin (m + 1) → Fin n := Fin.cons (α := fun _ => Fin n) e v
def bS {n m : ℕ} (v : Fin m → Fin n) (es : Fin n) : Fin (m + 1) → Fin n := Fin.snoc (α := fun _ => Fin n) v es
def sg2 {m : ℕ} (w w' : Fin m) : ℤ :=
  if w'.val < w.val then (-1) ^ (w.val + w'.val) else (-1) ^ (w.val + w'.val + 1)
def IsBorder {n m : ℕ} (e es : Fin n) (v : Fin m → Fin n) : Prop :=
  Function.Injective v ∧ e ≠ es ∧ (∀ j, v j ≠ e) ∧ ∀ j, v j ≠ es
def BorderE : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n m : ℕ) (E : Fin n → Fin n → A) (e es : Fin n) (v : Fin m → Fin n),
    GlRel E → IsBorder e es v → ∀ u : ℂ,
      qminor E (bE e v) (bE e v) u = Tm E u e e * qminor E v v (u - 1) -
        ∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
          (E (v w) e * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 2) * E e (v x))
def BorderS : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n m : ℕ) (E : Fin n → Fin n → A) (e es : Fin n) (v : Fin m → Fin n),
    GlRel E → IsBorder e es v → ∀ u : ℂ,
      qminor E (bS v es) (bS v es) u = qminor E v v u * Tm E (u - (m : ℂ)) es es -
        ∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
          (E es (v x) * qminor E (v ∘ skip1 w) (v ∘ skip1 x) u * E (v w) es)
def BorderFull : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n m : ℕ) (E : Fin n → Fin n → A) (e es : Fin n) (v : Fin m → Fin n),
    GlRel E → IsBorder e es v → ∀ u : ℂ,
      qminor E (bE e (bS v es)) (bE e (bS v es)) u =
        Tm E u e e * qminor E v v (u - 1) * Tm E (u - (m : ℂ) - 1) es es
        - (∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
            (E es (v x) * Tm E u e e * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 1) * E (v w) es))
        - (∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
            (E (v w) e * qminor E (v ∘ skip1 w) (v ∘ skip1 x) (u - 2) * Tm E (u - (m : ℂ) - 1) es es * E e (v x)))
        - (∑ w : Fin m, ∑ w' : Fin m, ∑ x : Fin m, ∑ x' : Fin m,
            if w ≠ w' ∧ x ≠ x' then ((sg2 w w' * sg2 x x' : ℤ) : A) *
              (E (v w) e * E es (v x) *
                qminor E (v ∘ skip2 (min w w') (max w w')) (v ∘ skip2 (min x x') (max x x')) (u - 2) *
                E e (v x') * E (v w') es)
            else 0)
        + (((-1 : ℤ) ^ (m + 1) : ℤ) : A) * (E es e * qminor E (bE e v) (bS v es) (u - 1))
        + ∑ w : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + 1 + m) : ℤ) : A) *
            (E (v w) e * qminor E (Fin.snoc (α := fun _ => Fin n) (v ∘ skip1 w) es ∘ Fin.cast (by
                have := w.isLt; omega)) v (u - 1) * E e es)
end PI


