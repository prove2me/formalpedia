-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementQ
-- name    : Formalism_HermitianCurvature_StatementQ
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T14:06:08.818725+00:00
-- url     : https://prove2.me/theorems/fe3244a9-1ea3-47d9-9f16-d89ca213d141
-- title:
--   Statement Q
-- statement:
--   Definitions and structural lemmas for Statement Q, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementQ.lean

import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_StatementM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
namespace Formalism.FourierDecayAlt.Q
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
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
def ExpRowsFromRowForm : Prop := RowForm → ExpFirstRow ∧ ExpLastRow
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
def Econj {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ) :
    Fin n → Fin n → A := fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d
def chatA {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) (a β : Fin n → ℂ) : A :=
  ∑ i : Fin n, ∑ j : Fin n, ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * β i * a j) • qminor E (skip1 i) (skip1 j) u
def chat2A {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) (a a' β β' : Fin n → ℂ) : A :=
  ∑ i : Fin n, ∑ i' : Fin n, ∑ j : Fin n, ∑ j' : Fin n,
    if i < i' ∧ j < j' then
      ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ)) * (β i * β' i' - β i' * β' i) *
        (a j * a' j' - a j' * a' j)) • qminor E (skip2 i i') (skip2 j j') u
    else 0
def ContractionsCovariant : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ),
    GlRel E → Q * P = 1 → P * Q = 1 → ∀ (u : ℂ) (a a' β β' : Fin n → ℂ),
      qdet (Econj E P Q) u = qdet E u ∧
      chatA (Econj E P Q) u (Q *ᵥ a) (β ᵥ* P) = chatA E u a β ∧
      chat2A (Econj E P Q) u (Q *ᵥ a) (Q *ᵥ a') (β ᵥ* P) (β' ᵥ* P) = chat2A E u a a' β β'
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
def BorderFromExpansions : Prop :=
  ExpFirstCol → ExpLastCol → ExpFirstRow → ExpLastRow → QSkewRow → BorderE ∧ BorderS ∧ BorderFull
abbrev Mx (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
def mdim (k r : ℕ) (i : Fin (r + 1)) : ℕ := 2 * (r - i.val) + k + 1
def posL (k r : ℕ) (i : Fin (r + 1)) (j : Fin (mdim k r i)) : Fin (2 * r + k + 1) :=
  ⟨j.val + i.val, by have h1 := j.isLt; have h2 := i.isLt; unfold mdim at h1; omega⟩
def uC (k r : ℕ) (i : Fin (r + 1)) (Y : ℂ) : ℂ := Y + ((mdim k r i : ℂ) - 1) / 2
section Objects
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
abbrev EH (k r : ℕ) (a b : Fin (2 * r + k + 1)) (f : Mx k r → E) : Mx k r → E := EabH (Hpk k r) a b f
def chatL {n t : ℕ} (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (pos : Fin t → Fin n) (u : ℂ) (a β : Matrix (Fin n) (Fin n) ℂ → Fin t → ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => ∑ i : Fin t, ∑ j : Fin t,
    ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * β g i * a g j) • qminorOp Eop (pos ∘ skip1 i) (pos ∘ skip1 j) u f g
def chat2L {n t : ℕ} (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (pos : Fin t → Fin n) (u : ℂ) (a a' β β' : Matrix (Fin n) (Fin n) ℂ → Fin t → ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => ∑ i : Fin t, ∑ i' : Fin t, ∑ j : Fin t, ∑ j' : Fin t,
    if i < i' ∧ j < j' then
      ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ)) * (β g i * β' g i' - β g i' * β' g i) *
        (a g j * a' g j' - a g j' * a' g j)) • qminorOp Eop (pos ∘ skip2 i i') (pos ∘ skip2 j j') u f g
    else 0
def yv (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (g : Mx k r) : Fin (mdim k r i) → ℂ :=
  fun j => (g⁻¹ *ᵥ fvec k r z i) (posL k r i j)
def ybv (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (g : Mx k r) : Fin (mdim k r i) → ℂ :=
  fun j => herm (Hpk k r) (g *ᵥ bvec (posL k r i j)) (fvec k r z i)
def xv (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) : Fin (mdim k r i) → ℂ :=
  fun j => fvec k r z' i (posL k r i j)
def xbv (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) : Fin (mdim k r i) → ℂ :=
  fun j => herm (Hpk k r) (bvec (posL k r i j)) (fvec k r z' i)
def capL (k r : ℕ) (i : Fin (r + 1)) (u : ℂ) (f : Mx k r → E) : Mx k r → E :=
  qminorOp (EH k r) (posL k r i) (posL k r i) u f
def CV (k r : ℕ) (Y : ℂ) (f : Mx k r → E) : Mx k r → E := capL k r 0 (uC k r 0 Y) f
def tL (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (Y : ℂ) :
    Fin 2 → Fin 2 → (Mx k r → E) → (Mx k r → E) :=
  fun p q f =>
    match p, q with
    | 0, 0 => capL k r i (uC k r i Y) f
    | 0, 1 => -(chatL (EH k r) (posL k r i) (uC k r i Y - 1) (fun _ => xv k r z' i) (ybv k r z i) f)
    | 1, 0 => -(chatL (EH k r) (posL k r i) (uC k r i Y) (yv k r z i) (fun _ => xbv k r z' i) f)
    | 1, 1 => -(chat2L (EH k r) (posL k r i) (uC k r i Y - 1) (yv k r z i) (fun _ => xv k r z' i)
        (ybv k r z i) (fun _ => xbv k r z' i) f)
def Glev (k r : ℕ) (i : Fin (r + 1)) : Set (Mx k r) :=
  {g | g ∈ UH (Hpk k r) ∧ ∀ a : Fin r, a.val < i.val →
    g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)}
def Nlev (k r : ℕ) (i : Fin (r + 1)) : Set (Mx k r) := Nset k r ∩ Glev k r i
def Slev (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) : Set (Mx k r) :=
  {s | ∃ h ∈ UWset k r z, ∃ m ∈ Nlev k r i, s = h * m}
def IsDom (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (D : Set (Mx k r)) : Prop :=
  IsOpen D ∧ ∀ g ∈ Glev k r i ∩ D, ∀ s ∈ Slev k r z i, ∀ s' ∈ Slev k r z' i, s * g * s' ∈ D
def SmoothLev (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (f : Mx k r → E) : Prop :=
  ∀ g₀ ∈ Glev k r i ∩ D, ∃ (U : Set (Mx k r)) (F : Mx k r → E),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, g ∈ Glev k r i → f g = F g
def LeftEq (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (D : Set (Mx k r)) (f : Mx k r → E) : Prop :=
  ∀ g ∈ Glev k r i ∩ D, ∀ n ∈ Nlev k r i, f (n * g) = psi k r z cStd n • f g
def RightEq (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (D : Set (Mx k r)) (f : Mx k r → E) : Prop :=
  ∀ g ∈ Glev k r i ∩ D, ∀ n ∈ Nlev k r i, f (g * n) = psi k r z' cStd n • f g
end Objects
section Classes
variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
def FFl (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (i : Fin (r + 1)) (D : Set (Mx k r)) : Set (Mx k r → (Wq →L[ℂ] Wp)) :=
  {J | SmoothLev k r i D J ∧ LeftEq k r z i D J ∧ RightEq k r z' i D J ∧
    ∀ g ∈ Glev k r i ∩ D, ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', J (h * g * h') = (π h).comp ((J g).comp (π' h'))}
end Classes
def CapLZero : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (u : ℂ) (f : Mx k r → E),
    capL k r 0 u f = capelliH (Hpk k r) u f
def TLZero : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + (k + 1) + 1) → ℂ) (Y : ℂ)
    (p q : Fin 2) (f : Mx (k + 1) r → E),
    tL (k + 1) r z z' 0 Y p q f =
      QQop (m := 2 * r + k) (EabH (Hpk (k + 1) r)) (((2 * r + (k + 1) + 1 : ℕ) : ℂ) / 2 - 1 / 2) Y
        (fun g => g⁻¹ *ᵥ fvec (k + 1) r z 0) (fun g j => herm (Hpk (k + 1) r) (g *ᵥ bvec j) (fvec (k + 1) r z 0))
        (fvec (k + 1) r z' 0) (fun j => herm (Hpk (k + 1) r) (bvec j) (fvec (k + 1) r z' 0)) p q f
def FFZero : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)),
    inWb k r z → inWb k r z' → FFl k r z z' π π' 0 Set.univ = EqF k r z z' cStd π π'
def LevelTransfer : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k i r' : ℕ) (z z' : Fin (2 * r' + k + 1) → ℂ) (Y : ℂ)
    (p q : Fin 2) (f : Mx k (i + r') → E) (g : Mx k r'), g ∈ UH (Hpk k r') →
    tL k (i + r') (liftVec k i r' z) (liftVec k i r' z') ⟨i, by omega⟩ Y p q f (ιLev k i r' g) =
      tL k r' z z' 0 Y p q (fun x => f (ιLev k i r' x)) g
def GlevImage : Prop :=
  ∀ k i r' : ℕ, Glev k (i + r') ⟨i, by omega⟩ = ιLev k i r' '' UH (Hpk k r')
def w1 (k r : ℕ) (l : Fin r) (c : ℂ) : Mx k r := fun p q =>
  if p = esI k r l ∧ q = eI k r l then c
  else if p = eI k r l ∧ q = esI k r l then (star c)⁻¹
  else if p = q ∧ p ≠ eI k r l ∧ p ≠ esI k r l then 1 else 0
def wCell (k r : ℕ) (i : Fin (r + 1)) (c : Fin r → ℂ) : Mx k r :=
  (((List.finRange r).filter fun a => a.val < i.val).map fun a => w1 k r a (c a)).prod
def cellD (k r : ℕ) (l : Fin r) : Set (Mx k r) :=
  {g | herm (Hpk k r) (g *ᵥ bvec (eI k r l)) (bvec (eI k r l)) ≠ 0}
def WeylLevelElementFacts : Prop :=
  ∀ (k r : ℕ) (l : Fin r) (c : ℂ), c ≠ 0 → w1 k r l c ∈ Glev k r l.castSucc ∧
    ∀ g ∈ Glev k r l.succ, g ∈ Glev k r l.castSucc ∧ w1 k r l c * g = g * w1 k r l c ∧
      herm (Hpk k r) ((w1 k r l c * g) *ᵥ bvec (eI k r l)) (bvec (eI k r l)) = c
def WCellBigCell : Prop :=
  ∀ (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    bigCell k r c μ = wCell k r (Fin.last r) c * bigCell k r (fun _ => 1) μ * wCell k r (Fin.last r) (fun _ => 1)
def QMinorLeftH : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (n t : ℕ) (H : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) (a b : Fin t → Fin n) (u : ℂ) (h : Matrix (Fin n) (Fin n) ℂ),
    qminorOp (EabH H) a b u (fun x => f (h * x)) = fun x => qminorOp (EabH H) a b u f (h * x)
def EabPres : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1))
    (D : Set (Mx k r)) (a b : Fin (mdim k r i)) (f f₂ : Mx k r → E) (s : ℂ), IsOpen D →
    SmoothLev k r i D f → SmoothLev k r i D f₂ →
      SmoothLev k r i D (EH k r (posL k r i a) (posL k r i b) f) ∧
      ((∀ g ∈ Glev k r i ∩ D, ∀ n ∈ Nlev k r i, n * g ∈ D) → LeftEq k r z i D f →
        LeftEq k r z i D (EH k r (posL k r i a) (posL k r i b) f)) ∧
      ∀ g ∈ Glev k r i ∩ D, EH k r (posL k r i a) (posL k r i b) (fun x => f x + s • f₂ x) g =
        EH k r (posL k r i a) (posL k r i b) f g + s • EH k r (posL k r i a) (posL k r i b) f₂ g
def EabGlLev : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r))
    (a b c d : Fin (mdim k r i)) (f : Mx k r → E), IsOpen D → SmoothLev k r i D f → ∀ g ∈ Glev k r i ∩ D,
    EH k r (posL k r i a) (posL k r i b) (EH k r (posL k r i c) (posL k r i d) f) g -
        EH k r (posL k r i c) (posL k r i d) (EH k r (posL k r i a) (posL k r i b) f) g =
      (if b = c then EH k r (posL k r i a) (posL k r i d) f g else 0) -
        (if d = a then EH k r (posL k r i c) (posL k r i b) f g else 0)
def RuleRight : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (l : Fin r)
    (D : Set (Mx k r)) (f : Mx k r → E), inWb k r z' → IsOpen D → SmoothLev k r l.castSucc D f →
    RightEq k r z' l.castSucc D f → ∀ g ∈ Glev k r l.castSucc ∩ D,
      (∀ j, EH k r (eI k r l) (posL k r l.succ j) f g = xv k r z' l.succ j • f g) ∧
      (∀ j, EH k r (posL k r l.succ j) (esI k r l) f g = xbv k r z' l.succ j • f g) ∧
      EH k r (eI k r l) (esI k r l) f g = 0
def RuleLeft : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (l : Fin r)
    (D : Set (Mx k r)) (f : Mx k r → E), inWb k r z → IsOpen D → SmoothLev k r l.castSucc D f →
    (∀ g ∈ Glev k r l.castSucc ∩ D, ∀ n ∈ Nlev k r l.castSucc, n * g ∈ D) →
    LeftEq k r z l.castSucc D f → ∀ (c : ℂ), c ≠ 0 → ∀ g₁ ∈ Glev k r l.succ, w1 k r l c * g₁ ∈ D →
      (∀ j, EH k r (posL k r l.succ j) (eI k r l) f (w1 k r l c * g₁) =
        (c⁻¹ * ybv k r z l.succ g₁ j) • f (w1 k r l c * g₁)) ∧
      (∀ j, EH k r (esI k r l) (posL k r l.succ j) f (w1 k r l c * g₁) =
        ((star c)⁻¹ * yv k r z l.succ g₁ j) • f (w1 k r l c * g₁)) ∧
      EH k r (esI k r l) (eI k r l) f (w1 k r l c * g₁) = 0
def RuleTorus : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (l : Fin r)
    (D : Set (Mx k r)) (f : Mx k r → E), IsOpen D → SmoothLev k r l.castSucc D f →
    ∀ c ∈ OmX r, ∀ g₁ ∈ Glev k r l.succ, w1 k r l (c l) * g₁ ∈ D →
      EH k r (eI k r l) (eI k r l) f (w1 k r l (c l) * g₁) = pOp l (fun c' => f (w1 k r l (c' l) * g₁)) c ∧
      EH k r (esI k r l) (esI k r l) f (w1 k r l (c l) * g₁) = -pbOp l (fun c' => f (w1 k r l (c' l) * g₁)) c
def YLeibniz : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1))
    (D : Set (Mx k r)) (a b c : Fin (mdim k r i)) (f : Mx k r → E), IsOpen D → SmoothLev k r i D f →
    ∀ g ∈ Glev k r i ∩ D,
      EH k r (posL k r i a) (posL k r i b) (fun x => yv k r z i x c • f x) g =
        yv k r z i g c • EH k r (posL k r i a) (posL k r i b) f g - (if a = c then yv k r z i g b • f g else 0) ∧
      EH k r (posL k r i a) (posL k r i b) (fun x => ybv k r z i x c • f x) g =
        ybv k r z i g c • EH k r (posL k r i a) (posL k r i b) f g + (if b = c then ybv k r z i g a • f g else 0)
def TInvariant : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1))
    (D : Set (Mx k r)) (f : Mx k r → E) (Y : ℂ) (p q : Fin 2), inWb k r z → inWb k r z' → IsDom k r z z' i D →
    SmoothLev k r i D f → ∀ s ∈ Slev k r z i, ∀ s' ∈ Slev k r z' i, ∀ g ∈ Glev k r i ∩ D,
      tL k r z z' i Y p q (fun x => f (s * x * s')) g = tL k r z z' i Y p q f (s * g * s')
def TPreservesFF : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (i : Fin (r + 1)) (D : Set (Mx k r)) (Y : ℂ) (p q : Fin 2), inWb k r z → inWb k r z' → IsDom k r z z' i D →
    ∀ J ∈ FFl k r z z' π π' i D, tL k r z z' i Y p q J ∈ FFl k r z z' π π' i D
def TLinLoc : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1))
    (D : Set (Mx k r)) (Y : ℂ) (p q : Fin 2) (f f₂ : Mx k r → E) (s : ℂ), IsOpen D →
    SmoothLev k r i D f → SmoothLev k r i D f₂ → ∀ g ∈ Glev k r i ∩ D,
      tL k r z z' i Y p q (fun x => f x + s • f₂ x) g = tL k r z z' i Y p q f g + s • tL k r z z' i Y p q f₂ g ∧
      ((∀ x ∈ Glev k r i ∩ D, f x = f₂ x) → tL k r z z' i Y p q f g = tL k r z z' i Y p q f₂ g)
section Chain
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
abbrev Fn (k r : ℕ) (E : Type*) := (Fin r → ℂ) → Mx k r → E
def grp {k r : ℕ} (Θ : (Mx k r → E) → Mx k r → E) : Fn k r E → Fn k r E := fun Φ c => Θ (Φ c)
def crd {k r : ℕ} (R : ((Fin r → ℂ) → E) → (Fin r → ℂ) → E) : Fn k r E → Fn k r E :=
  fun Φ c g => R (fun c' => Φ c' g) c
abbrev OM (X : Type*) := Fin 2 → Fin 2 → X → X
def oMul {X : Type*} [AddCommMonoid X] (M N : OM X) : OM X := fun a b f => ∑ c : Fin 2, M a c (N c b f)
def TL (k : ℕ) {r : ℕ} (l : Fin r) (Y : ℂ) : OM (Fn k r E) := fun a b => crd (Tmat l Y a b)
def TLs (k : ℕ) {r : ℕ} (l : Fin r) (Y : ℂ) : OM (Fn k r E) := fun a b => crd (TmatStar l Y a b)
def QL (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (Y : ℂ) : OM (Fn k r E) :=
  fun a b => grp (tL k r z z' i Y a b)
def res1 (k r : ℕ) (l : Fin r) (J : Mx k r → E) : Fn k r E :=
  fun c g => ((‖c l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ) • J (w1 k r l (c l) * g)
def resG (k r : ℕ) (i : Fin (r + 1)) (J : Mx k r → E) : Fn k r E :=
  fun c g => ((∏ a : Fin r, (if a.val < i.val then ‖c a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ) •
    J (wCell k r i c * g)
def sandw (k r : ℕ) (Y : ℂ) : ℕ → OM (Fn k r E) → OM (Fn k r E)
  | 0, M => M
  | i + 1, M => sandw k r Y i (if h : i < r then oMul (TLs k ⟨i, h⟩ Y) (oMul M (TL k ⟨i, h⟩ Y)) else M)
def vAB (r : ℕ) (Y : ℂ) : ℕ → (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)
  | 0 => (id, fun _ => 0)
  | i + 1 =>
    if h : i < r then
      (fun f => Y • (vAB r Y i).1 f + pOp ⟨i, h⟩ ((vAB r Y i).1 f) - cOp ⟨i, h⟩ ((vAB r Y i).2 f),
        fun f => ciOp ⟨i, h⟩ ((vAB r Y i).1 f))
    else vAB r Y i
def vABs (r : ℕ) (Y : ℂ) : ℕ → (((Fin r → ℂ) → E) → (Fin r → ℂ) → E) × (((Fin r → ℂ) → E) → (Fin r → ℂ) → E)
  | 0 => (id, fun _ => 0)
  | i + 1 =>
    if h : i < r then
      (fun f => (vABs r Y i).1 (Y • f - pbOp ⟨i, h⟩ f) - (vABs r Y i).2 (cbOp ⟨i, h⟩ f),
        fun f => (vABs r Y i).1 (cbiOp ⟨i, h⟩ f))
    else vABs r Y i
def cmp {X : Type*} (v : X × X) (a : Fin 2) : X := if a = 0 then v.1 else v.2
end Chain
def ChainStep : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (l : Fin r) (D : Set (Mx k r)) (Y : ℂ) (a b : Fin 2), inWb k r z → inWb k r z' →
    IsDom k r z z' l.castSucc D → ∀ J ∈ FFl k r z z' π π' l.castSucc D,
    ∀ c ∈ OmX r, ∀ g ∈ Glev k r l.succ, w1 k r l (c l) * g ∈ D →
      res1 k r l (tL k r z z' l.castSucc Y a b J) c g =
        oMul (TLs k l Y) (oMul (QL k r z z' l.succ Y) (TL k l Y)) a b (res1 k r l J) c g
def ChainStepRaw : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (l : Fin r) (D : Set (Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' →
    IsDom k r z z' l.castSucc D → ∀ J ∈ FFl k r z z' π π' l.castSucc D,
    ∀ c ∈ OmX r, ∀ g ∈ Glev k r l.succ, w1 k r l (c l) * g ∈ D →
      let Φ : Fn k r (Wq →L[ℂ] Wp) := fun c' x => J (w1 k r l (c' l) * x)
      let u : ℂ := uC k r l.castSucc Y
      let Pp : Fn k r (Wq →L[ℂ] Wp) → Fn k r (Wq →L[ℂ] Wp) := fun Ψ => u • Ψ + crd (pOp l) Ψ
      let Pm : Fn k r (Wq →L[ℂ] Wp) → Fn k r (Wq →L[ℂ] Wp) :=
        fun Ψ => (u - (Mdim k r l : ℂ) + 1) • Ψ - crd (pbOp l) Ψ
      capL k r l.castSucc u J (w1 k r l (c l) * g) =
        (Pp (QL k r z z' l.succ Y 0 0 (Pm Φ)) + Pp (crd (cbiOp l) (QL k r z z' l.succ Y 1 0 Φ)) +
          crd (ciOp l) (QL k r z z' l.succ Y 0 1 (Pm Φ)) +
          crd (ciOp l) (crd (cbiOp l) (QL k r z z' l.succ Y 1 1 Φ))) c g
def SmoothFam {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + 1))
    (U₀ : Set ((Fin r → ℂ) × Mx k r)) (Φ : Fn k r E) : Prop :=
  ∀ x₀ ∈ U₀, x₀.2 ∈ Glev k r i → ∃ (U : Set ((Fin r → ℂ) × Mx k r)) (F : (Fin r → ℂ) × Mx k r → E),
    IsOpen U ∧ x₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ x ∈ U, x.2 ∈ Glev k r i → Φ x.1 x.2 = F x
def FamFF {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (i : Fin (r + 1)) (Dc : (Fin r → ℂ) → Set (Mx k r)) (Φ : Fn k r (Wq →L[ℂ] Wp)) : Prop :=
  SmoothFam k r i {x | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1} Φ ∧ ∀ c ∈ OmX r, Φ c ∈ FFl k r z z' π π' i (Dc c)
def TJointSmooth : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1))
    (U₀ : Set ((Fin r → ℂ) × Mx k r)) (Φ : Fn k r E) (Y : ℂ) (p q : Fin 2), IsOpen U₀ → SmoothFam k r i U₀ Φ →
      SmoothFam k r i U₀ (fun c g => tL k r z z' i Y p q (Φ c) g)
def ResMem : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (l : Fin r) (D : Set (Mx k r)), inWb k r z → inWb k r z' → IsDom k r z z' l.castSucc D →
    ∀ J ∈ FFl k r z z' π π' l.castSucc D,
      (∀ c : ℂ, c ≠ 0 →
        IsDom k r z z' l.succ {g | w1 k r l c * g ∈ D} ∧
        (fun g => J (w1 k r l c * g)) ∈ FFl k r z z' π π' l.succ {g | w1 k r l c * g ∈ D}) ∧
      FamFF k r z z' π π' l.succ (fun c => {g | w1 k r l (c l) * g ∈ D}) (res1 k r l J)
def FamOps : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (i : Fin (r + 1)) (Dc : (Fin r → ℂ) → Set (Mx k r)) (Φ : Fn k r (Wq →L[ℂ] Wp)), inWb k r z → inWb k r z' →
    IsOpen {x : (Fin r → ℂ) × Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1} → FamFF k r z z' π π' i Dc Φ →
    ∀ (a : Fin r) (j : Fin 6), FamFF k r z z' π π' i Dc (crd (opL a j) Φ)
def ResGFam : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Mx k r)), inWb k r z → inWb k r z' → IsDom k r z z' 0 D →
    ∀ J ∈ FFl k r z z' π π' 0 D, ∀ i : Fin (r + 1),
      FamFF k r z z' π π' i (fun c => {g | wCell k r i c * g ∈ D}) (resG k r i J)
def ResSurj : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (l : Fin r) (D₁ : Set (Mx k r)) (φ : ℂ → ℂ) (Ψ : Mx k r → (Wq →L[ℂ] Wp)), inWb k r z → inWb k r z' →
    IsDom k r z z' l.succ D₁ → ContDiffOn ℝ ∞ φ {c | c ≠ 0} → Ψ ∈ FFl k r z z' π π' l.succ D₁ →
    ∃ D₀ : Set (Mx k r), IsDom k r z z' l.castSucc D₀ ∧ D₀ ⊆ cellD k r l ∧
      (∀ c, c ≠ 0 → ∀ g ∈ Glev k r l.succ, (w1 k r l c * g ∈ D₀ ↔ g ∈ D₁)) ∧
      ∃ J ∈ FFl k r z z' π π' l.castSucc D₀, ∀ c, c ≠ 0 → ∀ g ∈ Glev k r l.succ ∩ D₁, J (w1 k r l c * g) = φ c • Ψ g
def CellDecomp : Prop :=
  ∀ (k r : ℕ) (l : Fin r), ∀ g ∈ Glev k r l.castSucc ∩ cellD k r l, ∃ n ∈ Nlev k r l.castSucc, ∃ n' ∈ Nlev k r l.castSucc,
    ∃ g₁ ∈ Glev k r l.succ, g = n * (w1 k r l (herm (Hpk k r) (g *ᵥ bvec (eI k r l)) (bvec (eI k r l))) * g₁) * n'
def CellDense : Prop :=
  ∀ (k r : ℕ) (l : Fin r), Glev k r l.castSucc ⊆ closure (Glev k r l.castSucc ∩ cellD k r l)
def ChainAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (i : Fin (r + 1)) (D : Set (Mx k r)) (Y : ℂ) (a b : Fin 2), inWb k r z → inWb k r z' →
    IsDom k r z z' 0 D → ∀ J ∈ FFl k r z z' π π' 0 D,
    ∀ c ∈ OmX r, ∀ g ∈ Glev k r i, wCell k r i c * g ∈ D →
      resG k r i (tL k r z z' 0 Y a b J) c g = sandw k r Y i.val (QL k r z z' i Y) a b (resG k r i J) c g
def CVv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (i : Fin (r + 1)) (D : Set (Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' →
    IsDom k r z z' 0 D → ∀ J ∈ FFl k r z z' π π' 0 D,
    ∀ c ∈ OmX r, ∀ g ∈ Glev k r i, wCell k r i c * g ∈ D →
      resG k r i (CV k r Y J) c g =
        (∑ a : Fin 2, ∑ b : Fin 2, crd (cmp (vABs r Y i.val) a)
          (QL k r z z' i Y a b (crd (cmp (vAB r Y i.val) b) (resG k r i J)))) c g
def VMonic : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (r i : ℕ), i ≤ r →
    ∃ a : ℕ → ((Fin r → ℂ) → E) → (Fin r → ℂ) → E, ∀ (Y : ℂ), ∀ f ∈ WSm r E,
      (vAB r Y i).1 f = Y ^ i • f + ∑ j ∈ Finset.range i, Y ^ j • a j f
def ChainStepFromRules : Prop :=
  BorderE → BorderS → BorderFull → EabGlLev → EabPres → QMinorLeftH → RuleRight → RuleLeft → RuleTorus → WeylLevelElementFacts →
    ChainStepRaw ∧ ChainStep
def ChainFromStep : Prop :=
  ChainStep → ResMem → ResGFam → FamOps → TPreservesFF → TLinLoc → WeylLevelElementFacts → ChainAll ∧ CVv
def CptOn (k r : ℕ) (i : Fin (r + 1)) (f : Mx k r → ℂ) : Prop :=
  ∃ K : Set (Mx k r), IsCompact K ∧ ∀ g ∈ Glev k r i, g ∉ K → f g = 0
def inLieLev (k r : ℕ) (i : Fin (r + 1)) (X : Mx k r) : Prop :=
  Xᴴ * Hpk k r + Hpk k r * X = 0 ∧ ∀ a : Fin r, a.val < i.val →
    X *ᵥ bvec (eI k r a) = 0 ∧ X *ᵥ bvec (esI k r a) = 0
def RdSkew : Prop :=
  ∀ (k r : ℕ) (i : Fin (r + 1)) (μ : Measure (Mt k r)), B.IsHaarOn (Glev k r i) μ →
    ∀ (X : Mx k r) (f₁ f₂ : Mx k r → ℂ), inLieLev k r i X → SmoothLev k r i Set.univ f₁ → SmoothLev k r i Set.univ f₂ →
      CptOn k r i f₁ → CptOn k r i f₂ →
      (∫ x : Mt k r, RdV X f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ) =
        -∫ x : Mt k r, f₁ (Matrix.of x) * star (RdV X f₂ (Matrix.of x)) ∂μ
def HermHaar : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (μ : Measure (Mt k r)),
    B.IsHaarOn (Glev k r i) μ → inWb k r z → inWb k r z' →
    ∀ (f₁ f₂ : Mx k r → ℂ), SmoothLev k r i Set.univ f₁ → SmoothLev k r i Set.univ f₂ →
      CptOn k r i f₁ → CptOn k r i f₂ → ∀ (Y : ℂ) (a b : Fin 2),
      (∫ x : Mt k r, tL k r z z' i Y a b f₁ (Matrix.of x) * star (f₂ (Matrix.of x)) ∂μ) =
        ∫ x : Mt k r, f₁ (Matrix.of x) * star (tL k r z z' i (star Y) b a f₂ (Matrix.of x)) ∂μ
def HermFromSteps : Prop :=
  RdSkew → StarMinor → ContractionsCovariant → MoveVec → MoveCov → YLeibniz → EabGlLev → EabPres → HermHaar
def zetaL (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (g : Mx k r) : ℂ :=
  herm (Hpk k r) (g *ᵥ fvec k r z' i) (fvec k r z i)
def GGl (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) : ℝ :=
  Complex.normSq (zetaL k r z z' (Fin.last r) g) - Tz k r z * Tz k r z'
def Leading : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)),
    inWb k r z → inWb k r z' →
    ∃ A : Fin 2 → Fin 2 → ℕ → (Mx k r → E) → Mx k r → E, ∀ (D : Set (Mx k r)) (f : Mx k r → E), IsOpen D →
      SmoothLev k r i D f → ∀ g ∈ Glev k r i ∩ D, ∀ Y : ℂ,
        tL k r z z' i Y 0 0 f g = Y ^ mdim k r i • f g + ∑ j ∈ Finset.range (mdim k r i), Y ^ j • A 0 0 j f g ∧
        tL k r z z' i Y 0 1 f g = -((zetaL k r z z' i g * Y ^ (mdim k r i - 1)) • f g) +
          ∑ j ∈ Finset.range (mdim k r i - 1), Y ^ j • A 0 1 j f g ∧
        tL k r z z' i Y 1 0 f g = -((star (zetaL k r z z' i g) * Y ^ (mdim k r i - 1)) • f g) +
          ∑ j ∈ Finset.range (mdim k r i - 1), Y ^ j • A 1 0 j f g ∧
        tL k r z z' i Y 1 1 f g = ∑ j ∈ Finset.range (mdim k r i - 1), Y ^ j • A 1 1 j f g
def Chat2Adapted : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin (n + 2) → Fin (n + 2) → A)
    (P Q : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ), GlRel E → Q * P = 1 → P * Q = 1 →
    ∀ (u : ℂ) (β β' : Fin (n + 2) → ℂ), (∀ j : Fin (n + 2), 2 ≤ j.val → (β ᵥ* P) j = 0 ∧ (β' ᵥ* P) j = 0) →
      chat2A E u (fun p => P p 0) (fun p => P p 1) β β' =
        ((β ᵥ* P) 0 * (β' ᵥ* P) 1 - (β ᵥ* P) 1 * (β' ᵥ* P) 0) • qminor (Econj E P Q) (skip2 0 1) (skip2 0 1) u
def ChatAdapted : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → A)
    (P Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), GlRel E → Q * P = 1 → P * Q = 1 →
    ∀ (u : ℂ) (β : Fin (n + 1) → ℂ), (∀ j : Fin (n + 1), j ≠ Fin.last n → (β ᵥ* P) j = 0) →
      chatA E u (fun p => P p (Fin.last n)) β =
        (β ᵥ* P) (Fin.last n) • qminor (Econj E P Q) (skip1 (Fin.last n)) (skip1 (Fin.last n)) u
section Types
variable {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
def dRep {n : ℕ} (π : Matrix (Fin n) (Fin n) ℂ → (Wp →L[ℂ] Wp)) (X : Matrix (Fin n) (Fin n) ℂ) (v : Wp) : Wp :=
  deriv (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) v) 0
def EcRep {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (Wp →L[ℂ] Wp))
    (Z : Matrix (Fin n) (Fin n) ℂ) (v : Wp) : Wp :=
  dRep π (hpart1 H Z) v + Complex.I • dRep π (hpart2 H Z) v
def unitB {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (Bs : Fin m → Fin n → ℂ) (a b : Fin m) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun p q => Bs a p * herm H (bvec q) (Bs b)
def qmF {X : Type*} [AddCommGroup X] [Module ℂ X] {n t : ℕ} (Eop : Fin n → Fin n → X → X)
    (a b : Fin t → Fin n) (u : ℂ) (x : X) : X :=
  ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ) •
    (List.ofFn fun k : Fin t => fun y : X =>
      (if a (σ k) = b k then (u - ((k : ℕ) : ℂ)) • y else 0) + Eop (a (σ k)) (b k) y).foldr (fun T h => T h) x)
def qmFrev {X : Type*} [AddCommGroup X] [Module ℂ X] {n t : ℕ} (Eop : Fin n → Fin n → X → X)
    (a b : Fin t → Fin n) (u : ℂ) (x : X) : X :=
  ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ) •
    (List.ofFn fun k : Fin t => fun y : X =>
      (if a (σ k) = b k then (u - ((k : ℕ) : ℂ)) • y else 0) + Eop (a (σ k)) (b k) y).foldl (fun h T => T h) x)
def IsFrameOf (k r : ℕ) {m : ℕ} (vs : List (Fin (2 * r + k + 1) → ℂ)) (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) : Prop :=
  (∀ a, inWb k r (Bs a)) ∧ (∀ a b, herm (Hpk k r) (Bs a) (Bs b) = if a = b then 1 else 0) ∧
    ∀ a, ∀ v ∈ vs, herm (Hpk k r) (Bs a) v = 0
def capRep (k r : ℕ) {m : ℕ} (π : Mx k r → (Wp →L[ℂ] Wp)) (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (w : ℂ) (v : Wp) : Wp :=
  qmF (fun a b => EcRep (Hpk k r) π (unitB (Hpk k r) Bs a b)) id id w v
def CapParam (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) : Prop :=
  ∀ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [z] Bs → ∀ (w : ℂ) (v : Wp),
    capRep k r π Bs w v = (∏ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (u i : ℂ))) • v
def IsType (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) : Prop :=
  Nontrivial Wp ∧ IsCRepOn (UWset k r z) π ∧ ContinuousOn π (UWset k r z) ∧ (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) ∧
    (∀ S : Submodule ℂ Wp, (∀ h ∈ UWset k r z, ∀ v ∈ S, π h v ∈ S) → S = ⊥ ∨ S = ⊤) ∧ CapParam k r z π u
end Types
section RZ
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def RZ {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => RdV (hpart1 H Z) f g + Complex.I • RdV (hpart2 H Z) f g
def LdV {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => deriv (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X) * g)) 0
def LZ {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => LdV (hpart1 H Z) f g + Complex.I • LdV (hpart2 H Z) f g
def capR (k r : ℕ) {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (w : ℂ) (f : Mx k r → E) : Mx k r → E :=
  qmF (fun a b => RZ (Hpk k r) (unitB (Hpk k r) Bs a b)) id id w f
def capLft (k r : ℕ) {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (w : ℂ) (f : Mx k r → E) : Mx k r → E :=
  qmFrev (fun a b => LZ (Hpk k r) (unitB (Hpk k r) Bs a b)) id id w f
end RZ
def CapelliIdentityEntry : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (D : Set (Mx k r)) (f : Mx k r → E), inWb k r z → inWb k r z' → IsOpen D → SmoothLev k r (Fin.last r) D f →
    ∀ g ∈ Glev k r (Fin.last r) ∩ D, GGl k r z z' g ≠ 0 →
    ∀ Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [g⁻¹ *ᵥ z, z'] Bs → ∀ Y : ℂ,
      tL k r z z' (Fin.last r) Y 1 1 f g = (GGl k r z z' g : ℂ) • capR k r Bs (Y + ((k : ℂ) - 2) / 2) f g
def RightTypeAction : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wq]
    (k r m : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Mx k r)), inWb k r z → inWb k r z' → IsDom k r z z' (Fin.last r) D →
    IsCRepOn (UWset k r z') π' → ContinuousOn π' (UWset k r z') →
    ∀ J ∈ FFl k r z z' π π' (Fin.last r) D, ∀ g ∈ Glev k r (Fin.last r) ∩ D,
    ∀ Bs : Fin m → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [z'] Bs → ∀ (w : ℂ) (v : Wq),
      capR k r Bs w J g v = J g (capRep k r π' Bs w v)
def LeftTypeAction : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp]
    (k r m : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Mx k r)), inWb k r z → inWb k r z' → IsDom k r z z' (Fin.last r) D →
    IsCRepOn (UWset k r z) π → ContinuousOn π (UWset k r z) →
    ∀ J ∈ FFl k r z z' π π' (Fin.last r) D, ∀ g ∈ Glev k r (Fin.last r) ∩ D,
    ∀ Bs : Fin m → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [z] Bs → ∀ (w : ℂ) (v : Wq),
      capLft k r Bs w J g v = capRep k r π Bs w (J g v)
def Branching : Prop :=
  ∀ (Wp : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp] (P : M.Par), P.OK → P.u' = P.u →
    ∀ (z e : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)), inWb P.k P.r z → 0 < Tz P.k P.r z →
    IsType P.k P.r z π P.u → inWb P.k P.r e → herm (Hpk P.k P.r) e z = 0 → herm (Hpk P.k P.r) e e = 1 →
    ∃ S : M.Ty P → Submodule ℂ Wp, DirectSum.IsInternal S ∧
      (∀ ρ, S ρ ≠ ⊥ ∧ ∀ S' : Submodule ℂ Wp, S' ≤ S ρ →
        (∀ h ∈ UWset P.k P.r z, h *ᵥ e = e → ∀ v ∈ S', π h v ∈ S') → S' = ⊥ ∨ S' = S ρ) ∧
      ∀ Bs : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ, IsFrameOf P.k P.r [z, e] Bs → ∀ (ρ : M.Ty P) (w : ℂ), ∀ v ∈ S ρ,
        capRep P.k P.r π Bs w v = M.xC P ρ (w - ((P.k : ℂ) - 2) / 2) • v
def IsPlace {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) : Prop :=
  P.OK ∧ inWb P.k P.r z ∧ inWb P.k P.r z' ∧ Tz P.k P.r z = P.T ∧ Tz P.k P.r z' = P.T' ∧
    IsType P.k P.r z π P.u ∧ IsType P.k P.r z' π' P.u'
def RadialDecompositionSpectral : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (D : Set (Mx P.k P.r)),
    IsPlace P z z' π π' → IsDom P.k P.r z z' (Fin.last P.r) D → (∀ g ∈ D, GGl P.k P.r z z' g ≠ 0) →
    ∀ J ∈ FFl P.k P.r z z' π π' (Fin.last P.r) D, ∃ dec : M.Ty P → Mx P.k P.r → (Wq →L[ℂ] Wp),
      (∀ ρ, dec ρ ∈ FFl P.k P.r z z' π π' (Fin.last P.r) D) ∧
      (∀ g ∈ Glev P.k P.r (Fin.last P.r) ∩ D, J g = ∑ ρ, dec ρ g) ∧
      ∀ (ρ : M.Ty P) (Y : ℂ), ∀ g ∈ Glev P.k P.r (Fin.last P.r) ∩ D,
        tL P.k P.r z z' (Fin.last P.r) Y 1 1 (dec ρ) g = ((GGl P.k P.r z z' g : ℂ) * M.xC P ρ Y) • dec ρ g
def RadialDecompositionOfParts : Prop :=
  Chat2Adapted → ContractionsCovariant → CapelliIdentityEntry → RightTypeAction → Branching → TPreservesFF → RadialDecompositionSpectral
def TTriples : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ) (l : Fin m), ∀ f ∈ WSm m E,
    (cOp l (ciOp l f) = f ∧ ciOp l (cOp l f) = f ∧ pOp l (cOp l f) = cOp l (pOp l f) + cOp l f) ∧
    (cbiOp l (cbOp l f) = f ∧ cbOp l (cbiOp l f) = f ∧
      -pbOp l (-cbiOp l f) = -cbiOp l (-pbOp l f) + -cbiOp l f) ∧
    ∀ i j : Fin 6, (holoIdx i ↔ ¬ holoIdx j) → opL l i (opL l j f) = opL l j (opL l i f)
def RTTAt (k r : ℕ) (i : Fin (r + 1)) : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Mx k r)), inWb k r z → inWb k r z' → IsDom k r z z' i D →
    ∀ J ∈ FFl k r z z' π π' i D, ∀ g ∈ Glev k r i ∩ D, ∀ (u v : ℂ) (a b c d : Fin 2),
      (u - v) • (tL k r z z' i u a b (tL k r z z' i v c d J) g - tL k r z z' i v c d (tL k r z z' i u a b J) g) =
        tL k r z z' i u c b (tL k r z z' i v a d J) g - tL k r z z' i v c b (tL k r z z' i u a d J) g
def RTTLevel : Prop := ∀ (k r : ℕ) (i : Fin (r + 1)), RTTAt k r i
def CapCommute : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (f : Mx k r → E),
    IsOpen D → SmoothLev k r i D f → ∀ g ∈ Glev k r i ∩ D, ∀ u v : ℂ,
      capL k r i u (capL k r i v f) g = capL k r i v (capL k r i u f) g
def RTTSandwich : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (QQ : ℂ → Matrix (Fin 2) (Fin 2) A) (p c ci p' c' ci' : A),
    YangianSpanCharacter.T.WeylRel p c ci → YangianSpanCharacter.T.WeylRel p' c' ci' →
    (∀ x ∈ ({p, c, ci} : Set A), ∀ y ∈ ({p', c', ci'} : Set A), x * y = y * x) →
    (∀ x ∈ ({p, c, ci, p', c', ci'} : Set A), ∀ Y a b, x * QQ Y a b = QQ Y a b * x) →
    ∀ Y Y' : ℂ,
      let C : ℂ → A := fun y => (YangianSpanCharacter.T.Tm y p' c' ci' * QQ y * YangianSpanCharacter.T.Tm y p c ci) 0 0
      let X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
        ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - YangianSpanCharacter.T.Pf A) * YangianSpanCharacter.T.E1 (QQ Y') * YangianSpanCharacter.T.E2 (QQ Y) -
          YangianSpanCharacter.T.E2 (QQ Y) * YangianSpanCharacter.T.E1 (QQ Y') * ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - YangianSpanCharacter.T.Pf A)
      algebraMap ℂ A (Y' - Y - 1) * (C Y' * C Y - C Y * C Y') =
        ((YangianSpanCharacter.T.T2 Y p' c' ci' * YangianSpanCharacter.T.T1 Y' p' c' ci') * X * (YangianSpanCharacter.T.T1 Y' p c ci * YangianSpanCharacter.T.T2 Y p c ci)) (0, 0) (0, 0)
def RTTIndependence : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (x : Fin 2 × Fin 2 → Fin 2 × Fin 2 → V) (Y Y' : ℂ), Y' ≠ Y + 1 →
    (∀ (c : ℂ), c ≠ 0 → ∀ (β : ℂ) (n : ℤ),
      ∑ A : Fin 2 × Fin 2, ∑ B : Fin 2 × Fin 2,
        ((if A = (0, 0) then (Y - β) * (Y' - β) else if A = (0, 1) then Y' - β else if A = (1, 0) then Y - β + 1 else 1) *
          (if B = (0, 0) then (Y' + (β + n)) * (Y + (β + n)) else if B = (0, 1) then Y' + (β + n) - 1
            else if B = (1, 0) then Y + (β + n) else 1) *
          (((‖c‖ : ℂ) ^ (2 * β)) * c ^ n * (c ^ ((B.1 : ℕ) + (B.2 : ℕ)))⁻¹ * (star c ^ ((A.1 : ℕ) + (A.2 : ℕ)))⁻¹)) • x A B = 0) →
    ∀ A B, x A B = 0
def RTTUpper : Prop := ∀ (k r : ℕ) (l : Fin r), RTTAt k r l.succ
def RTTUpperFromSteps : Prop :=
  ChainStep → ResSurj → CapCommute → TPreservesFF → TTriples → RTTSandwich → RTTIndependence → Leading → TLinLoc →
    RTTUpper
def FFTransfer : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r' : ℕ) (z z' : Fin (2 * r' + k + 1) → ℂ) (π : Mx k r' → (Wp →L[ℂ] Wp)) (π' : Mx k r' → (Wq →L[ℂ] Wq))
    (D : Set (Mx k r')), inWb k r' z → inWb k r' z' → IsDom k r' z z' 0 D → ∀ J ∈ FFl k r' z z' π π' 0 D,
    ∃ (π₁ : Mx k (1 + r') → (Wp →L[ℂ] Wp)) (π₁' : Mx k (1 + r') → (Wq →L[ℂ] Wq)) (D₁ : Set (Mx k (1 + r')))
      (f : Mx k (1 + r') → (Wq →L[ℂ] Wp)),
      inWb k (1 + r') (liftVec k 1 r' z) ∧ inWb k (1 + r') (liftVec k 1 r' z') ∧
      IsDom k (1 + r') (liftVec k 1 r' z) (liftVec k 1 r' z') ⟨1, by omega⟩ D₁ ∧
      f ∈ FFl k (1 + r') (liftVec k 1 r' z) (liftVec k 1 r' z') π₁ π₁' ⟨1, by omega⟩ D₁ ∧
      ∀ g ∈ UH (Hpk k r'), (ιLev k 1 r' g ∈ D₁ ↔ g ∈ D) ∧ f (ιLev k 1 r' g) = J g
def RTTLevelFromUpper : Prop := RTTUpper → LevelTransfer → GlevImage → FFTransfer → TLinLoc → RTTLevel
def epsJ (c d : Fin 2) : ℂ := if c = 0 ∧ d = 1 then 1 else if c = 1 ∧ d = 0 then -1 else 0
def DetAt (i : (P : M.Par) → Fin (P.r + 1)) : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (D : Set (Mx P.k P.r)),
    IsPlace P z z' π π' → IsDom P.k P.r z z' (i P) D →
    ∀ J ∈ FFl P.k P.r z z' π π' (i P) D, ∀ g ∈ Glev P.k P.r (i P) ∩ D, ∀ (Y : ℂ) (c d : Fin 2),
      (tL P.k P.r z z' (i P) (Y + 1) 0 c (tL P.k P.r z z' (i P) Y 1 d J) g -
          tL P.k P.r z z' (i P) (Y + 1) 1 c (tL P.k P.r z z' (i P) Y 0 d J) g = (M.qC P Y * epsJ c d) • J g) ∧
      (tL P.k P.r z z' (i P) Y c 0 (tL P.k P.r z z' (i P) (Y + 1) d 1 J) g -
          tL P.k P.r z z' (i P) Y c 1 (tL P.k P.r z z' (i P) (Y + 1) d 0 J) g = (M.qC P Y * epsJ c d) • J g)
def DetLevel : Prop := ∀ i : (P : M.Par) → Fin (P.r + 1), DetAt i
def QdetFromRTT : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (QQ : ℂ → Matrix (Fin 2) (Fin 2) A), W.IsRTT QQ → ∀ Y : ℂ, ∃ qh : A,
    (QQ (Y + 1))ᵀ * YangianSpanCharacter.T.J A * QQ Y = qh • YangianSpanCharacter.T.J A ∧ QQ Y * YangianSpanCharacter.T.J A * (QQ (Y + 1))ᵀ = qh • YangianSpanCharacter.T.J A ∧
    ∀ Y' a b, qh * QQ Y' a b = QQ Y' a b * qh
def qhat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)
    (f : Mx k r → E) : Mx k r → E :=
  fun g => tL k r z z' (Fin.last r) (Y + 1) 0 0 (tL k r z z' (Fin.last r) Y 1 1 f) g -
    tL k r z z' (Fin.last r) (Y + 1) 1 0 (tL k r z z' (Fin.last r) Y 0 1 f) g
def IsRegular (k r : ℕ) (f : Mx k r → ℂ) : Prop :=
  ∃ p : MvPolynomial ((Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) ℂ,
    ∀ g, f g = MvPolynomial.eval (Sum.elim (fun x => g x.1 x.2) (fun x => g⁻¹ x.1 x.2)) p
def DetHatOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (D : Set (Mx k r)) (f : Mx k r → E) : Prop :=
  ∀ (Bs Bs' : Fin k → Fin (2 * r + k + 1) → ℂ), IsFrameOf k r [z] Bs → IsFrameOf k r [z'] Bs' →
    ∀ g ∈ Glev k r (Fin.last r) ∩ D, ∀ Y : ℂ,
      qhat k r z z' Y f g =
        -((Tz k r z * Tz k r z' : ℝ) : ℂ) • capLft k r Bs (Y + (k : ℂ) / 2) (capR k r Bs' (Y + (k : ℂ) / 2) f) g
def DetHat : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (D : Set (Mx k r))
    (f : Mx k r → E), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsOpen D →
    SmoothLev k r (Fin.last r) D f → DetHatOn k r z z' D f
def DetHatRegular : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (f : Mx k r → ℂ),
    inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsRegular k r f → DetHatOn k r z z' Set.univ f
def RegularToSmooth : Prop := DetHatRegular → DetHat
def InZZ (k : ℕ) (u u' : ℕ → ℝ) : Prop :=
  (∀ s ∈ Finset.Icc 2 k, max (u s) (u' s) < min (u (s - 1)) (u' (s - 1))) ∧ ∀ s ∈ Finset.Icc 1 k, u s ≠ u' s
def DetGeneric : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (f : Mx k r → ℂ) (u u' : ℕ → ℝ),
    inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsRegular k r f → InZZ k u u' →
    ∀ (Bs Bs' : Fin k → Fin (2 * r + k + 1) → ℂ), IsFrameOf k r [z] Bs → IsFrameOf k r [z'] Bs' →
    (∀ g ∈ Glev k r (Fin.last r), ∀ Y : ℂ,
      capLft k r Bs (Y + (k : ℂ) / 2) f g = (∏ i ∈ Finset.Icc 1 k, (Y + 1 / 2 + (u i : ℂ))) • f g ∧
      capR k r Bs' (Y + (k : ℂ) / 2) f g = (∏ i ∈ Finset.Icc 1 k, (Y + 1 / 2 + (u' i : ℂ))) • f g) →
    ∀ g ∈ Glev k r (Fin.last r), ∀ Y : ℂ,
      qhat k r z z' Y f g = (-((Tz k r z * Tz k r z' : ℝ) : ℂ) *
        ∏ i ∈ Finset.Icc 1 k, ((Y + 1 / 2 + (u i : ℂ)) * (Y + 1 / 2 + (u' i : ℂ)))) • f g
def LemmaD : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] (DD : ℕ → Set (A →+ A)), DD 0 = {0} →
    (∀ n, ∀ D ∈ DD (n + 1), ∀ a : A, ∃ D' ∈ DD n, ∀ b, D' b = D (a * b) - a * D b) →
    ∀ A' : AddSubgroup A, (∀ x ∈ A', ∀ y ∈ A', x * y ∈ A') →
    (∀ b : A, ∃ a₁ ∈ A', ∃ a₂ ∈ A', a₂ ≠ 0 ∧ a₂ * b = a₁) →
    ∀ n, ∀ D ∈ DD n, (∀ x ∈ A', D x = 0) → D = 0
def DetCoreFromSteps : Prop :=
  RTTLevel → QdetFromRTT → DetHat → RightTypeAction → LeftTypeAction → TPreservesFF → TLinLoc →
    DetAt fun P => Fin.last P.r
def DetLevelFromCore : Prop :=
  (DetAt fun P => Fin.last P.r) → ChainStep → ResMem → FamOps → TTriples → TPreservesFF → TLinLoc → TJointSmooth →
    CellDecomp → CellDense → DetLevel
def EigenCoeff : Prop :=
  ∀ (Vs : Type) [NormedAddCommGroup Vs] [NormedSpace ℂ Vs] (k r : ℕ) (σ : Mx k r → (Vs →L[ℂ] Vs)) (v : Vs)
    (lam : Fin (2 * r + k + 1) → ℂ), IsCRepOn (UH (Hpk k r)) σ → SmoothLev k r 0 Set.univ (fun g => σ g v) →
    (∀ u : ℂ, qmF (fun a b => EcRep (Hpk k r) σ (Matrix.single a b 1)) id id u v =
      (∏ s, (u - (((2 * r + k + 1 : ℕ) : ℂ) - 1) / 2 + lam s)) • v) →
    ∀ (ℓ : Vs →L[ℂ] ℂ) (Y : ℂ), ∀ g ∈ UH (Hpk k r),
      CV k r Y (fun x => ℓ (σ x v)) g = (∏ s, (Y + lam s)) • ℓ (σ g v)
def CkLev {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + 1)) (m : ℕ) (D : Set (Mx k r))
    (f : Mx k r → E) : Prop :=
  ∀ g₀ ∈ Glev k r i ∩ D, ∃ (U : Set (Mx k r)) (F : Mx k r → E),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ m F U ∧ ∀ g ∈ U, g ∈ Glev k r i → f g = F g
def OmPlus (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (Mx k r) :=
  {g | (∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' g l ≠ 0) ∧ 0 < Gf k r z z' g}
def BesselCommutes : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ) (F : Mx k r → (Wq →L[ℂ] Wp)) (Y : ℂ),
    2 * r + k + 1 ≤ m → ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < (A - 6 * r * m) / (9 * (r + 1)) → B.InCC A m F →
    B.InCC A m (CV k r Y F) →
    ∃ Jt : Mx k r → (Wq →L[ℂ] Wp), CkLev k r 0 (2 * r + k + 1) (OmPlus k r D.z D.z') Jt ∧
      LeftEq k r D.z 0 (OmPlus k r D.z D.z') Jt ∧ RightEq k r D.z' 0 (OmPlus k r D.z D.z') Jt ∧
      (∀ g ∈ Glev k r 0 ∩ OmPlus k r D.z D.z', ∀ h ∈ UWset k r D.z, ∀ h' ∈ UWset k r D.z',
        Jt (h * g * h') = (D.π h).comp ((Jt g).comp (D.π' h'))) ∧
      (∀ᵐ q ∂(volume.restrict (B.Qset D)), Jt (B.gq D q) = B.JF D F (B.gq D q)) ∧
      ∀ᵐ q ∂(volume.restrict (B.Qset D)), CV k r Y Jt (B.gq D q) = B.JF D (CV k r Y F) (B.gq D q)
def EigenBessel : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ) (F : Mx k r → (Wq →L[ℂ] Wp)) (Y PY : ℂ),
    2 * r + k + 1 ≤ m → ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < (A - 6 * r * m) / (9 * (r + 1)) → B.InCC A m F →
    (∀ g ∈ UH (Hpk k r), CV k r Y F g = PY • F g) →
    ∃ Jt : Mx k r → (Wq →L[ℂ] Wp), CkLev k r 0 (2 * r + k + 1) (OmPlus k r D.z D.z') Jt ∧
      LeftEq k r D.z 0 (OmPlus k r D.z D.z') Jt ∧ RightEq k r D.z' 0 (OmPlus k r D.z D.z') Jt ∧
      (∀ g ∈ Glev k r 0 ∩ OmPlus k r D.z D.z', ∀ h ∈ UWset k r D.z, ∀ h' ∈ UWset k r D.z',
        Jt (h * g * h') = (D.π h).comp ((Jt g).comp (D.π' h'))) ∧
      (∀ᵐ q ∂(volume.restrict (B.Qset D)), Jt (B.gq D q) = B.JF D F (B.gq D q)) ∧
      ∀ᵐ q ∂(volume.restrict (B.Qset D)), CV k r Y Jt (B.gq D q) = PY • Jt (B.gq D q)
def EigenBesselFromCommutes : Prop := BesselCommutes → B.CCLin → EigenBessel
def Pr (V : Type*) [AddCommGroup V] [Module ℂ V] : Type _ := Module.End ℂ V × (Module.End ℂ V)ᵐᵒᵖ
section PairRing
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
instance : Ring (Pr V) := inferInstanceAs (Ring (Module.End ℂ V × (Module.End ℂ V)ᵐᵒᵖ))
instance : Algebra ℂ (Pr V) :=
  RingHom.toAlgebra' ((algebraMap ℂ (Module.End ℂ V)).prod
      ((algebraMap ℂ (Module.End ℂ V)ᵐᵒᵖ).comp (starRingEnd ℂ)))
    (fun z x => Prod.ext (Algebra.commutes z x.1) (Algebra.commutes (starRingEnd ℂ z) x.2))
instance : StarRing (Pr V) where
  star x := (x.2.unop, MulOpposite.op x.1)
  star_involutive _ := rfl
  star_mul _ _ := rfl
  star_add _ _ := rfl
instance : StarModule ℂ (Pr V) where
  star_smul z x := by
    refine Prod.ext ?_ ?_
    · change x.2.unop * (algebraMap ℂ (Module.End ℂ V) (starRingEnd ℂ z)) =
        algebraMap ℂ (Module.End ℂ V) (starRingEnd ℂ z) * x.2.unop
      exact (Algebra.commutes _ _).symm
    · change MulOpposite.op (algebraMap ℂ (Module.End ℂ V) z * x.1) =
        MulOpposite.op (algebraMap ℂ (Module.End ℂ V) (starRingEnd ℂ (starRingEnd ℂ z))) * MulOpposite.op x.1
      rw [Complex.conj_conj, ← MulOpposite.op_mul, Algebra.commutes]
def mkP (X Xs : Module.End ℂ V) : Pr V := (X, MulOpposite.op Xs)
end PairRing
def DomR (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set ((Fin r → ℂ) × Mx k r) :=
  {x | x.1 ∈ OmX r ∧ x.2 ∈ Glev k r (Fin.last r) ∧ 0 < GGl k r z z' x.2}
def RadSp (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq)) :
    Submodule ℂ (Fn k r (Wq →L[ℂ] Wp)) where
  carrier := {Φ | (∀ x, x ∉ DomR k r z z' → Φ x.1 x.2 = 0) ∧
    (∀ x₀ ∈ DomR k r z z', ∃ (U : Set ((Fin r → ℂ) × Mx k r)) (F : (Fin r → ℂ) × Mx k r → (Wq →L[ℂ] Wp)),
      IsOpen U ∧ x₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ x ∈ U, x.2 ∈ Glev k r (Fin.last r) → Φ x.1 x.2 = F x) ∧
    (∀ x ∈ DomR k r z z', ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z',
      Φ x.1 (h * x.2 * h') = (π h).comp ((Φ x.1 x.2).comp (π' h')))}
  zero_mem' := ⟨fun _ _ => rfl, fun x₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩,
    fun _ _ _ _ _ _ => by simp⟩
  add_mem' := by
    rintro Φ Ψ ⟨h0, hs, he⟩ ⟨h0', hs', he'⟩
    refine ⟨fun x hx => by simp [h0 x hx, h0' x hx], fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
    · obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs x₀ hx₀
      obtain ⟨U', F', hU', hxU', hF', hΨ⟩ := hs' x₀ hx₀
      exact ⟨U ∩ U', F + F', hU.inter hU', ⟨hxU, hxU'⟩, (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right),
        fun x hx hg => by simp [hΦ x hx.1 hg, hΨ x hx.2 hg]⟩
    · simp only [Pi.add_apply]
      rw [he x hx h hh h' hh', he' x hx h hh h' hh']
      ext v
      simp
  smul_mem' := by
    rintro a Φ ⟨h0, hs, he⟩
    refine ⟨fun x hx => by simp [h0 x hx], fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
    · obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs x₀ hx₀
      exact ⟨U, a • F, hU, hxU, hF.const_smul a, fun x hx hg => by simp [hΦ x hx hg]⟩
    · simp only [Pi.smul_apply]
      rw [he x hx h hh h' hh']
      ext v
      simp
def fnVal (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (j : Fin 6) (g : Mx k r) : ℂ :=
  match j with
  | 0 => zetaL k r z z' (Fin.last r) g
  | 1 => (zetaL k r z z' (Fin.last r) g)⁻¹
  | 2 => star (zetaL k r z z' (Fin.last r) g)
  | 3 => (star (zetaL k r z z' (Fin.last r) g))⁻¹
  | 4 => (GGl k r z z' g : ℂ)
  | 5 => ((GGl k r z z' g : ℂ))⁻¹
def fnConj : Fin 6 → Fin 6 := ![2, 3, 0, 1, 4, 5]
structure ActualOps (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) {Wp Wq : Type*} [NormedAddCommGroup Wp]
    [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] (π : Mx k r → (Wp →L[ℂ] Wp))
    (π' : Mx k r → (Wq →L[ℂ] Wq)) where
  t : ℂ → Fin 2 → Fin 2 → Module.End ℂ (RadSp k r z z' π π')
  op : Fin r → Fin 6 → Module.End ℂ (RadSp k r z z' π π')
  fn : Fin 6 → Module.End ℂ (RadSp k r z z' π π')

  t_apply : ∀ Y a b (Φ : RadSp k r z z' π π'), ∀ x ∈ DomR k r z z',
    (t Y a b Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = tL k r z z' (Fin.last r) Y a b ((Φ : Fn k r (Wq →L[ℂ] Wp)) x.1) x.2
  op_apply : ∀ l i (Φ : RadSp k r z z' π π'), (op l i Φ : Fn k r (Wq →L[ℂ] Wp)) = crd (opL l i) (Φ : Fn k r (Wq →L[ℂ] Wp))
  fn_apply : ∀ j (Φ : RadSp k r z z' π π'), ∀ x ∈ DomR k r z z',
    (fn j Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = fnVal k r z z' j x.2 • (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2
def ActualOpsExist : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)), IsPlace P z z' π π' →
    Nonempty (ActualOps P.k P.r z z' π π')
def RadOps : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)), IsPlace P z z' π π' →
    ∀ Φ ∈ RadSp P.k P.r z z' π π',
      (∀ (l : Fin P.r) (j : Fin 6), crd (opL l j) Φ ∈ RadSp P.k P.r z z' π π' ∧
        ∀ Ψ ∈ RadSp P.k P.r z z' π π', ∀ s : ℂ,
          crd (opL l j) (Φ + s • Ψ) = crd (opL l j) Φ + s • crd (opL l j) Ψ) ∧
      ∀ j : Fin 6, (fun c g => (DomR P.k P.r z z').indicator
        (fun x => fnVal P.k P.r z z' j x.2 • Φ x.1 x.2) (c, g)) ∈ RadSp P.k P.r z z' π π'
def ActualOpsFromSteps : Prop := TPreservesFF → TLinLoc → TJointSmooth → RadOps → ActualOpsExist
section Level
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
def ActualOps.QQ (X : ActualOps k r z z' π π') (Y : ℂ) : Matrix (Fin 2) (Fin 2) (Pr (RadSp k r z z' π π')) :=
  Matrix.of fun a b => mkP (X.t Y a b) (X.t (star Y) b a)
def IsActualLevel (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r) : Prop :=
  (∀ l, L.p l = mkP (X.op l 0) (-X.op l 3)) ∧ (∀ l, L.pb l = mkP (X.op l 3) (-X.op l 0)) ∧
  (∀ l, L.c l = mkP (X.op l 1) (X.op l 4)) ∧ (∀ l, L.ci l = mkP (X.op l 2) (X.op l 5)) ∧
  (∀ l, L.cb l = mkP (X.op l 4) (X.op l 1)) ∧ (∀ l, L.cbi l = mkP (X.op l 5) (X.op l 2)) ∧
  L.ζ = mkP (X.fn 0) (X.fn 2) ∧ L.ζi = mkP (X.fn 1) (X.fn 3) ∧ L.ζb = mkP (X.fn 2) (X.fn 0) ∧
  L.ζbi = mkP (X.fn 3) (X.fn 1) ∧ L.GG = mkP (X.fn 4) (X.fn 4) ∧ L.GGi = mkP (X.fn 5) (X.fn 5) ∧
  L.TT = ((Tz k r z * Tz k r z' : ℝ) : ℂ)
end Level
def LevelStartActual : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)), IsPlace P z z' π π' →
    ∀ (X : ActualOps P.k P.r z z' π π') (l : ℕ),
      ∃ (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))),
        IsActualLevel X L ∧ (∀ Y, st.QQ Y = M.sgn P l • X.QQ Y) ∧ st.q = M.qC P ∧
        st.inv = {Y | ∀ ρ : M.Ty P, M.xC P ρ Y ≠ 0} ∧ Fr.IsStarLevel L ∧ Fr.IsLevelStart L st
structure NFData (P : M.Par) (𝒜 : Type) [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] where
  L : R.LevelData 𝒜 P.r
  κ : (M.Ty P → ℂ) →ₐ[ℂ] 𝒜
  SS : ℕ → 𝒜
namespace NFData
variable {P : M.Par} {𝒜 : Type} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] (d : NFData P 𝒜)
def x (Y : ℂ) : 𝒜 := d.κ fun ρ => M.xC P ρ Y
def weightedSumBis (Y : ℂ) : 𝒜 := ∑ l ∈ Finset.Icc 1 (P.k - 1), d.SS l * d.κ fun ρ => M.xEx P {l} ρ Y
def S12 (Y : ℂ) : 𝒜 := ∑ l ∈ Finset.Icc 1 (P.k - 1), (d.κ fun ρ => M.xEx P {l} ρ Y) * star (d.SS l)
def S4 (Y : ℂ) : 𝒜 :=
  ∑ l ∈ Finset.Icc 1 (P.k - 1), ∑ j ∈ (Finset.Icc 1 (P.k - 1)).erase l,
    star (d.SS l) * d.SS j * d.κ fun ρ => M.xEx P {l, j} ρ Y
def QQ (Y : ℂ) : Matrix (Fin 2) (Fin 2) 𝒜 :=
  !![d.L.GGi * (d.κ fun ρ => M.wC P ρ Y) + d.L.GG * d.x Y * d.L.m0 Y * d.L.l0 Y +
      d.L.GG * d.L.m0 Y * d.L.GGi * d.weightedSumBis Y + d.S12 Y * d.L.l0 Y + d.L.GGi * d.S4 Y,
    d.L.GG * d.x Y * d.L.m0 Y + d.S12 Y;
    d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y, d.L.GG * d.x Y]
def Rel : Prop :=
  (∀ f : M.Ty P → ℂ, star (d.κ f) = d.κ (fun ρ => star (f ρ))) ∧
  (∀ f : M.Ty P → ℂ, ∀ g ∈ d.L.fns ∪ {d.L.nab, d.L.nabs}, Commute (d.κ f) g) ∧
  (∀ l, ∀ g ∈ d.L.fns ∪ Set.range d.L.p ∪ Set.range d.L.pb, Commute (d.SS l) g) ∧
  (∀ l (f g : M.Ty P → ℂ), (∀ ρ ρ', M.Up P l ρ ρ' → g ρ' = f ρ) → d.κ g * d.SS l = d.SS l * d.κ f) ∧
  (∀ l ∈ Finset.Icc 1 (P.k - 1),
    d.L.nab * d.SS l = d.SS l * d.L.nab - d.L.ζb * d.L.GGi * d.SS l ∧
    d.L.nabs * d.SS l = d.SS l * d.L.nabs - d.L.ζ * d.L.GGi * d.SS l) ∧
  (∀ l ∈ Finset.Icc 1 (P.k - 1), star (d.SS l) * d.SS l = d.κ fun ρ => ((M.Nrm P l ρ : ℝ) : ℂ))
end NFData
def ModelIsNF : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (M.A P) P.r), M.IsModelLevel P L → ∀ Y : ℂ,
    (NFData.mk L (M.kap P) (M.SS P)).QQ Y = M.QQr P Y
def NormalFormActual : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)), IsPlace P z z' π π' →
    ∀ X : ActualOps P.k P.r z z' π π', ∃ d : NFData P (Pr (RadSp P.k P.r z z' π π')),
      IsActualLevel X d.L ∧ Fr.IsStarLevel d.L ∧ d.Rel ∧ ∀ Y : ℂ, X.QQ Y = d.QQ Y
def ActualStart : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)), IsPlace P z z' π π' →
    ∀ X : ActualOps P.k P.r z z' π π', Wd.IsStart X.QQ (M.qC P) ∧ ∀ Y Y', Commute (X.QQ Y 1 0) (X.QQ Y' 1 0)
def ZetaComm : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (D : Set (Mx k r))
    (f : Mx k r → E), inWb k r z → inWb k r z' → IsOpen D → SmoothLev k r (Fin.last r) D f →
    ∀ g ∈ Glev k r (Fin.last r) ∩ D, ∀ Y : ℂ,
      let ζ : Mx k r → ℂ := zetaL k r z z' (Fin.last r)
      let t := fun (a b : Fin 2) (h : Mx k r → E) => tL k r z z' (Fin.last r) Y a b h g
      t 1 0 (fun x => ζ x • f x) = ζ g • t 1 0 f - t 1 1 f ∧
      t 1 1 (fun x => ζ x • f x) = ζ g • t 1 1 f ∧
      t 0 1 (fun x => ζ x • f x) = ζ g • t 0 1 f ∧
      t 0 1 (fun x => star (ζ x) • f x) = star (ζ g) • t 0 1 f + t 1 1 f ∧
      t 1 0 (fun x => star (ζ x) • f x) = star (ζ g) • t 1 0 f ∧
      t 1 1 (fun x => star (ζ x) • f x) = star (ζ g) • t 1 1 f
def ActualAdjoint : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)), IsPlace P z z' π π' →
    ∀ (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r)), B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ →
    ∀ (Φ Ψ : RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ), c ∈ OmX P.r →
      (∃ K : Set (Mx P.k P.r), IsCompact K ∧ K ⊆ {g | 0 < GGl P.k P.r z z' g} ∧
        ∀ g ∈ Glev P.k P.r (Fin.last P.r), g ∉ K →
          (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0 ∧ (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0) →
      ∀ (Y : ℂ) (a b : Fin 2) (v : Wq),
        (∫ x : Mt P.k P.r, ⟪(X.t Y a b Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x) v,
            (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x) v⟫_ℂ ∂μ) =
          ∫ x : Mt P.k P.r, ⟪(Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x) v,
            (X.t (star Y) b a Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x) v⟫_ℂ ∂μ
def ActualAdjointFromHerm : Prop := HermHaar → ActualAdjoint
def NormalFormFromModule : Prop :=
  ActualStart → ZetaComm → Leading → RadialDecompositionSpectral → ActualOpsExist → NormalFormActual
def LevelStartFromNormalForm : Prop :=
  NormalFormActual → ActualStart → ModelIsNF → M.InterlaceSignTwo → LevelStartActual
def ActualStartFromLevels : Prop :=
  RTTLevel → (DetAt fun P => Fin.last P.r) → TLinLoc → ActualStart
end Formalism.FourierDecayAlt.Q


