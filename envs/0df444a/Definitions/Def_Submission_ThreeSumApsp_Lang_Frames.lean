-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
-- name    : Submission_ThreeSumApsp_Lang_Frames
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:29:42.975244+00:00
-- url     : https://prove2.me/theorems/fb8cf310-4ce7-4ca5-845a-0f2edaff60a4
-- title:
--   Frames
-- statement:
--   Definitions and structural lemmas for Frames, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Frames.lean

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.toNat_natCast_add_natCast


set_option autoImplicit false
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
@[simp] def setLocal : List ℤ → ℕ → ℤ → List ℤ
  | [], 0, z => [z]
  | [], x + 1, z => 0 :: setLocal [] x z
  | _ :: l, 0, z => z :: l
  | a :: l, x + 1, z => a :: setLocal l x z
theorem frame_setLocal : ∀ (l : List ℤ) (x : ℕ) (z : ℤ) (y : ℕ),
    frame (setLocal l x z) y = if y = x then z else frame l y
  | [], 0, z, 0 => by simp
  | [], 0, z, y + 1 => by simp
  | [], x + 1, z, 0 => by simp
  | [], x + 1, z, y + 1 => by simpa using frame_setLocal [] x z y
  | a :: l, 0, z, 0 => by simp
  | a :: l, 0, z, y + 1 => by simp
  | a :: l, x + 1, z, 0 => by simp
  | a :: l, x + 1, z, y + 1 => by simpa using frame_setLocal l x z y
theorem update_frame_setLocal (l : List ℤ) (x : ℕ) (z : ℤ) :
    Function.update (frame l) x z = frame (setLocal l x z) := by
  funext y
  rw [frame_setLocal, Function.update_apply]
@[simp] def Expr.Gives (lim : Limits) (σ : State) (e : Expr) (z : ℤ) : Prop :=
  e.Safe lim σ ∧ e.val σ = z
section rules
variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}
end rules
@[simp] def setLocals (l : List ℤ) : List (ℕ × ℤ) → List ℤ
  | [] => l
  | p :: ps => setLocals (setLocal l p.1 p.2) ps
@[simp] def updateLocals (loc : ℕ → ℤ) : List (ℕ × ℤ) → ℕ → ℤ
  | [] => loc
  | p :: ps => updateLocals (Function.update loc p.1 p.2) ps
@[simp] def refreshLocals (l : List ℤ) (loc : ℕ → ℤ) : List ℕ → List ℤ
  | [] => l
  | x :: xs => refreshLocals (setLocal l x (loc x)) loc xs
def SameFrame (l m : List ℤ) : Prop := frame l = frame m
def LocalsBut (xs : List ℕ) (l : List ℤ) (loc : ℕ → ℤ) : Prop :=
  ∀ y ∉ xs, loc y = frame l y
section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}
variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}
end
end Light


