-- Prove2me | Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
-- name    : Formalism_FormalDegreeBessel_StatementWR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:46:20.145562+00:00
-- url     : https://prove2.me/theorems/6a699f55-3137-44dc-b471-2e3505e3f78d
-- title:
--   Statement WR
-- statement:
--   Definitions and structural lemmas for Statement WR, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/StatementWR.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace Formalism.QuantumDeterminants
def OmX (m : ℕ) : Set (Fin m → ℂ) := {x | ∀ l, x l ≠ 0}
def WSm (m : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] : Submodule ℂ ((Fin m → ℂ) → E) where
  carrier := {f | ContDiffOn ℝ ∞ f (OmX m) ∧ ∀ x, x ∉ OmX m → f x = 0}
  zero_mem' := ⟨contDiffOn_const, fun _ _ => rfl⟩
  add_mem' := fun {f g} hf hg => ⟨hf.1.add hg.1, fun x hx => by simp [hf.2 x hx, hg.2 x hx]⟩
  smul_mem' := fun a {f} hf => ⟨hf.1.const_smul a, fun x hx => by simp [hf.2 x hx]⟩
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def wirt (l : Fin m) (f : (Fin m → ℂ) → E) (x : Fin m → ℂ) : E :=
  (1 / 2 : ℂ) • (fderiv ℝ f x (Pi.single l 1) - Complex.I • fderiv ℝ f x (Pi.single l Complex.I))
def wirtBar (l : Fin m) (f : (Fin m → ℂ) → E) (x : Fin m → ℂ) : E :=
  (1 / 2 : ℂ) • (fderiv ℝ f x (Pi.single l 1) + Complex.I • fderiv ℝ f x (Pi.single l Complex.I))
open Classical in

def pOp (l : Fin m) (f : (Fin m → ℂ) → E) : (Fin m → ℂ) → E := fun x =>
  if x ∈ OmX m then x l • wirt l f x else 0
open Classical in

def pbOp (l : Fin m) (f : (Fin m → ℂ) → E) : (Fin m → ℂ) → E := fun x =>
  if x ∈ OmX m then star (x l) • wirtBar l f x else 0
def cOp (l : Fin m) (f : (Fin m → ℂ) → E) : (Fin m → ℂ) → E := fun x => x l • f x
def ciOp (l : Fin m) (f : (Fin m → ℂ) → E) : (Fin m → ℂ) → E := fun x => (x l)⁻¹ • f x
def cbOp (l : Fin m) (f : (Fin m → ℂ) → E) : (Fin m → ℂ) → E := fun x => star (x l) • f x
def cbiOp (l : Fin m) (f : (Fin m → ℂ) → E) : (Fin m → ℂ) → E := fun x => (star (x l))⁻¹ • f x
def opL (l : Fin m) : Fin 6 → ((Fin m → ℂ) → E) → (Fin m → ℂ) → E
  | 0 => pOp l | 1 => cOp l | 2 => ciOp l | 3 => pbOp l | 4 => cbOp l | 5 => cbiOp l
def holoIdx (i : Fin 6) : Prop := (i : ℕ) < 3
def PresOps : Prop :=
  ∀ (m : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin m) (i : Fin 6)
    (f : (Fin m → ℂ) → E), f ∈ WSm m E → opL l i f ∈ WSm m E
def LinOps : Prop :=
  ∀ (m : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin m) (i : Fin 6)
    (f g : (Fin m → ℂ) → E) (a : ℂ), f ∈ WSm m E → g ∈ WSm m E →
      opL l i (f + g) = opL l i f + opL l i g ∧ opL l i (a • f) = a • opL l i f
def WeylFun : Prop :=
  ∀ (m : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin m) (f : (Fin m → ℂ) → E),
    f ∈ WSm m E →
      cOp l (ciOp l f) = f ∧ ciOp l (cOp l f) = f ∧ pOp l (cOp l f) = cOp l (pOp l f) + cOp l f ∧
      cbOp l (cbiOp l f) = f ∧ cbiOp l (cbOp l f) = f ∧ pbOp l (cbOp l f) = cbOp l (pbOp l f) + cbOp l f
def CommFun : Prop :=
  ∀ (m : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (l k : Fin m) (i j : Fin 6)
    (f : (Fin m → ℂ) → E), f ∈ WSm m E → (l ≠ k ∨ (holoIdx i ↔ ¬ holoIdx j)) →
      opL l i (opL k j f) = opL k j (opL l i f)
def AdjFun : Prop :=
  ∀ (m : ℕ) (l : Fin m) (f g : (Fin m → ℂ) → ℂ), f ∈ WSm m ℂ → g ∈ WSm m ℂ →
    HasCompactSupport f → HasCompactSupport g → tsupport f ⊆ OmX m → tsupport g ⊆ OmX m →
      (∫ x, pOp l f x * star (g x) * ((∏ k, Complex.normSq (x k))⁻¹ : ℝ)) =
        -(∫ x, f x * star (pbOp l g x) * ((∏ k, Complex.normSq (x k))⁻¹ : ℝ))
end Formalism.QuantumDeterminants


