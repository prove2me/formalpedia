-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_MultiIndexDerivation
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_MultiIndexDerivation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:45.412956+00:00
-- url     : https://prove2.me/theorems/e4c733fd-71ad-46f1-babb-15546cd3cd29
-- title:
--   Multi Index Derivation
-- statement:
--   Definitions and structural lemmas for Multi Index Derivation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/MultiIndexDerivation.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace FunctorialResolution.EmbeddedResolution
section
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
def multiIndexDeriv {h : ℕ} (D : Fin h → Derivation k R R) (α : Fin h → ℕ) (x : R) : R :=
  Fin.foldr h (fun i y => (⇑(D i))^[α i] y) x
@[simp]
theorem multiIndexDeriv_of_isEmpty (D : Fin 0 → Derivation k R R) (α : Fin 0 → ℕ) :
    multiIndexDeriv D α = id := by
  funext x
  simp [multiIndexDeriv]
theorem foldr_eq_self_of_forall_eq_self {A : Type*} :
    ∀ (n : ℕ) (f : Fin n → A → A), (∀ (i : Fin n) (y : A), f i y = y) →
      ∀ x : A, Fin.foldr n f x = x := by
  intro n
  induction n with
  | zero =>
      intro f hf x
      simp
  | succ n ih =>
      intro f hf x
      rw [Fin.foldr_succ, ih (fun i => f i.succ) (fun i y => hf i.succ y) x]
      exact hf 0 x
@[simp]
theorem multiIndexDeriv_zero {h : ℕ} (D : Fin h → Derivation k R R) (f : R) :
    multiIndexDeriv D (0 : Fin h → ℕ) f = f := by
  unfold multiIndexDeriv
  exact foldr_eq_self_of_forall_eq_self h (fun i y => (⇑(D i))^[(0 : Fin h → ℕ) i] y)
    (fun i y => by simp) f
@[simp]
theorem multiIndexDeriv_fun_zero {h : ℕ} (D : Fin h → Derivation k R R) (f : R) :
    multiIndexDeriv D (fun _ => 0) f = f :=
  multiIndexDeriv_zero D f
theorem fin_cons_self_tail {m : ℕ} (β : Fin (m + 1) → ℕ) :
    Fin.cons (β 0) (fun i => β i.succ) = β := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp
  · intro j
    simp
def finSuccFunEquivProd (m : ℕ) : (Fin (m + 1) → ℕ) ≃ ℕ × (Fin m → ℕ) where
  toFun β := (β 0, fun i => β i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv β := fin_cons_self_tail β
  right_inv p := by
    rcases p with ⟨a, b⟩
    simp
def unitMultiIndex {h : ℕ} (i : Fin h) : Fin h → ℕ := fun j => if j = i then 1 else 0
end
end FunctorialResolution.EmbeddedResolution


