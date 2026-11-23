-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
-- name    : Formalism_PeriodIntegrals_FlagGramNonneg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:09:49.71105+00:00
-- url     : https://prove2.me/theorems/480cd09c-5f3a-4b44-813f-155eaf046d03
-- title:
--   Flag Gram Nonneg
-- statement:
--   Definitions and structural lemmas for Flag Gram Nonneg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/FlagGramNonneg.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField
namespace PI.FlagGramNonneg
def cT {A : Type} [CommRing A] (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A := (M.map σ)ᵀ
def Jpq (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks 1 0 0 (-1)
def HasSignature {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n ℂ) (p q : ℕ) : Prop :=
  ∃ e : n ≃ Fin p ⊕ Fin q, ∃ P : GL (Fin p ⊕ Fin q) ℂ,
    cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * J.reindex e e *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Jpq p q
def leadMinorE {E : Type} [Field E] {N : ℕ} (A : Matrix (Fin N) (Fin N) E) (l : ℕ) : E := by
  classical
  exact if h : l ≤ N then (A.submatrix (Fin.castLE h) (Fin.castLE h)).det else 0
def gram {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {N : ℕ} (b : Module.Basis (Fin N) E V) : Matrix (Fin N) (Fin N) E :=
  fun i j => hT (b i) (b j)
def IsFlag {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (T : E) (e : Fin r → V) (z : V) : Prop :=
  LinearIndependent E e ∧ (∀ a b, hT (e a) (e b) = 0) ∧ (∀ a, hT (e a) z = 0) ∧ hT z z = -T
def fvec {V : Type} {r : ℕ} (e : Fin r → V) (z : V) : Fin (r + 1) → V :=
  Fin.snoc (α := fun _ => V) e z
def zhat {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
    (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (f f' : Fin (r + 1) → V) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  fun a b => hT (f a) (f' b)
def gval {E : Type} [Field E] [StarRing E] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) : E :=
  leadMinorE Z (r + 1) * star (leadMinorE Z (r + 1)) - T * T' * (leadMinorE Z r * star (leadMinorE Z r))
end PI.FlagGramNonneg
namespace PI
open PI.FlagGramNonneg
def FlagGramNonneg : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (hT : V →ₗ⋆[E] V →ₗ[E] E), hT.IsSymm → hT.Nondegenerate →
    ∀ (N : ℕ) (b : Module.Basis (Fin N) E V) (τ : E →+* ℂ),
    (∀ a, τ (star a) = starRingEnd ℂ (τ a)) →
    ∀ (p r T T' : ℕ), HasSignature ((gram hT b).map τ) p (r + 1) → 0 < T → 0 < T' →
    ∀ (e e' : Fin r → V) (z z' : V), IsFlag hT (T : E) e z → IsFlag hT (T' : E) e' z' →
      ∃ c : ℝ, 0 ≤ c ∧ τ (gval (zhat hT (fvec e z) (fvec e' z')) (T : E) (T' : E)) = c
end PI


