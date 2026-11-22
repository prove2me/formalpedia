-- Prove2me | Definitions.Def_Formalism_SobolevGaussianKernels_StatementEI
-- name    : Formalism_SobolevGaussianKernels_StatementEI
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:13:03.194802+00:00
-- url     : https://prove2.me/theorems/08aefb4d-db87-4646-81e2-8b1a8b34cf72
-- title:
--   Statement EI
-- statement:
--   Definitions and structural lemmas for Statement EI, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SobolevGaussianKernels/StatementEI.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.SL.IwahoriBlocks
variable {E : Type*} [CommRing E] [StarRing E] {V : Type*} [AddCommGroup V] [Module E V]
def IsHerm (h : V →ₗ[E] V →ₗ⋆[E] E) : Prop := ∀ v w, h w v = star (h v w)
def eich (h : V →ₗ[E] V →ₗ⋆[E] E) (x u : V) (s : E) (v : V) : V :=
  v + h v u • x - h v x • (u + s • x)
def EichIsom : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x u : V) (s : E),
    IsHerm h → h x x = 0 → h u x = 0 → s + star s = h u u →
    ∀ v w, h (eich h x u s v) (eich h x u s w) = h v w
def EichInv : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x u : V) (s : E),
    IsHerm h → h x x = 0 → h u x = 0 → s + star s = h u u →
    ∀ v, eich h x (-u) (star s) (eich h x u s v) = v ∧ eich h x u s (eich h x (-u) (star s) v) = v
def EichComp : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x a b : V) (s t : E),
    IsHerm h → h x x = 0 → h a x = 0 → h b x = 0 →
    ∀ v, eich h x a s (eich h x b t v) = eich h x (a + b) (s + t + h b a) v
def EichShift : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x u : V) (s c : E),
    ∀ v, eich h x (u + c • x) s v = eich h x u (s + c - star c) v
def EichEquiv : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (g : V →ₗ[E] V), (∀ v w, h (g v) (g w) = h v w) →
    ∀ (x u : V) (s : E) (v : V), g (eich h x u s v) = eich h (g x) (g u) s (g v)
def EichMove : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x x' u : V) (s : E),
    IsHerm h → h u x = 0 → h u x' = 0 →
    ∀ v, h v x' = 0 →
      eich h x u s (eich h x' u s v) = v + h v u • (x + x') - (h v x + h v u * h x' x) • (u + s • x)
def EichNew : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x x' u : V) (s : E),
    (h u x = 0 → eich h x u s u = u + h u u • x) ∧
    (h x' u = 0 → eich h x u s x' = x' - h x' x • (u + s • x))
def EichPair : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (x x' u : V) (s : E),
    IsHerm h → h u x = 0 → h u x' = 0 →
    ∀ y z, h y x = 0 → h y u = 0 → h z x' = 0 →
      h y (eich h x u s (eich h x' u s z)) = h y z + star (h z u) * h y x'
def EichInt : Prop :=
  ∀ (E : Type) [CommRing E] [StarRing E] (V : Type) [AddCommGroup V] [Module E V]
    (h : V →ₗ[E] V →ₗ⋆[E] E) (O : Subring E) (abelian₂ : AddSubgroup V) (x x' u : V) (s : E),
    IsHerm h →
    (∀ a ∈ O, ∀ v ∈ abelian₂, a • v ∈ abelian₂) →
    (∀ v ∈ abelian₂, ∀ w ∈ abelian₂, h v w ∈ O) →
    u ∈ abelian₂ → x + x' ∈ abelian₂ → s • x ∈ abelian₂ → h x' x ∈ O → h u x = 0 → h u x' = 0 →
    ∀ v ∈ abelian₂, h v x' = 0 → eich h x u s (eich h x' u s v) ∈ abelian₂
end Formalism.SL.IwahoriBlocks


