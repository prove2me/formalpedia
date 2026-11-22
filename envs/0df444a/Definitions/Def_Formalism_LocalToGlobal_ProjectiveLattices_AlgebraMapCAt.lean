-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:25:28.820916+00:00
-- url     : https://prove2.me/theorems/55f260a5-ae71-4738-9765-8b3237b533ea
-- title:
--   Algebra Map CAt
-- statement:
--   Definitions and structural lemmas for Algebra Map CAt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AlgebraMapCAt.lean

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
namespace Formalism.L2.Pj
open MvPolynomial
structure TRing (K : Type) [Field K] : Type where
  n : ℕ
  I : Ideal (MvPolynomial (Fin n) K)
  rad : I.IsRadical
namespace TRing
variable {K : Type} [Field K]
abbrev R (p : TRing K) : Type := MvPolynomial (Fin p.n) K ⧸ p.I
end TRing
section Rules
variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
abbrev Rules : Type := ∀ p : TRing K, pts p.R → p.R
def wchar [Fintype ι] {S : Type} [CommRing S] (e : ι → ℕ) (t : ι → Sˣ) : S :=
  ∏ i, ((t i : Sˣ) : S) ^ e i
def IsNatural (f : Rules pts) : Prop :=
  ∀ (p q : TRing K) (φ : p.R →ₐ[K] q.R) (y : pts p.R) (z : pts q.R), mapR φ y z → f q z = φ (f p y)
def IsWeight [Fintype ι] (e : ι → ℕ) (f : Rules pts) : Prop :=
  ∀ (p : TRing K) (t : ι → (p.R)ˣ) (y y' : pts p.R), borR t y y' → f p y' = wchar e t * f p y
def secW [Fintype ι] (e : ι → ℕ) : Submodule K (Rules pts) where
  carrier := {f | IsNatural pts mapR f ∧ IsWeight pts borR e f}
  zero_mem' := ⟨fun p q φ y z _ => by simp, fun p t y y' _ => by simp⟩
  add_mem' := fun {f g} hf hg =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h, hg.1 p q φ y z h],
     fun p t y y' h => by simp [hf.2 p t y y' h, hg.2 p t y y' h, mul_add]⟩
  smul_mem' := fun c f hf =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h],
     fun p t y y' h => by simp [hf.2 p t y y' h]⟩
def FromTest {S : Type} [CommRing S] [Algebra K S] (y : pts S) : Prop :=
  ∃ (p : TRing K) (φ : p.R →ₐ[K] S) (y' : pts p.R), mapR φ y' y
def evalAt (f : Rules pts) {S : Type} [CommRing S] [Algebra K S] (y : pts S) : S :=
  open Classical in
  if h : FromTest pts mapR y then h.choose_spec.choose (f h.choose h.choose_spec.choose_spec.choose)
  else 0
theorem evalAt_add (f g : Rules pts) {S : Type} [CommRing S] [Algebra K S] (y : pts S) :
    evalAt pts mapR (f + g) y = evalAt pts mapR f y + evalAt pts mapR g y := by
  unfold evalAt; split_ifs <;> simp
theorem evalAt_smul (c : K) (f : Rules pts) {S : Type} [CommRing S] [Algebra K S] (y : pts S) :
    evalAt pts mapR (c • f) y = algebraMap K S c * evalAt pts mapR f y := by
  unfold evalAt; split_ifs <;> simp [Algebra.smul_def]
def evalL {S : Type} [CommRing S] [Algebra K S] (y : pts S) : Rules pts →ₗ[K] S where
  toFun f := evalAt pts mapR f y
  map_add' f g := evalAt_add pts mapR f g y
  map_smul' c f := by rw [RingHom.id_apply, evalAt_smul, Algebra.smul_def]
def EvalWD : Prop :=
  ∀ (f : Rules pts), IsNatural pts mapR f →
    ∀ (S : Type) [CommRing S] [Algebra K S] (p q : TRing K) (φ : p.R →ₐ[K] S) (ψ : q.R →ₐ[K] S)
      (y : pts p.R) (z : pts q.R) (w : pts S), mapR φ y w → mapR ψ z w → φ (f p y) = ψ (f q z)
end Rules
section Complex
variable {K : Type} [Field K]
def CAt (_σ : K →+* ℂ) : Type := ℂ
instance (σ : K →+* ℂ) : CommRing (CAt σ) := inferInstanceAs (CommRing ℂ)
instance (σ : K →+* ℂ) : Algebra K (CAt σ) := σ.toAlgebra
def cabs {σ : K →+* ℂ} (z : CAt σ) : ℝ := ‖(show ℂ from z)‖
variable {ι : Type} [Fintype ι]
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
def ptNorm (σ : K →+* ℂ) (fnorm : pts (CAt σ) → ι → ℝ) (e : ι → ℕ) (f : Rules pts)
    (y : pts (CAt σ)) : ℝ :=
  cabs (evalAt pts mapR f y) * ∏ i, |fnorm y i|⁻¹ ^ e i
def supAt (σ : K →+* ℂ) (fnorm : pts (CAt σ) → ι → ℝ) (e : ι → ℕ) (f : Rules pts) : ℝ :=
  ⨆ y : pts (CAt σ), ptNorm pts mapR σ fnorm e f y
def BddAt (σ : K →+* ℂ) (fnorm : pts (CAt σ) → ι → ℝ) (e : ι → ℕ) (f : Rules pts) : Prop :=
  BddAbove (Set.range (ptNorm pts mapR σ fnorm e f))
end Complex
end Formalism.L2.Pj


