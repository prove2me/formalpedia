-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:24:02.166598+00:00
-- url     : https://prove2.me/theorems/4379a8c1-0a1f-43b4-a690-a1450e6d87d3
-- title:
--   Restrict Orthogonal Complement Nondeg
-- statement:
--   Definitions and structural lemmas for Restrict Orthogonal Complement Nondeg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictOrthogonalComplementNondeg.lean

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.S3x6
open Module
structure Inv {K : Type} [Field K] (σ : K →+* K) : Prop where
  invol : ∀ x, σ (σ x) = x
  norm_surj : ∀ c, σ c = c → ∃ y, σ y * y = c
  trace_one : ∃ l, l + σ l = 1
variable {K : Type} [Field K] {σ : K →+* K}
def Herm {V : Type} [AddCommGroup V] [Module K V] (h : V →ₛₗ[σ] V →ₗ[K] K) : Prop :=
  ∀ u v, σ (h u v) = h v u
def Nondeg {V : Type} [AddCommGroup V] [Module K V] (h : V →ₛₗ[σ] V →ₗ[K] K) : Prop :=
  ∀ u, (∀ v, h u v = 0) → u = 0
def Ortho {V : Type} [AddCommGroup V] [Module K V] (h : V →ₛₗ[σ] V →ₗ[K] K) {ι : Type} [DecidableEq ι]
    (b : ι → V) : Prop := ∀ i j, h (b i) (b j) = if i = j then 1 else 0
section A1
variable {V : Type} [AddCommGroup V] [Module K V]
def restrictFormAlt (h : V →ₛₗ[σ] V →ₗ[K] K) (W : Submodule K V) : W →ₛₗ[σ] W →ₗ[K] K :=
  h.domRestrict₁₂ W W
lemma orthonormal_cons_iff {h : V →ₛₗ[σ] V →ₗ[K] K} (hh : Herm h) {n : ℕ} (v : V) (c : Fin n → V) :
    Ortho h (Fin.cons v c : Fin (n + 1) → V) ↔ h v v = 1 ∧ (∀ i, h v (c i) = 0) ∧ Ortho h c := by
  constructor
  · intro H
    refine ⟨by simpa using H 0 0, fun i => ?_, fun i j => ?_⟩
    · have := H 0 i.succ
      simpa [(Fin.succ_ne_zero i).symm] using this
    · have := H i.succ j.succ
      simpa using this
  · rintro ⟨h1, h2, h3⟩ i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa using h1
    · simpa [(Fin.succ_ne_zero j).symm] using h2 j
    · have : h (c i) v = 0 := by rw [← hh v (c i), h2 i, map_zero]
      simpa [Fin.succ_ne_zero i] using this
    · simpa using h3 i j
end A1
def orthonormalFrameEquiv {V : Type} [AddCommGroup V] [Module K V] {h : V →ₛₗ[σ] V →ₗ[K] K} (hh : Herm h)
    (n : ℕ) : {b : Fin (n + 1) → V // Ortho h b} ≃
      Σ v : {v : V // h v v = 1},
        {c : Fin n → LinearMap.ker (h v.1) // Ortho (restrictFormAlt h (LinearMap.ker (h v.1))) c} where
  toFun b :=
    have H : Ortho h (Fin.cons (b.1 0) (fun i => b.1 i.succ) : Fin (n + 1) → V) := by
      have : (Fin.cons (b.1 0) (fun i => b.1 i.succ) : Fin (n + 1) → V) = b.1 :=
        Fin.cons_self_tail b.1
      rw [this]; exact b.2
    ⟨⟨b.1 0, ((orthonormal_cons_iff hh _ _).1 H).1⟩,
      ⟨fun i => ⟨b.1 i.succ, LinearMap.mem_ker.2 (((orthonormal_cons_iff hh _ _).1 H).2.1 i)⟩,
        fun i j => ((orthonormal_cons_iff hh _ _).1 H).2.2 i j⟩⟩
  invFun p := ⟨Fin.cons p.1.1 (fun i => ((p.2.1 i : LinearMap.ker (h p.1.1)) : V)),
    (orthonormal_cons_iff hh _ _).2 ⟨p.1.2, fun i => LinearMap.mem_ker.1 (p.2.1 i).2,
      fun i j => p.2.2 i j⟩⟩
  left_inv b := Subtype.ext (Fin.cons_self_tail b.1)
  right_inv p := by
    rcases p with ⟨⟨v, hv⟩, ⟨c, hc⟩⟩
    rfl
section A2
variable {V : Type} [AddCommGroup V] [Module K V]
def gramMatrix (h : V →ₛₗ[σ] V →ₗ[K] K) {ι : Type} (x : ι → V) : Matrix ι ι K :=
  Matrix.of fun i j => h (x i) (x j)
end A2
section PartC
open Finset
variable (K : Type) [Field K] [Fintype K] (q : ℕ)
end PartC
section PartD
open Matrix Formalism.FourierDecayAlt.S3
noncomputable def hJ (σ : K →+* K) {n : ℕ} (J : Matrix (Fin n) (Fin n) K) :
    (Fin n → K) →ₛₗ[σ] (Fin n → K) →ₗ[K] K := Matrix.toLinearMapₛₗ₂' K σ (RingHom.id K) J
end PartD
end Formalism.FourierDecayAlt.P.S3x6
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


