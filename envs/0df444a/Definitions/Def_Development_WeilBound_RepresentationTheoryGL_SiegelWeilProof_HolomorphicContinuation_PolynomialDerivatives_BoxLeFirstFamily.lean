-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BoxLeFirstFamily
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BoxLeFirstFamily
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T12:20:01.76789+00:00
-- url     : https://prove2.me/theorems/958e3d0b-32e9-5e33-9cef-42bb9cd7f24c
-- title:
--   Box Le First Family
-- statement:
--   Definitions and structural lemmas for Box Le First Family, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/BoxLeFirstFamily.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymKEqZeroOfOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace PositivityTheory.Rg.Sw.LC
namespace CoreD
variable {m n : ℕ} {ε : Fin m → Bool}
theorem opMono_add (t : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) (f g : PX m n) :
    opMono t (f + g) = opMono t f + opMono t g := by
  simp [opMono, map_add, mul_add]
theorem opMono_smul (t : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) (r : ℂ) (f : PX m n) :
    opMono t (r • f) = r • opMono t f := by
  simp [opMono, map_smul, mul_smul_comm]
def opL (s : Sym m n) : Module.End ℂ (PX m n) where
  toFun := op s
  map_add' f g := by simp [op, opMono_add, smul_add, Finset.sum_add_distrib]
  map_smul' r f := by simp [op, opMono_smul, Finset.smul_sum, smul_comm r]
@[simp] theorem opL_apply (s : Sym m n) (f : PX m n) : opL s f = op s f := rfl
theorem op_eq (s : Sym m n) (T : Finset _) (h : s.support ⊆ T) (f : PX m n) :
    op s f = ∑ t ∈ T, s.coeff t • opMono t f := by
  unfold op
  refine Finset.sum_subset h fun t _ ht => ?_
  rw [mem_support_iff, not_not] at ht
  rw [ht, zero_smul]
theorem op_add_sym (s₁ s₂ : Sym m n) (f : PX m n) : op (s₁ + s₂) f = op s₁ f + op s₂ f := by
  classical
  rw [op_eq (s₁ + s₂) (s₁.support ∪ s₂.support) support_add, op_eq s₁ (s₁.support ∪ s₂.support)
    Finset.subset_union_left, op_eq s₂ (s₁.support ∪ s₂.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by rw [coeff_add, add_smul]
theorem op_smul_sym (s : Sym m n) (r : ℂ) (f : PX m n) : op (r • s) f = r • op s f := by
  classical
  rw [op_eq (r • s) s.support support_smul, op, Finset.smul_sum]
  exact Finset.sum_congr rfl fun t _ => by rw [coeff_smul, smul_eq_mul, mul_smul]
def Ad {V : Submodule ℂ (PX m n)} (K : Module.End ℂ (PX m n)) (KV : Module.End ℂ V) :
    Module.End ℂ (V →ₗ[ℂ] PX m n) where
  toFun h := K ∘ₗ h - h ∘ₗ KV
  map_add' h₁ h₂ := LinearMap.ext fun f => by simp; abel
  map_smul' r h := LinearMap.ext fun f => by simp [smul_sub]
section main
variable (R : Set (Fin m → ℕ)) (hV : ∀ (i j : Fin n), ∀ f ∈ box ε R, KopL ε i j f ∈ box ε R)
def KV (i j : Fin n) : Module.End ℂ (box (n := n) ε R) := (KopL ε i j).restrict (hV i j)
def OmH : Module.End ℂ (box (n := n) ε R →ₗ[ℂ] PX m n) :=
  ∑ ij : Fin n × Fin n, Ad (KopL ε ij.1 ij.2) (KV R hV ij.1 ij.2) * Ad (KopL ε ij.2 ij.1) (KV R hV ij.2 ij.1)
def rr (N : ℕ) : S (n := n) ε N →ₗ[ℂ] (box (n := n) ε R →ₗ[ℂ] PX m n) where
  toFun x := opL x.1 ∘ₗ (box ε R).subtype
  map_add' x y := LinearMap.ext fun f => op_add_sym x.1 y.1 f.1
  map_smul' r x := LinearMap.ext fun f => op_smul_sym x.1 r f.1
variable (hS : SymKComm)
include hS
end main
end CoreD
end PositivityTheory.Rg.Sw.LC


