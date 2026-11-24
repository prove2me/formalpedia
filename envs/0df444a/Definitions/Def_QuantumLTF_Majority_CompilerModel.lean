-- Prove2me | Definitions.Def_QuantumLTF_Majority_CompilerModel
-- name    : QuantumLTF_Majority_CompilerModel
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-23T21:55:33.021807+00:00
-- url     : https://prove2.me/theorems/578d4998-497c-49da-b2de-c446d8ff999f
-- title:
--   Finite-dimensional phase-query clock model
-- statement:
--   Finite complex Hilbert spaces for the adversary compiler: a replicated public clock state, a private Boolean phase oracle, a recursive run alternating the oracle with input-independent unitaries, and an output-label measurement event. These are operational definitions for equations (129)–(134) of the paper; the model carries no unproved compiler or state-conversion assumptions.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331v3, Section 4.5.1, equations (129)–(134), pp. 50–52. Explicit constant obtained by choosing N=ceil(72(T+1)) in the catalyst clock construction.

import Mathlib.Analysis.InnerProductSpace.Positive

set_option autoImplicit false

noncomputable def compiler_clock_public {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N t : ℕ) (a : ι) : EuclideanSpace ℂ (Fin N × Option ι) :=
  ∑ j : Fin N, EuclideanSpace.single
    (j, if (j : ℕ) < t then some a else none) 1

noncomputable def compiler_sign_oracle {κ : Type*} [Fintype κ]
    (bit : κ → Bool) : EuclideanSpace ℂ κ ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ where
  toFun x := WithLp.toLp 2 (fun j => (if bit j then (-1 : ℂ) else 1) * x j)
  invFun x := WithLp.toLp 2 (fun j => (if bit j then (-1 : ℂ) else 1) * x j)
  left_inv x := by
    ext j
    simp only [WithLp.ofLp_toLp]
    split_ifs <;> simp
  right_inv x := by
    ext j
    simp only [WithLp.ofLp_toLp]
    split_ifs <;> simp
  map_add' x y := by ext j; simp [mul_add]
  map_smul' a x := by ext j; simp [mul_left_comm]
  norm_map' x := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    change ‖(if bit j then (-1 : ℂ) else 1) * x j‖ ^ 2 = ‖x j‖ ^ 2
    split_ifs <;> simp

noncomputable def compiler_left {α β : Type*} [Fintype α] [Fintype β]
    (x : EuclideanSpace ℂ α) : EuclideanSpace ℂ (α ⊕ β) :=
  WithLp.toLp 2 (Sum.elim (fun a => x a) (fun _ => 0))

noncomputable def compiler_clock_run {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (U : ℕ → E ≃ₗᵢ[𝕜] E) (O : E ≃ₗᵢ[𝕜] E) : ℕ → E ≃ₗᵢ[𝕜] E
  | 0 => LinearIsometryEquiv.refl 𝕜 E
  | j+1 => (compiler_clock_run U O j).trans (O.trans (U j))

noncomputable def compiler_clock_start {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ) :
    EuclideanSpace ℂ (Fin N × Option ι) :=
  ∑ j : Fin N, EuclideanSpace.single (j, none) 1

def compiler_success_event {ι α β : Type*} (a : ι) : (α × Option ι) ⊕ β → Prop
  | Sum.inl (_, label) => label = some a
  | Sum.inr _ => False

instance compiler_success_event_decidable {ι α β : Type*} [DecidableEq ι] (a : ι) :
    DecidablePred (compiler_success_event (α := α) (β := β) a) := by
  intro j
  cases j <;> unfold compiler_success_event <;> infer_instance


