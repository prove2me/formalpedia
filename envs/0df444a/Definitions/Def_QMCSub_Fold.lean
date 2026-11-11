-- Prove2me | Definitions.Def_QMCSub_Fold
-- name    : QMCSub_Fold
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T09:01:42.916202+00:00
-- url     : https://prove2.me/theorems/0d0908f3-b482-4fc1-b947-304809aee343
-- title:
--   Polynomial-time fold with a static component and a size-bounded state
-- statement:
--   A general principle for the finite Boolean-machine runtime. Let a step $d\mapsto\mathrm{step}(s,d)$ be polynomial-time, and suppose the encoding length of its output is bounded by a polynomial in the encoding length of the static data $s$ alone. Then folding the step over a list, carrying $s$ unchanged, is polynomial-time. The dynamic component of the fold is the iterate $\mathrm{step}(s,\cdot)^{[\ell]}$ for a list of length $\ell$.
-- source:
--   Supporting library for QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2 (Prove2me mission 'Quantum Max-Cut: 0.526 energy estimation'; Anshu, Gosset, Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394). Method: rounded dual subgradient iteration for the Max-Cut semidefinite relaxation with matrix-power approximate subgradients.

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

/-!
Generic polynomial-time fold with a static component and a size-guarded dynamic component.
-/

namespace QMCSub

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open Polynomial

variable {σ δ α : Type}

/-- Fold a step function over a list, carrying an unchanged static component. -/
def gfold (step : σ → δ → δ) (as : List α) (b : σ × δ) : σ × δ :=
  as.foldl (fun b _ => (b.1, step b.1 b.2)) b

theorem gfold_nil (step : σ → δ → δ) (b : σ × δ) : gfold step ([] : List α) b = b := rfl

theorem gfold_cons (step : σ → δ → δ) (a : α) (as : List α) (b : σ × δ) :
    gfold step (a :: as) b = gfold step as (b.1, step b.1 b.2) := rfl

theorem gfold_append (step : σ → δ → δ) (as bs : List α) (b : σ × δ) :
    gfold step (as ++ bs) b = gfold step bs (gfold step as b) := by
  simp only [gfold, List.foldl_append]

theorem gfold_fst (step : σ → δ → δ) (as : List α) (b : σ × δ) :
    (gfold step as b).1 = b.1 := by
  induction as generalizing b with
  | nil => rfl
  | cons a as ih => rw [gfold_cons, ih]

/-- The dynamic component after a fold is the iterate of the step. -/
theorem gfold_snd (step : σ → δ → δ) (as : List α) (s : σ) (d : δ) :
    (gfold step as (s, d)).2 = (step s)^[as.length] d := by
  induction as generalizing d with
  | nil => rfl
  | cons a as ih =>
      rw [gfold_cons, ih, List.length_cons, Function.iterate_succ_apply]

theorem gfold_eq (step : σ → δ → δ) (as : List α) (s : σ) (d : δ) :
    gfold step as (s, d) = (s, (step s)^[as.length] d) := by
  apply Prod.ext
  · exact gfold_fst step as (s, d)
  · exact gfold_snd step as s d

section size
variable [Coding σ] [Coding δ] [Coding α]

theorem gfold_size (step : σ → δ → δ) (Q : Polynomial ℕ)
    (hQ : ∀ s d, (enc (step s d)).length ≤ Q.eval (enc s).length)
    (as : List α) (b : σ × δ) :
    (enc (gfold step as b)).length ≤
      (enc b).length + (2 * (enc b.1).length + 1 + Q.eval (enc b.1).length) := by
  rcases List.eq_nil_or_concat as with h | ⟨pre, a, h⟩
  · subst h
    rw [gfold_nil]
    omega
  · subst h
    rw [List.concat_eq_append, gfold_append, gfold_cons, gfold_nil]
    have h1 := gfold_fst step pre b
    change (encodePair enc enc ((gfold step pre b).1,
      step (gfold step pre b).1 (gfold step pre b).2)).length ≤ _
    rw [encodePair_length, h1]
    have h2 := hQ b.1 (gfold step pre b).2
    dsimp only at h2 ⊢
    omega

/-- A fold of a polynomial-time step with a polynomially size-bounded output is polynomial-time. -/
theorem poly_gfold [Inhabited α] (step : σ → δ → δ)
    (hstep : Poly (fun x : σ × δ => step x.1 x.2))
    (Q : Polynomial ℕ) (hQ : ∀ s d, (enc (step s d)).length ≤ Q.eval (enc s).length) :
    Poly (fun x : List α × (σ × δ) => gfold step x.1 x.2) := by
  let op : (σ × δ) × α → σ × δ := fun x => (x.1.1, step x.1.1 x.1.2)
  have hop : Poly op := by
    have h1 : Poly (fun x : (σ × δ) × α => x.1.1) := Poly.comp Poly.fst Poly.fst
    have h2 : Poly (fun x : (σ × δ) × α => step x.1.1 x.1.2) := Poly.comp hstep Poly.fst
    exact Poly.pair h1 h2
  refine ⟨(PolyProgram.listFold (ea := (enc : α → List Bool)) (eb := (enc : σ × δ → List Bool))
    (op := op) hop.program default (X + (2 * X + 1 + Q)) ?_).congr _ (fun x => rfl)⟩
  intro as b pre suf _
  have h := gfold_size (α := α) step Q hQ pre b
  have hb1 : (enc b.1).length ≤ (enc b).length := by
    change _ ≤ (encodePair enc enc b).length
    rw [encodePair_length]
    omega
  have hbN : (enc b).length ≤
      (encodePair (encodeList (enc : α → List Bool)) (enc : σ × δ → List Bool) (as, b)).length := by
    rw [encodePair_length]
    dsimp only
    omega
  have hmono := polynomial_eval_mono Q (hb1.trans hbN)
  simp only [eval_add, eval_mul, eval_ofNat, eval_X, eval_one]
  change (enc (gfold step pre b)).length ≤ _
  omega

end size

end QMCSub


