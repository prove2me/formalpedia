-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_MatrixGeometry
-- name    : QuantumSepPoly_Frobenius_MatrixGeometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:28.020262+00:00
-- url     : https://prove2.me/theorems/58046379-a7bb-4bf7-8a15-428060e4b2f0
-- title:
--   Complex matrix and vector geometry
-- statement:
--   For $x\in\mathbb C^d$, write $\|x\|_2^2=\sum_a|x_a|^2$. For a complex matrix $M$, define the unnormalized Frobenius norm and largest-entry norm by
--   $$\|M\|_F=\sqrt{\sum_{i,j}|M_{ij}|^2},\qquad \|M\|_{\max}=\max_{i,j}|M_{ij}|.$$
--   Product vectors have coordinates $x_a y_c$, their pure densities are outer products, and quadratic objectives take the real part. Normalization returns the first basis vector at zero and otherwise divides by the Euclidean norm. The largest-entry norm is explicitly zero on the empty matrix. These operations provide the common geometry; the relevant theorems require positive local dimension.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), §§2–5, p. 6 (PDF p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Mathlib

noncomputable section

namespace QuantumSepPoly.Frobenius
open scoped BigOperators

/-- §2, p.6: finite complex vectors and unnormalized Euclidean geometry. -/
abbrev Vec (d : ℕ) := Fin d → ℂ
abbrev Op (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
abbrev Bip (d : ℕ) := Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ

def vecSq {d : ℕ} (x : Vec d) : ℝ := ∑ a, ‖x a‖ ^ 2

def vecNorm {d : ℕ} (x : Vec d) : ℝ := Real.sqrt (vecSq x)

def frob {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) : ℝ :=
  Real.sqrt (∑ a, ∑ b, ‖M a b‖ ^ 2)

def maxEntry {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) : ℝ :=
  Finset.univ.sup' (by simp) (fun a : Option (ι × ι) =>
    match a with | none => 0 | some (i,j) => ‖M i j‖)

def tensorVec {d : ℕ} (x y : Vec d) (i : Fin d × Fin d) : ℂ := x i.1 * y i.2

def pure {ι : Type*} (x : ι → ℂ) : Matrix ι ι ℂ := fun i j => x i * star (x j)

def productDensity {d : ℕ} (x y : Vec d) : Bip d := pure (tensorVec x y)

def productValue {d : ℕ} (M : Bip d) (x y : Vec d) : ℝ :=
  (∑ i, ∑ j, star (tensorVec x y i) * M i j * tensorVec x y j).re

def firstVector (d : ℕ) : Vec d := fun i => if i.val = 0 then 1 else 0

def normalize {d : ℕ} (x : Vec d) : Vec d :=
  if vecSq x = 0 then firstVector d else fun i => x i / (vecNorm x : ℂ)

def normalizeSqrt {d : ℕ} (x : Vec d) : Vec d :=
  fun i => (Real.sqrt (d : ℝ) : ℂ) * normalize x i

end QuantumSepPoly.Frobenius


