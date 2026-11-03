-- Prove2me | Definitions.Def_ProxFlatIP_Spindle
-- name    : ProxFlatIP_Spindle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:13:38.973352+00:00
-- url     : https://prove2.me/theorems/6d1bfaac-2182-4753-a26c-8aec6f360206
-- title:
--   The cone $C(A,x^*)$, the spindle $S(A,x^*)$ and faces
-- statement:
--   Let $A\in\mathbb Z^{m\times n}$ have rows $a_i^\top$, and let $x^*\in\mathbb R^n$.
--
--   1. The **cone** is
--   $$C(A,x^*):=\{x\in\mathbb R^n:\ \operatorname{sign}(a_i^\top x^*)\cdot a_i^\top x\ge0\ \ \forall i\text{ with }a_i^\top x^*\ne0,\quad a_i^\top x=0\ \ \forall i\text{ with }a_i^\top x^*=0\}.$$
--   2. The **spindle** is $S(A,x^*):=C(A,x^*)\cap(x^*-C(A,x^*))$.
--   3. A **face** of a polytope $S$ is a nonempty exposed subset, and a **$d$-face** is a face of affine dimension $d$.
--
--   The spindle is the polytope that sits between $0$ and $x^*$. The paper travels from $x^*$ to $0$ along faces of nested spindles.
--
--   **Formalization Note** Exposed subsets are Mathlib's `IsExposed`; $S$ itself is exposed by the zero functional. For a polytope, the nonempty exposed subsets are exactly its nonempty faces. Affine dimension is the `finrank` of the direction of `affineSpan`.
-- source:
--   Celaya, Kuhlmann, Paat, Weismantel, Proximity and flatness bounds for linear integer optimization, arXiv:2211.14941v1 [math.OC] (preprint, 27 Nov 2022), https://arxiv.org/abs/2211.14941v1, p.5 (C, S); faces and their dimensions as used in Lemma 6, p.8

import Mathlib
import Definitions.Def_ProxFlatIP_Polyhedra

open Matrix

namespace ProxFlatIP

/-! # The cone `C(A,x*)`, the spindle `S(A,x*)`, and faces of a polytope

Celaya–Kuhlmann–Paat–Weismantel, arXiv:2211.14941v1 (preprint): p.5, used on p.8. -/

variable {m n : ℕ}

/-- `C(A,x*) := {x ∈ ℝⁿ : sign(a_i⊤x*) · a_i⊤x ≥ 0 ∀ i with a_i⊤x* ≠ 0,
a_i⊤x = 0 ∀ i with a_i⊤x* = 0}` (p.5). -/
def coneC (A : Matrix (Fin m) (Fin n) ℤ) (xs : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, (realMat A *ᵥ xs) i ≠ 0 → 0 ≤ Real.sign ((realMat A *ᵥ xs) i) * (realMat A *ᵥ x) i) ∧
    ∀ i, (realMat A *ᵥ xs) i = 0 → (realMat A *ᵥ x) i = 0}

/-- `S(A,x*) := C(A,x*) ∩ (x* − C(A,x*))` (p.5). -/
def spindle (A : Matrix (Fin m) (Fin n) ℤ) (xs : Fin n → ℝ) : Set (Fin n → ℝ) :=
  coneC A xs ∩ (fun c => xs - c) '' coneC A xs

/-- `F` is a face of the polytope `S`: a nonempty exposed subset. `S` itself is exposed by the zero
functional. For a polytope these are exactly the nonempty faces. -/
def IsFace (S F : Set (Fin n → ℝ)) : Prop := F.Nonempty ∧ IsExposed ℝ S F

/-- `F` is a `d`-face of `S`: a face of affine dimension `d`. -/
noncomputable def IsDimFace (S : Set (Fin n → ℝ)) (d : ℕ) (F : Set (Fin n → ℝ)) : Prop :=
  IsFace S F ∧ Module.finrank ℝ (affineSpan ℝ F).direction = d

end ProxFlatIP


