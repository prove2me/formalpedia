-- Prove2me | Definitions.Def_LogBarrierIPM_Iterations_Supplement_PuiseuxGeometry
-- name    : LogBarrierIPM_Iterations_Supplement_PuiseuxGeometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T17:08:19.661079+00:00
-- url     : https://prove2.me/theorems/def03851-f88c-4c49-9f62-ed73e511ac80
-- title:
--   Puiseux polyhedra, generation, tropical polyhedra and directed metrics
-- statement:
--   Let $K$ be the field of absolutely convergent generalized real Puiseux series and $\mathbb T=\mathbb R\cup\{-\infty\}$. For $A\in K^{p\times d}$ and $b\in K^p$, define
--   $$\mathcal P=\{x:Ax\le b\},\qquad \mathcal P(t)=\{x\in\mathbb R^d:A(t)x\le b(t)\}.$$
--   Equations and order over $K$ mean the corresponding relations between evaluations for every sufficiently large $t$. Finite nonnegative combinations define convex-hull-plus-cone generation over both fields. A tropical polyhedron is an intersection of finitely many tropical affine halfspaces; boundedness means a finite coordinatewise upper bound. The affine Hilbert distance is $d_H(x,y)=\delta_F(x,y)+\delta_F(y,x)$. Its directed set distance, and that for $d_\infty$, use supremum $0$ for an empty source and infimum $+\infty$ for an empty target. These interfaces supply §§3.1–3.3 without replacing the already published series, logarithm or Funk metric.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 8, def-puiseux-polyhedron

import Mathlib
import Definitions.Def_LogBarrierIPM_Curvature_PuiseuxLP
import Definitions.Def_LogBarrierIPM_Iterations_LogMetrics

open Filter Matrix

namespace LogBarrierIPM.Iterations.Supplement

open LogBarrierIPM.Curvature

/-- Arithmetic and order over K are expressed through eventual evaluations (p. 7). -/
def KNonneg (f : Puiseux) : Prop := ∀ᶠ t in atTop, 0 ≤ f.eval t

def KPositive (f : Puiseux) : Prop := ∀ᶠ t in atTop, 0 < f.eval t

def KEq (f g : Puiseux) : Prop := ∀ᶠ t in atTop, f.eval t = g.eval t

def KLe (f g : Puiseux) : Prop := ∀ᶠ t in atTop, f.eval t ≤ g.eval t

/-- Real specialization and the polyhedron (9), with no artificial orthant rows. -/
def realPolyhedron {p d : ℕ} (A : Matrix (Fin p) (Fin d) Puiseux)
    (b : Fin p → Puiseux) (t : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, ∑ j, (A i j).eval t * x j ≤ (b i).eval t}

def kPolyhedron {p d : ℕ} (A : Matrix (Fin p) (Fin d) Puiseux)
    (b : Fin p → Puiseux) : Set (Fin d → Puiseux) :=
  {x | ∀ᶠ t in atTop, evalFun x t ∈ realPolyhedron A b t}

def kOrthant {d : ℕ} (P : Set (Fin d → Puiseux)) : Prop :=
  ∀ x ∈ P, ∀ i, KNonneg (x i)

/-- A finite nonnegative convex combination plus a finite nonnegative conic combination. -/
def realGenerated {d q r : ℕ} (u : Fin q → Fin d → ℝ)
    (v : Fin r → Fin d → ℝ) : Set (Fin d → ℝ) :=
  {x | ∃ α : Fin q → ℝ, ∃ β : Fin r → ℝ,
    (∀ i, 0 ≤ α i) ∧ (∀ j, 0 ≤ β j) ∧ (∑ i, α i) = 1 ∧
    ∀ k, x k = (∑ i, α i * u i k) + ∑ j, β j * v j k}

def kGenerated {d q r : ℕ} (u : Fin q → Fin d → Puiseux)
    (v : Fin r → Fin d → Puiseux) : Set (Fin d → Puiseux) :=
  {x | ∃ α : Fin q → Puiseux, ∃ β : Fin r → Puiseux,
    ∀ᶠ t in atTop, (∀ i, 0 ≤ (α i).eval t) ∧ (∀ j, 0 ≤ (β j).eval t) ∧
      (∑ i, (α i).eval t) = 1 ∧
      ∀ k, (x k).eval t = (∑ i, (α i).eval t * (u i k).eval t) +
        ∑ j, (β j).eval t * (v j k).eval t}

/-- Tropical affine halfspaces, including p = 0 and bottom coordinates. -/
def IsTropicalPolyhedron {d : ℕ} (P : Set (Fin d → WithBot ℝ)) : Prop :=
  ∃ p : ℕ, ∃ A A' : Matrix (Fin p) (Fin d) (WithBot ℝ),
    ∃ b b' : Fin p → WithBot ℝ,
    P = {x | ∀ i, max (Finset.univ.sup (fun j => A i j + x j)) (b i) ≤
      max (Finset.univ.sup (fun j => A' i j + x j)) (b' i)}

def TropicalBounded {d : ℕ} (P : Set (Fin d → WithBot ℝ)) : Prop :=
  ∃ M : Fin d → ℝ, ∀ x ∈ P, ∀ i, x i ≤ (M i : WithBot ℝ)

/-- The affine Hilbert metric, always in [0,+∞]; no bottom-plus-top arithmetic. -/
noncomputable def dHilbert {d : ℕ} (x y : Fin d → WithBot ℝ) : EReal :=
  funk x y + funk y x

/-- Directed distances: sup of an empty source is 0; inf of an empty target is +∞. -/
noncomputable def directedDistance {d : ℕ}
    (D : (Fin d → WithBot ℝ) → (Fin d → WithBot ℝ) → EReal)
    (X Y : Set (Fin d → WithBot ℝ)) : EReal :=
  max 0 (⨆ x ∈ X, ⨅ y ∈ Y, D x y)

noncomputable def hausdorffH {d : ℕ} (X Y : Set (Fin d → WithBot ℝ)) : EReal :=
  directedDistance dHilbert X Y

noncomputable def hausdorffInf {d : ℕ} (X Y : Set (Fin d → WithBot ℝ)) : EReal :=
  directedDistance dInf X Y

noncomputable def logImage {d : ℕ} (t : ℝ) (P : Set (Fin d → ℝ)) :
    Set (Fin d → WithBot ℝ) := logtVec t '' P

end LogBarrierIPM.Iterations.Supplement


