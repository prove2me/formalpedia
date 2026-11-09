-- Prove2me | Definitions.Def_MultiSpinCounting_Positive_Polytopes
-- name    : MultiSpinCounting_Positive_Polytopes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:22:27.175373+00:00
-- url     : https://prove2.me/theorems/d6f11e6c-6811-48b7-b1e7-7010f47e69bb
-- title:
--   Explicit rational constraint recursion and finite Hilbert diameters
-- statement:
--   A rational polytope is stored as a finite list of rational linear inequalities in $q$ real coordinates, with its actual coefficient serialization. At an isolated vertex it is the exact normalized field vector. Otherwise it contains nonnegativity, normalization, and the pairwise constraints
--   $$L^t_{ab}z_b\le z_a\le U^t_{ab}z_b\quad(a\ne b).$$
--   At depth zero the coefficients are the field ratio times the products of minimum or maximum interaction-row ratios. At positive depth, the child instance and its depth-$t-1$ polytope are explicitly reconstructed for every neighbor and ordered spin pair; the real minimum and maximum row-ratio objectives are rounded outward before their products form $L^t_{ab},U^t_{ab}$. The same $P$ is used throughout.
--
--   The Hilbert diameter is the supremum of the published Hilbert distances over pairs of feasible points. Well-definedness is a conclusion predicate: nonempty compact feasible set, strictly positive coordinates, bounded Hilbert distances, and attainment of that diameter. Child optimization well-definedness additionally asserts positive denominators and attained positive minima and attained maxima. These properties are never assumed in the polytope data.
--
--   With $\bar\Delta=4\operatorname{arctanh}c$ and $\rho=Dc$, the depth and precision functions are exactly the natural ceilings in (4.6), with constants $4$ and $32$ and minimum precision $3$. The definitions isolate the construction from the subsequent soundness and accuracy theorems.
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), pp. 14–16, Definition 4.1, (4.1)–(4.6)

import Mathlib
import Definitions.Def_MultiSpinCounting_Positive_Rounding

noncomputable section

namespace MultiSpinCounting.Positive
open OnlineCRS.Combine

/-- Explicit rational inequality data, not a set equipped with soundness axioms. -/
structure PolyData (q : ℕ) where
  rows : List ((Fin q → ℚ) × ℚ)

def polySet {q : ℕ} (B : PolyData q) : Set (Fin q → ℝ) :=
  {z | ∀ r ∈ B.rows, ∑ a, (r.1 a : ℝ) * z a ≤ (r.2 : ℝ)}

def encPoly {q : ℕ} (B : PolyData q) : List Sym :=
  encNat q ++ [3] ++ encNat B.rows.length ++ [3] ++
    B.rows.flatMap (fun r => encVec r.1 ++ encRat r.2 ++ [3])

def finiteMin {q : ℕ} (f : Fin q → ℚ) : ℚ := by
  classical
  exact if h : (Finset.univ.image f).Nonempty then (Finset.univ.image f).min' h else 0

def finiteMax {q : ℕ} (f : Fin q → ℚ) : ℚ := by
  classical
  exact if h : (Finset.univ.image f).Nonempty then (Finset.univ.image f).max' h else 0

/-- The actual rows of (4.1)--(4.4), or two inequalities per singleton equality. -/
def makePoly {n q : ℕ} (Φ : Instance n q ℚ) (v : Fin n)
    (L U : Fin q → Fin q → ℚ) : PolyData q := by
  classical
  exact if (neighbors Φ v).Nonempty then
    ⟨((List.finRange q).map (fun a => (fun c => if c = a then -1 else 0, 0))) ++
      [(fun _ => 1, 1), (fun _ => -1, -1)] ++
      ((List.finRange q).flatMap (fun a =>
        ((List.finRange q).filter (fun b => b ≠ a)).flatMap (fun b =>
          [(fun c => (if c = b then L a b else 0) - (if c = a then 1 else 0), 0),
           (fun c => (if c = a then 1 else 0) - (if c = b then U a b else 0), 0)])))⟩
    else ⟨(List.finRange q).flatMap (fun a =>
      [(fun c => if c = a then 1 else 0, Φ.field v a / ∑ c, Φ.field v c),
       (fun c => if c = a then -1 else 0, -(Φ.field v a / ∑ c, Φ.field v c))])⟩

def rowRatio {n q : ℕ} (Φ : Instance n q ℚ) (v i : Fin n)
    (a b : Fin q) (z : Fin q → ℝ) : ℝ :=
  (∑ c, (Φ.interaction v i a c : ℝ) * z c) /
    (∑ c, (Φ.interaction v i b c : ℝ) * z c)

/-- Recursion is on depth, with new explicit child data at each call. P is fixed. -/
def polyData {n q : ℕ} (P : ℕ) : ℕ → Instance n q ℚ → Fin n → PolyData q
  | 0, Φ, v => makePoly Φ v
      (fun a b => Φ.field v a / Φ.field v b *
        ∏ i ∈ neighbors Φ v, finiteMin (fun c => Φ.interaction v i a c / Φ.interaction v i b c))
      (fun a b => Φ.field v a / Φ.field v b *
        ∏ i ∈ neighbors Φ v, finiteMax (fun c => Φ.interaction v i a c / Φ.interaction v i b c))
  | t+1, Φ, v => makePoly Φ v
      (fun a b => Φ.field v a / Φ.field v b *
        ∏ i ∈ neighbors Φ v, roundDown P
          (sInf (rowRatio Φ v i a b '' polySet (polyData P t (child Φ v i a b) i))))
      (fun a b => Φ.field v a / Φ.field v b *
        ∏ i ∈ neighbors Φ v, roundUp P
          (sSup (rowRatio Φ v i a b '' polySet (polyData P t (child Φ v i a b) i))))

def polytope {n q : ℕ} (P t : ℕ) (Φ : Instance n q ℚ) (v : Fin n) : Set (Fin q → ℝ) :=
  polySet (polyData P t Φ v)

def hilbertValues {q : ℕ} (T : Set (Fin q → ℝ)) : Set ℝ :=
  {r | ∃ x ∈ T, ∃ y ∈ T, r = CompOT.Sinkhorn.hilbertMetric x y}

def hilbertDiameter {q : ℕ} (T : Set (Fin q → ℝ)) : ℝ := sSup (hilbertValues T)

/-- All domain requirements are conclusions of Fact 4.2, never query hypotheses. -/
def PolyWellDefined {q : ℕ} (T : Set (Fin q → ℝ)) : Prop :=
  T.Nonempty ∧ IsCompact T ∧ (∀ z ∈ T, ∀ a, 0 < z a) ∧
  BddAbove (hilbertValues T) ∧
  (∃ x ∈ T, ∃ y ∈ T, CompOT.Sinkhorn.hilbertMetric x y = hilbertDiameter T)

def ExtremaWellDefined {n q : ℕ} (P t : ℕ) (Φ : Instance n q ℚ) (v : Fin n) : Prop :=
  ∀ a b : Fin q, a ≠ b → ∀ i ∈ neighbors Φ v,
    let T := polytope P t (child Φ v i a b) i
    T.Nonempty ∧ IsCompact T ∧
    (∀ z ∈ T, 0 < ∑ c, (Φ.interaction v i b c : ℝ) * z c) ∧
    (∃ z ∈ T, IsLeast (rowRatio Φ v i a b '' T) (rowRatio Φ v i a b z) ∧
      0 < rowRatio Φ v i a b z) ∧
    (∃ z ∈ T, IsGreatest (rowRatio Φ v i a b '' T) (rowRatio Φ v i a b z))

def accuracyDepth (N : ℕ) (K α D c ε : ℝ) : ℕ :=
  ⌈Real.log (4*K*(N:ℝ)^α*D*max 1 (4*Real.artanh c)/ε) / Real.log (1/(D*c))⌉₊

def accuracyPrecision (N : ℕ) (K α D c ε : ℝ) : ℕ :=
  max 3 ⌈Real.log (32*K*(N:ℝ)^α*D/(ε*(1-D*c))) / Real.log 2⌉₊

end MultiSpinCounting.Positive


