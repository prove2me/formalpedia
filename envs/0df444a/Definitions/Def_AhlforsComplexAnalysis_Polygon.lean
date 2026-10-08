-- Prove2me | Definitions.Def_AhlforsComplexAnalysis_Polygon
-- name    : AhlforsComplexAnalysis_Polygon
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-06T12:18:23.31001+00:00
-- url     : https://prove2.me/theorems/501f0877-da78-43aa-94ef-714be77e9a71
-- title:
--   Polygonal paths, their integrals and winding function
-- statement:
--   A *polygon* is a finite list of vertices $\ell=[v_0,v_1,\dots,v_n]$ in $\mathbb C$, traversed along the
--   segments $[v_0,v_1],\dots,[v_{n-1},v_n]$; it is *closed* if $v_0=v_n$. For $g:\mathbb C\to\mathbb C$ the integral along
--   $\ell$ is the sum of the segment integrals,
--
--   $$\int_\ell g\,dz=\sum_{k<n}\int_0^1 g\bigl(v_k+t(v_{k+1}-v_k)\bigr)\,(v_{k+1}-v_k)\,dt .$$
--
--   Integrals are interval integrals in the sense of Lean, which are $0$ for non-integrable integrands; every statement below holds under this convention, and for continuous $g$ the integral is the usual line integral.
--
--   The module also defines
--
--   * `PolyIn U l`: every segment of the polygon lies in the set $U$ (for a one-vertex polygon: its vertex lies in $U$);
--   * `polyTrace l`: the set of points of the polygon, the union of its segments (for a one-vertex polygon: that vertex);
--   * `IsClosedPoly l`: the polygon is nonempty and closed ($v_0=v_n$);
--   * `windInt l a`$=\int_\ell\frac{dz}{z-a}$, which is $2\pi i$ times the winding number of a closed polygon about $a\notin\ell$. It is deliberately kept complex valued: no integrality of winding numbers is used anywhere in this development. For $a$ on the polygon the value is a junk value with no geometric meaning, and no statement in this development evaluates it there.
--
--   Integrals are interval integrals in the sense of Lean, which are $0$ for non-integrable integrands.
--
--   Two structural facts are recorded with the definitions: the trace of a polygon is compact, and it is contained in $U$ whenever the polygon lies in $U$.
--
--   These polygonal paths are the curves used to prove the general (homology) form of Cauchy's theorem in the style of Dixon, which in turn gives the existence of logarithms and roots on regions with connected complement in the extended plane.
-- source:
--   Polygonal version of the general (homology) Cauchy theorem: L. V. Ahlfors, Complex Analysis, 3rd ed., McGraw-Hill, 1979, Ch. 4 section 4 (the general statement of Cauchy's theorem and its proof, due to Dixon); also Rudin, Real and Complex Analysis, 3rd ed., Ch. 10 (Cauchy's theorem for cycles)

import Mathlib

namespace AhlforsComplexAnalysis.Polygon

open Set

/-- Integral of `g` along the segment from `a` to `b`, parametrised by `t ↦ a + t (b - a)`, `t ∈ [0, 1]`. -/
noncomputable def segInt (g : ℂ → ℂ) (a b : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, g (a + (t : ℂ) * (b - a)) * (b - a)

/-- Integral of `g` along the polygonal path through the vertices `[v₀, v₁, …, vₙ]`
(the sum of the segment integrals over consecutive vertices). -/
noncomputable def polyInt (g : ℂ → ℂ) : List ℂ → ℂ
  | a :: b :: rest => segInt g a b + polyInt g (b :: rest)
  | _ => 0

/-- Every segment of the polygon (and, for a one-vertex polygon, its vertex) lies in `U`. -/
def PolyIn (U : Set ℂ) : List ℂ → Prop
  | a :: b :: rest => segment ℝ a b ⊆ U ∧ PolyIn U (b :: rest)
  | [a] => a ∈ U
  | [] => True

/-- The set of points of the polygon: the union of its segments. -/
def polyTrace : List ℂ → Set ℂ
  | a :: b :: rest => segment ℝ a b ∪ polyTrace (b :: rest)
  | [a] => {a}
  | [] => ∅

/-- A polygon is closed when it is nonempty and its first and last vertices coincide. -/
def IsClosedPoly (l : List ℂ) : Prop := l ≠ [] ∧ l.head? = l.getLast?

/-- `2πi` times the winding number of the polygon `l` about the point `a`, that is
`∫_l dz / (z - a)`. It is deliberately kept complex valued. -/
noncomputable def windInt (l : List ℂ) (a : ℂ) : ℂ := polyInt (fun z => (z - a)⁻¹) l

@[simp] lemma polyInt_nil (g : ℂ → ℂ) : polyInt g [] = 0 := rfl

@[simp] lemma polyInt_singleton (g : ℂ → ℂ) (a : ℂ) : polyInt g [a] = 0 := rfl

lemma polyInt_cons_cons (g : ℂ → ℂ) (a b : ℂ) (rest : List ℂ) :
    polyInt g (a :: b :: rest) = segInt g a b + polyInt g (b :: rest) := rfl

lemma polyIn_cons_cons (U : Set ℂ) (a b : ℂ) (rest : List ℂ) :
    PolyIn U (a :: b :: rest) ↔ segment ℝ a b ⊆ U ∧ PolyIn U (b :: rest) := Iff.rfl

lemma polyIn_singleton (U : Set ℂ) (a : ℂ) : PolyIn U [a] ↔ a ∈ U := Iff.rfl

/-- The trace of a polygon is compact. -/
theorem polyTrace_isCompact (l : List ℂ) : IsCompact (polyTrace l) := by
  induction l with
  | nil => simp [polyTrace]
  | cons a t ih =>
    cases t with
    | nil => simp [polyTrace]
    | cons b rest =>
      have hseg : IsCompact (segment ℝ a b) := by
        rw [segment_eq_image' ℝ a b]
        exact isCompact_Icc.image (by fun_prop)
      exact hseg.union ih

/-- If a polygon lies in `U` then its trace is contained in `U`. -/
theorem polyTrace_subset {U : Set ℂ} {l : List ℂ} (hl : PolyIn U l) : polyTrace l ⊆ U := by
  induction l with
  | nil => simp [polyTrace]
  | cons a t ih =>
    cases t with
    | nil => simpa [polyTrace] using (polyIn_singleton U a).1 hl
    | cons b rest =>
      rw [polyIn_cons_cons] at hl
      exact Set.union_subset hl.1 (ih hl.2)

end AhlforsComplexAnalysis.Polygon


