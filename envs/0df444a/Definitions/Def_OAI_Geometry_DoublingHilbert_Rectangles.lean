-- Prove2me | Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
-- name    : OAI_Geometry_DoublingHilbert_Rectangles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T22:09:28.235227+00:00
-- url     : https://prove2.me/theorems/f25fcbc4-b8f4-4c2a-a454-34eff50cae88
-- title:
--   Uniform probability on intervals and rectangles, bounded measurable fields, and grid cells
-- statement:
--   This module sets up the averaging framework used for the derivative estimates on the plane.
--
--   1. **Segments and their uniform law.** A segment is a pair of reals $a<b$; its length is $b-a>0$, and its law is the uniform probability measure
--   $$
--   \mu_{[a,b]}=\frac{1}{b-a}\,\lambda|_{(a,b]},
--   $$
--   where $\lambda$ is Lebesgue measure on $\mathbb{R}$. This is a probability measure.
--
--   2. **Rectangles.** A rectangle $Q$ is a pair of segments $[a,b]$ (horizontal) and $[c,d]$ (vertical). Its law is the product $\mu_Q=\mu_{[a,b]}\otimes\mu_{[c,d]}$, the uniform probability on $Q$, so that $\int g\,d\mu_Q$ is the mean of $g$ over $Q$. The closed rectangle is $[a,b]\times[c,d]$, the open rectangle is $(a,b)\times(c,d)$, and the area is $(b-a)(d-c)$. For $p\in\mathbb{R}^2$ and $r>0$, the square centered at $p$ is $[p_1-r,p_1+r]\times[p_2-r,p_2+r]$.
--
--   3. **Bounded fields.** A function $g:X\to E$ on a measurable space $X$ with values in a normed group $E$ is a bounded field if it is strongly measurable and $\sup_x\|g(x)\|<\infty$, that is, $\|g(x)\|\le M$ for some real $M$ and all $x$.
--
--   4. **Grids and cells.** For $a\in\mathbb{R}$, a step $h>0$ and an integer $n>0$, the grid segment is $[a,a+nh]$, of length $nh$; for $i\in\mathbb{N}$ the $i$-th cell is $[a+ih,a+(i+1)h]$, of length $h$.
--
--   Uniform laws turn averages over rectangles into expectations, so that Fubini's theorem and elementary probabilistic inequalities can be applied directly; bounded fields are the class of integrands (derivative columns of Lipschitz maps and their measurable selections) for which all these integrals exist.
--
--   **Formalization Note** The structures are `Segment` (with fields `lo`, `hi` and the proof `lo < hi`) and `Rectangle`; the definitions are `Segment.length`, `Segment.law` (normalized Lebesgue measure on the half-open interval `Ioc lo hi`; the excluded endpoint is a null set), `Rectangle.law`, `Rectangle.closed`, `Rectangle.interior`, `Rectangle.area`, `Rectangle.square`, `IsBoundedField`, `Segment.grid` and `Segment.cell`, together with probability-measure instances and the length formulas `grid_length` and `cell_length`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Rectangles.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Rectangles.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DoublingHilbert mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration

namespace OAI

/-! Rectangle probability measures, transport estimates, and finite averaging. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace DoublingHilbert

/-- Uniform probability on a nondegenerate real interval. -/
structure Segment where
  lo : ℝ
  hi : ℝ
  lt : lo < hi

namespace Segment

def length (I : Segment) : ℝ := I.hi - I.lo

theorem length_pos (I : Segment) : 0 < I.length := sub_pos.mpr I.lt

def law (I : Segment) : Measure ℝ :=
  (ENNReal.ofReal I.length)⁻¹ • volume.restrict (Ioc I.lo I.hi)

instance (I : Segment) : IsProbabilityMeasure I.law := by
  constructor
  simp only [law, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioc, length,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr I.length_pos)
    ENNReal.ofReal_ne_top

end Segment

structure Rectangle where
  x : Segment
  y : Segment

namespace Rectangle

def law (Q : Rectangle) : Measure (ℝ × ℝ) := Q.x.law.prod Q.y.law

def closed (Q : Rectangle) : Set (ℝ × ℝ) :=
  Icc Q.x.lo Q.x.hi ×ˢ Icc Q.y.lo Q.y.hi

def interior (Q : Rectangle) : Set (ℝ × ℝ) :=
  Ioo Q.x.lo Q.x.hi ×ˢ Ioo Q.y.lo Q.y.hi

instance (Q : Rectangle) : IsProbabilityMeasure Q.law := by
  unfold law
  infer_instance

end Rectangle

section BoundedFields
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

/-- Globally bounded strongly measurable fields; all derivative selections below have this property. -/
def IsBoundedField (g : X → E) : Prop :=
  StronglyMeasurable g ∧ ∃ M : ℝ, ∀ x, ‖g x‖ ≤ M

namespace IsBoundedField

end IsBoundedField
end BoundedFields

end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology

namespace Rectangle

end Rectangle

namespace IsBoundedField
variable {X Y I E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E]

variable [NormedSpace ℝ E]

end IsBoundedField
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

section RectangleFTC
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end RectangleFTC
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace Rectangle

def area (Q : Rectangle) : ℝ := Q.x.length * Q.y.length

def square (p : Base) (r : ℝ) (hr : 0 < r) : Rectangle :=
  ⟨⟨p.1 - r, p.1 + r, by linarith⟩, ⟨p.2 - r, p.2 + r, by linarith⟩⟩

end Rectangle

section LocalSquare
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end LocalSquare
end
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

namespace Segment

def grid (a h : ℝ) (n : ℕ) (hh : 0 < h) (hn : 0 < n) : Segment :=
  ⟨a, a + n * h, by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    exact lt_add_of_pos_right a (mul_pos hn' hh)⟩

def cell (a h : ℝ) (hh : 0 < h) (i : ℕ) : Segment :=
  ⟨a + i * h, a + (↑(i + 1) : ℝ) * h, by push_cast; nlinarith⟩

@[simp] theorem grid_length (a h : ℝ) (n : ℕ) (hh : 0 < h) (hn : 0 < n) :
    (grid a h n hh hn).length = n * h := by simp [grid, length]

@[simp] theorem cell_length (a h : ℝ) (hh : 0 < h) (i : ℕ) :
    (cell a h hh i).length = h := by simp [cell, length]; ring

end Segment

namespace Rectangle

end Rectangle
end
end DoublingHilbert

end

end OAI


