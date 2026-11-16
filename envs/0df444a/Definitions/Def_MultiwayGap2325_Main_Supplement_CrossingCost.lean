-- Prove2me | Definitions.Def_MultiwayGap2325_Main_Supplement_CrossingCost
-- name    : MultiwayGap2325_Main_Supplement_CrossingCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:20:27.595422+00:00
-- url     : https://prove2.me/theorems/5419901c-cd69-46ea-bb7f-d86543d81adc
-- title:
--   Essential directional crossings and extended non-opposite-cut cost
-- statement:
--   For a finite labeling $c$ on an interval $J$, let $N(c;J)$ be the least, over all representatives agreeing almost everywhere on $J$, of the supremum of the number of adjacent label changes in finite increasing samples. For an open subset of the line, sum this number over its distinct connected components. For direction $e_i-e_j$ on $\Omega_S$, use the line coordinate $x_i=t$ and transverse coordinates $x_k=y_k$ for $k\notin\{i,j\}$, with $x_j=1-t-\sum y_k$. This chart satisfies $dx=dy\,dt$.
--
--   For open $U$ the crossing mass is
--
--   $$\mu_{ij}^S(C)(U)=\int N\bigl(t\mapsto C(y+t(e_i-e_j));\{t:y+t(e_i-e_j)\in U\cap\operatorname{int}\Omega_S\}\bigr)\,dy.$$
--
--   When all coordinate directions have finite crossings, use the uniquely specified finite Borel measure extending these open-set masses. Its existence is tested from the actual labeling, never supplied as data or required as a hypothesis on a random cut. The extension characterization is the operational meaning of the crossing measure; Fact 5.5 guarantees it for Borel labelings with finite crossings. Without finite crossings or such an extension, the face cost is $+\infty$.
--
--   The actual extended cost is
--
--   $$\operatorname{cost}(C)=\sum_S\sum_{i<j\in S}\int w_{ij}^S\,d\mu_{ij}^S(C)
--   +\sum_S\sum_{i\in S}\int_{\Phi_i^S}g_i^S(y)1[C(y)\ne i]\,d\sigma(y).$$
--
--   It uses the cut's actual boundary labels. Infinite unweighted crossings incur infinite face cost even when a weight vanishes. These definitions give Theorem 3.4 a cost functional independent of all flow inequalities.
--
--   **Formalization Note** Counts and costs take values in $[0,+\infty]$. Integrals of nonnegative functions are lower integrals, not totalized Bochner integrals. A zero fallback in the measure selector is bypassed by the infinite-cost branch whenever no finite extension exists. Ambient cut values outside the simplex are unused.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), Definition 5.4, p. 15; Fact 5.5 and discussion, pp. 16–17; equation (5), p. 5

import Definitions.Def_MultiwayGap2325_Main_Supplement_Geometry

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace MultiwayGap2325.Main.Supplement

attribute [local instance] Classical.propDecidable

/-- Extend an existing cut off the simplex only to evaluate ambient-coordinate formulas.
All geometric integrals are supported on the simplex, so these off-domain values are unused. -/
def ambientCut {q : ℕ} (C : Simplex q → CutLabel q) (x : Vec q) : CutLabel q :=
  if h : x ∈ stdSimplex ℝ (Fin q) then C ⟨x, h⟩ else none

/-- Definition 5.4: supremum over all finite strictly increasing samples in an interval. -/
def changes {q : ℕ} (J : Set ℝ) (c : ℝ → CutLabel q) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (t : Fin (n + 1) → ℝ) (_ : StrictMono t) (_ : ∀ i, t i ∈ J),
    ∑ i : Fin n, if c (t i.castSucc) ≠ c (t i.succ) then (1 : ℝ≥0∞) else 0

/-- Null-set changes do not count. The original function is an admissible representative. -/
def essentialChanges {q : ℕ} (J : Set ℝ) (c : ℝ → CutLabel q) : ℝ≥0∞ :=
  ⨅ (d : ℝ → CutLabel q) (_ : d =ᵐ[volume.restrict J] c), changes J d

/-- The distinct connected components, counted once each. -/
def intervalComponents (A : Set ℝ) : Set (Set ℝ) :=
  {J | ∃ t ∈ A, J = connectedComponentIn A t}

def openChanges {q : ℕ} (A : Set ℝ) (c : ℝ → CutLabel q) : ℝ≥0∞ :=
  ∑' J : intervalComponents A, essentialChanges J.val c

/-- Coordinates transverse to e_i-e_j. Together with x_i=t this chart has determinant ±1. -/
abbrev TransverseCoordinates {q : ℕ} (S : Face q) (i j : Fin q) :=
  {k : Fin q // k ∈ S.val ∧ k ≠ i ∧ k ≠ j}

def coordinateLine {q : ℕ} (S : Face q) (i j : Fin q)
    (y : TransverseCoordinates S i j → ℝ) (t : ℝ) : Vec q :=
  fun k => if k = i then t else if k = j then 1 - t - ∑ a, y a
    else if h : k ∈ S.val ∧ k ≠ i ∧ k ≠ j then y ⟨k, h⟩ else 0

/-- Open-set crossing mass from actual essential line crossings, with dx=dy dt. -/
def crossingMass {q : ℕ} (T : ℝ) (S : Face q) (i j : Fin q)
    (C : Simplex q → CutLabel q) (U : Set (Vec q)) : ℝ≥0∞ :=
  ∫⁻ y : TransverseCoordinates S i j → ℝ,
    openChanges {t | coordinateLine S i j y t ∈ U ∩ omegaInterior T S}
      (fun t => ambientCut C (coordinateLine S i j y t))

/-- Characterizes the finite Borel extension of the open-set masses in Definition 5.4.
It is not supplied as data or a hypothesis on cuts. -/
def IsCrossingMeasure {q : ℕ} (T : ℝ) (S : Face q) (i j : Fin q)
    (C : Simplex q → CutLabel q) (μ : Measure (Vec q)) : Prop :=
  μ Set.univ < ⊤ ∧ ∀ U : Set (Vec q), IsOpen U → μ U = crossingMass T S i j C U

/-- Choice of the uniquely determined finite measure when it exists. The zero fallback is
never used for the cost of a cut without finite crossing measures: that cost is +∞. -/
def crossingMeasure {q : ℕ} (T : ℝ) (S : Face q) (i j : Fin q)
    (C : Simplex q → CutLabel q) : Measure (Vec q) :=
  if h : ∃ μ, IsCrossingMeasure T S i j C μ then h.choose else 0

/-- Both the essential finite-crossing criterion and its Borel extension are operational tests.
The extension exists precisely in the finite-crossing case by the source's Fact 5.5. -/
def HasFiniteCrossings {q : ℕ} (T : ℝ) (S : Face q)
    (C : Simplex q → CutLabel q) : Prop :=
  ∀ ij ∈ directions S,
    crossingMass T S ij.1 ij.2 C Set.univ < ⊤ ∧
    ∃ μ, IsCrossingMeasure T S ij.1 ij.2 C μ

/-- Definition 5.4, including +∞ when any unweighted directional crossing count is infinite. -/
def faceCost {q : ℕ} (T : ℝ) (W : Weighting q) (S : Face q)
    (C : Simplex q → CutLabel q) : ℝ≥0∞ :=
  if HasFiniteCrossings T S C then
    ∑ ij ∈ directions S,
      ∫⁻ x, ENNReal.ofReal (W.weight S ij.1 ij.2 x) ∂crossingMeasure T S ij.1 ij.2 C
  else ⊤

/-- Boundary labels are the original pointwise labels, not BV traces or interior limits. -/
def terminalCost {q : ℕ} (T : ℝ) (W : Weighting q)
    (C : Simplex q → CutLabel q) : ℝ≥0∞ :=
  ∑ S : Face q, ∑ i ∈ S.val,
    ∫⁻ x, if ambientCut C x ≠ some i then ENNReal.ofReal (W.terminal S i x) else 0
      ∂facetMeasure T S i

/-- Actual nonnegative extended cost, with no Bochner-integral totalization. -/
def cutCost {q : ℕ} (T : ℝ) (W : Weighting q)
    (C : Simplex q → CutLabel q) : ℝ≥0∞ :=
  (∑ S : Face q, faceCost T W S C) + terminalCost T W C

end MultiwayGap2325.Main.Supplement


