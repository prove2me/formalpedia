-- Prove2me | Definitions.Def_MultiwayGap2325_Main_Supplement_Geometry
-- name    : MultiwayGap2325_Main_Supplement_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:19:15.291204+00:00
-- url     : https://prove2.me/theorems/2b49e6ae-372b-4339-9d12-82b0114f5d16
-- title:
--   Truncated-face geometry, matched measures and weightings
-- statement:
--   Let $q$ be the number of coordinates and $T$ the truncation threshold. Faces range over all subsets $S\subseteq[q]$ with $|S|\ge2$. The truncated face and terminal facets are
--
--   $$\Omega_S=\{x\in\Delta_q:\operatorname{supp}(x)\subseteq S,\ 0\le x_i\le T\ (i\in S)\},\qquad
--   \Phi_i^S=\{x\in\Omega_S:x_i=T\}.$$
--
--   Volume is Lebesgue measure after deleting the least coordinate of $S$. On a terminal facet, fix $x_i=T$ and delete the least other coordinate; this gives counting mass at an interval endpoint. Interior means relative interior in the affine hull. Cells are compact full-dimensional polytopes specified by finitely many affine inequalities, covering the truncated face with disjoint relative interiors. A weighting supplies finitely many cells, nonnegative symmetric bounded Borel interior densities $w_{ij}^S$, their continuous cell extensions, and bounded nonnegative measurable terminal densities $g_i^S$. The Borel density values on cell walls are retained separately from the extensions.
--
--   The actual terminal mass and fractional cost are
--
--   $$B=\sum_S\sum_{i\in S}\int_{\Phi_i^S}g_i^S\,d\sigma,\qquad
--   L=\sum_S\sum_{i<j\in S}\int_{\Omega_S}w_{ij}^S\,dx+(1-T)B.$$
--
--   These definitions reuse the published full real simplex. They provide the geometric and weighting interface for the three additional theorems.
--
--   **Formalization Note** Ambient coordinate functions are used only on the stated affine hulls. Pushforward measures come from explicit continuous affine charts. Regularity is a predicate on raw data; no target identity or cost bound is a constructor field.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), §§3.2, 5.1, pp. 5–6, 11–13, equations (6)–(7), (11)–(12)

import Definitions.Def_MultiwayGap2325_Main_RandomCuts

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace MultiwayGap2325.Main.Supplement

/-- Every source face is present, including the intervals. -/
abbrev Face (q : ℕ) := {S : Finset (Fin q) // 2 ≤ S.card}
abbrev Vec (q : ℕ) := Fin q → ℝ

def pivot {q : ℕ} (S : Face q) : Fin q :=
  S.val.min' (Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) S.property))

abbrev Coordinates {q : ℕ} (S : Face q) :=
  {i : Fin q // i ∈ S.val ∧ i ≠ pivot S}

/-- Affine hull and relative interior use the existing full real simplex. -/
def hull {q : ℕ} (S : Face q) : Set (Vec q) :=
  {x | (∀ i, i ∉ S.val → x i = 0) ∧ ∑ i ∈ S.val, x i = 1}

def omega {q : ℕ} (T : ℝ) (S : Face q) : Set (Vec q) :=
  {x | x ∈ hull S ∧ ∀ i ∈ S.val, 0 ≤ x i ∧ x i ≤ T}

def omegaInterior {q : ℕ} (T : ℝ) (S : Face q) : Set (Vec q) :=
  {x | x ∈ hull S ∧ ∀ i ∈ S.val, 0 < x i ∧ x i < T}

def terminalFacet {q : ℕ} (T : ℝ) (S : Face q) (i : Fin q) : Set (Vec q) :=
  {x | x ∈ omega T S ∧ x i = T}

/-- Delete the pivot coordinate. The Jacobians between such charts have modulus one. -/
def lift {q : ℕ} (S : Face q) (y : Coordinates S → ℝ) : Vec q :=
  fun i => if i = pivot S then 1 - ∑ j, y j
    else if h : i ∈ S.val ∧ i ≠ pivot S then y ⟨i, h⟩ else 0

def drop {q : ℕ} (S : Face q) (x : Vec q) : Coordinates S → ℝ :=
  fun i => x i.val

def faceVolume {q : ℕ} (T : ℝ) (S : Face q) : Measure (Vec q) :=
  (Measure.map (lift S) volume).restrict (omega T S)

/-- For a terminal facet, keep i fixed and delete a different coordinate. -/
def facetPivot {q : ℕ} (S : Face q) (i : Fin q) : Fin q :=
  if h : (S.val.erase i).Nonempty then (S.val.erase i).min' h else pivot S

abbrev FacetCoordinates {q : ℕ} (S : Face q) (i : Fin q) :=
  {j : Fin q // j ∈ S.val ∧ j ≠ i ∧ j ≠ facetPivot S i}

def facetLift {q : ℕ} (T : ℝ) (S : Face q) (i : Fin q)
    (y : FacetCoordinates S i → ℝ) : Vec q :=
  fun j => if j = i then T else if j = facetPivot S i then 1 - T - ∑ k, y k
    else if h : j ∈ S.val ∧ j ≠ i ∧ j ≠ facetPivot S i then y ⟨j, h⟩ else 0

/-- Matched surface measure; when |S|=2 this is unit counting mass at the endpoint. -/
def facetMeasure {q : ℕ} (T : ℝ) (S : Face q) (i : Fin q) : Measure (Vec q) :=
  (Measure.map (facetLift T S i) volume).restrict (terminalFacet T S i)

/-- A compact polytope given by finitely many affine inequalities in the face hull. -/
def IsCell {q : ℕ} (S : Face q) (P : Set (Vec q)) : Prop :=
  P ⊆ hull S ∧ IsCompact P ∧
  (interior (lift S ⁻¹' P)).Nonempty ∧
  ∃ n : ℕ, ∃ a : Fin n → Vec q, ∃ b : Fin n → ℝ,
    P = {x | x ∈ hull S ∧ ∀ k, ∑ i ∈ S.val, a k i * x i ≤ b k}

/-- Finite full-dimensional subdivision, fixed independently of a cut. -/
def IsSubdivision {q : ℕ} (T : ℝ) (S : Face q)
    (cells : Finset (Set (Vec q))) : Prop :=
  (∀ P ∈ cells, IsCell S P) ∧
  (∀ x, x ∈ omega T S ↔ ∃ P ∈ cells, x ∈ P) ∧
  ∀ P ∈ cells, ∀ Q ∈ cells, P ≠ Q →
    Disjoint (interior (lift S ⁻¹' P)) (interior (lift S ⁻¹' Q))

/-- Unordered directions are enumerated once. Symmetry is imposed on the densities. -/
def directions {q : ℕ} (S : Face q) : Finset (Fin q × Fin q) :=
  (S.val.product S.val).filter (fun ij => ij.1 < ij.2)

/-- Raw weighting data. Regularity is a separate predicate, not a constructor requirement. -/
structure Weighting (q : ℕ) where
  cells : Face q → Finset (Set (Vec q))
  weight : Face q → Fin q → Fin q → Vec q → ℝ
  cellWeight : Face q → Set (Vec q) → Fin q → Fin q → Vec q → ℝ
  terminal : Face q → Fin q → Vec q → ℝ

def Weighting.Regular {q : ℕ} (T : ℝ) (W : Weighting q) : Prop :=
  (∀ S, IsSubdivision T S (W.cells S)) ∧
  (∀ S i j, i ∈ S.val → j ∈ S.val → i ≠ j →
    Measurable ((omega T S).indicator (W.weight S i j)) ∧
    (∀ x ∈ omega T S, 0 ≤ W.weight S i j x ∧
      W.weight S i j x = W.weight S j i x) ∧
    (∃ M : ℝ, ∀ x ∈ omega T S, |W.weight S i j x| ≤ M) ∧
    ∀ P ∈ W.cells S,
      ContinuousOn (fun y => W.cellWeight S P i j (lift S y)) (lift S ⁻¹' P) ∧
      ∀ y ∈ interior (lift S ⁻¹' P),
        W.cellWeight S P i j (lift S y) = W.weight S i j (lift S y)) ∧
  (∀ S i, i ∈ S.val →
    Measurable ((terminalFacet T S i).indicator (W.terminal S i)) ∧
    (∀ x ∈ terminalFacet T S i, 0 ≤ W.terminal S i x) ∧
    ∃ M : ℝ, ∀ x ∈ terminalFacet T S i, |W.terminal S i x| ≤ M)

/-- The actual terminal-edge mass, equation (6). -/
def totalB {q : ℕ} (T : ℝ) (W : Weighting q) : ℝ :=
  ∑ S : Face q, ∑ i ∈ S.val, ∫ x, W.terminal S i x ∂facetMeasure T S i

/-- Fractional cost in the half-L1 metric, equation (7). -/
def totalL {q : ℕ} (T : ℝ) (W : Weighting q) : ℝ :=
  (∑ S : Face q, ∑ ij ∈ directions S, ∫ x, W.weight S ij.1 ij.2 x ∂faceVolume T S) +
    (1 - T) * totalB T W

end MultiwayGap2325.Main.Supplement


