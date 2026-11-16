-- Prove2me | Definitions.Def_MultiwayGap2325_Main_Supplement_Flows
-- name    : MultiwayGap2325_Main_Supplement_Flows
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:19:51.089205+00:00
-- url     : https://prove2.me/theorems/590945fe-71e4-4f39-b843-488a833218c0
-- title:
--   Cellwise label flows, capacity, conservation and actual allowance
-- statement:
--   For every truncated face $\Omega_S$ and every allowed label $\ell\in S\cup\{*\}$, raw flow data supply a vector-field formula on each cell, and a nonnegative allowance density $\epsilon^S$. The star flow is zero. Valid fields are bounded and tangent, continuously differentiable on each closed cell, with equal normal components across shared facets; tangential components may jump.
--
--   For every point of each closed cell, all allowed labels $\ell,m$, and every nonempty proper subset $I\subset S$, capacity requires
--
--   $$\left|\sum_{i\in I}(F_{\ell,i}^S-F_{m,i}^S)\right|
--   \le\sum_{i\in I,j\in S\setminus I}w_{ij}^S.$$
--
--   Here weights at a cell boundary use the continuous extension from that cell. The terminal condition is $F_{\ell,i}^S=g_i^S1[\ell=i]$ on $\Phi_i^S$. Conservation requires, almost everywhere on each face,
--
--   $$\operatorname{div}F_\ell^S\le-\sum_{j\notin S}F_{\ell,j}^{S\cup\{j\}}+\epsilon^S.$$
--
--   Divergence is the trace of the derivative in deleted coordinates. Parent supply uses the parent's field at the same geometric point. Each face has its own field. Allowances are integrable, and their total is computed once per face:
--
--   $$R=\sum_S\int_{\Omega_S}\epsilon^S\,dx.$$
--
--   Flow-instance validity consists of the preceding regularity, capacity, terminal and conservation conditions, with the weighting regularity. It contains no lower bound, cost inequality, certificate existence or optimality assumption. Separate predicates express that label fields are affine on their entire faces and that interior and terminal densities are constant. These allow the existence result to assert its geometric structure explicitly.
--
--   **Formalization Note** A fixed incident-cell choice evaluates formulas on cell walls. Normal continuity makes the relevant normal fluxes agree on shared facets. The source's almost-everywhere conservation leaves lower-dimensional cell intersections immaterial.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), Definition 3.3, p. 7; §5.1, pp. 11–13, equations (8)–(9), (11)–(13)

import Definitions.Def_MultiwayGap2325_Main_Supplement_Geometry

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace MultiwayGap2325.Main.Supplement

attribute [local instance] Classical.propDecidable

/-- The star label and precisely the terminal labels of this face. -/
def Allowed {q : ℕ} (S : Face q) (l : CutLabel q) : Prop :=
  l = none ∨ ∃ i ∈ S.val, l = some i

/-- Raw cell formulas and allowances, without validity or any target inequality. -/
structure FlowData (q : ℕ) where
  weighting : Weighting q
  field : (S : Face q) → Set (Vec q) → CutLabel q → Vec q → Vec q
  allowance : Face q → Vec q → ℝ

/-- A fixed choice of incident cell. Only normal components are independent on cell walls. -/
def incidentCell {q : ℕ} (D : FlowData q) (S : Face q) (x : Vec q) : Set (Vec q) :=
  if h : ∃ P ∈ D.weighting.cells S, x ∈ P then h.choose else ∅

def flowAt {q : ℕ} (D : FlowData q) (S : Face q) (l : CutLabel q) (x : Vec q) : Vec q :=
  D.field S (incidentCell D S x) l x

/-- Trace of the derivative in the independent coordinates, with the cell formula at its walls. -/
def cellDivergence {q : ℕ} (D : FlowData q) (S : Face q)
    (P : Set (Vec q)) (l : CutLabel q) (x : Vec q) : ℝ :=
  ∑ i : Coordinates S,
    (fderivWithin ℝ (fun y => D.field S P l (lift S y) i.val)
      (lift S ⁻¹' P) (drop S x)) (Pi.single i 1)

def divergenceAt {q : ℕ} (D : FlowData q) (S : Face q)
    (l : CutLabel q) (x : Vec q) : ℝ :=
  cellDivergence D S (incidentCell D S x) l x

/-- Normal covectors live on all coordinates; adding a constant has no effect on tangent flows. -/
def pairing {q : ℕ} (S : Face q) (a v : Vec q) : ℝ := ∑ i ∈ S.val, a i * v i

/-- Common facets, rather than lower-dimensional intersections, carry normal matching. -/
def CommonFacet {q : ℕ} (S : Face q) (P Q : Set (Vec q)) (a : Vec q) (b : ℝ) : Prop :=
  (P ∩ Q).Nonempty ∧
  Module.finrank ℝ (vectorSpan ℝ (P ∩ Q)) = S.val.card - 2 ∧
  (∃ i ∈ S.val, ∃ j ∈ S.val, a i ≠ a j) ∧
  (∀ x ∈ P, pairing S a x ≤ b) ∧
  (∀ x ∈ Q, b ≤ pairing S a x)

def FlowData.Regular {q : ℕ} (T : ℝ) (D : FlowData q) : Prop :=
  D.weighting.Regular T ∧
  (∀ S P, P ∈ D.weighting.cells S → ∀ l, Allowed S l →
    ContDiffOn ℝ 1 (fun y => D.field S P l (lift S y)) (lift S ⁻¹' P) ∧
    (∀ x ∈ P, (∀ i, i ∉ S.val → D.field S P l x i = 0) ∧
      ∑ i ∈ S.val, D.field S P l x i = 0) ∧
    (∃ M : ℝ, ∀ x ∈ P, ‖D.field S P l x‖ ≤ M)) ∧
  (∀ S P, P ∈ D.weighting.cells S → ∀ x ∈ P, D.field S P none x = 0) ∧
  (∀ S P, P ∈ D.weighting.cells S → ∀ Q ∈ D.weighting.cells S, P ≠ Q →
    ∀ a b, CommonFacet S P Q a b → ∀ l, Allowed S l → ∀ x ∈ P ∩ Q,
      pairing S a (D.field S P l x) = pairing S a (D.field S Q l x)) ∧
  (∀ S, (∀ x ∈ omega T S, 0 ≤ D.allowance S x) ∧
    Integrable (D.allowance S) (faceVolume T S))

/-- Equation (8) at every point of every closed cell. -/
def Capacity {q : ℕ} (D : FlowData q) : Prop :=
  ∀ S P, P ∈ D.weighting.cells S → ∀ x ∈ P,
    ∀ l m, Allowed S l → Allowed S m → ∀ I : Finset (Fin q),
      I.Nonempty → I ⊂ S.val →
      |∑ i ∈ I, (D.field S P l x i - D.field S P m x i)| ≤
        ∑ i ∈ I, ∑ j ∈ S.val \ I, D.weighting.cellWeight S P i j x

/-- The actual terminal boundary values, using every incident cell's formula. -/
def TerminalCondition {q : ℕ} (T : ℝ) (D : FlowData q) : Prop :=
  ∀ S P, P ∈ D.weighting.cells S → ∀ i ∈ S.val,
    ∀ x ∈ P ∩ terminalFacet T S i, ∀ l, Allowed S l →
      D.field S P l x i = if l = some i then D.weighting.terminal S i x else 0

def parent {q : ℕ} (S : Face q) (j : Fin q) : Face q :=
  ⟨insert j S.val, le_trans S.property (Finset.card_le_card (Finset.subset_insert j S.val))⟩

/-- The source sign is minus the parent coordinate flow, not the child's field. -/
def incomingSupply {q : ℕ} (D : FlowData q) (S : Face q)
    (l : CutLabel q) (x : Vec q) : ℝ :=
  - ∑ j ∈ Finset.univ \ S.val, flowAt D (parent S j) l x j

/-- Equation (9) almost everywhere; the top face has the empty parent sum. -/
def Conservation {q : ℕ} (T : ℝ) (D : FlowData q) : Prop :=
  ∀ S l, Allowed S l → ∀ᵐ x ∂faceVolume T S,
    divergenceAt D S l x ≤ incomingSupply D S l x + D.allowance S x

/-- Definition 3.3 with exactly the regularity specified in §5.1. No cost bounds occur here. -/
def IsFlowInstance {q : ℕ} (T : ℝ) (D : FlowData q) : Prop :=
  D.Regular T ∧ Capacity D ∧ TerminalCondition T D ∧ Conservation T D

/-- Each face's allowance is counted once, never once per label. -/
def totalR {q : ℕ} (T : ℝ) (D : FlowData q) : ℝ :=
  ∑ S : Face q, ∫ x, D.allowance S x ∂faceVolume T S

/-- For the existential statement in Theorem 3.5, affine on each whole truncated face. -/
def HasAffineLabelFlows {q : ℕ} (_T : ℝ) (D : FlowData q) : Prop :=
  ∀ S l, Allowed S l → ∃ A : Vec q →L[ℝ] Vec q, ∃ b : Vec q,
    ∀ P ∈ D.weighting.cells S, ∀ x ∈ P, D.field S P l x = A x + b

def HasConstantWeights {q : ℕ} (T : ℝ) (D : FlowData q) : Prop :=
  (∀ S i j, i ∈ S.val → j ∈ S.val → i ≠ j →
    ∃ c : ℝ, ∀ x ∈ omega T S, D.weighting.weight S i j x = c) ∧
  (∀ S i, i ∈ S.val → ∃ c : ℝ, ∀ x ∈ terminalFacet T S i,
    D.weighting.terminal S i x = c)

end MultiwayGap2325.Main.Supplement


