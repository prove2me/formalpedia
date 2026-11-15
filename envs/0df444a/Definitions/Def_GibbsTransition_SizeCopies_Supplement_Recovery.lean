-- Prove2me | Definitions.Def_GibbsTransition_SizeCopies_Supplement_Recovery
-- name    : GibbsTransition_SizeCopies_Supplement_Recovery
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:34:50.682261+00:00
-- url     : https://prove2.me/theorems/0418dd1b-e769-4c49-b8dd-0a3894fd62a6
-- title:
--   Normalized partial traces and canonical interaction recovery
-- statement:
--   For an operator on a finite tensor product, $E_S$ is the partial trace over the complement divided by that complement's dimension. Removing the scalar trace from each local term gives
--   $$h_0=c_0I+g_0,\qquad h_i=c_iI+A_i\otimes I+I\otimes B_i+G_i,\qquad g_\infty=g_0+\sum_i(A_i+B_i).$$
--   Both one-site normalized partial traces of each $G_i$ vanish. For trace-free one-site and side-two bulk inputs $X_1,X_2$, set $C_x=E_{\{x\}}X_2$ and $\bar C=\frac18\sum_xC_x$. The recovery formulas are $2\bar C-X_1$ and $E_{\{x,y\}}X_2-C_x\otimes I-I\otimes C_y$ on a directed edge in each direction.
--
--   The canonical Hamiltonian has these recovered on-site and connected edge terms, the original field coupling, and no boundary. Its limiting energy differs from the original by the explicit field-independent scalar $c_0+c_1+c_2+c_3$, which leaves energy secants unchanged.
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), (40)–(44),(52), printed pp. 12–14 (PDF pp. 14–16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Supplement_Field
open scoped Matrix.Norms.L2Operator
set_option autoImplicit false

noncomputable section

namespace GibbsTransition.SizeCopies.Supplement
attribute [local instance] Classical.propDecidable

def traceFree {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : Matrix n n ℂ :=
  A - (Matrix.trace A / (Fintype.card n : ℂ)) • 1

def tensor {q : ℕ} (A B : Local q) : Pair q := fun s t => A s.1 t.1 * B s.2 t.2

def traceRight {q : ℕ} (A : Pair q) : Local q :=
  fun s t => (q : ℂ)⁻¹ * ∑ j : Fin q, A (s,j) (t,j)

def traceLeft {q : ℕ} (A : Pair q) : Local q :=
  fun s t => (q : ℂ)⁻¹ * ∑ j : Fin q, A (j,s) (j,t)

def gaugeA {q : ℕ} (A : Pair q) : Local q := traceFree (traceRight A)
def gaugeB {q : ℕ} (A : Pair q) : Local q := traceFree (traceLeft A)
def connected {q : ℕ} (A : Pair q) : Pair q :=
  traceFree A - tensor (gaugeA A) 1 - tensor 1 (gaugeB A)

def canonical {q : ℕ} (u : FieldInteraction q) : FieldInteraction q where
  onsite := traceFree u.onsite + ∑ i : Fin 3, (gaugeA (u.edge i) + gaugeB (u.edge i))
  edge := fun i => connected (u.edge i)

def scalarShift {q : ℕ} (u : FieldInteraction q) : ℝ :=
  (Matrix.trace u.onsite).re / q + ∑ i : Fin 3, (Matrix.trace (u.edge i)).re / (q : ℝ)^2

/-- Trace out the complement, divided by its dimension. The zero label is
used only as a dummy complement representative; q>0 in every application. -/
def partialSite {q L : ℕ} (A : Cube q L) (x : Site L) : Local q :=
  fun a b => (q : ℂ)^(-(L^3-1 : ℕ) : ℤ) *
    ∑ s : Config q L, if (s x).val = 0 then
      A (Function.update s x a) (Function.update s x b) else 0

def partialEdge {q L : ℕ} (A : Cube q L) (x y : Site L) : Pair q :=
  fun a b => (q : ℂ)^(-(L^3-2 : ℕ) : ℤ) *
    ∑ s : Config q L, if (s x).val = 0 ∧ (s y).val = 0 then
      A (Function.update (Function.update s x a.1) y a.2)
        (Function.update (Function.update s x b.1) y b.2) else 0

def corner : Site 2 := fun _ => 0
def adjacent (i : Fin 3) : Site 2 := fun j => if j = i then 1 else 0

def averageSite {q : ℕ} (X : Cube q 2) : Local q :=
  (1/8 : ℂ) • ∑ x : Site 2, partialSite X x

def recoveredOnsite {q : ℕ} (X1 : Local q) (X2 : Cube q 2) : Local q :=
  (2 : ℂ) • averageSite X2 - X1

def recoveredEdge {q : ℕ} (X2 : Cube q 2) (i : Fin 3) : Pair q :=
  partialEdge X2 corner (adjacent i) - tensor (partialSite X2 corner) 1 -
    tensor 1 (partialSite X2 (adjacent i))

def recovered {q : ℕ} (X1 : Local q) (X2 : Cube q 2) : FieldInteraction q :=
  ⟨recoveredOnsite X1 X2, recoveredEdge X2⟩

/-- The Hamiltonian (42) has no common boundary; scalar and boundary gauge
removal changes limiting energy only by scalarShift. -/
def canonicalHamiltonian {q : ℕ} (u : FieldInteraction q) (P : Local q)
    (L : ℕ) (phi : ℝ) : Cube q L :=
  fieldBulk u L - phi • ∑ x : Site L, embedSite P x

def canonicalEnergy {q : ℕ} (u : FieldInteraction q) (P : Local q)
    (L : ℕ) (phi : ℝ) : ℝ :=
  sInf (spectrum ℝ (canonicalHamiltonian u P L phi)) / (L : ℝ)^3

end GibbsTransition.SizeCopies.Supplement


