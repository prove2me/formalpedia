-- Prove2me | Definitions.Def_QuantumTriangleFinding_Search_TriangleComparison
-- name    : QuantumTriangleFinding_Search_TriangleComparison
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:28:20.576336+00:00
-- url     : https://prove2.me/theorems/075fc2c0-eb31-4e09-b866-92c00f090319
-- title:
--   Four-input triangle comparison, star resolvents and degree tails
-- statement:
--   For a positive input $y$ with unique triangle $T$ and $U\subsetneq T$, let $y^U$ retain all outside edges and contain precisely $U$ on $T$. The four-input comparison and its selected workspace vectors are
--   $$ (T_Tf)^y=\sum_{i\in T}f^{y^{\{i\}}}-2f^{y^\varnothing},\qquad (f_U^{(T)})^y=f^{y^U}.$$
--   Their output weights are those of $\mu_T$. Each transformed input used here is in the negative support. Evaluation away from support is assigned zero but is never used on such transformed inputs in the stated regime.
--
--   For a vertex $w$ let $L_w=\sum_{i\in\mathrm{st}(w)}D_i$. For a triangle put $H_T=\sum_{w\in V(T)}L_w$, $F_w=(I+L_w/R)^{-1}$ and $F_T=(I+H_T/R)^{-1}$. The comparison kernel $\Upsilon_R$ has unweighted $T$-component $T_TF_T$. Its positive-law norm supplies the direct-sum normalization:
--   $$\|\Upsilon_R f\|^2=\frac1M\sum_T\|T_TF_Tf\|^2.$$
--   Phase-query errors are the actual commutators across these input registers.
--
--   The degree threshold and rare-input quantities are fixed by the host and density:
--   $$d_0=\lceil8\Delta p\rceil,\quad c_{\rm tail}=8\log8-7,\quad b=\min\{1,2m e^{-c_{\rm tail}\Delta p}\},\quad \tau^2=144p^2\Delta^2b.$$
--   The local analytic regime is $M\ge1$, $0<p\le1/(10\sqrt\Delta)$ and $\Delta p\ge1$. It assumes no conclusion, success bound or commutation property.
-- source:
--   Arjan Cornelissen, Amin Shiraz Gilani, Xingyu Zhou, STOC 2027 submission #1375 (October 2026), §5.1, (5.7), p. 27; selected vectors, p. 28; (5.14), (5.16)–(5.19), p. 29; (5.25), p. 31

import Definitions.Def_QuantumTriangleFinding_Search_GraphModel

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace QuantumTriangleFinding.Search

/-- Equation (5.7): replace only the triangle coordinates, retaining precisely U. -/
def modifiedInput {N : ℕ} {G : SimpleGraph (Fin N)} (T : Triangle G)
    (y : Edge G → Bool) (U : Finset (Edge G)) : Edge G → Bool := by
  classical
  exact fun e => if e ∈ triangleEdges T then decide (e ∈ U) else y e

/-- Evaluation in support coordinates. On the transformed inputs used in Section 5,
support membership follows from uniqueness and p in (0,1). -/
def atInput {I W : Type} [Fintype I] [Fintype W] (ρ : (I → Bool) → ℝ)
    (f : Joint ρ W) (x : I → Bool) : EuclideanSpace ℂ W := by
  classical
  exact ∑ z, if z.val = x then f z else 0

/-- Raw row of the four-input map, in unweighted workspace coordinates. -/
def fourInputRow {N : ℕ} {G : SimpleGraph (Fin N)} (T : Triangle G)
    (y x : Edge G → Bool) : ℂ := by
  classical
  exact (∑ i ∈ triangleEdges T, if x = modifiedInput T y {i} then 1 else 0) -
    2 * (if x = modifiedInput T y ∅ then 1 else 0)

def localComparison {N : ℕ} {G : SimpleGraph (Fin N)} (T : Triangle G) (p : ℝ) :
    Matrix (Support (triangleLaw T p)) (Support (negativeLaw G p)) ℂ :=
  fun y x => fourInputRow T y.val x.val

def selectedVector {N : ℕ} {G : SimpleGraph (Fin N)} {W : Type} [Fintype W]
    (T : Triangle G) (p : ℝ) (U : Finset (Edge G))
    (f : Joint (negativeLaw G p) W) : Joint (triangleLaw T p) W :=
  fun y => atInput (negativeLaw G p) f (modifiedInput T y.val U)

def starOperator {N : ℕ} (G : SimpleGraph (Fin N)) (p : ℝ) (w : Fin N) :
    Matrix (Support (negativeLaw G p)) (Support (negativeLaw G p)) ℂ :=
  blockDifferences (negativeLaw G p) (starEdges G w)

def triangleOperator {N : ℕ} {G : SimpleGraph (Fin N)} (T : Triangle G) (p : ℝ) :
    Matrix (Support (negativeLaw G p)) (Support (negativeLaw G p)) ℂ :=
  ∑ w ∈ T.val, starOperator G p w

def starAverage {N : ℕ} (G : SimpleGraph (Fin N)) (p R : ℝ) (w : Fin N) :=
  resolvent (starOperator G p w) R

def triangleAverage {N : ℕ} {G : SimpleGraph (Fin N)} (T : Triangle G) (p R : ℝ) :=
  resolvent (triangleOperator T p) R

/-- Equation (5.25). The positive-law norm itself supplies the 1/M in squared norm,
so no extra 1/√M belongs in these unweighted coordinates. -/
def triangleTransfer {N : ℕ} (G : SimpleGraph (Fin N)) (p R : ℝ) :
    Matrix (Support (positiveLaw G p)) (Support (negativeLaw G p)) ℂ :=
  fun y x => ∑ z, fourInputRow y.val.1 y.val.2 z.val *
    triangleAverage y.val.1 p R z x

def localQueryError {N : ℕ} {G : SimpleGraph (Fin N)} (T : Triangle G) (p : ℝ) (e : Edge G) :=
  inputPhase (triangleLaw T p) id e * localComparison T p -
    localComparison T p * inputPhase (negativeLaw G p) id e

def transferQueryError {N : ℕ} (G : SimpleGraph (Fin N)) (p R : ℝ) (e : Edge G) :=
  inputPhase (positiveLaw G p) Prod.snd e * triangleTransfer G p R -
    triangleTransfer G p R * inputPhase (negativeLaw G p) id e

/-- Equations (5.16)–(5.19): these quantities are computed, never adjustable parameters. -/
def degreeThreshold {N : ℕ} (G : SimpleGraph (Fin N)) (p : ℝ) : ℤ :=
  ⌈8 * (maxDegree G : ℝ) * p⌉

def sampledMaxDegree {N : ℕ} (G : SimpleGraph (Fin N)) (x : Edge G → Bool) : ℕ :=
  Finset.univ.sup fun w => (starEdges G w).sum fun e => if x e then 1 else 0

def tailConstant : ℝ := 8 * Real.log 8 - 7

def tailBound {N : ℕ} (G : SimpleGraph (Fin N)) (p : ℝ) : ℝ :=
  min 1 (2 * (edgeCount G : ℝ) * Real.exp (-tailConstant * (maxDegree G : ℝ) * p))

def tauSq {N : ℕ} (G : SimpleGraph (Fin N)) (p : ℝ) : ℝ :=
  144 * p ^ 2 * (maxDegree G : ℝ) ^ 2 * tailBound G p

/-- Exactly the analytic hypotheses used in Lemmas 5.3–5.6, not the later success bound. -/
def LocalRegime {N : ℕ} (G : SimpleGraph (Fin N)) (p : ℝ) : Prop :=
  1 ≤ triangleCount G ∧ 0 < p ∧ p ≤ 1 / (10 * Real.sqrt (maxDegree G : ℝ)) ∧
    1 ≤ (maxDegree G : ℝ) * p

end QuantumTriangleFinding.Search


