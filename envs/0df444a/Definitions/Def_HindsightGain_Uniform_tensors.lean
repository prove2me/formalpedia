-- Prove2me | Definitions.Def_HindsightGain_Uniform_tensors
-- name    : HindsightGain_Uniform_tensors
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:27.664971+00:00
-- url     : https://prove2.me/theorems/3e0deb92-d0e6-4392-8d32-4ba5f240fe29
-- title:
--   Euclidean tensor arrays, support directions and distinct-index radii
-- statement:
--   For a finite Euclidean coordinate set $I$, an order-$k$ tensor is an array $w\in\mathbb R^{I^k}$ with the Euclidean sum-of-squares norm. For a coefficient tensor $C$ of degree $r$, define
--   $$f_C(x)=\sum_{b\in I^r}C_b\prod_jx_{b_j},\quad (L_Cw)_i=\sum_{a\in I^{r-1}}C_{(i,a)}w_a,\quad h_B(v)=\max_{u\in B}\langle u,v\rangle.$$
--   Symmetry means invariance of $C$ under every permutation of its arguments. Define $W(y,z)=\sum_{k=0}^{r-1}y^{\otimes k}\otimes z^{\otimes(r-1-k)}$, with the zeroth tensor power equal to $1$. Polynomial maxima and supports use real suprema, with nonempty compact sets supplied by their users.
--   For a model, $I=[n]\times[D]$. The tensor $T$ is the full $r!$-permutation average of the original interactions as in (12), and $L_i$ is the block of $D$ rows of $L_T$ belonging to variable $i$. Its squared Frobenius norm sums the squares of those matrix coefficients. The projection $P_{\ne}$ keeps precisely entries whose variable indices are distinct. Finally,
--   $$R_k(\zeta)^2=\sum_{i_1,\ldots,i_{r-1}\ \mathrm{distinct}}\prod_{j\le k}\zeta_{i_j}^2\prod_{j>k}p_{i_j}^2.$$
--   This concrete algebraic layer supplies the comparison and fluctuation statements. The permutation average includes every permutation; the original interactions need not be symmetric. Real suprema outside the declared compact nonempty domains are unused total-function values.
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, §2, (11), p.13; §3.1–3.4, (12), (14)–(17), (20), (23), pp.14–18

import Mathlib
import Definitions.Def_HindsightGain_Uniform_optima

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HindsightGain.Uniform

/-- Coordinate arrays with the Euclidean norm, including scalar zeroth tensors. -/
abbrev Tensor (ι : Type) (k : ℕ) := EuclideanSpace ℝ (Fin k → ι)

def support {ι : Type} [Fintype ι] (B : Set (EuclideanSpace ℝ ι))
    (v : EuclideanSpace ℝ ι) : ℝ :=
  sSup ((fun u => inner ℝ u v) '' B)

def diagonal {ι : Type} [Fintype ι] {r : ℕ} (C : Tensor ι r)
    (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ a : Fin r → ι, C a * ∏ j, x (a j)

def symmetric {ι : Type} [Fintype ι] {r : ℕ} (C : Tensor ι r) : Prop :=
  ∀ (σ : Equiv.Perm (Fin r)) (a : Fin r → ι), C (a ∘ σ) = C a

/-- Prepending the first tensor coordinate; the proof only checks finite indices. -/
def prepend {ι : Type} {r : ℕ} (i : ι) (a : Fin (r - 1) → ι) : Fin r → ι :=
  fun j => if h : j.val = 0 then i else a ⟨j.val - 1, by omega⟩

/-- Equation (14), the coefficient matrix reshaped with its first coordinate as row. -/
def tensorL {ι : Type} [Fintype ι] {r : ℕ} (C : Tensor ι r)
    (w : Tensor ι (r - 1)) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => ∑ a : Fin (r - 1) → ι, C (prepend i a) * w a)

def mixedTensor {ι : Type} [Fintype ι] (y z : EuclideanSpace ℝ ι)
    (k q : ℕ) : Tensor ι q :=
  WithLp.toLp 2 (fun a => ∏ j : Fin q, if j.val < k then y (a j) else z (a j))

/-- Equation (17); for k = 0 the first product is the scalar 1. -/
def comparisonTensor {ι : Type} [Fintype ι] (r : ℕ)
    (y z : EuclideanSpace ℝ ι) : Tensor ι (r - 1) :=
  ∑ k : Fin r, mixedTensor y z k.val (r - 1)

def polynomialMax {ι : Type} [Fintype ι] {r : ℕ} (C : Tensor ι r)
    (B : Set (EuclideanSpace ℝ ι)) : ℝ := sSup (diagonal C '' B)

/-- Equation (12) in coefficients: the full permutation average of the original interactions. -/
def symmetrized {n D r : ℕ} (M : Model n D r) : Tensor (Fin n × Fin D) r :=
  WithLp.toLp 2 (fun b => (1 / (Nat.factorial r : ℝ)) *
    ∑ σ : Equiv.Perm (Fin r), ∑ e : Edge n r, ∑ a : Fin r → Fin D,
      M.A e a * ∏ j : Fin r,
        if b (σ j) = (e.val.orderEmbOfFin e.property j, a j) then 1 else 0)

def rowBlock {n D r : ℕ} (M : Model n D r) (i : Fin n)
    (w : Tensor (Fin n × Fin D) (r - 1)) : Vec D :=
  WithLp.toLp 2 (fun a => tensorL (symmetrized M) w (i, a))

def rowFrobeniusSq {n D r : ℕ} (M : Model n D r) (i : Fin n) : ℝ :=
  ∑ a : Fin D, ∑ b : Fin (r - 1) → Fin n × Fin D,
    (symmetrized M (prepend (i, a) b)) ^ 2

/-- Equation (16): distinct variable indices, regardless of internal coordinates. -/
def distinctProjection {n D k : ℕ} (w : Tensor (Fin n × Fin D) k) : Tensor (Fin n × Fin D) k :=
  WithLp.toLp 2 (fun a => if Function.Injective (fun j => (a j).1) then w a else 0)

/-- Equation (23), the exact ordered-distinct-tuple radius. -/
def radius {n r : ℕ} (k : ℕ) (ζ p : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ a : Fin (r - 1) → Fin n,
    if Function.Injective a then
      ∏ j : Fin (r - 1), if j.val < k then (ζ (a j)) ^ 2 else (p (a j)) ^ 2
    else 0)

end HindsightGain.Uniform


