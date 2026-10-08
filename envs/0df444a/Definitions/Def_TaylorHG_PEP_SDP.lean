-- Prove2me | Definitions.Def_TaylorHG_PEP_SDP
-- name    : TaylorHG_PEP_SDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:55.337095+00:00
-- url     : https://prove2.me/theorems/119891bb-3181-40a7-b93f-597f655bfe90
-- title:
--   Fixed-step methods and the exact SDP model
-- statement:
--   A fixed-step run follows $x_i=x_0-\sum_{k<i}h_{i,k}\nabla f(x_k)$. The columns $[g_0,\ldots,g_N,x_0]$ give a Gram matrix $G$; the vectors $h_i,u_i$ and matrices $A_{ij},A_R$ encode the interpolation and radius constraints. The primal SDP is
--
--   $$\sup_{G\succeq0,\,v\in\mathbb R^{N+1}} b^\top v+\operatorname{Tr}(CG)$$
--
--   subject to $v_j-v_i+\operatorname{Tr}(GA_{ij})\leq0$ for all $i,j\in\{0,\ldots,N,*\}$ and $\operatorname{Tr}(GA_R)\leq R^2$. The function-level value takes the same criterion over class members, minimizers, and actual fixed-step runs. A rank-constrained value adds $\operatorname{rank}G\leq d$.
--
--   **Formalization Note** These values use extended-real suprema, so empty and unbounded feasible sets retain their mathematical values. The star data are zero, and function values are normalized by subtracting the value at a minimizer. The finite-$L$ matrices use division by $L-\mu$.
-- source:
--   Taylor, Hendrickx & Glineur, arXiv:1502.05666v6, pp. 3, 12–14, Definition 4, (PEP), (sdp-PEP)

import Mathlib
import Definitions.Def_TaylorHG_PEP_Interp

namespace TaylorHG.PEP

/-- Definition 4, with the unused coefficients above the strict lower triangle set to zero. -/
def hcoef {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ)
    (i k : Fin (N + 1)) : ℝ :=
  if h : k.val < i.val then
    H ⟨i.val - 1, by omega⟩ ⟨k.val, by omega⟩
  else 0

/-- A fixed-step run, using the gradient oracle of a smooth function. -/
def IsFixedStepRun {d N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : Fin (N + 1) → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ i, x i = x 0 - ∑ k : Fin (N + 1), hcoef H i k • gradient f (x k)

/-- The row vector `h_i` of §3.3, with the last coordinate for the initial point. -/
def hvec {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ)
    (i : Option (Fin (N + 1))) : Fin (N + 2) → ℝ :=
  match i with
  | none => 0
  | some i => Pi.single (Fin.last (N + 1)) 1 -
      ∑ k : Fin (N + 1), hcoef H i k • Pi.single (Fin.castSucc k) (1 : ℝ)

/-- The vector `u_i` of §3.3; the star index is zero. -/
def uvec {N : ℕ} (i : Option (Fin (N + 1))) : Fin (N + 2) → ℝ :=
  match i with
  | none => 0
  | some i => Pi.single (Fin.castSucc i) 1

/-- An outer product. -/
def outer {n : ℕ} (v w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun a b => v a * w b

/-- The paper's `A_ij`, with the factor of two in the display made explicit. -/
noncomputable def Amat {N : ℕ} (μ L : NNReal) (H : Matrix (Fin N) (Fin N) ℝ)
    (i j : Option (Fin (N + 1))) : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ :=
  let hi := hvec H i
  let hj := hvec H j
  let ui := uvec i
  let uj := uvec j
  (1 / 2 : ℝ) •
    (((L : ℝ) / ((L : ℝ) - (μ : ℝ))) •
      (outer uj (hi - hj) + outer (hi - hj) uj) +
     (1 / ((L : ℝ) - (μ : ℝ))) • outer (ui - uj) (ui - uj) +
     ((μ : ℝ) / ((L : ℝ) - (μ : ℝ))) •
       (outer ui (hj - hi) + outer (hj - hi) ui) +
     (((L : ℝ) * (μ : ℝ)) / ((L : ℝ) - (μ : ℝ))) • outer (hi - hj) (hi - hj))

/-- The initial-radius matrix `A_R`. -/
def ARmat (N : ℕ) : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ :=
  outer (Pi.single (Fin.last (N + 1)) 1) (Pi.single (Fin.last (N + 1)) 1)

/-- A Gram matrix for the specified vector columns. -/
noncomputable def gramOf {d N : ℕ} (col : Fin (N + 2) → EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ :=
  fun a b => inner ℝ (col a) (col b)

/-- The normalized function value at the star index is zero. -/
def fext {N : ℕ} (fv : Fin (N + 1) → ℝ) : Option (Fin (N + 1)) → ℝ
  | none => 0
  | some i => fv i

/-- The points represented by the `h_i` columns. -/
def pointOf {d N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ)
    (col : Fin (N + 2) → EuclideanSpace ℝ (Fin d))
    (i : Option (Fin (N + 1))) : EuclideanSpace ℝ (Fin d) :=
  ∑ a : Fin (N + 2), hvec H i a • col a

/-- The subgradients represented by the `u_i` columns. -/
def gradOf {d N : ℕ} (col : Fin (N + 2) → EuclideanSpace ℝ (Fin d))
    (i : Option (Fin (N + 1))) : EuclideanSpace ℝ (Fin d) :=
  ∑ a : Fin (N + 2), uvec i a • col a

/-- The paper's linear performance criterion under translation to a general minimizer. -/
noncomputable def criterion {d N : ℕ} (b : Fin (N + 1) → ℝ)
    (C : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (xstar : EuclideanSpace ℝ (Fin d))
    (x : Fin (N + 1) → EuclideanSpace ℝ (Fin d)) : ℝ :=
  b ⬝ᵥ (fun i => f (x i) - f xstar) +
    (C * gramOf (Fin.snoc (fun i => gradient f (x i)) (x 0 - xstar))).trace

/-- Feasible pairs of the primal semidefinite program. -/
def SdpFeasible {N : ℕ} (μ L : NNReal) (R : ℝ)
    (H : Matrix (Fin N) (Fin N) ℝ)
    (G : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ)
    (fv : Fin (N + 1) → ℝ) : Prop :=
  G.PosSemidef ∧
  (∀ i j : Option (Fin (N + 1)), fext fv j - fext fv i +
    (G * Amat μ L H i j).trace ≤ 0) ∧
  (G * ARmat N).trace ≤ R ^ 2

/-- Function-level worst-case value of (PEP). -/
noncomputable def worstCase (d : ℕ) {N : ℕ} (μ L : NNReal) (R : ℝ)
    (H : Matrix (Fin N) (Fin N) ℝ) (b : Fin (N + 1) → ℝ)
    (C : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) : EReal :=
  sSup {r : EReal | ∃ (f : EuclideanSpace ℝ (Fin d) → ℝ)
      (x : Fin (N + 1) → EuclideanSpace ℝ (Fin d))
      (xstar : EuclideanSpace ℝ (Fin d)),
      FClass μ (L : ENNReal) f ∧ (∀ y, f xstar ≤ f y) ∧
      ‖x 0 - xstar‖ ≤ R ∧ IsFixedStepRun H f x ∧
      r = (criterion b C f xstar x : EReal)}

/-- Value of (sdp-PEP), including empty and unbounded cases. -/
noncomputable def sdpValue {N : ℕ} (μ L : NNReal) (R : ℝ)
    (H : Matrix (Fin N) (Fin N) ℝ) (b : Fin (N + 1) → ℝ)
    (C : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) : EReal :=
  sSup {r : EReal | ∃ (G : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ)
      (fv : Fin (N + 1) → ℝ),
      SdpFeasible μ L R H G fv ∧ r = ((b ⬝ᵥ fv + (C * G).trace : ℝ) : EReal)}

/-- The rank-constrained SDP value of Proposition 2. -/
noncomputable def sdpValueRank (d : ℕ) {N : ℕ} (μ L : NNReal) (R : ℝ)
    (H : Matrix (Fin N) (Fin N) ℝ) (b : Fin (N + 1) → ℝ)
    (C : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) : EReal :=
  sSup {r : EReal | ∃ (G : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ)
      (fv : Fin (N + 1) → ℝ),
      SdpFeasible μ L R H G fv ∧ G.rank ≤ d ∧
      r = ((b ⬝ᵥ fv + (C * G).trace : ℝ) : EReal)}

end TaylorHG.PEP


