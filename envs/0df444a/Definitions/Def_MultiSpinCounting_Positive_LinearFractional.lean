-- Prove2me | Definitions.Def_MultiSpinCounting_Positive_LinearFractional
-- name    : MultiSpinCounting_Positive_LinearFractional
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:21:25.764095+00:00
-- url     : https://prove2.me/theorems/89a75d4f-d58f-4472-95a9-de7d4da8a5df
-- title:
--   Affine rational linear-fractional programs and the explicit Charnes–Cooper LP
-- statement:
--   A program has free real variables $x\in\mathbb R^d$, rational data $A,b,c,\alpha,d_0,\beta$, and a choice of minimization or maximization:
--   $$\operatorname{opt}_{Ax\le b}\frac{c^\top x+\alpha}{d_0^\top x+\beta}.$$
--   No sign restriction on $x$ is built into the feasible region. Its binary encoding includes dimensions, optimization direction and all coefficients.
--
--   The transformed program uses the published unrestricted rational-LP data, with direction stored separately. In variables $(t,y)$ it has
--   $$Ay-bt\le0,\qquad d_0^\top y+\beta t=1,\qquad t\ge0,$$
--   and objective $c^\top y+\alpha t$. Equality is represented by two inequalities, giving exactly $d+1$ variables and $m+3$ rows. The maps are $(t,y)=(1/(d_0^\top x+\beta),x/(d_0^\top x+\beta))$ and $x=y/t$. Exact optimum means an attained objective value dominating all feasible values in the chosen direction. These definitions contain no optimization oracle or asserted correctness.
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), pp. 9–10, (2.3), Theorem 2.3 and its proof

import Mathlib
import Definitions.Def_MultiSpinCounting_Positive_Encoding
import Definitions.Def_RobustToDynamics_encLP

noncomputable section

namespace MultiSpinCounting.Positive
open OnlineCRS.Combine

/-- Free real variables, rational inequalities, and an affine fractional objective (2.3). -/
structure AffineLFP (d m : ℕ) where
  A : Fin m → Fin d → ℚ
  b : Fin m → ℚ
  c : Fin d → ℚ
  alpha : ℚ
  den : Fin d → ℚ
  beta : ℚ
  maximize : Bool

def lfpFeasible {d m : ℕ} (L : AffineLFP d m) : Set (Fin d → ℝ) :=
  {x | ∀ i, ∑ j, (L.A i j : ℝ) * x j ≤ (L.b i : ℝ)}

def denominator {d m : ℕ} (L : AffineLFP d m) (x : Fin d → ℝ) : ℝ :=
  (∑ j, (L.den j : ℝ) * x j) + L.beta

def lfpValue {d m : ℕ} (L : AffineLFP d m) (x : Fin d → ℝ) : ℝ :=
  ((∑ j, (L.c j : ℝ) * x j) + L.alpha) / denominator L x

def encLFP {d m : ℕ} (L : AffineLFP d m) : List Sym :=
  encNat d ++ [3] ++ encNat m ++ [3] ++ [bit L.maximize] ++
  RobustToDynamics.encMat L.A ++ encVec L.b ++
  encVec L.c ++ encRat L.alpha ++ [3] ++ encVec L.den ++ encRat L.beta

/-- Direction is separate from the reused, unrestricted rational LP data. -/
structure DirectedLP where
  program : RobustToDynamics.LPInst
  maximize : Bool

def lpFeasible (L : DirectedLP) : Set (Fin L.program.q → ℝ) :=
  {x | ∀ i, ∑ j, (L.program.A i j : ℝ) * x j ≤ (L.program.b i : ℝ)}

def lpValue (L : DirectedLP) (x : Fin L.program.q → ℝ) : ℝ :=
  ∑ j, (L.program.c j : ℝ) * x j

def encLP (L : DirectedLP) : List Sym :=
  [bit L.maximize] ++ RobustToDynamics.encLP L.program

/-- Explicit Charnes--Cooper LP: variables (t,y); Ay-bt≤0, ±(d·y+βt)≤±1, -t≤0. -/
def charnesCooper {d m : ℕ} (L : AffineLFP d m) : DirectedLP where
  program := {
   p := m+3
   q := d+1
   A := fun i j => if h : i.val < m then
      if hj : j.val = 0 then -L.b ⟨i.val,h⟩
      else L.A ⟨i.val,h⟩ ⟨j.val-1, by omega⟩
    else if i.val = m then
      if hj : j.val = 0 then L.beta else L.den ⟨j.val-1, by omega⟩
    else if i.val = m+1 then
      if hj : j.val = 0 then -L.beta else -L.den ⟨j.val-1, by omega⟩
    else if hj : j.val = 0 then -1 else 0
   b := fun i => if i.val < m then 0 else if i.val = m then 1
    else if i.val = m+1 then -1 else 0
   c := fun j => if hj : j.val = 0 then L.alpha else L.c ⟨j.val-1, by omega⟩ }
  maximize := L.maximize

def ccForward {d m : ℕ} (L : AffineLFP d m) (x : Fin d → ℝ) : Fin (d+1) → ℝ :=
  fun j => if hj : j.val = 0 then (denominator L x)⁻¹
    else x ⟨j.val-1, by omega⟩ / denominator L x

def ccInverse {d : ℕ} (z : Fin (d+1) → ℝ) : Fin d → ℝ :=
  fun j => z j.succ / z 0

def IsLFPOptimum {d m : ℕ} (L : AffineLFP d m) (r : ℚ) : Prop :=
  (∃ x ∈ lfpFeasible L, lfpValue L x = (r : ℝ)) ∧
  (∀ x ∈ lfpFeasible L, if L.maximize then lfpValue L x ≤ (r : ℝ)
    else (r : ℝ) ≤ lfpValue L x)

end MultiSpinCounting.Positive


