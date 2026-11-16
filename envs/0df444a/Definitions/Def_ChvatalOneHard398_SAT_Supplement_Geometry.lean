-- Prove2me | Definitions.Def_ChvatalOneHard398_SAT_Supplement_Geometry
-- name    : ChvatalOneHard398_SAT_Supplement_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:16:17.679389+00:00
-- url     : https://prove2.me/theorems/4d4650da-acba-4ed4-9a2f-6d8e97504c7e
-- title:
--   Widths, rational parallelepipeds and the dimension-preserving BDD reduction
-- statement:
--   For a set $P\subseteq\mathbb R^d$ and a direction $c$, the width is the sum of the support values in directions $c$ and $-c$. Nonempty unbounded directions have infinite width; the empty set has width zero. Write $\|w\|_1=\sum_i|w_i|$. A square integer matrix is unimodular when its determinant is $1$ or $-1$; a dual basis has independent columns generating the dual lattice.
--
--   For rational nonsingular $B$, rational $t$ and real $r>0$, set
--   $$Q(B,t,r)=\{x:\ |(Bx-t)_i|\le r\text{ for all }i\}.$$
--   Rational query data are thin when $0<r<\lambda_1(B\mathbb Z^d)/(2d^2)$. Feasibility means the existence of an integral point of this set.
--
--   The BDD promise for Theorem 7 uses the factor $1/(4n^2)$. Its reduction uses the published adaptive next-step machine and fixed polynomial bounds on every raw input and oracle. The oracle is correct only on thin queries; every actual query has rational data, positive radius and nonsingular basis in the input dimension. On promised inputs the output is a closest lattice vector. This interface adds no oracle correctness off the promise.
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.8–12, §2, §3.2 and Theorem 7. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Oracle

namespace ChvatalOneHard398.SAT.Supplement
open scoped BigOperators
open CombOpt.ChvatalRank

/-- Empty sets have width zero. Nonempty unbounded directions have infinite width. -/
noncomputable def width {d : ℕ} (P : Set (Fin d → ℝ)) (c : Fin d → ℝ) : EReal := by
  classical
  exact if P.Nonempty then
    sSup ((fun x : Fin d → ℝ => ((∑ i, c i * x i : ℝ) : EReal)) '' P) +
    sSup ((fun x : Fin d → ℝ => ((∑ i, -c i * x i : ℝ) : EReal)) '' P)
  else 0

def oneNorm {d : ℕ} (w : Fin d → ℝ) : ℝ := ∑ i, |w i|

def unimodular {d : ℕ} (U : Matrix (Fin d) (Fin d) ℤ) : Prop :=
  U.det = 1 ∨ U.det = -1

noncomputable def dualBasis {d : ℕ} (L : Submodule ℤ (E d))
    (W : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  W.det ≠ 0 ∧ lattice W = RegevLWE.GaussConv.dual L

noncomputable def parallelepiped {d : ℕ} (B : Matrix (Fin d) (Fin d) ℚ)
    (t : Fin d → ℚ) (r : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, |(∑ j, (B i j : ℝ) * x j) - t i| ≤ r}

structure ParaInput where
  d : ℕ
  B : Matrix (Fin d) (Fin d) ℚ
  t : Fin d → ℚ
  r : ℚ

noncomputable def ParaInput.poly (Q : ParaInput) := parallelepiped Q.B Q.t Q.r

def ParaInput.Valid (Q : ParaInput) : Prop := Q.B.det ≠ 0 ∧ 0 < Q.r

noncomputable def ParaInput.Thin (Q : ParaInput) : Prop :=
  Q.Valid ∧ (Q.r : ℝ) < RegevLWE.SmoothingLB.lambda1 (qLattice Q.B) / (2 * (Q.d : ℝ)^2)

noncomputable def ParaInput.Feasible (Q : ParaInput) : Prop :=
  ∃ x, x ∈ Q.poly ∧ IsIntegralVector x

def encPara (Q : ParaInput) : List OnlineCRS.Combine.Sym :=
  OnlineCRS.Combine.encNat Q.d ++ [2] ++
  frame (RobustToDynamics.encMat Q.B) ++ frame (OnlineCRS.Combine.encVec Q.t) ++
  OnlineCRS.Combine.encRat Q.r

noncomputable def BDDPromise7 (x : BDDInput) : Prop :=
  0 < x.n ∧ x.basis.det ≠ 0 ∧
  latticeDist (qLattice x.basis) (qVec x.target) ≤
    RegevLWE.SmoothingLB.lambda1 (qLattice x.basis) / (4 * (x.n : ℝ)^2)

noncomputable def ParaOracle (orc : ParaInput → Bool) : Prop :=
  ∀ Q, Q.Thin → (orc Q = true ↔ Q.Feasible)

/-- The query trace condition holds even outside the BDD promise. Raw singular bases are
handled without making oracle calls, so every actual query has nonsingular basis. -/
noncomputable def Reduction7 : Prop :=
  ∃ (A : OracleAlg BDDInput ParaInput (List ℚ)) (p : Polynomial ℕ),
    IsPolyOracle encBDD encPara encOutput A p ∧
    (∀ orc x, ∀ Q ∈ (oracleRun A orc x (p.eval (encBDD x).length) []).queries,
      Q.Valid ∧ Q.d = x.n) ∧
    ∀ orc, ParaOracle orc → ∀ x, BDDPromise7 x →
      ∃ v, (oracleRun A orc x (p.eval (encBDD x).length) []).output = some v ∧ BDDCorrect x v

end ChvatalOneHard398.SAT.Supplement


