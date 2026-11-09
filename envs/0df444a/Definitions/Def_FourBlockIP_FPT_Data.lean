-- Prove2me | Definitions.Def_FourBlockIP_FPT_Data
-- name    : FourBlockIP_FPT_Data
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:50.029515+00:00
-- url     : https://prove2.me/theorems/4eb3587c-e426-4d2b-aac4-f54fa3d3f8d0
-- title:
--   4-block instances, block-sparse encoding and attained optimality
-- statement:
--   A 4-block instance contains natural dimensions $r,s,t,p,n$, a coefficient bound $\Delta$, integer blocks $A_0,B_i,C_i,D_i$, integer right-hand sides, and integer lower and upper bounds. Only $B_i$ and $D_i$ have entries bounded in absolute value by $\Delta$. The variable space consists of $p$ global variables followed by $n$ blocks of $t$ local variables. Feasibility means
--
--   $$A_0y+\sum_i B_ix_i=b_0,\qquad C_i y+D_ix_i=b_i,\qquad l\le(y,x)\le u.$$
--
--   The encoding stores dimensions, $A_0$, each tuple $(B_i,C_i,D_i,b_i)$, then $b_0,l,u$, using row-major matrix entries. It stores no dense zero-filled constraint matrix. A correct output is $[0]$ exactly when no feasible vector exists; otherwise it is a leading $1$ followed by a feasible vector attaining an objective value at most that of every feasible vector. The domain length is the maximum absolute coordinate difference $|u_j-l_j|$, zero when there are no variables. Inconsistent bounds are allowed and lead to infeasibility.
--
--   This is the instance and output interface used by the goal, including all zero-dimensional cases.
-- source:
--   Martin Koutecký, Alexandra Lassota, Koen Ligthart, 4-Block Integer Programming is in FPT, STOC 2027 submission #392 (October 2026), p. 3, equation (2), Theorem 2 and the definition of solving; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/392.pdf

import Mathlib

namespace FourBlockIP.FPT

/-- The entries of (2), p. 3. Global columns are unrestricted. Bounds need not be consistent. -/
structure Instance where
  r : ℕ
  s : ℕ
  t : ℕ
  p : ℕ
  n : ℕ
  delta : ℕ
  A0 : Matrix (Fin r) (Fin p) ℤ
  B : Fin n → Matrix (Fin r) (Fin t) ℤ
  C : Fin n → Matrix (Fin s) (Fin p) ℤ
  D : Fin n → Matrix (Fin s) (Fin t) ℤ
  B_bound : ∀ i a j, |B i a j| ≤ (delta : ℤ)
  D_bound : ∀ i a j, |D i a j| ≤ (delta : ℤ)
  b0 : Fin r → ℤ
  bi : Fin n → Fin s → ℤ
  l : (Fin p ⊕ (Fin n × Fin t)) → ℤ
  u : (Fin p ⊕ (Fin n × Fin t)) → ℤ

abbrev Var (I : Instance) := Fin I.p ⊕ (Fin I.n × Fin I.t)

def castVec {ι : Type*} (x : ι → ℤ) : ι → ℝ := fun j => (x j : ℝ)

def encodeVec {n : ℕ} (x : Fin n → ℤ) : List ℤ := List.ofFn x

def encodeMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : List ℤ :=
  (List.ofFn fun i => List.ofFn (A i)).flatten

def encodeBlockVec (I : Instance) (x : Var I → ℤ) : List ℤ :=
  List.ofFn (fun j => x (.inl j)) ++
    (List.ofFn fun i => List.ofFn fun j => x (.inr (i,j))).flatten

/-- Linear-size block-sparse layout: dimensions; A0; (Bi,Ci,Di,bi)i; b0; l; u. -/
def encode (I : Instance) : List ℤ :=
  ([I.r, I.s, I.t, I.p, I.n, I.delta] : List ℤ) ++ encodeMat I.A0 ++
    (List.ofFn fun i => encodeMat (I.B i) ++ encodeMat (I.C i) ++
      encodeMat (I.D i) ++ encodeVec (I.bi i)).flatten ++
    encodeVec I.b0 ++ encodeBlockVec I I.l ++ encodeBlockVec I I.u

def decodeBlockVec (I : Instance) (xs : List ℤ) : Var I → ℤ
  | .inl j => xs.getD j.val 0
  | .inr (i,j) => xs.getD (I.p + i.val * I.t + j.val) 0

def Feasible (I : Instance) (x : Var I → ℤ) : Prop :=
  (∀ a, (∑ j, I.A0 a j * x (.inl j)) +
    (∑ i, ∑ j, I.B i a j * x (.inr (i,j))) = I.b0 a) ∧
  (∀ i a, (∑ j, I.C i a j * x (.inl j)) +
    (∑ j, I.D i a j * x (.inr (i,j))) = I.bi i a) ∧
  (∀ j, I.l j ≤ x j ∧ x j ≤ I.u j)

/-- Attained optimality, rather than an infimum with a default value. -/
def Optimal (I : Instance) (f : (Var I → ℝ) → ℝ) (x : Var I → ℤ) : Prop :=
  Feasible I x ∧ ∀ z, Feasible I z → f (castVec x) ≤ f (castVec z)

def CorrectOutput (I : Instance) (f : (Var I → ℝ) → ℝ) (out : List ℤ) : Prop :=
  (out = [0] ↔ ¬ ∃ x, Feasible I x) ∧
    ((∃ x, Feasible I x) → ∃ x, Optimal I f x ∧ out = 1 :: encodeBlockVec I x)

/-- Maximum absolute width, zero on an empty variable set. -/
def domainLength {ι : Type*} [Fintype ι] (l u : ι → ℤ) : ℕ :=
  Finset.univ.sup (fun j => (u j - l j).natAbs)

end FourBlockIP.FPT


