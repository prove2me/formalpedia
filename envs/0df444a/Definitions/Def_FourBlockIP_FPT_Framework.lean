-- Prove2me | Definitions.Def_FourBlockIP_FPT_Framework
-- name    : FourBlockIP_FPT_Framework
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:59.885526+00:00
-- url     : https://prove2.me/theorems/a76767d4-b491-4c62-9bc5-839e3b1c786a
-- title:
--   Framework feasibility, input layouts and runtime expressions
-- statement:
--   The bounded equality subproblem has constraints $Ax=b$ and $l\le x\le u$; its optimality predicate requires an attained minimum against every feasible integer vector. The framework problem has variables $(y,x)$ with
--
--   $$Cy+Ax=b,\quad Vy\le w,\quad y\in\mathbb Z^p,\quad l\le x\le u,\quad x\in\mathbb Z^n,$$
--
--   and objective $g(y)+f(x)$. Its correct output either reports infeasibility exactly or supplies an attained optimum. The optimization subroutine receives $m,n,A,\bar l,\bar u,b,\bar x_0$; multiplication receives $m,n,A,x$. The final framework program receives integer data $m,n,p,\ell,A,C,l,u,b$ and exact real data $V,w,c_0,\rho$. All matrices are row-major. Subroutine optimum/product outputs are plain vectors; final solver outputs carry the feasibility flag.
--
--   The runtime expressions are the full bounds of Lemmas 6–7 and Theorem 2, with absolute constants explicit. The framework uses $\log_2(\rho+2)$ and $\log_2(p+2)$; the goal uses the C1 padding and natural base-two logarithms of arguments increased by two. These are numerical expressions, not algorithm definitions or assumptions of correctness.
-- source:
--   Martin Koutecký, Alexandra Lassota, Koen Ligthart, 4-Block Integer Programming is in FPT, STOC 2027 submission #392 (October 2026), p. 7, (6), (7) and Lemma 6 runtime; p. 3, Theorem 2 runtime (C1, R1, R2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/392.pdf

import Mathlib
import Definitions.Def_FourBlockIP_FPT_ValueFunctions

namespace FourBlockIP.FPT

def eqBoxFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (l u : Fin n → ℤ) (b : Fin m → ℤ) (x : Fin n → ℤ) : Prop :=
  (fun i => ∑ j, A i j * x j) = b ∧ ∀ j, l j ≤ x j ∧ x j ≤ u j

def eqBoxOptimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (l u : Fin n → ℤ) (b : Fin m → ℤ) (f : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℤ) : Prop :=
  eqBoxFeasible A l u b x ∧
    ∀ z, eqBoxFeasible A l u b z → f (castVec x) ≤ f (castVec z)

/-- Framework subroutine input: m,n,A,lbar,ubar,b,xbar0. -/
def optInput {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (l u : Fin (n+m) → ℤ) (b : Fin m → ℤ) (x0 : Fin (n+m) → ℤ) : List ℤ :=
  ([m,n] : List ℤ) ++ encodeMat A ++ encodeVec l ++ encodeVec u ++
    encodeVec b ++ encodeVec x0

def mulInput {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (x : Fin n → ℤ) : List ℤ :=
  ([m,n] : List ℤ) ++ encodeMat A ++ encodeVec x

def mixedObjective {p n : ℕ} (g : (Fin p → ℝ) → ℝ) (f : (Fin n → ℝ) → ℝ)
    (z : Fin (p+n) → ℝ) : ℝ :=
  g (fun j => z ⟨j.val, by omega⟩) + f (fun j => z ⟨p+j.val, by omega⟩)

def mixedFeasible {m n p ell : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (C : Matrix (Fin m) (Fin p) ℤ) (l u : Fin n → ℤ) (b : Fin m → ℤ)
    (V : Matrix (Fin ell) (Fin p) ℝ) (w : Fin ell → ℝ)
    (y : Fin p → ℤ) (x : Fin n → ℤ) : Prop :=
  (∀ i, (∑ j, C i j * y j) + (∑ j, A i j * x j) = b i) ∧
    (∀ i, (∑ j, V i j * (y j : ℝ)) ≤ w i) ∧
    (∀ j, l j ≤ x j ∧ x j ≤ u j)

def mixedCorrect {m n p ell : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (C : Matrix (Fin m) (Fin p) ℤ) (l u : Fin n → ℤ) (b : Fin m → ℤ)
    (V : Matrix (Fin ell) (Fin p) ℝ) (w : Fin ell → ℝ)
    (g : (Fin p → ℝ) → ℝ) (f : (Fin n → ℝ) → ℝ) (out : List ℤ) : Prop :=
  (out = [0] ↔ ¬ ∃ y x, mixedFeasible A C l u b V w y x) ∧
  ((∃ y x, mixedFeasible A C l u b V w y x) →
    ∃ y x, mixedFeasible A C l u b V w y x ∧
      (∀ y' x', mixedFeasible A C l u b V w y' x' →
        g (castVec y) + f (castVec x) ≤ g (castVec y') + f (castVec x')) ∧
      out = 1 :: (encodeVec y ++ encodeVec x))

/-- Framework integer input: m,n,p,ell,A,C,l,u,b, with row-major matrices. -/
def frameworkInput {m n p : ℕ} (ell : ℕ) (A : Matrix (Fin m) (Fin n) ℤ)
    (C : Matrix (Fin m) (Fin p) ℤ) (l u : Fin n → ℤ) (b : Fin m → ℤ) : List ℤ :=
  ([m,n,p,ell] : List ℤ) ++ encodeMat A ++ encodeMat C ++
    encodeVec l ++ encodeVec u ++ encodeVec b

/-- Exact real input, not restricted to rational data: V,w,center,radius. -/
def frameworkRealInput {ell p : ℕ} (V : Matrix (Fin ell) (Fin p) ℝ)
    (w : Fin ell → ℝ) (center : Fin p → ℝ) (rho : ℝ) : List ℝ :=
  (List.ofFn fun i => List.ofFn (V i)).flatten ++ List.ofFn w ++ List.ofFn center ++ [rho]

noncomputable def frameworkBound (c p M U : ℕ) (Topt : ℕ → ℕ)
    (Tmul m ell width : ℕ) (rho : ℝ) : ℝ :=
  (c : ℝ) * (M : ℝ)^p * (2 : ℝ)^(c*p^2*Nat.log 2 (p+2)) *
    ((Real.logb 2 (rho+2))^c + Real.logb 2 (rho+2) *
      ((Topt ((1+2*U)*width) + Tmul + m + ell : ℕ) : ℝ))

/-- Bound in Theorem 2, with C1 padding and saturated integer logarithms. -/
def goalBound (c : ℕ) (I : Instance) : ℕ :=
  let rr := max I.r 1
  let pp := max I.p 1
  let dd := max I.delta 1
  let N := max I.t 1 * max I.n 1
  let E := (c * (rr+I.s) * dd)^(rr*(rr+I.s)) * pp +
    c * pp^2 * Nat.log 2 (pp+2)
  2^E * c * N * (Nat.log 2 (N+2))^c *
    (Nat.log 2 (domainLength I.l I.u + 2))^c

end FourBlockIP.FPT


