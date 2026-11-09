-- Prove2me | Definitions.Def_ChvatalOneHard398_SAT_Rounding
-- name    : ChvatalOneHard398_SAT_Rounding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:45:17.062246+00:00
-- url     : https://prove2.me/theorems/6159e35d-739d-4527-b223-87e7c400e8b2
-- title:
--   Input, output, and complete specification of lattice rounding
-- statement:
--   The input is a rational basis $B$ in dimension $n$, a rational target $t$, and a rational $\nu>\sqrt n$. The output records a rational basis $B'$ of the same lattice, a rational lattice vector $v_0$, a rational scale $S>0$, a nonsingular integer matrix $M_0$, and an integer target $t'$. The specification includes both bounds on $S\lambda_1(L)$ and the lower bound on $\lambda_1(M_0\mathbb Z^n)$ from Lemma 25.
--
--   For every closest vector $v^*$ and every integer coefficient vector $y^*$ with $v^*=v_0+B'y^*$, it requires
--
--   $$\|t'-M_0y^*\|_\infty\le(1+1/\nu)S\operatorname{dist}(t,L)+\tfrac12+\tfrac12(3/2)^n.$$
--
--   The error is an integer vector by its type. The coordinate inequalities express exactly its infinity-norm bound. Encodings include dimensions and every output component. This is a predicate on ordinary output data, used as the conclusion of Lemma 25; it is not a hypothesis that supplies a rounding algorithm.
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.26, Lemma 25 (proof continues on p.27); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Encoding

namespace ChvatalOneHard398.SAT
open OnlineCRS.Combine
open scoped BigOperators

abbrev RoundInput := BDDInput × ℚ

structure RoundData where
  n : ℕ
  basis : Matrix (Fin n) (Fin n) ℚ
  v0 : Fin n → ℚ
  scale : ℚ
  matrix : Matrix (Fin n) (Fin n) ℤ
  target : Fin n → ℤ

def encRoundInput (x : RoundInput) : List Sym := frame (encBDD x.1) ++ encRat x.2

def encRoundData (o : RoundData) : List Sym :=
  frame (encNat o.n) ++ frame (RobustToDynamics.encMat o.basis) ++ frame (encVec o.v0) ++
  frame (encRat o.scale) ++ frame (RobustToDynamics.encMat (fun i j => (o.matrix i j : ℚ))) ++
  encVec (fun i => (o.target i : ℚ))

noncomputable def RoundCorrect (x : RoundInput) (o : RoundData) : Prop :=
  ∃ (B' : Matrix (Fin x.1.n) (Fin x.1.n) ℚ) (v0 : Fin x.1.n → ℚ)
      (S : ℚ) (M0 : Matrix (Fin x.1.n) (Fin x.1.n) ℤ) (t' : Fin x.1.n → ℤ),
    o = ⟨x.1.n,B',v0,S,M0,t'⟩ ∧
    B'.det ≠ 0 ∧ qLattice B' = qLattice x.1.basis ∧ qVec v0 ∈ qLattice x.1.basis ∧
    0 < S ∧ M0.det ≠ 0 ∧
    (x.2 : ℝ)*(3/2 : ℝ)^x.1.n ≤ (S : ℝ)*RegevLWE.SmoothingLB.lambda1 (qLattice x.1.basis) ∧
    (S : ℝ)*RegevLWE.SmoothingLB.lambda1 (qLattice x.1.basis) ≤
      (x.2 : ℝ)*(3/2 : ℝ)^x.1.n*(2 : ℝ)^(((x.1.n : ℝ)+1)/2) ∧
    (1-Real.sqrt x.1.n/(x.2 : ℝ))*(S : ℝ)*RegevLWE.SmoothingLB.lambda1 (qLattice x.1.basis) ≤
      RegevLWE.SmoothingLB.lambda1 (zLattice M0) ∧
    ∀ (vstar : E x.1.n) (ystar : Fin x.1.n → ℤ),
      vstar ∈ qLattice x.1.basis →
      ‖qVec x.1.target-vstar‖ = latticeDist (qLattice x.1.basis) (qVec x.1.target) →
      vstar = qVec v0 + WithLp.toLp 2 (fun i => ∑ j, (B' i j : ℝ)*(ystar j : ℝ)) →
      ∀ i, |((t' i - ∑ j, M0 i j * ystar j : ℤ) : ℝ)| ≤
        (1+1/(x.2 : ℝ))*(S : ℝ)*latticeDist (qLattice x.1.basis) (qVec x.1.target) +
        1/2 + 1/2*(3/2 : ℝ)^x.1.n

end ChvatalOneHard398.SAT


