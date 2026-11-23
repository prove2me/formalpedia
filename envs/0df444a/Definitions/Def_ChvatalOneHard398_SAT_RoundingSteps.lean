-- Prove2me | Definitions.Def_ChvatalOneHard398_SAT_RoundingSteps
-- name    : ChvatalOneHard398_SAT_RoundingSteps
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:57:04.514806+00:00
-- url     : https://prove2.me/theorems/539211c7-8ca9-42ab-9152-6b292ff514b2
-- title:
--   Lemma 25 — LLL/nearest-plane certificate and entrywise rounding
-- statement:
--   For Lemma 25 (Del Pia, pp.26–27), `PreRoundData` stores the input, the LLL-reduced basis $B'$, the nearest-plane lattice vector $v_0$, the final power-of-two scale $S$, the mesh parameter $\tau$, and the ideal scale $S_0$. The encoding is the same length-framed binary encoding as `encRoundData`, followed by $\tau$ and $S_0$. `PreRoundCorrect` records only the properties supplied by LLL and nearest plane: $B'$ is nonsingular and spans the original lattice; $v_0$ is a lattice vector; $S,\tau,S_0>0$; $S_0\tau=\nu a$ with $a=(3/2)^n$; $S_0\le S$; the two-sided scale bound; and the two coefficient bounds $\|y\|_1\le 2a\|B'y\|/\tau$ and $\|y\|_1\le(1+2\|t-v\|/\tau)a$ for the representation $v=v_0+B'y$. `nearestInt(q)` is $\lfloor q+1/2\rfloor$, and `finishRound` performs precisely $M_0=[SB']$ and $c_0=[S(t-v_0)]$, entrywise. These definitions do not assert any theorem about the rounded output.
-- source:
--   Del Pia, proof of Lemma 25, pp.26–27, especially the LLL coefficient estimate, nearest-plane estimate, scale S, and definition of M0 and c0.

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Rounding

namespace ChvatalOneHard398.SAT
open OnlineCRS.Combine
open scoped BigOperators

structure PreRoundData where
  input : RoundInput
  basis : Matrix (Fin input.1.n) (Fin input.1.n) ℚ
  v0 : Fin input.1.n → ℚ
  scale : ℚ
  tau : ℚ
  scale0 : ℚ

def encPreRoundData (p : PreRoundData) : List Sym :=
  frame (encRoundInput p.input) ++ frame (RobustToDynamics.encMat p.basis) ++
  frame (encVec p.v0) ++ frame (encRat p.scale) ++ frame (encRat p.tau) ++
  encRat p.scale0

def nearestInt (q : ℚ) : ℤ := ⌊q + 1 / 2⌋

def finishRound (p : PreRoundData) : RoundData where
  n := p.input.1.n
  basis := p.basis
  v0 := p.v0
  scale := p.scale
  matrix := fun i j => nearestInt (p.scale * p.basis i j)
  target := fun i => nearestInt (p.scale * (p.input.1.target i - p.v0 i))

noncomputable def PreRoundCorrect (p : PreRoundData) : Prop :=
  let x := p.input
  let n := x.1.n
  let a : ℝ := (3 / 2 : ℝ) ^ n
  p.basis.det ≠ 0 ∧ qLattice p.basis = qLattice x.1.basis ∧
  qVec p.v0 ∈ qLattice x.1.basis ∧ 0 < p.scale ∧ 0 < p.tau ∧ 0 < p.scale0 ∧
  (x.2 : ℝ) * a ≤ (p.scale : ℝ) * RegevLWE.SmoothingLB.lambda1 (qLattice x.1.basis) ∧
  (p.scale : ℝ) * RegevLWE.SmoothingLB.lambda1 (qLattice x.1.basis) ≤
    (x.2 : ℝ) * a * (2 : ℝ) ^ (((n : ℝ) + 1) / 2) ∧
  (p.scale0 : ℝ) * (p.tau : ℝ) = (x.2 : ℝ) * a ∧
  (p.scale0 : ℝ) ≤ (p.scale : ℝ) ∧
  (∀ y : Fin n → ℤ,
    ∑ k, |(y k : ℝ)| ≤ 2 * a *
      ‖WithLp.toLp 2 (fun i => ∑ j, (p.basis i j : ℝ) * (y j : ℝ))‖ / (p.tau : ℝ)) ∧
  ∀ (v : E n) (y : Fin n → ℤ),
    v ∈ qLattice x.1.basis →
    v = qVec p.v0 + WithLp.toLp 2 (fun i => ∑ j, (p.basis i j : ℝ) * (y j : ℝ)) →
    ∑ k, |(y k : ℝ)| ≤
      (1 + 2 * ‖qVec x.1.target - v‖ / (p.tau : ℝ)) * a

end ChvatalOneHard398.SAT


