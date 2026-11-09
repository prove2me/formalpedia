-- Prove2me | Definitions.Def_AlmostLinearModComp_Composition_EvaluationAlgorithm
-- name    : AlmostLinearModComp_Composition_EvaluationAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:18.1268+00:00
-- url     : https://prove2.me/theorems/b2d79398-f81d-4805-840c-aaed03ae34d8
-- title:
--   Block array preparation and the complete two-pass circuit
-- statement:
--   For each of the $3\cdot2^m$ offsets, the preparation circuit computes the common factor in monomial coordinates, applies the monic Hankel multiplication, then applies the previously stored transposed changes in increasing order. Binary powering computes the shared powers; no common factor or next array is supplied for free. Every entry of the next array is assembled from its unique offset and basis index.
--
--   The standalone array circuit accepts only the modulus, targets, and the complete arrays of earlier stages. It reconstructs their fixed-scalar programs and charges that preparation too. For $v=1$ the previous-stage list is empty.
--
--   Algorithm 1 prepares and stores every change in increasing order and applies them to the input coordinate vector in decreasing order. Its input contains only the modulus coefficients, target coefficients and outer-polynomial coefficients. The one resulting gate list includes all arrays, all scalar preparation, both passes, and every output coefficient. The multiplier syntax is an unconstrained implementation parameter; existence of suitable syntax and the complete complexity bound are theorem conclusions, never definition fields or hypotheses.
-- source:
--   yang zhou, Mingsheng Wang, Almost-Linear Modular Composition over Arbitrary Commutative Rings, STOC 2027 submission #450 (October 2026), §3.3, equation (10), Lemma 3.2, printed p.7 / PDF p.8; Algorithm 1 and Proposition 4.1, printed p.8 / PDF p.9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/450.pdf

import Definitions.Def_AlmostLinearModComp_Composition_CoordinateAlgorithm

namespace AlmostLinearModComp.Composition

def Stage.blockSide {d : Radices} (s : Stage d) (i : ℕ) : ℕ :=
  if i = s.j.val then 3 else 2

def Stage.blockWeight {d : Radices} (s : Stage d) (i : ℕ) : ℕ :=
  ((List.range i).map s.blockSide).prod

def Stage.blockCount {d : Radices} (s : Stage d) : ℕ := s.blockWeight (d.m + 1)

def Stage.blockDigit {d : Radices} (s : Stage d) (b i : ℕ) : ℕ :=
  b / s.blockWeight i % s.blockSide i

/-- Entire equation (10) block construction. Shared factors are computed by binary
powering; H and each earlier transposed change are actually executed in source order. -/
def nextArrayW (B : Multipliers) {d : Radices} (s : Stage d) (L : ℕ)
    (f targets : WVec) (previous : List StoredChange) : Code WVec := do
  let factors ← (List.range (d.m + 1)).mapM fun i => do
    let a := if i < d.m then (targets.drop (i * d.size * L)).take (d.size * L)
      else wires (d.size * L) fun k => .integer (if k = s.v * L then 1 else 0)
    quotientPower B d.size L f (s.sides i) a
  let blocks ← (List.range s.blockCount).mapM fun b => do
    let mut common := unitXT d.size L
    for i in List.range (d.m + 1) do
      let power ← quotientPower B d.size L f (s.blockDigit b i) (factors[i]?.getD [])
      common ← quotientProduct B d.size L f common power
    let mut block ← hankelMultiply B d.size L f common
    for change in previous do
      block ← applyChangeTranspose change d.size L block
    pure block
  return wires (s.arraySize * L) fun k =>
    let gamma := s.arrayDigit (k / L)
    let b := ((List.range (d.m + 1)).map fun i =>
      s.blockWeight i * (gamma i / s.sides i)).sum
    let e := ((List.finRange d.m).map fun i =>
      d.weight i * (gamma i.val % s.sides i.val)).sum +
      s.v * (gamma d.m % s.sides d.m)
    atW (blocks[b]?.getD []) (e * L + k % L)

def earlierStages {d : Radices} (s : Stage d) : List (Stage d) :=
  (allStages d).filter fun u => u.v < s.v

/-- Input layout: F, all targets, then each previous stage's complete M array.
Only those previous arrays are read; the next array is an output. -/
def arrayCircuit (B : Multipliers) {d : Radices} (s : Stage d) (L : ℕ) : Circuit :=
  compile do
    let f := wires d.size Wire.input
    let targets := wires (d.m * d.size * L) fun i => .input (d.size + i)
    let mut cursor := d.size + d.m * d.size * L
    let mut previous := []
    for u in earlierStages s do
      let array := wires (u.arraySize * L) fun i => .input (cursor + i)
      let change ← prepareChange B u L L f array
      previous := previous ++ [change]
      cursor := cursor + u.arraySize * L
    nextArrayW B s L f targets previous

/-- Algorithm 1: increasing preparation, then decreasing applications. No scalar, array,
Hankel matrix, or correctness/cost certificate is accepted from outside this computation. -/
def algorithmOneCircuit (B : Multipliers) (d : Radices) (L : ℕ) : Circuit :=
  compile do
    let f := wires d.size Wire.input
    let targets := wires (d.m * d.size * L) fun i => .input (d.size + i)
    let mut stored := []
    for s in allStages d do
      let array ← nextArrayW B s L f targets stored
      let change ← prepareChange B s L L f array
      stored := stored ++ [change]
    let mut p := wires (d.size * L) fun i => .input (d.size + d.m * d.size * L + i)
    for change in stored.reverse do
      p ← applyChange change p
    return p

end AlmostLinearModComp.Composition


