-- Prove2me | Definitions.Def_NuclearTensor_Membership_Regimes
-- name    : NuclearTensor_Membership_Regimes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T22:18:06.734018+00:00
-- url     : https://prove2.me/theorems/3db221be-a555-476c-8ed5-98db46d7675e
-- title:
--   Operational covers in both order/dimension regimes
-- statement:
--   For $k\le d^2$, store a $\delta/4$ grid in each compressed unit ball. For each grid point, test predecessors in order using actual feasible projection approximations of error at most $\delta/8$, retain the first whose residual is strictly below $\delta/2$, and store its predecessor and local point. The recorded row stops immediately after success, or after all predecessors fail. Terminal candidates are the given local service's feasible $\epsilon_0/4$-accurate answers, compared by their actual objective values.
--
--   For $k>d^2$, construct actual $\gamma$-nets of the original local sets, with $\gamma=\epsilon_0/(4k)$, and regroup into $m=\min(k,\lceil\sqrt{dk}\rceil)$ balanced consecutive blocks. Block options are explicitly enumerated products of local-net vectors. At each compressed layer enumerate predecessor/block-option pairs, find the closest grid point by a finite scan, and retain the first witness per marked grid bucket. Terminal optimization is finite enumeration, followed by witness traceback and conversion to original local vectors.
--
--   All ranks, grids, tested projection points, nets, cover witnesses, and terminal data are finite array outputs of the counted program. This is an output behavior specification: no global approximation or runtime is a field of its data structures. The source accuracy guarantee and running time are separate conclusions of Lemma 5.1.
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), pp.18–20, both regimes in the proof of Lemma 5.1

import Definitions.Def_NuclearTensor_Membership_Optimization

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace NuclearTensor.Membership

structure Retained {ds : List ℕ} (C : PrefixData ds) (j : ℕ) where
  parent : ℕ
  factor : Vec (ds.getD j 0)
  point : Vec (C.rank (j + 1))
  bucket : ℕ

def previousNode {ds : List ℕ} {C : PrefixData ds} (S : FiniteCover C)
    (j p : ℕ) : Vec (C.rank j) :=
  if h : p < S.count j then S.node j ⟨p, h⟩ else 0

def matchesLayer {ds : List ℕ} {C : PrefixData ds} (S : FiniteCover C)
    (j : ℕ) (es : List (Retained C j)) : Prop :=
  List.ofFn (fun t => encodeVec (S.node (j + 1) t)) = es.map (fun e => encodeVec e.point) ∧
  List.ofFn (S.parent j) = es.map Retained.parent ∧
  List.ofFn (fun t => encodeVec (S.factor j t)) = es.map (fun e => encodeVec e.factor)

/-- The first successful predecessor for a grid point; a row stores only the tested
prefix, so the source's stop-after-success rule is retained. -/
def projectionNode {ds : List ℕ} (C : PrefixData ds) (S : FiniteCover C)
    (δ : ℝ) (j g : ℕ) (grid : Vec (C.rank (j + 1)))
    (row : List (Vec (ds.getD j 0))) : Option (Retained C j) :=
  ((List.range row.length).find? (fun p =>
    ‖mtv (C.embedding j) (outer (previousNode S j p) (row[p]?.getD 0)) - grid‖ < δ / 2)).map
    (fun p => ⟨p, row[p]?.getD 0,
      mtv (C.embedding j) (outer (previousNode S j p) (row[p]?.getD 0)), g⟩)

def dedupRetained {ds : List ℕ} {C : PrefixData ds} {j : ℕ}
    (es : List (Retained C j)) : List (Retained C j) := by
  classical
  exact es.foldl (fun acc e => if ∃ a ∈ acc, a.point = e.point then acc else acc ++ [e]) []

structure SmallOrderData (ds : List ℕ) where
  chain : PrefixData ds
  cover : FiniteCover chain
  grids : (j : ℕ) → List (Vec (chain.rank (j + 1)))
  projections : (j g : ℕ) → List (Vec (ds.getD j 0))
  terminal : Fin (cover.count (ds.length - 1)) → Vec (ds.getD (ds.length - 1) 0)

def terminalLinear {ds : List ℕ} (C : PrefixData ds)
    (p : Vec (C.rank (ds.length - 1))) : Vec (ds.getD (ds.length - 1) 0) :=
  WithLp.toLp 2 (fun b => ∑ a : Fin (C.rank (ds.length - 1)),
    entry (C.tensor (ds.length - 1))
      (a.val * ds.getD (ds.length - 1) 0 + b.val) * p a)

def smallOrderBehavior (σ : Spectral) (O : LocalOracle)
    (K : (j : ℕ) → Set (Vec (O.dimensions.getD j 0))) (ε : ℝ)
    (M : Tensor O.dimensions) (D : SmallOrderData O.dimensions) (x : Tuple O.dimensions) : Prop :=
  let ds := O.dimensions
  let η := compressionAccuracy ε ds.length
  let δ := coverAccuracy ε ds.length
  algorithm1 σ η M D.chain ∧
  (∀ j, j + 1 < ds.length →
    isNet (unitBall (D.chain.rank (j + 1))) (δ / 4) (D.grids j) ∧
    (∀ g < (D.grids j).length,
      let grid := (D.grids j)[g]?.getD 0
      let row := D.projections j g
      row.length ≤ D.cover.count j ∧
      (∀ p < row.length, row[p]?.getD 0 ∈ K j ∧
        ∀ y ∈ K j,
          ‖mtv (D.chain.embedding j) (outer (previousNode D.cover j p) (row[p]?.getD 0)) - grid‖ ≤
          ‖mtv (D.chain.embedding j) (outer (previousNode D.cover j p) y) - grid‖ + δ / 8) ∧
      (∀ p, p + 1 < row.length →
        δ / 2 ≤ ‖mtv (D.chain.embedding j)
          (outer (previousNode D.cover j p) (row[p]?.getD 0)) - grid‖) ∧
      (row.length = D.cover.count j ∨
        ∃ p < row.length, ‖mtv (D.chain.embedding j)
          (outer (previousNode D.cover j p) (row[p]?.getD 0)) - grid‖ < δ / 2)) ∧
    matchesLayer D.cover j (dedupRetained
      ((List.range (D.grids j).length).filterMap fun g =>
        projectionNode D.chain D.cover δ j g ((D.grids j)[g]?.getD 0) (D.projections j g)))) ∧
  finiteCoverProperty D.chain K δ D.cover ∧
  (∀ t, ∃ h : ds.length - 1 < ds.length,
    D.terminal t = O.answer ⟨ds.length - 1, h⟩
      (terminalLinear D.chain (D.cover.node (ds.length - 1) t)) (terminalAccuracy ε)) ∧
  ∃ t : Fin (D.cover.count (ds.length - 1)),
    traceback D.cover t.val x ∧ x (ds.length - 1) = D.terminal t ∧
    ∀ u : Fin (D.cover.count (ds.length - 1)),
      inner ℝ (terminalLinear D.chain (D.cover.node (ds.length - 1) u)) (D.terminal u) ≤
      inner ℝ (terminalLinear D.chain (D.cover.node (ds.length - 1) t)) (D.terminal t)

def choices {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: xss => xs.flatMap (fun x => (choices xss).map (List.cons x))

def blockPoints (ds : List ℕ) (m j : ℕ)
    (nets : (i : ℕ) → List (Vec (ds.getD i 0))) : List (Vec ((block ds m j).prod)) :=
  let begin := j * ds.length / m
  let arrays := (List.range (block ds m j).length).map fun i =>
    (nets (begin + i)).map encodeVec
  (choices arrays).map fun xs => product (fun i =>
    decodeVec ((block ds m j).getD i 0) (xs[i]?.getD []))

def blockTuple (ds : List ℕ) (m : ℕ) (x : Tuple ds) : Tuple (groupedDimensions ds m) :=
  fun j => decodeVec ((groupedDimensions ds m).getD j 0)
    (encodeVec (product (ds := block ds m j) (fun i =>
      decodeVec ((block ds m j).getD i 0) (encodeVec (x (j * ds.length / m + i))))))

/-- Closest grid point, using an explicit finite scan and first-index tie breaking. -/
def closest {n : ℕ} (q : Vec n) (grid : List (Vec n)) : Option ℕ :=
  (List.range grid.length).foldl (fun best i => match best with
    | none => some i
    | some t => if ‖q - (grid[i]?.getD 0)‖ < ‖q - (grid[t]?.getD 0)‖ then some i else best) none

/-- Enumerate every predecessor/block-vector pair and retain the first witness per marked
nearest-grid bucket. All grid searches and witness entries are explicit finite operations. -/
def greedyLayer {ds : List ℕ} (C : PrefixData ds) (S : FiniteCover C) (j : ℕ) (δ : ℝ)
    (grid : List (Vec (C.rank (j + 1)))) (localPoints : List (Vec (ds.getD j 0))) :
    List (Retained C j) :=
  let candidates := (List.range (S.count j)).flatMap fun p => localPoints.map fun x =>
    (p, x, mtv (C.embedding j) (outer (previousNode S j p) x))
  candidates.foldl (fun acc e =>
    match closest e.2.2 grid with
    | none => acc
    | some g => if ‖e.2.2 - (grid[g]?.getD 0)‖ ≤ δ / 4 ∧
        ¬ ∃ a ∈ acc, a.bucket = g then acc ++ [⟨e.1, e.2.1, e.2.2, g⟩] else acc) []

structure LargeOrderData (ds : List ℕ) where
  nets : (j : ℕ) → List (Vec (ds.getD j 0))
  chain : PrefixData (groupedDimensions ds (blockCount ds))
  cover : FiniteCover chain
  grids : (j : ℕ) → List (Vec (chain.rank (j + 1)))

def largeOrderBehavior (σ : Spectral) (O : LocalOracle)
    (K : (j : ℕ) → Set (Vec (O.dimensions.getD j 0))) (ε : ℝ)
    (M : Tensor O.dimensions) (D : LargeOrderData O.dimensions) (x : Tuple O.dimensions) : Prop :=
  let ds := O.dimensions
  let m := blockCount ds
  let gs := groupedDimensions ds m
  let η := compressionAccuracy ε m
  let δ := coverAccuracy ε m
  let localSets := fun j => {z : Vec (gs.getD j 0) |
    encodeVec z ∈ (blockPoints ds m j D.nets).map encodeVec}
  gs.prod = ds.prod ∧ gs.length = m ∧ 0 < m ∧
  (∀ j < ds.length, isNet (K j) (localNetAccuracy ε ds.length) (D.nets j)) ∧
  algorithm1 σ η (decodeVec gs.prod (encodeVec M)) D.chain ∧
  (∀ j, j + 1 < m →
    isNet (unitBall (D.chain.rank (j + 1))) (δ / 4) (D.grids j) ∧
    matchesLayer D.cover j (greedyLayer D.chain D.cover j δ (D.grids j)
      ((blockPoints ds m j D.nets).map fun z => decodeVec (gs.getD j 0) (encodeVec z)))) ∧
  finiteCoverProperty D.chain localSets δ D.cover ∧
  (∀ j < ds.length, x j ∈ D.nets j) ∧
  algorithm2Output D.chain localSets D.cover (blockTuple ds m x)

/-- The complete intermediate data are explicit array outputs of the counted program,
not assumed optimizers. The global approximation is a separate theorem conclusion. -/
def smallOrderReals {ds : List ℕ} (D : SmallOrderData ds) : List ℝ :=
  encodePrefixReals D.chain ++ encodeCoverReals D.cover ++
  ((List.range (ds.length - 1)).map fun j =>
    ((D.grids j).map encodeVec).flatten ++
    ((List.range (D.grids j).length).map fun g =>
      ((D.projections j g).map encodeVec).flatten).flatten).flatten ++
  (List.ofFn fun t => encodeVec (D.terminal t)).flatten

def largeOrderReals {ds : List ℕ} (D : LargeOrderData ds) : List ℝ :=
  ((List.range ds.length).map fun j => ((D.nets j).map encodeVec).flatten).flatten ++
  encodePrefixReals D.chain ++ encodeCoverReals D.cover ++
  ((List.range (blockCount ds - 1)).map fun j => ((D.grids j).map encodeVec).flatten).flatten

def smallOrderIntegers {ds : List ℕ} (D : SmallOrderData ds) : List ℤ :=
  encodePrefixIntegers D.chain ++ encodeCoverIntegers D.cover ++
  ((List.range (ds.length - 1)).map fun j =>
    [((D.grids j).length : ℤ)] ++
    ((List.range (D.grids j).length).map fun g => ((D.projections j g).length : ℤ))).flatten

def largeOrderIntegers {ds : List ℕ} (D : LargeOrderData ds) : List ℤ :=
  ((List.range ds.length).map fun j => ((D.nets j).length : ℤ)) ++
  encodePrefixIntegers D.chain ++ encodeCoverIntegers D.cover ++
  ((List.range (blockCount ds - 1)).map fun j => ((D.grids j).length : ℤ))

def realizesRegimes (σ : Spectral) (O : LocalOracle)
    (K : (j : ℕ) → Set (Vec (O.dimensions.getD j 0))) (ε : ℝ)
    (M : Tensor O.dimensions) (s : Configuration) (x : Tuple O.dimensions) : Prop :=
  if O.dimensions.length ≤ maxDimension O.dimensions ^ 2 then
    ∃ D : SmallOrderData O.dimensions, smallOrderBehavior σ O K ε M D x ∧
      outputIntegers s = smallOrderIntegers D ∧
      outputReals s = encodeTuple x ++ smallOrderReals D
  else ∃ D : LargeOrderData O.dimensions, largeOrderBehavior σ O K ε M D x ∧
      outputIntegers s = largeOrderIntegers D ∧
      outputReals s = encodeTuple x ++ largeOrderReals D

end NuclearTensor.Membership


