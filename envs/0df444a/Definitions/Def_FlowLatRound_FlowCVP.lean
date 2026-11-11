-- Prove2me | Definitions.Def_FlowLatRound_FlowCVP
-- name    : FlowLatRound_FlowCVP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:57:13.731614+00:00
-- url     : https://prove2.me/theorems/52541e75-233b-4600-b6d1-af428d0ee7af
-- title:
--   Lemma C.3, pp.23–24 — the closest-vector decoder for flow lattices (rounding of loops and a min-cost flow by successive shortest paths)
-- statement:
--   The decoder of Lemma C.3, on a multigraph $G$ and a rational target $y$:
--
--   1. a loop $e$ gets the nearest integer to $y_e$, half-integers rounded down;
--   2. for the other edges, $w=\lceil\sqrt m\rceil$, $\ell_e=\lceil y_e\rceil-w$, $u_e=\lfloor y_e\rfloor+w$, and $z_e=\ell_e+x_e$ with $0\le x_e\le u_e-\ell_e$; edge $e$ is expanded into unit arcs of costs $c_{e,j}=2(\ell_e+j-y_e)-1$, $j=1,\dots,u_e-\ell_e$;
--   3. the min-cost flow is computed by successive shortest paths after saturating all negative-cost arcs: while a vertex has positive imbalance, Bellman–Ford from all such vertices, and one unit is pushed to the least-index reachable vertex of negative imbalance.
--
--   Every operation is charged in the bit-cost model, and the output is a function of $(G,y)$.
--
--   **Formalization Note** The paper says only "a polynomial-time minimum-cost flow algorithm"; successive shortest paths is the algorithm fixed here.
-- source:
--   Chang, Replicable Mean Estimation via Random Lattice Rounding (manuscript, STOC 2027 submission, sha256 35bd3e4b…aeac), Lemma C.3 and its proof, pp.23–24 (PDF 25–26); Lemma 3.1, p.6 (PDF 8)

import Mathlib
import Definitions.Def_FlowLatRound_FlowGraph
import Definitions.Def_FlowLatRound_CostModel

namespace FlowLatRound

/-! # The closest-vector decoder of Lemma C.3

Chang, *Replicable Mean Estimation via Random Lattice Rounding* (manuscript, STOC 2027
submission, sha256 35bd3e4b…aeac), Lemma C.3 and its proof, pp.23–24 (PDF 25–26); Lemma 3.1,
p.6 (PDF 8).

**Formalization Note.** `flowCVP G y` is the proof's algorithm, run on a rational target `y`:
* a loop `e` gets `z_e = ⌈y_e − ½⌉`, the nearest integer with half-integers rounded down;
* for a non-loop edge, `w = ⌈√m⌉`, `ℓ_e = ⌈y_e⌉ − w`, `u_e = ⌊y_e⌋ + w`, `z_e = ℓ_e + x_e` with
  `0 ≤ x_e ≤ u_e − ℓ_e`; the edge is expanded into unit arcs of costs
  `c_{e,j} = 2(ℓ_e + j − y_e) − 1`, `j = 1, …, u_e − ℓ_e`, which are nondecreasing in `j`, so an
  optimal flow uses an initial segment of them and `x_e` arcs in use are represented by the number
  `x_e`;
* the paper fixes "a polynomial-time minimum-cost flow algorithm" without naming it. The
  algorithm fixed here is **successive shortest paths** after saturating every negative-cost arc:
  start from `x_e = #{j : c_{e,j} < 0}` (then every residual arc has cost `≥ 0`); while some
  vertex has positive imbalance (inflow minus outflow of `z`), run Bellman–Ford (`n` rounds) on the
  residual network from all vertices of positive imbalance, take the least-index vertex of
  negative imbalance that is reached, and push one unit along the recorded shortest path. The
  residual arcs of edge `e` are `src → dst` of cost `c_{e,x_e+1}` (if `x_e < u_e − ℓ_e`) and
  `dst → src` of cost `−c_{e,x_e}` (if `x_e > 0`). The loop runs at most (initial total positive
  imbalance) + 1 times.
* Every rational operation is charged `opCost` of its operands, every list step and every
  array access `1`; the program is a function of `(G, y)`, hence deterministic. -/

/-- `⌈√m⌉`, by linear search (`O(√m)` charged steps). -/
def ceilSqrtC (m : ℕ) : Counted ℕ := go (m + 1) 0
where
  go : ℕ → ℕ → Counted ℕ
    | 0, w => pure w
    | fuel + 1, w => do
        charge (opCost w w + opCost (w * w) m)
        if w * w < m then go fuel (w + 1) else pure w

/-- The bit length of a rational vector, `Σ_e ratBits (y_e)`. -/
def bitsQ {m : ℕ} (y : Fin m → ℚ) : ℕ := ∑ e, ratBits (y e)

/-- A residual arc: from `frm` to `tgt`, on edge `e`, forward (`x_e += 1`) or backward
(`x_e −= 1`), with its cost. -/
structure Arc (n m : ℕ) where
  frm : Fin n
  tgt : Fin n
  e : Fin m
  fwd : Bool
  cost : ℚ

/-- The unit-arc cost `c_{e,j} = 2(ℓ_e + j − y_e) − 1`, charged operation by operation. -/
def margCostC (lo j : ℤ) (y : ℚ) : Counted ℚ := do
  let s1 : ℚ := (lo : ℚ) + j
  let s2 : ℚ := s1 - y
  let s3 : ℚ := 2 * s2
  charge (opCost lo j + opCost s1 y + opCost 2 s2 + opCost s3 1)
  pure (s3 - 1)

/-- One Bellman–Ford round: relax every arc in order (strict improvements only). -/
def relaxC {n m : ℕ} (arcs : List (Arc n m)) (st : (Fin n → Option ℚ) × (Fin n → Option (Arc n m))) :
    Counted ((Fin n → Option ℚ) × (Fin n → Option (Arc n m))) :=
  arcs.foldlM (fun (st : (Fin n → Option ℚ) × (Fin n → Option (Arc n m))) a => do
    charge 3
    match st.1 a.frm with
    | none => pure st
    | some da => do
        let cand := da + a.cost
        charge (opCost da a.cost)
        match st.1 a.tgt with
        | none => pure (Function.update st.1 a.tgt (some cand), Function.update st.2 a.tgt (some a))
        | some dt => do
            charge (opCost cand dt)
            if cand < dt then
              pure (Function.update st.1 a.tgt (some cand), Function.update st.2 a.tgt (some a))
            else pure st)
    st

/-- `k` Bellman–Ford rounds. -/
def bfC {n m : ℕ} (arcs : List (Arc n m)) :
    ℕ → (Fin n → Option ℚ) × (Fin n → Option (Arc n m)) →
      Counted ((Fin n → Option ℚ) × (Fin n → Option (Arc n m)))
  | 0, st => pure st
  | k + 1, st => do
      let st' ← relaxC arcs st
      bfC arcs k st'

/-- The arcs of the recorded shortest path ending at `v` (at most `fuel` steps back). -/
def pathC {n m : ℕ} (pred : Fin n → Option (Arc n m)) : ℕ → Fin n → Counted (List (Arc n m))
  | 0, _ => pure []
  | fuel + 1, v => do
      charge 1
      match pred v with
      | none => pure []
      | some a => do
          let r ← pathC pred fuel a.frm
          pure (a :: r)

/-- The number of constant-size operations of the per-edge setup of `flowCVP` at edge `e`,
each charged `opCost` of its operands. -/
def setupCost {m : ℕ} (y : Fin m → ℚ) (w : ℤ) (e : Fin m) : ℕ :=
  let c : ℤ := ⌈y e⌉
  let f : ℤ := ⌊y e⌋
  let lo := c - w
  let hi := f + w
  let r : ℤ := ⌈y e + 1 / 2⌉
  let t := r - 1 - lo
  opCost (y e) 1 + opCost (y e) 1 + opCost c w + opCost f w + opCost hi lo +
    opCost (y e) (1 / 2) + opCost (y e + 1 / 2) 1 + opCost r 1 + opCost (r - 1) lo +
    opCost (hi - lo) t + opCost 0 (min (hi - lo) t) +
    opCost (y e) (1 / 2) + opCost (y e - 1 / 2) 1 + 6

namespace MGraph

variable {n m : ℕ} (G : MGraph n m)

/-- Imbalances `Σ_{dst e = v} z_e − Σ_{src e = v} z_e` of `z = ℓ + x` over non-loop edges. -/
def imbalanceC (lo x : Fin m → ℤ) : Counted (Fin n → ℤ) :=
  (List.finRange m).foldlM (fun (imb : Fin n → ℤ) e => do
    charge 4
    if G.src e = G.dst e then pure imb
    else do
      let z := lo e + x e
      charge (opCost (lo e) (x e) + opCost (imb (G.dst e)) z + opCost (imb (G.src e)) z + 4)
      pure (Function.update (Function.update imb (G.dst e) (imb (G.dst e) + z))
        (G.src e) (imb (G.src e) - z)))
    (fun _ => 0)

/-- The residual arcs of the pseudoflow `x` (non-loop edges only). -/
def arcsC (y : Fin m → ℚ) (lo U x : Fin m → ℤ) : Counted (List (Arc n m)) :=
  (List.finRange m).foldlM (fun (acc : List (Arc n m)) e => do
    charge 4
    if G.src e = G.dst e then pure acc
    else do
      charge (opCost (x e) (U e) + opCost (x e) 0 + 2)
      let fw ← if x e < U e then do
          charge (opCost (x e) 1)
          let c ← margCostC (lo e) (x e + 1) (y e)
          pure [(⟨G.src e, G.dst e, e, true, c⟩ : Arc n m)]
        else pure []
      let bw ← if 0 < x e then do
          let c ← margCostC (lo e) (x e) (y e)
          charge (opCost c 0)
          pure [(⟨G.dst e, G.src e, e, false, -c⟩ : Arc n m)]
        else pure []
      charge (acc.length + 2)
      pure (acc ++ fw ++ bw))
    []

/-- Successive shortest paths: at most `fuel` augmentations of one unit. -/
def sspC (y : Fin m → ℚ) (lo U : Fin m → ℤ) : ℕ → (Fin m → ℤ) → Counted (Fin m → ℤ)
  | 0, x => pure x
  | fuel + 1, x => do
      let imb ← G.imbalanceC lo x
      charge (∑ v, (opCost (imb v) 0 + 1))
      if ∀ v, imb v ≤ 0 then pure x
      else do
        let arcs ← G.arcsC y lo U x
        charge (n + 1)
        let dist0 : Fin n → Option ℚ := fun v => if 0 < imb v then some 0 else none
        let st ← bfC arcs n (dist0, fun _ => none)
        charge (∑ v, (opCost (imb v) 0 + 2))
        match (List.finRange n).find? (fun v => decide (imb v < 0) && (st.1 v).isSome) with
        | none => pure x
        | some t => do
            let path ← pathC st.2 (n + 1) t
            let x' ← path.foldlM (fun (x : Fin m → ℤ) a => do
                charge (opCost (x a.e) 1 + 2)
                pure (Function.update x a.e (if a.fwd then x a.e + 1 else x a.e - 1))) x
            sspC y lo U fuel x'

/-- The closest-vector decoder of Lemma C.3: a closest point of `Λ_G` to the rational target
`y ∈ H_G`, computed by rounding loops and by a min-cost flow on the expanded network. -/
def flowCVP (y : Fin m → ℚ) : Counted (Fin m → ℤ) := do
  let w ← ceilSqrtC m
  charge (∑ e, setupCost y w e + m + 1)
  let lo : Fin m → ℤ := fun e => ⌈y e⌉ - w
  let U : Fin m → ℤ := fun e => (⌊y e⌋ + w) - lo e
  let x0 : Fin m → ℤ := fun e => max 0 (min (U e) (⌈y e + 1 / 2⌉ - 1 - lo e))
  let imb0 ← G.imbalanceC lo x0
  charge (∑ v, (opCost (imb0 v) 0 + opCost (∑ u, max (imb0 u) 0) (imb0 v) + 2))
  let K : ℕ := (∑ v, max (imb0 v) 0).toNat
  let x ← G.sspC y lo U (K + 1) x0
  charge (m * (opCost (max n m) (max n m) + 2))
  pure (fun e => if G.src e = G.dst e then ⌈y e - 1 / 2⌉ else lo e + x e)

end MGraph

end FlowLatRound


