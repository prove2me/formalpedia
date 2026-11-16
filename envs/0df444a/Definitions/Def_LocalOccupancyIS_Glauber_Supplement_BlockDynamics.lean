-- Prove2me | Definitions.Def_LocalOccupancyIS_Glauber_Supplement_BlockDynamics
-- name    : LocalOccupancyIS_Glauber_Supplement_BlockDynamics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:58:35.471131+00:00
-- url     : https://prove2.me/theorems/5360fe69-ac2b-4d18-a41e-f468e0f67613
-- title:
--   Neighborhood block process and enumerating implementation
-- statement:
--   Let $G$ be a finite simple graph, $N(u)$ its open neighborhood, and $\lambda>0$ its fugacity. The published kernels $Q_u$ and $P_u$ resample the open neighborhood and then its center. Laws multiply on the left. Define
--
--   $$K_N=\frac1n\sum_u Q_uP_u,\qquad B_T(\nu)=\frac1T\sum_{j=0}^{T-1}\mathbb E_{\nu K_N^j}|I|.$$
--
--   The implementation enumerates all subsets $S\subseteq N(u)$, tests independence and compatibility with the fixed exterior, assigns weight $\lambda^{|S|}$ to feasible assignments and zero to others, normalizes, samples exactly, and then updates the center. Maintained occupied-neighbor counters permit exterior compatibility tests without scanning all vertices. The definitions include the counter initialization values, the local update of those counters, the actual table and its pushed-forward law, and charged loop traces for enumeration and maintenance.
--
--   Work counts table accesses, adjacency and spin tests, real arithmetic, writes and exact random choice. Site selection and the center update have constant cost. Weights use at most $|N(u)|$ multiplications each; table summation, normalization and weighted choice have linear cost in the table length. Counter initialization is charged separately. This is the source's exact-arithmetic and exact-random-choice model for arbitrary real fugacity, without a finite-bit complexity claim. The formula for the law fixes the exterior semantically; the implementation overwrites only the block bits.
-- source:
--   Ewan Davies, Brian Tan, STOC 2027 submission #982 (October 2026), pp.3–4, equation (2), Theorem 1; §3 pp.12–13

import Definitions.Def_LocalOccupancyIS_Glauber_Parameters

open scoped BigOperators

namespace LocalOccupancyIS.Glauber.Supplement
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Left action: resample the open neighborhood, then the center. -/
def blockKernel (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) :
    Matrix (State G) (State G) ℝ :=
  (Fintype.card V : ℝ)⁻¹ • ∑ u, Q G lam u * P G lam u

def blockMean (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (ν : State G → ℝ) (T : ℕ) : ℝ :=
  (∑ j ∈ Finset.range T,
    expectation (push ν (blockKernel G lam ^ j)) (fun σ => size σ.val)) / T

/-- Maintained occupied-neighbor counters. Initialization is outside the per-step cost. -/
def counters (G : SimpleGraph V) [DecidableRel G.Adj] (σ : State G) : V → ℕ :=
  fun v => nbrSize G v σ.val

/-- Prepared once from the maintained counters, using only block adjacency queries. -/
def blockedTable (G : SimpleGraph V) [DecidableRel G.Adj] (u : V)
    (σ : State G) (occ : V → ℕ) : V → ℕ := fun v =>
  occ v - ((G.neighborFinset u).filter
    (fun w => G.Adj v w ∧ σ.val w = true)).card

/-- Local feasibility, using the cached exterior-blocked counts. -/
def candidateOK (G : SimpleGraph V) [DecidableRel G.Adj]
    (outside : V → ℕ) (S : Finset V) : Prop :=
  (∀ v ∈ S, outside v = 0) ∧ ∀ v ∈ S, ∀ w ∈ S, ¬ G.Adj v w

def candidateWeight (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (outside : V → ℕ) (S : Finset V) : ℝ :=
  open Classical in
  if candidateOK G outside S then lam ^ S.card else 0

/-- Enumerate every assignment once; exterior counters are prepared before the loop.
Only entries for v in N(u) of the lazy blockedTable are evaluated, and cached. -/
def candidateTable (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (u : V) (σ : State G) (occ : V → ℕ) : List (Finset V × ℝ) :=
  let outside := blockedTable G u σ occ
  (G.neighborFinset u).powerset.toList.map
    (fun S => (S, candidateWeight G lam outside S))

def tableMass (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (u : V) (σ : State G) (occ : V → ℕ) : ℝ :=
  ((candidateTable G lam u σ occ).map Prod.snd).sum

/-- Exact weighted choice from the table, pushed forward to configurations.
The exterior equality in this law is semantic, not a scan performed by the sampler:
the sampler keeps the old exterior and overwrites only the d neighborhood bits. -/
def enumerationRow (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (u : V) (σ : State G) (occ : V → ℕ) (τ : State G) : ℝ :=
  (((candidateTable G lam u σ occ).map (fun row =>
    if (∀ v ∉ G.neighborFinset u, τ.val v = σ.val v) ∧
       (∀ v ∈ G.neighborFinset u, τ.val v = decide (v ∈ row.1))
    then row.2 else 0)).sum) / tableMass G lam u σ occ

def enumerationQ (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (u : V) :
    Matrix (State G) (State G) ℝ := fun σ => enumerationRow G lam u σ (counters G σ)

/-- Update old counters locally by the removed and added contributions of spins
in the closed neighborhood. The implementation traverses the adjacency lists of
those d+1 vertices and changes the corresponding counter entries. -/
def maintainedCounts (G : SimpleGraph V) [DecidableRel G.Adj] (u : V)
    (σ τ : State G) (occ : V → ℕ) : V → ℕ := fun v =>
  occ v - ((insert u (G.neighborFinset u)).filter (fun w =>
    G.Adj v w ∧ σ.val w = true ∧ τ.val w = false)).card +
  ((insert u (G.neighborFinset u)).filter (fun w =>
    G.Adj v w ∧ σ.val w = false ∧ τ.val w = true)).card

/-- Exact-real primitive instructions charged by the enumerating implementation.
A pair test reads two assignment bits and the adjacency table. A weight is formed by
at most d multiplications, rather than treating exponentiation as a unit primitive. -/
inductive BlockOp where
  | readCounter | readSpin | adjacency | arithmetic | writeCell | randomChoice
  deriving DecidableEq

/-- A conservative instruction trace for preparing the d exterior-blocked counters,
materializing all 2^d assignments, testing all d² pairs for each assignment, forming
weights, summing, normalizing, and exact weighted choice. All loops run in full. -/
def enumerationTrace (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : List BlockOp :=
  let d := (G.neighborFinset u).card
  List.replicate d BlockOp.readCounter ++
  List.replicate (8*d*d + 6*d) BlockOp.arithmetic ++
  ((G.neighborFinset u).powerset.toList.flatMap (fun _ =>
    List.replicate d BlockOp.readSpin ++
    List.replicate (d*d) BlockOp.adjacency ++
    List.replicate (10*d*d + 16*d + 10) BlockOp.arithmetic ++
    List.replicate (d+1) BlockOp.writeCell)) ++
  List.replicate (3 * (G.neighborFinset u).powerset.card) BlockOp.arithmetic ++
  [BlockOp.randomChoice]

/-- After the neighborhood and center choices, update the maintained counters
by adding/removing one contribution at each neighbor of every changed spin.
Scanning unchanged spins too gives this conservative actual loop trace. -/
def maintenanceTrace (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : List BlockOp :=
  (insert u (G.neighborFinset u)).toList.flatMap (fun v =>
    [BlockOp.readSpin, BlockOp.readSpin] ++
    (G.neighborFinset v).toList.flatMap (fun _ =>
      [BlockOp.readCounter, BlockOp.arithmetic, BlockOp.writeCell]))

/-- Uniform site choice, enumeration, single-site center update and counter maintenance.
The center's counter makes its update constant work; initial counter construction
is charged separately. Real arithmetic and exact finite weighted choice are primitives. -/
def blockWork (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : ℕ :=
  10 + (enumerationTrace G u).length + (maintenanceTrace G u).length

end
end LocalOccupancyIS.Glauber.Supplement


