-- Prove2me | Definitions.Def_DistributedMIS_LocalLowerBound_Simulation
-- name    : DistributedMIS_LocalLowerBound_Simulation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:12.104724+00:00
-- url     : https://prove2.me/theorems/29397a7d-2f9b-4143-8c5e-48ec0021e60f
-- title:
--   Tentative IDs, gated simulation, conflict repair and parameters
-- statement:
--   Split clique coordinates into the ordered halves P and Q. Each directed edge contributes its P-by-Q matrix block to its source; the reverse edge uses the disjoint reverse block. XOR over neighbors, divide into b_ID-bit chunks, and set each tentative identifier to one plus the chunk modulo n. A clique produces candidates only when its radius-(T+1) tentative IDs are distinct. Candidates execute the given LOCAL program using tapes indexed by tentative ID and ports sorted by neighbor ID. A candidate survives precisely when no graph neighbor is a candidate.
--
--   $$L=k\left(1+D\sum_{i=0}^{T+1}(D-1)^i\right),\quad
--   \delta_{ID}=L(L-1)/n,\quad \gamma_{EXT}=(k+1)^D e^{-k2^{-D}}.$$
--
--   The simulation rule, identifiers, ball sizes and the final parameter map all have explicit bodies. The matrix measure is the infinite fair product; there is no independent reverse-edge matrix or shared random tape.
-- source:
--   Seri Khoury, Aaron Schild, STOC 2027 submission #411 (October 2026), pinned submission dated October 30, 2026; §2.3, pp. 8–9; §3 and Proposition 3.1, pp. 9–10; Appendix A.1–A.2, pp. 32–33; A.5, pp. 34–35 (printed = PDF)

import Definitions.Def_DistributedMIS_LocalLowerBound_EdgeRules
import Definitions.Def_DistributedMIS_LocalLowerBound_LocalPrograms

noncomputable section

namespace DistributedMIS.LocalLowerBound

def matrixMeasure (k : ℕ) : MeasureTheory.Measure (Matrices k) :=
  MeasureTheory.Measure.infinitePi (fun _ : BitIndex k => fairBit)

def matrixProbability {k : ℕ} (E : Set (Matrices k)) : ℝ := (matrixMeasure k E).toReal

def idBits (n : ℕ) : ℕ := ⌈Real.log n / Real.log 2⌉₊

def blockPairs (k : ℕ) : List (Fin k × Fin k) :=
  ((List.finRange k).filter (fun a => a.val < k/2)).flatMap
    (fun a => ((List.finRange k).filter (fun b => k/2 ≤ b.val)).map (fun b => (a,b)))

def blockBit {k : ℕ} (ω : Matrices k) (u v j : ℕ) : Bool :=
  match (blockPairs k)[j]? with
  | none => false
  | some (a,b) => edgeBit ω u v a b

def tentativeID {V : Type} {k : ℕ} (n : ℕ) (nbr : V → List V) (label : V → ℕ)
    (ω : Matrices k) (v : V) (a : Fin k) : ℕ :=
  1 + ((∑ i ∈ Finset.range (idBits n),
    if (nbr v).foldl (fun z u => Bool.xor z
      (blockBit ω (label v) (label u) (a.val * idBits n + i))) false then 2^i else 0) % n)

def cliqueNeighbors {V : Type} [DecidableEq V] {k : ℕ}
    (nbr : V → List V) (label : V → ℕ) (ω : Matrices k) (x : V × Fin k) : List (V × Fin k) :=
  (((List.finRange k).filter (fun b => b ≠ x.2)).map (fun b => (x.1,b))) ++
    (nbr x.1).flatMap (fun u =>
      ((List.finRange k).filter (fun b => edgeBit ω (label x.1) (label u) x.2 b)).map (fun b => (u,b)))

def sortedPorts {V : Type} (nbr : V → List V) (ids : V → ℕ) (v : V) : List V :=
  (nbr v).mergeSort (fun u w => ids u ≤ ids w)

def networkBall {V : Type} [DecidableEq V] (nbr : V → List V) : ℕ → V → Finset V
  | 0, v => {v}
  | s+1, v => (networkBall nbr s v).biUnion (fun u => insert u (nbr u).toFinset)

def distinctIDs {V : Type} [DecidableEq V] {k : ℕ} (n s : ℕ)
    (nbr : V → List V) (label : V → ℕ) (ω : Matrices k) (v : V) : Prop :=
  Set.InjOn (fun x : V × Fin k => tentativeID n nbr label ω x.1 x.2)
    {x | x.1 ∈ networkBall nbr s v}

def tableTape {n : ℕ} (W : Fin n → PrivateTape) (i : ℕ) : PrivateTape :=
  if h : 0 < i ∧ i-1 < n then W ⟨i-1,h.2⟩ else fun _ => false

def candidate {V : Type} [DecidableEq V] {k : ℕ} (P : LocalProgram)
    (n advice T : ℕ) (W : Fin n → PrivateTape) (nbr : V → List V) (label : V → ℕ)
    (ω : Matrices k) (x : V × Fin k) : Bool := by
  classical
  let ids := fun y : V × Fin k => tentativeID n nbr label ω y.1 y.2
  exact if distinctIDs n (T+1) nbr label ω x.1 then
    localOutput P n advice T (sortedPorts (cliqueNeighbors nbr label ω) ids)
      ids (fun y => tableTape W (ids y)) x
    else false

def repaired {V : Type} [DecidableEq V] {k : ℕ} (P : LocalProgram)
    (n advice T : ℕ) (W : Fin n → PrivateTape) (nbr : V → List V) (label : V → ℕ)
    (ω : Matrices k) (x : V × Fin k) : Bool :=
  candidate P n advice T W nbr label ω x &&
    (cliqueNeighbors nbr label ω x).all (fun y => !(candidate P n advice T W nbr label ω y))

def simulatedChoice {V : Type} [DecidableEq V] {k : ℕ} (P : LocalProgram)
    (n advice T : ℕ) (W : Fin n → PrivateTape) (nbr : V → List V) (label : V → ℕ)
    (ω : Matrices k) (v : V) : Output k :=
  (List.finRange k).find? (fun a => repaired P n advice T W nbr label ω (v,a))

def simulationRule (G : SimpleGraph ℕ) [G.LocallyFinite] {k : ℕ}
    (P : LocalProgram) (n advice T : ℕ) (W : Fin n → PrivateTape) : RawRule k := by
  classical
  exact fun v ω a => if simulatedChoice P n advice T W
    (fun u => (G.neighborFinset u).toList) id ω v = a then 1 else 0

def localBallSize (D k T : ℕ) : ℕ :=
  k * (1 + D * ∑ i ∈ Finset.range (T+2), (D-1)^i)

def identifierError (n D k T : ℕ) : ℝ :=
  let L := localBallSize D k T
  (L : ℝ) * (L-1 : ℝ) / n

def externalError (D k : ℕ) : ℝ :=
  (k+1 : ℝ)^D * Real.exp (-(k : ℝ) * (2 : ℝ)^(-(D : ℤ)))

def regularBallBound (D g : ℕ) : ℕ :=
  1 + D * ∑ i ∈ Finset.range (g-2), (D-1)^i

def finiteParameters (n D k N T D₀ : ℕ) (H : SimpleGraph (Fin N)) : Prop :=
  D₀ ≤ D ∧ (D : ℝ) ≤ Real.log k ∧ Real.log k ≤ (D : ℝ)^2 ∧
  Even k ∧ k*N ≤ n ∧ k * idBits n ≤ k^2/4 ∧
  (∀ v, by classical exact H.degree v = D) ∧ (2*T+8 : ℕ) ≤ H.egirth

def reductionD (n : ℕ) : ℕ := ⌊Real.log n / 4⌋₊
def reductionK (n : ℕ) : ℕ := 2 * ⌈Real.exp (reductionD n : ℝ) / 2⌉₊
def reductionN (n : ℕ) : ℕ := 2 * (n / (2 * reductionK n))

end DistributedMIS.LocalLowerBound


