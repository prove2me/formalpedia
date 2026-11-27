-- Prove2me | Definitions.Def_DirectedHamiltonicity_CycleSearch
-- name    : DirectedHamiltonicity_CycleSearch
-- status  : Definition
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:06:25.924868+00:00
-- url     : https://prove2.me/theorems/ed40343d-fc49-5388-bf21-adf1ed284ab9
-- title:
--   Finite fair-coin oracle search for a certified directed Hamiltonian cycle
-- statement:
--   The edge deletion search uses dyadic draws of endpoints, masks, group weights, and a target coefficient. It amplifies weighted-path parity calls and verifies the orbit of a surviving cycle. The encoding specifies all finite tapes, including short strings. The work budget and RAM realization predicate record the cost of the remaining compilation step.
-- source:
--   T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, Section 2, proof of Theorem 1. https://arxiv.org/html/2609.39062v2#S2

import Definitions.Def_DirectedHamiltonicity_ParitySampler
import Definitions.Def_DirectedHamiltonicity_Main_ArcCopies
import Definitions.Def_DirectedHamiltonicity_Main_Algorithms

/-! Finite oracle search from Section 2 of Koana and Kumabe, Breaking the 2^n barrier for directed hamiltonicity. The external program is called on normal weighted-path instance tapes. Every array index, random alphabet, tie convention, tape block and final cycle check is fixed. -/

section

namespace DirectedHamiltonicity.Main.GroupIsolation

open Multidigraph Classical

open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V] {d : ℕ}

variable (adj : V → V → Prop) [DecidableRel adj] (S : SArc adj → Finset (Fin d)) (s t : V)

variable (hs : ∀ u, ¬ adj u s)

abbrev Other (s : V) := {v : V // v ≠ s}

def dest (a : ArcCopy adj S) : Other s :=
  ⟨a.1.1.2, fun h => hs a.1.1.1 (h ▸ a.1.2)⟩

def weight (w : Other s × Fin d → ℕ) (a : ArcCopy adj S) : ℕ :=
  w (dest adj S s hs a, a.2.1)

end DirectedHamiltonicity.Main.GroupIsolation

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open GroupIsolation Multidigraph FiniteSampling Classical

open scoped BigOperators

def copyMask (u : Fin 50) : Finset (Fin 3) :=
  Finset.univ.filter fun j => (if u.val = 0 then 0 else 1 + (u.val-1)/7).testBit j.val

variable {V : Type} [Fintype V] [DecidableEq V] (adj : V → V → Prop) [DecidableRel adj]

variable (s t : V) (hs : ∀ u, ¬ adj u s)

abbrev Labels (s : V) := Other s × Fin 3

abbrev labelCount (s : V) := Fintype.card (Labels s)

def labelWeight (v : Labels s → Fin (2*labelCount s)) (x : Labels s) : ℕ := (v x).val+1

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open Multidigraph Classical

def pathAdj {n : ℕ} (adj : Fin n → Fin n → Bool) (s t u v : Fin n) : Prop :=
  adj u v = true ∧ u ≠ v ∧ v ≠ s ∧ u ≠ t

instance {n : ℕ} (adj : Fin n → Fin n → Bool) (s t : Fin n) : DecidableRel (pathAdj adj s t) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

section Search

variable {E : Type} [DecidableEq E]

/-- Greedy edge deletion. The Boolean query sees the current graph with the candidate edge removed. -/
def prune (ask : E → Finset E → Bool) (G : Finset E) : List E → Finset E
  | [] => G
  | e :: es => prune ask (if ask e (G.erase e) then G.erase e else G) es

end Search

def edges {n : ℕ} (adj : Fin n → Fin n → Bool) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => adj p.1 p.2 = true

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open Multidigraph Classical

section Padding

variable {V E A : Type} [Fintype V] [Fintype E] [Fintype A] [DecidableEq V]

def paddedTail (H : Multidigraph V E) (decode : A → Option E) (s : V) (a : A) : V :=
  (decode a).elim s H.tail

def paddedHead (H : Multidigraph V E) (decode : A → Option E) (s : V) (a : A) : V :=
  (decode a).elim s H.head

def paddedWeight (w : E → ℕ) (decode : A → Option E) (a : A) : ℕ :=
  (decode a).elim 0 w

def paddedGraph (H : Multidigraph V E) (decode : A → Option E) (s : V) : Multidigraph V A :=
  ⟨paddedTail H decode s,paddedHead H decode s⟩

end Padding

variable {n : ℕ} (a : Fin n → Fin n → Prop) [DecidableRel a]

variable (S : SArc a → Finset (Fin 3)) (s : Fin n) (hs : ∀ u, ¬ a u s)

abbrev Slot (n : ℕ) := (Fin n × Fin n) × Fin 3

abbrev slotEquiv (n : ℕ) : Slot n ≃ Fin (n*n*3) :=
  (finProdFinEquiv.prodCongr (Equiv.refl _)).trans finProdFinEquiv

def decodePair (p : Slot n) : Option (ArcCopy a S) :=
  if ha : a p.1.1 p.1.2 then
    if hl : p.2 ∈ S ⟨p.1,ha⟩ then some ⟨⟨p.1,ha⟩,p.2,hl⟩ else none
  else none

def decodeSlot (i : Fin (n*n*3)) : Option (ArcCopy a S) :=
  decodePair a S ((slotEquiv n).symm i)

def inputGraph : Multidigraph (Fin n) (Fin (n*n*3)) := paddedGraph (copyGraph a S) (decodeSlot a S) s

def inputWeight (w : GroupIsolation.Other s × Fin 3 → ℕ) : Fin (n*n*3) → ℕ :=
  paddedWeight (GroupIsolation.weight a S s hs w) (decodeSlot a S)

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open Multidigraph GroupIsolation FiniteSampling Classical

abbrev Wmax (n : ℕ) := 6*(n-1)

abbrev Bmax (n : ℕ) := (n-1)*Wmax n

abbrev MatrixSeed (n : ℕ) := ((Fin n × Fin n) → Fin 50) × ((Fin n × Fin 3) → Fin (Wmax n))

/-- Finite trial data consisting of two endpoints, dense arc masks and group weights, and a target weight. -/
abbrev Draw (n : ℕ) := (Fin n × Fin n) × (MatrixSeed n × Fin (Bmax n+1))

/-- The admissible weight alphabet has the same size before and after restricting to non-start vertices. -/
theorem weightRange {n : ℕ} (s : Fin n) : Wmax n = 2*labelCount s := by
  simp [Wmax,labelCount,Labels,Other,Fintype.card_subtype_compl]
  omega

def restrictedSeed {n : ℕ} (a : Fin n → Fin n → Prop) [DecidableRel a] (s : Fin n)
    (z : MatrixSeed n) : (SArc a → Fin 50) × (Labels s → Fin (2*labelCount s)) :=
  (fun i => z.1 i.val, fun j => Fin.cast (weightRange s) (z.2 (j.1.val,j.2)))

def clean_no_in {n : ℕ} (adj : Fin n → Fin n → Bool) (s t : Fin n) : ∀ u, ¬pathAdj adj s t u s :=
  fun _ h => h.2.2.1 rfl

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open Multidigraph FiniteSampling TargetedSamplers Classical

noncomputable def outputBit (P : Program) (x coins : List Bool) : Bool :=
  decide (P.Outputs (runTapes x coins) (some [true]))

def majority {A : Type} (estimate : A → Bool) (r : ℕ) (x : Fin (2*r) → A) : Bool :=
  decide (r < (Finset.univ.filter (fun i => estimate (x i) = true)).card)

variable {n : ℕ} (adj : Fin n → Fin n → Prop) [DecidableRel adj]

variable (S : SArc adj → Finset (Fin 3)) (s t : Fin n) (hs : ∀ u, ¬ adj u s)

variable (w : GroupIsolation.Other s × Fin 3 → ℕ)

def parityInput (B : ℕ) : List Bool :=
  let H := inputGraph adj S s
  encodeParityInstance n (n*n*3) H.tail H.head (inputWeight adj S s hs w) s t B

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open Multidigraph GroupIsolation FiniteSampling TargetedSamplers Classical

def tableRank (n m b : ℕ) : ((Fin n × Fin m) → Fin b) ≃ Fin (b^(n*m)) :=
  (finProdFinEquiv.arrowCongr (Equiv.refl _)).trans finFunctionFinEquiv

abbrev drawCount (n : ℕ) := (n*n)*((50^(n*n)*(Wmax n)^(n*3))*(Bmax n+1))

def rankDraw (n : ℕ) : Draw n ≃ Fin (drawCount n) :=
  let tables := ((tableRank n n 50).prodCongr (tableRank n 3 (Wmax n))).trans finProdFinEquiv
  let inner := (tables.prodCongr (Equiv.refl (Fin (Bmax n+1)))).trans finProdFinEquiv
  (finProdFinEquiv.prodCongr inner).trans finProdFinEquiv

/-- One encoded weighted parity query. Invalid endpoints and an absent closing arc skip the call. -/
def candidateInput {n : ℕ} (adj : Fin n → Fin n → Bool) (z : Draw n) : Option (List Bool) :=
  let s := z.1.1
  let t := z.1.2
  if s ≠ t ∧ adj t s = true then
    let a := pathAdj adj s t
    let r := restrictedSeed a s z.2.1
    let S := fun e => copyMask (r.1 e)
    some (parityInput a S s t (clean_no_in adj s t) (labelWeight s r.2) z.2.2.val)
  else none

/-- Majority vote of the parity program on disjoint uniform strings. A rejected draw returns false. -/
noncomputable def verifiedQuery (P : Program) {n : ℕ} (adj : Fin n → Fin n → Bool)
    (r L : ℕ) (bits : CoinBlock (Draw n)) (c : Fin (2*r) → Fin L → Bool) : Bool :=
  ((decodeRank (rankDraw n) bits).bind (candidateInput adj)).elim false
    (fun x => majority (fun tape => outputBit P x (List.ofFn tape)) r c)

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open FiniteSampling Classical

def outerCeil (n : ℕ) := ⌈(50/49 : ℚ)^n⌉₊

def trialBlock (n : ℕ) := 4*(n*n*(Bmax n+1))*outerCeil n

def outerBlocks (n : ℕ) := 6*n*n+6

/-- Number of independent graph-and-weight trials in one decision. -/
def trials (n : ℕ) := trialBlock n * outerBlocks n

def majorityHalf (n : ℕ) := 2*((trials n).size + outerBlocks n)

/-- An integer upper bound for a single parity run and the length of one parity coin string. -/
def coinSpan (A k n : ℕ) :=
  A*⌈(15/8 : ℚ)^n⌉₊*(n+n*n*3+6*(n-1)+1)^k

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open Multidigraph FiniteSampling TargetedSamplers Classical

abbrev SeedPanel (n L : ℕ) := (Fin (trials n) → CoinBlock (Draw n)) × (Fin (2*majorityHalf n) → Fin L → Bool)

/-- Return true when at least one of the amplified trial queries returns true. -/
noncomputable def twoSided (P : Program) {n L : ℕ} (adj : Fin n → Fin n → Bool) (coins : SeedPanel n L) : Bool :=
  decide (∃ i, verifiedQuery P adj (majorityHalf n) L (coins.1 i) coins.2 = true)

def adjacency {n : ℕ} (G : Finset (Fin n × Fin n)) (u v : Fin n) : Bool := decide ((u,v) ∈ G)

def edgeOrder (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i => (List.finRange n).map fun j => (i,j)

/-- Delete each arc in row-major order if the trial decision still accepts the graph after deletion. -/
noncomputable def remaining (P : Program) {n L : ℕ} (adj : Fin n → Fin n → Bool) (z : SeedPanel n L) :=
  prune (fun _ G => twoSided P (adjacency G) z) (edges adj) (edgeOrder n)

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open Multidigraph

def nextVertex {n : ℕ} (R : Finset (Fin n × Fin n)) (u : Fin n) : Fin n :=
  ((List.finRange n).find? fun v => decide ((u,v) ∈ R)).getD u

/-- Check the distinct vertex orbit of the first retained outgoing neighbor, its edges, and its closing step. -/
def certify : (n : ℕ) → Finset (Fin n × Fin n) → Bool
  | 0, _ => false
  | n+1, R =>
    let f := nextVertex R
    let ord (i : Fin (n+1)) := f^[i.val] 0
    decide (f^[n+1] 0 = 0 ∧ (∀ i, (ord i, f (ord i)) ∈ R) ∧
      ∀ i j, ord i = ord j → i=j)

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open FiniteSampling TargetedSamplers Classical

abbrev seedWidth (n : ℕ) := Nat.clog 2 (Fintype.card (Draw n))

def coinCount (n L : ℕ) := trials n * seedWidth n + (2*majorityHalf n)*L

def panelEquiv (n L : ℕ) : (Fin (coinCount n L) → Bool) ≃ SeedPanel n L :=
  (splitCoins (trials n*seedWidth n) ((2*majorityHalf n)*L)).trans
    ((trialBlocks (trials n) (seedWidth n)).prodCongr (trialBlocks (2*majorityHalf n) L))

/-- Split a flat fair-bit tape into graph seeds and parity strings, padding missing bits with false. -/
def panelFromTape (n L : ℕ) (coins : List Bool) : SeedPanel n L :=
  panelEquiv n L fun i => coins[i.val]?.getD false

/-- The finite oracle procedure on a graph and a coin string. The parity routine is its parameter. -/
noncomputable def answer (P : Program) (A k : ℕ) {n : ℕ} (adj : Fin n → Fin n → Bool) (coins : List Bool) : Bool :=
  if n≤1 then smallCycleAnswer n adj else
    certify n (remaining P adj (panelFromTape n (coinSpan A k n) coins))

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open FiniteSampling Classical

/-- Product of the deletion, graph-trial, majority and per-query allowances. -/
def searchWork (A k n : ℕ) := (n*n+1)*(trials n+1)*(2*majorityHalf n+1)*
    (seedWidth n+coinSpan A k n+1)

end DirectedHamiltonicity.Main.CycleReduction

end

section

namespace DirectedHamiltonicity.Main.CycleReduction

open FiniteSampling TargetedSamplers Classical

/-- Every candidate query returns one bit within the specified integer allowance on every finite tape. -/
def QueryTime (P : Program) (A k : ℕ) : Prop :=
  ∀ {n : ℕ} (adj : Fin n → Fin n → Bool) (z : Draw n) (x : List Bool), candidateInput adj z = some x →
    ∀ coins : List Bool, ∃ cost, P.RunsIn (runTapes x coins) cost (some [outputBit P x coins]) ∧
      cost ≤ coinSpan A k n

open Classical in
noncomputable def acceptsFraction (f : List Bool → Bool) (L : ℕ) : ℝ :=
  ((Finset.univ.filter fun c : Fin L → Bool => f (List.ofFn c) = true).card:ℝ) / 2^L

/-- A single log-cost machine realizes every tape of the oracle search with polynomial overhead. -/
def ExecutesSearch (Q : Program) (A k : ℕ) : Prop :=
  ∃ (P : Program) (D : ℝ) (j : ℕ), 0 < D ∧
    ∀ (n : ℕ) (adj : Fin n → Fin n → Bool) (c : List Bool),
      ∃ cost, P.RunsIn (runTapes (encodeDigraph n adj) c) cost (some [answer Q A k adj c]) ∧
        (cost:ℝ) ≤ D*(searchWork A k n:ℝ)*((n:ℝ)+1)^j

end DirectedHamiltonicity.Main.CycleReduction

end


