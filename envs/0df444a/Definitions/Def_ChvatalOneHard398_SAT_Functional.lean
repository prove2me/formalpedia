-- Prove2me | Definitions.Def_ChvatalOneHard398_SAT_Functional
-- name    : ChvatalOneHard398_SAT_Functional
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:09.2578+00:00
-- url     : https://prove2.me/theorems/0b5191dd-0b6b-4eb6-8124-196ad4f79030
-- title:
--   Functional formulations and the binary residue-arithmetic template
-- statement:
--   A functional formulation has free variables, disjoint multiple-choice sets, a sequence of gates, and output fixings. Each gate records at most three earlier input identifiers and a finite Boolean truth table. Its output variables are followed by one auxiliary weight variable per input assignment. The exact-one system expresses normalization of the weights and each coordinate identity from the extended formulation
--
--   $$(x_{I_g},x_{O_g})=\sum_v x_{g,v}(v,f_g(v)),\qquad\sum_v x_{g,v}=1.$$
--
--   Validity checks ordering, truth-table dimensions, disjointness, and output-only fixings. It contains no integrality or rank guarantee. The polyhedron also has all coordinates in $[0,1]$, bounds implied by the source equations.
--
--   The residue template is computed from nonnegative weights and a modulus. It introduces constant gates, schoolbook adders and subtractors, comparisons through their final borrow bits, complement gates, and the final carry fixings of Lemma 20. Its outputs are residue digits and the integer coefficient list for the quotient. Substitution into an existing formulation renames the abstract inputs and appends the new gates. The template does not select objects by their semantic properties.
--
--   **Formalization Note** Weights are natural numbers, exactly the nonnegative integers of the source. $L=1+\lfloor\log_2(2K-1)\rfloor$ is the minimum allowed digit length when $K\ge1$. The template is total at raw $K=0$, which is outside the lemma's hypotheses.
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.20, §5.2, equation (1); Lemma 20 construction, pp.21–22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Formula

namespace ChvatalOneHard398.SAT
open scoped BigOperators

/-- A finite truth table. Its shape and input ordering are checked by Functional.Valid. -/
structure Gate where
  inputs : List ℕ
  outputs : ℕ
  table : List (List Bool)
  deriving Inhabited

def Gate.size (g : Gate) : ℕ := g.outputs + 2 ^ g.inputs.length

def bits (k v : ℕ) : List Bool := (List.range k).map (Nat.testBit v)

def truthTable (k : ℕ) (f : List Bool → List Bool) : List (List Bool) :=
  (List.range (2 ^ k)).map (fun v => f (bits k v))

structure Functional where
  free : ℕ
  choices : List (Finset ℕ)
  gates : List Gate
  fixings : List (ℕ × Bool)
  deriving Inhabited

def Functional.dim (X : Functional) : ℕ := X.free + (X.gates.map Gate.size).sum

def Functional.base (X : Functional) (g : ℕ) : ℕ :=
  X.free + ((X.gates.take g).map Gate.size).sum

def Functional.outputIDs (X : Functional) : List ℕ :=
  (List.range X.gates.length).flatMap fun j =>
    (List.range X.gates[j]!.outputs).map (X.base j + ·)

def Functional.Valid (X : Functional) : Prop :=
  (∀ I ∈ X.choices, ∀ u ∈ I, u < X.free) ∧
  X.choices.Pairwise Disjoint ∧
  (∀ j < X.gates.length, let g := X.gates[j]!
    g.inputs.length ≤ 3 ∧ (∀ u ∈ g.inputs, u < X.base j) ∧
    g.table.length = 2 ^ g.inputs.length ∧ (∀ row ∈ g.table, row.length = g.outputs)) ∧
  (∀ ub ∈ X.fixings, ub.1 ∈ X.outputIDs)

noncomputable def coord {n : ℕ} (x : Fin n → ℝ) (u : ℕ) : ℝ :=
  if h : u < n then x ⟨u,h⟩ else 0

/-- The exact-one equations of (1), p.20; variables for convex weights follow gate outputs. -/
def functionalExact (X : Functional) : Formula := Id.run do
  let mut rows := X.choices.map (fun I => I.image (fun u => (⟨u,true⟩ : Literal)))
  for j in List.range X.gates.length do
    let g := X.gates[j]!
    let b := X.base j
    let aux := b + g.outputs
    rows := rows ++ [((List.range (2 ^ g.inputs.length)).map (fun v => (⟨aux+v,true⟩ : Literal))).toFinset]
    for l in List.range g.inputs.length do
      rows := rows ++ [((⟨g.inputs[l]!,false⟩ : Literal) ::
        (((List.range (2 ^ g.inputs.length)).filter fun v => Nat.testBit v l).map
          fun v => (⟨aux+v,true⟩ : Literal))).toFinset]
    for o in List.range g.outputs do
      rows := rows ++ [((⟨b+o,false⟩ : Literal) ::
        (((List.range (2 ^ g.inputs.length)).filter fun v => (g.table[v]!).getD o false).map
          fun v => (⟨aux+v,true⟩ : Literal))).toFinset]
  rows := rows ++ X.fixings.map (fun ub => ({⟨ub.1,ub.2⟩} : Clause))
  return ⟨X.dim,rows⟩

noncomputable def functionalPoly (X : Functional) : Set (Fin X.dim → ℝ) :=
  exactOne (functionalExact X)

abbrev IntLinear := List (ℕ × ℤ)
noncomputable def evalLinear {n : ℕ} (c : IntLinear) (x : Fin n → ℝ) : ℝ :=
  (c.map fun uz => (uz.2 : ℝ) * coord x uz.1).sum

def pushGate (X : Functional) (ins : List ℕ) (outs : ℕ)
    (f : List Bool → List Bool) : Functional × List ℕ :=
  ({X with gates := X.gates ++ [⟨ins,outs,truthTable ins.length f⟩]},
    (List.range outs).map (X.dim + ·))

def fixOutput (X : Functional) (u : ℕ) (b : Bool) : Functional :=
  {X with fixings := X.fixings ++ [(u,b)]}

/-- Full adder/subtractor with a constant coefficient digit, including borrow/carry output. -/
def digitFunction (subtract : Bool) (theta : Bool) (v : List Bool) : List Bool :=
  let a : ℤ := if v.getD 0 false then 1 else 0
  let b : ℤ := if theta && v.getD 1 false then 1 else 0
  let c : ℤ := if v.getD 2 false then 1 else 0
  let z := if subtract then a-b-c else a+b+c
  [decide (z % 2 = 1), if subtract then decide (z < 0) else decide (2 ≤ z)]

/-- L schoolbook operations; the comparison subtraction leaves its final borrow unfixed. -/
def arithmetic (X : Functional) (L : ℕ) (r : List ℕ) (u theta zeroID : ℕ)
    (subtract fixLast : Bool) : Functional × List ℕ × ℕ := Id.run do
  let mut Y := X
  let mut carry := zeroID
  let mut result := []
  for l in List.range L do
    let z := pushGate Y [r.getD l zeroID,u,carry] 2 (digitFunction subtract (Nat.testBit theta l))
    Y := z.1
    result := result ++ [z.2[0]!]
    carry := z.2[1]!
  if fixLast then Y := fixOutput Y carry false
  return (Y,result,carry)

structure ResidueResult where
  model : Functional
  digits : List ℕ
  quotient : IntLinear
  deriving Inhabited

/-- The smallest L with 2^L ≥ 2K for K≥1; raw K=0 also has a total value. -/
def residueBits (K : ℕ) : ℕ := Nat.log 2 (2*K-1) + 1

/-- The actual template in the proof of Lemma 20, with abstract input variables 0,...,k-1. -/
def residueTemplate (weights : List ℕ) (K : ℕ) : ResidueResult := Id.run do
  let k := weights.length
  let L := residueBits K
  let z0 := pushGate ⟨k,[],[],[]⟩ [] 1 (fun _ => [false])
  let z1 := pushGate z0.1 [] 1 (fun _ => [true])
  let zeroID := z0.2[0]!
  let one := z1.2[0]!
  let mut X := z1.1
  let mut rho := List.replicate L zeroID
  let mut quotient : IntLinear := []
  for i in List.range k do
    let a := weights[i]!
    let add := arithmetic X L rho i (a % K) zeroID false true
    let cmp := arithmetic add.1 L add.2.1 one K zeroID true false
    let q := pushGate cmp.1 [cmp.2.2] 1 (fun v => [!(v.getD 0 false)])
    let sub := arithmetic q.1 L add.2.1 q.2[0]! K zeroID true true
    X := sub.1
    rho := sub.2.1
    quotient := quotient ++ [(i,((a/K : ℕ) : ℤ)),(q.2[0]!,1)]
  return ⟨X,rho,quotient⟩

/-- Substitute variables into the template, appending precisely its new gates and fixings. -/
def extendResidue (X : Functional) (u weights : List ℕ) (K : ℕ) : ResidueResult :=
  let z := residueTemplate weights K
  let rename := fun j => if j < weights.length then u.getD j 0 else X.dim + (j-weights.length)
  let gates := z.model.gates.map fun g => {g with inputs := g.inputs.map rename}
  ⟨{X with gates := X.gates ++ gates,
           fixings := X.fixings ++ z.model.fixings.map (fun ub => (rename ub.1,ub.2))},
    z.digits.map rename,z.quotient.map (fun uz => (rename uz.1,uz.2))⟩


noncomputable def gateVertex (g : Gate) (v : ℕ) : Fin (g.inputs.length + g.outputs) → ℝ :=
  Fin.append (fun i => if Nat.testBit v i.val then 1 else 0)
    (fun o => if (g.table[v]!).getD o.val false then 1 else 0)

noncomputable def gateCoordinates (X : Functional) (j : ℕ)
    (x : Fin X.dim → ℝ) : Fin (X.gates[j]!.inputs.length + X.gates[j]!.outputs) → ℝ :=
  Fin.append (fun i => coord x (X.gates[j]!.inputs[i.val]!))
    (fun o => coord x (X.base j + o.val))

def Extends {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ) : Prop :=
  ∀ i : Fin m, ∃ h : i.val < n, x ⟨i.val,h⟩ = y i

end ChvatalOneHard398.SAT


