-- Prove2me | Definitions.Def_ScalablePassiveQRAM_Device_Energy
-- name    : ScalablePassiveQRAM_Device_Energy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:52:54.208388+00:00
-- url     : https://prove2.me/theorems/20d77e29-de38-4a71-b3be-6c9f935ad7d1
-- title:
--   Actual root swaps, energy changes, and clean endpoint embeddings
-- statement:
--   The boundary protocol swaps each physical two-qubit port with an external register of the same encoding, prepares the input carrier, allows one free interval, swaps the outputs, and resets the two root carriers. Expected device energy is computed after tracing out the external registers.
--
--   $$E_{\rm boundary}=\sum_{i\text{ root operation}}|\operatorname{tr}(K_D\rho_{i+1})-\operatorname{tr}(K_D\rho_i)|,\qquad B_{\rm touch}=\sum_i2\|K_{\rm touch}(S_i)\|.$$
--
--   The touching Hamiltonian is selected from the actual interaction and pinning sums. The state trajectory executes the root operations and the free interval. Endpoints embed arbitrary logical and memory superpositions into the physical register space, so subsequent query claims have a single common phase.
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), §§3.3,4.2, equations (34),(36),(71) and its proof, pp.20,30. Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Definitions.Def_ScalablePassiveQRAM_Device_Branches
import Mathlib

noncomputable section
open scoped BigOperators Matrix
set_option synthInstance.maxSize 10000

namespace ScalablePassiveQRAM.Device
local instance energyDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance energyDecidableEq (a : Type) : DecidableEq a := Classical.decEq a

/-- External ports have the same two-qubit encoding as the device ports. -/
abbrev EnergyBasis (n : ℕ) := PortBasis n × Sector n

inductive RootOperation where
  | swap (k : ℕ)
  | prepare
  | reset (layer : ℕ)
  deriving DecidableEq, Repr

inductive QueryEvent where
  | boundary (op : RootOperation)
  | free
  deriving DecidableEq, Repr

def rootOperations (n : ℕ) : List RootOperation :=
  (List.range (n+1)).map RootOperation.swap ++ [.prepare] ++
  (List.range (n+1)).map RootOperation.swap ++ [.reset 0,.reset (length n)]

def events (n : ℕ) : List QueryEvent :=
  ((List.range (n+1)).map fun k => .boundary (.swap k)) ++
  [.boundary .prepare,.free] ++
  ((List.range (n+1)).map fun k => .boundary (.swap k)) ++
  [.boundary (.reset 0),.boundary (.reset (length n))]

def rootSupport (n : ℕ) : RootOperation → Finset (Qubit n)
  | .swap k => {portQ n k false,portQ n k true}
  | .prepare => (rootCarrier n 0).image (fun q => .inr (.inl q))
  | .reset j => (rootCarrier n j).image (fun q => .inr (.inl q))

def swapped (n k : ℕ) (i : EnergyBasis n) : EnergyBasis n :=
  ((fun q => if q.1.val = k then i.2.1 q else i.1 q),
   (fun q => if q.1.val = k then i.1 q else i.2.1 q),i.2.2)

def boundaryMap (n : ℕ) : RootOperation → Map (EnergyBasis n) (EnergyBasis n)
  | .swap k => fun X i j => X (swapped n k i) (swapped n k j)
  | .prepare => fun X i j => prepareCarrier n
      (fun a b => X (i.1,(i.2.1,a)) (j.1,(j.2.1,b))) i.2.2 j.2.2
  | .reset l => fun X i j => replace (rootCarrier n l) (fun _ => false)
      (fun a b => X (i.1,(i.2.1,a)) (j.1,(j.2.1,b))) i.2.2 j.2.2

def eventMap (n : ℕ) (Ω Δ : ℝ) (D : Database n) : QueryEvent →
    Map (EnergyBasis n) (EnergyBasis n)
  | .boundary op => boundaryMap n op
  | .free => extend (conjugate (evolve (sectorHamiltonian n Ω Δ D) (Real.pi / Ω)))

def expectedEnergy (n : ℕ) (Ω Δ : ℝ) (D : Database n) (X : Op (EnergyBasis n)) : ℝ :=
  ((sectorHamiltonian n Ω Δ D * WildeQIT.partialTraceLeft X).trace).re

def energyState (n j : ℕ) (Ω Δ : ℝ) (D : Database n) (X : Op (EnergyBasis n)) :
    Op (EnergyBasis n) :=
  ((events n).take j).foldl (fun σ e => eventMap n Ω Δ D e σ) X

/-- Absolute energy changes at actual root interventions; the free interval is excluded. -/
def boundaryCost (n : ℕ) (Ω Δ : ℝ) (D : Database n) (X : Op (EnergyBasis n)) : ℝ :=
  ((List.finRange (events n).length).map fun j => match (events n)[j] with
    | .free => 0
    | .boundary _ => |expectedEnergy n Ω Δ D (energyState n (j.val+1) Ω Δ D X) -
        expectedEnergy n Ω Δ D (energyState n j Ω Δ D X)|).sum

/-- The part of K touching S, with the interaction decomposition (20). -/
def touchHamiltonian (n : ℕ) (Ω Δ : ℝ) (D : Database n) (S : Finset (Qubit n)) : Op (Sector n) :=
  sectorMatrix n D (
    ((List.range (length n)).map fun j =>
      (((transitions n j).filter fun t => decide (¬ Disjoint t.support S)).map
        (interaction n Ω j)).sum).sum +
    ∑ q ∈ S, (Δ * pinningWeight q : ℂ) • number q)

/-- The exact root energy proof estimate, summed over the physical interventions. -/
def touchBudget (n : ℕ) (Ω Δ : ℝ) (D : Database n) : ℝ :=
  ((rootOperations n).map fun op => 2 * spectralNorm (touchHamiltonian n Ω Δ D (rootSupport n op))).sum

/-- Encoding of all logical/memory superpositions with a clean root endpoint. -/
def endpointEmbedding (n j : ℕ) : Matrix (Basis n) (Logical n × Database n) ℂ :=
  fun i l => ket (endpoint n j l.1.1 l.1.2 l.2) i

end ScalablePassiveQRAM.Device


