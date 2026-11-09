-- Prove2me | Definitions.Def_ScalablePassiveQRAM_Device_Interfaces
-- name    : ScalablePassiveQRAM_Device_Interfaces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:36:34.189488+00:00
-- url     : https://prove2.me/theorems/5f4926d9-0b09-4144-807c-1372cce32ade
-- title:
--   Thermal preparation, decoding, repeated algorithms, and channel distance
-- statement:
--   The logical ports use ordinary qubits and the physical ports use dual rails. Decoding retains the encoded block and sends its complement to the all-zero logical state, so invalid noisy port states are included. Input and output carrier controls are replacement channels; their old contents are traced out.
--
--   $$\Gamma_{\beta,D}=\frac{e^{-\beta K_D}}{\operatorname{tr}(e^{-\beta K_D})},\qquad \rho_{\beta,D}=\operatorname{tr}_{AB}\Gamma_{\beta,D}.$$
--
--   A query encodes the logical ports, prepares the input carrier, evolves under $K_D$, decodes, and resets the two root carriers. Algorithms have an arbitrary finite workspace and arbitrary quantum channels between their queries. The auxiliary marginal is prepared once and retained throughout execution. The channel distance uses the published trace norm and the same rectangular, unhalved supremum over all finite reference dimensions as Wilde's diamond norm, applied directly to explicit superoperators. No substantive CPTP proof is assumed in this interface.
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), §4,4.2, equations (61)–(64), pp.25–26,28–29. Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Definitions.Def_ScalablePassiveQRAM_Device_Hamiltonian
import Definitions.Def_WildeQIT_diamondNorm
import Definitions.Def_WildeQIT_partialTrace
import Mathlib

noncomputable section
open scoped BigOperators Matrix

namespace ScalablePassiveQRAM.Device

local instance interfacesDecidableEq (α : Type) : DecidableEq α := Classical.decEq α
local instance interfacesDecidable (p : Prop) : Decidable p := Classical.propDecidable p

abbrev Map (a b : Type) := Op a → Op b
abbrev Retained (n : ℕ) := AuxBasis n × Database n
abbrev Physical (n : ℕ) := PortBasis n × Retained n
abbrev Sector (n : ℕ) := PortBasis n × AuxBasis n

/-- Blockwise tensor extension; all reference coherences are retained. -/
def extend {a b r : Type} (Φ : Map a b) : Map (r × a) (r × b) :=
  fun X u v => Φ (fun i j => X (u.1,i) (v.1,j)) u.2 v.2

def conjugate {a b : Type} [Fintype a] (V : Matrix b a ℂ) : Map a b :=
  fun X => V * X * V.conjTranspose

def tensor {a b : Type} (X : Op a) (Y : Op b) : Op (a × b) :=
  fun i j => X i.1 j.1 * Y i.2 j.2

/-- Identical supremum to Wilde's rectangular unhalved norm, applied to explicit maps.
This avoids requiring substantive CPTP proofs in definition files. -/
def diamondDist {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (Φ Ψ : Map a b) : ℝ :=
  sSup {x : ℝ | ∃ (r : ℕ) (ρ : Op (Fin r × a)), WildeQIT.IsDensityOperator ρ ∧
    x = WildeQIT.traceDist (extend Φ ρ) (extend Ψ ρ)}

/-- Canonical tensor-coordinate identification with the physical qubit basis. -/
def assemble (n : ℕ) (p : PortBasis n) (a : AuxBasis n) (D : Database n) : Basis n
  | .inl q => p q
  | .inr (.inl q) => a q
  | .inr (.inr x) => D x

def fullMatrix (n : ℕ) (A : Op (Basis n)) : Op (Physical n) :=
  fun i j => A (assemble n i.1 i.2.1 i.2.2) (assemble n j.1 j.2.1 j.2.2)

def sectorMatrix (n : ℕ) (D : Database n) (A : Op (Basis n)) : Op (Sector n) :=
  fun i j => A (assemble n i.1 i.2 D) (assemble n j.1 j.2 D)

def sectorHamiltonian (n : ℕ) (Ω Δ : ℝ) (D : Database n) : Op (Sector n) :=
  sectorMatrix n D (physicalHamiltonian n Ω Δ)

/-- Gibbs state of ports plus auxiliaries; the denominator is the actual partition function. -/
def gibbs (n : ℕ) (Ω Δ β : ℝ) (D : Database n) : Op (Sector n) := by
  classical
  exact let e := NormedSpace.exp ((-β : ℂ) • sectorHamiltonian n Ω Δ D)
  (e.trace)⁻¹ • e

def thermalAux (n : ℕ) (Ω Δ β : ℝ) (D : Database n) : Op (AuxBasis n) :=
  WildeQIT.partialTraceLeft (gibbs n Ω Δ β D)

def portEncoding (n : ℕ) (l : Logical n) : PortBasis n :=
  fun (k,c) => c == (if h : k.val < n then l.1 ⟨k.val,h⟩ else l.2)

def zeroLogical (n : ℕ) : Logical n := (fun _ => false, false)

def encodingMatrix (n : ℕ) : Matrix (PortBasis n) (Logical n) ℂ := by
  classical
  exact fun p l => if p = portEncoding n l then 1 else 0

/-- Decode every port state, including invalid unary states, as on p.25. -/
def decode {r : Type} (n : ℕ) : Map (PortBasis n × r) (Logical n × r) := by
  classical
  exact fun X i j => X (portEncoding n i.1,i.2) (portEncoding n j.1,j.2) +
    if i.1 = zeroLogical n ∧ j.1 = zeroLogical n then
      ∑ p : PortBasis n, if (∃ l, p = portEncoding n l) then 0 else X (p,i.2) (p,j.2)
    else 0

/-- Replace a set of qubits by a prescribed pure bit configuration, tracing its old state. -/
def replace {q : Type} [Fintype q] [DecidableEq q] (S : Finset q) (c : q → Bool) :
    Map (q → Bool) (q → Bool) := by
  classical
  exact fun X u v =>
    if (∀ s ∈ S, u s = c s ∧ v s = c s) then
      ∑ w : ({s // s ∈ S} → Bool),
        X (fun s => if h : s ∈ S then w ⟨s,h⟩ else u s)
          (fun s => if h : s ∈ S then w ⟨s,h⟩ else v s)
    else 0

def rootCarrier (n j : ℕ) : Finset (Auxiliary n) := by
  classical
  exact Finset.univ.filter fun q => match q with
    | .inl ⟨k,v,_⟩ => k.val = j ∧ v = fun _ => false
    | _ => false

def startCarrier (n : ℕ) : AuxBasis n := by
  classical
  exact fun q => match q with
    | .inl ⟨j,v,s⟩ => decide (j.val = 0 ∧ v = (fun _ => false) ∧ s = 0)
    | _ => false

def prepareCarrier (n : ℕ) : Map (AuxBasis n) (AuxBasis n) :=
  replace (rootCarrier n 0) (startCarrier n)

def resetCarriers (n : ℕ) : Map (AuxBasis n) (AuxBasis n) :=
  replace (rootCarrier n 0 ∪ rootCarrier n (length n)) (fun _ => false)

def inputEncoding (n : ℕ) : Matrix (Sector n) (Logical n × AuxBasis n) ℂ := by
  classical
  exact fun i j => encodingMatrix n i.1 j.1 * if i.2 = j.2 then 1 else 0

/-- One query (62); the device is part of the output and is never re-prepared. -/
def thermalQuery (n : ℕ) (Ω Δ : ℝ) (D : Database n) :
    Map (Logical n × AuxBasis n) (Logical n × AuxBasis n) := by
  classical
  exact fun X => extend (resetCarriers n)
    (decode n (conjugate (evolve (sectorHamiltonian n Ω Δ D) (Real.pi / Ω))
      (conjugate (inputEncoding n) (extend (prepareCarrier n) X))))

def idealQuery (n : ℕ) (D : Database n) : Map (Logical n) (Logical n) :=
  fun X i j => X (i.1, xor i.2 (D i.1)) (j.1, xor j.2 (D j.1))

/-- A finite algorithm's workspace is arbitrary, and every inter-query map is a channel. -/
structure Algorithm (n w m : ℕ) where
  between : Fin (m+1) → WildeQIT.QChannel (Logical n × Fin w) (Logical n × Fin w)

def algorithmLift (n w : ℕ) {r : Type}
    (Φ : Map (Logical n) (Logical n)) : Map ((Logical n × Fin w) × r) ((Logical n × Fin w) × r) :=
  fun X i j => Φ (fun l k => X ((l,i.1.2),i.2) ((k,j.1.2),j.2)) i.1.1 j.1.1

def queryLift (n w : ℕ) {r : Type}
    (Φ : Map (Logical n × r) (Logical n × r)) :
    Map ((Logical n × Fin w) × r) ((Logical n × Fin w) × r) :=
  fun X i j => Φ (fun l k => X ((l.1,i.1.2),l.2) ((k.1,j.1.2),k.2))
    (i.1.1,i.2) (j.1.1,j.2)

def localAlgorithm {n w m : ℕ} {r : Type} (A : Algorithm n w m) (k : Fin (m+1)) :
    Map ((Logical n × Fin w) × r) ((Logical n × Fin w) × r) :=
  fun X i j => (A.between k).apply (fun l h => X (l,i.2) (h,j.2)) i.1 j.1

def runAlgorithm {n w m : ℕ} {r : Type} (A : Algorithm n w m)
    (Q : Map ((Logical n × Fin w) × r) ((Logical n × Fin w) × r))
    (ρ : Op r) : Map (Logical n × Fin w) ((Logical n × Fin w) × r) :=
  fun X => (List.finRange m).foldl (fun σ k =>
    localAlgorithm A ⟨k.val+1,by omega⟩ (Q σ))
    (localAlgorithm A ⟨0,by omega⟩ (tensor X ρ))

def idealAlgorithm {n w m : ℕ} (A : Algorithm n w m) (D : Database n) :
    Map (Logical n × Fin w) (Logical n × Fin w) :=
  fun X => (List.finRange m).foldl (fun σ k => (A.between ⟨k.val+1,by omega⟩).apply
    (fun i j => idealQuery n D (fun l h => σ (l,i.2) (h,j.2)) i.1 j.1))
    ((A.between ⟨0,by omega⟩).apply X)

def thermalAlgorithm {n w m : ℕ} (A : Algorithm n w m) (Ω Δ β : ℝ) (D : Database n) :=
  runAlgorithm A (queryLift n w (thermalQuery n Ω Δ D)) (thermalAux n Ω Δ β D)

def thermalError {n w m : ℕ} (A : Algorithm n w m) (Ω Δ β : ℝ) (D : Database n) : ℝ :=
  diamondDist (thermalAlgorithm A Ω Δ β D)
    (fun X => tensor (idealAlgorithm A D X) (thermalAux n Ω Δ β D))

end ScalablePassiveQRAM.Device


