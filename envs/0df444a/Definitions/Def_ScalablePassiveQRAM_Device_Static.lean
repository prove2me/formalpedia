-- Prove2me | Definitions.Def_ScalablePassiveQRAM_Device_Static
-- name    : ScalablePassiveQRAM_Device_Static
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:44:41.391218+00:00
-- url     : https://prove2.me/theorems/4358730d-1e5f-465b-90ee-48ac701fed26
-- title:
--   The recorded interface and arbitrary supported static perturbations
-- statement:
--   A coherent root record keeps the algorithm's address while a copy is encoded in the physical ports. Output decoding clears and discards the temporary address as in equation (48). Initially the auxiliaries are vacant and the memory is $|D\rangle$; this is a different preparation from the thermal model.
--
--   $$\widetilde K=K+\sum_\alpha E_\alpha,\qquad W=\max_x\sum_{\alpha:S_\alpha\cap F_x^+\ne\varnothing}\delta_\alpha,\qquad \lambda_{\rm err}=\max_q\sum_{\alpha:q\in S_\alpha}\delta_\alpha.$$
--
--   The finite perturbation family is Hermitian, supported on arbitrary subsets, and bounded in spectral operator norm. Support means tensoring with identity outside the declared set. Terms may act on memory, ports, record, carriers, or switches. The full memory remains physical qubits during evolution and is traced out at the end. The comparison channel queries the original database.
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), §§4,4.3, equations (47)–(49),(72)–(75), pp.26,30–31. Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Definitions.Def_ScalablePassiveQRAM_Device_Interfaces
import Mathlib

noncomputable section
open scoped BigOperators Matrix

namespace ScalablePassiveQRAM.Device

local instance staticDecidableEq (α : Type) : DecidableEq α := Classical.decEq α
local instance staticDecidable (p : Prop) : Decidable p := Classical.propDecidable p

abbrev Recorded (n : ℕ) := Address n × Physical n
abbrev ExtendedQubit (n : ℕ) := Fin n ⊕ Qubit n

/-- Spectral operator norm, using Euclidean vectors, independent of the default matrix norm. -/
def spectralNorm {a : Type} [Fintype a] [DecidableEq a] (A : Op a) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖

def recordedBits (n : ℕ) (i : Recorded n) : ExtendedQubit n → Bool
  | .inl k => i.1 k
  | .inr q => assemble n i.2.1 i.2.2.1 i.2.2.2 q

/-- An operator supported on S is an arbitrary operator on S tensored with identity outside S.
No locality assumption is made. -/
def supportedOn (n : ℕ) (S : Finset (ExtendedQubit n)) (E : Op (Recorded n)) : Prop :=
  ∃ A : Op ({q // q ∈ S} → Bool), ∀ i j,
    E i j = if (∀ q, q ∉ S → recordedBits n i q = recordedBits n j q) then
      A (fun q => recordedBits n i q) (fun q => recordedBits n j q) else 0

structure StaticErrors (n : ℕ) where
  count : ℕ
  term : Fin count → Op (Recorded n)
  support : Fin count → Finset (ExtendedQubit n)
  bound : Fin count → ℝ
  hermitian : ∀ α, (term α).conjTranspose = term α
  supported : ∀ α, supportedOn n (support α) (term α)
  norm_le : ∀ α, spectralNorm (term α) ≤ bound α

def extendedFootprint (n : ℕ) (x : Address n) : Finset (ExtendedQubit n) :=
  Finset.univ.filter fun q => match q with
  | .inl _ => true
  | .inr (.inl _) => true
  | .inr (.inr (.inr a)) => a = x
  | .inr q => q ∈ footprint n x

def branchWeight {n : ℕ} (E : StaticErrors n) : ℝ :=
  ((Finset.univ : Finset (Address n)).toList.map fun x =>
    ∑ α, if ¬ Disjoint (E.support α) (extendedFootprint n x) then E.bound α else 0).foldl max 0

def errorIncidence {n : ℕ} (E : StaticErrors n) : ℝ :=
  ((Finset.univ : Finset (ExtendedQubit n)).toList.map fun q =>
    ∑ α, if q ∈ E.support α then E.bound α else 0).foldl max 0

def recordedHamiltonian (n : ℕ) (Ω Δ : ℝ) : Op (Recorded n) :=
  fun i j => if i.1 = j.1 then fullMatrix n (physicalHamiltonian n Ω Δ) i.2 j.2 else 0

def realizedHamiltonian {n : ℕ} (E : StaticErrors n) (Ω Δ : ℝ) : Op (Recorded n) :=
  recordedHamiltonian n Ω Δ + ∑ α, E.term α

def prepareRetained (n : ℕ) : Map (Retained n) (Retained n) :=
  fun X i j => prepareCarrier n (fun a b => X (a,i.2) (b,j.2)) i.1 j.1

def resetRetained (n : ℕ) : Map (Retained n) (Retained n) :=
  fun X i j => resetCarriers n (fun a b => X (a,i.2) (b,j.2)) i.1 j.1

/-- W_rec, equation (47). The algorithm's address remains at the root. -/
def recordEncoding (n : ℕ) : Matrix (Recorded n) (Logical n × Retained n) ℂ :=
  fun i j => if i.1 = j.1.1 ∧ i.2.1 = portEncoding n j.1 ∧ i.2.2 = j.2 then 1 else 0

def xorAddress (n : ℕ) (a b : Address n) : Address n := fun i => xor (a i) (b i)

/-- Equation (48), including the temporary address clear and trace. -/
def recordedDecode (n : ℕ) : Map (Recorded n) (Logical n × Retained n) :=
  fun X i j => ∑ t : Address n,
    decode n (fun a b => X (i.1.1,a) (j.1.1,b))
      ((xorAddress n t i.1.1,i.1.2),i.2) ((xorAddress n t j.1.1,j.1.2),j.2)

def staticQuery {n : ℕ} (E : StaticErrors n) (Ω Δ : ℝ) :
    Map (Logical n × Retained n) (Logical n × Retained n) :=
  fun X => extend (resetRetained n) (recordedDecode n
    (conjugate (evolve (realizedHamiltonian E Ω Δ) (Real.pi / Ω))
      (conjugate (recordEncoding n) (extend (prepareRetained n) X))))

def cleanRetained (n : ℕ) (D : Database n) : Op (Retained n) :=
  outer (ket ((fun _ => false),D)) (ket ((fun _ => false),D))

def staticAlgorithm {n w m : ℕ} (A : Algorithm n w m) (E : StaticErrors n)
    (Ω Δ : ℝ) (D : Database n) : Map (Logical n × Fin w) (Logical n × Fin w) :=
  fun X => WildeQIT.partialTraceRight (runAlgorithm A (queryLift n w (staticQuery E Ω Δ)) (cleanRetained n D) X)

def staticError {n w m : ℕ} (A : Algorithm n w m) (E : StaticErrors n)
    (Ω Δ : ℝ) (D : Database n) : ℝ :=
  diamondDist (staticAlgorithm A E Ω Δ D) (idealAlgorithm A D)

end ScalablePassiveQRAM.Device


