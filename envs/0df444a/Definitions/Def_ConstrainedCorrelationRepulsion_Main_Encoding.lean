-- Prove2me | Definitions.Def_ConstrainedCorrelationRepulsion_Main_Encoding
-- name    : ConstrainedCorrelationRepulsion_Main_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:30:24.432194+00:00
-- url     : https://prove2.me/theorems/42c5c959-a3ce-4459-8c72-f9ea027f5889
-- title:
--   Finite input and output formats for the computational milestones
-- statement:
--   Units are numbered in the order of their finite vertex masks. A local index is a bit mask of these unit numbers, and table addresses pair it with the size layer. Graph, unit, metric and local-table oracles expose only the explicitly supplied input data. LP output is read from the program's rational memory. Candidate output is a finite vertex-set indicator.
--
--   The query-order predicate checks every reachable machine state and every actual local-table query. Deterministic code contains no Bernoulli instruction. Initial states for projection contain the supplied partition labels, not an optimum. These finite formats connect the mathematical construction laws to actual charged programs and allow uniform statements about all vertex counts.
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Figures 4–5, §§4–6, printed pp.8–11, 17–35 (PDF pp.9–12, 18–36)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Preclustering
import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Sampler

namespace ConstrainedCorrelationRepulsion.Main

open Classical
open scoped BigOperators

def Deterministic (code : Program) : Prop :=
  ∀ d p, Instruction.bernoulli d p ∉ code

noncomputable def vertexMask {n : ℕ} (B : Finset (Fin n)) : ℕ := ∑ v ∈ B, 2^v.val

noncomputable def unitNumber {n : ℕ} (U : Units n) (B : Finset (Fin n)) : ℕ :=
  (U.blocks.filter (fun D => vertexMask D < vertexMask B)).card

noncomputable def unitMask {n : ℕ} (U : Units n) (T : Finset (Finset (Fin n))) : ℕ :=
  ∑ B ∈ T, 2^(unitNumber U B)

noncomputable def decodeIndex {n : ℕ} (U : Units n) (mask : ℕ) : Finset (Finset (Fin n)) :=
  U.blocks.filter (fun B => mask.testBit (unitNumber U B) = true)

noncomputable def lpInputOracle {n : ℕ} (I : Instance n) (U : Units n) : ℕ → ℕ → ℕ → ℝ :=
  fun bank u v => if bank = 4 then
    if h : u < n ∧ v < n then
      (if unitOf U ⟨u,h.1⟩ = unitOf U ⟨v,h.2⟩ then 1 else 0) else 0
    else inputOracle I bank u v

noncomputable def samplerOracle {n : ℕ} (I : Instance n) (U : Units n) (y : LocalTable n) :
    ℕ → ℕ → ℕ → ℝ := fun bank s mask =>
  if bank = 3 then y s (decodeIndex U mask) else lpInputOracle I U bank s mask

def levelInitial (n r : ℕ) : MachineState :=
  {initialState n with natReg := Function.update (initialState n).natReg 1 r}

noncomputable def readTable {n : ℕ} (U : Units n) (r : ℕ) (s : MachineState) : LocalTable n :=
  fun layer T => if layer ∈ Finset.Icc 1 n ∧ T ⊆ U.blocks ∧ T.card ≤ r then
    s.realMem (layer * 2^n + unitMask U T) else 0

noncomputable def outputSet {n : ℕ} (s : MachineState) : Finset (Fin n) :=
  Finset.univ.filter (fun v => s.natMem v.val = 1)

noncomputable def metricOracle {n : ℕ} (I : Instance n) (x : Fin n → Fin n → ℝ) :
    ℕ → ℕ → ℕ → ℝ := fun bank u v =>
  if bank = 3 then if h : u < n ∧ v < n then x ⟨u,h.1⟩ ⟨v,h.2⟩ else 0
  else inputOracle I bank u v

noncomputable def repairOracle {n : ℕ} (I : Instance n) (x : Fin n → Fin n → ℝ)
    (D : Finset (Fin n)) : ℕ → ℕ → ℕ → ℝ := fun bank u v =>
  if bank = 5 then (if ∃ a : Fin n, a.val = u ∧ a ∈ D then 1 else 0)
  else metricOracle I x bank u v

noncomputable def projectionInitial {n : ℕ} (Q : Partition n) : MachineState :=
  {initialState n with natMem := fun i => if h : i < n then (Q ⟨i,h⟩).val else 0}

def lpBound (C n r : ℕ) : ℕ := polynomialBound C (C*(r+1)) n

/-- Actual input-query order, checked on every reachable intermediate machine state. -/
def QueriesBounded {n : ℕ} (code : Program) (I : Instance n) (U : Units n)
    (y : LocalTable n) (r B : ℕ) : Prop :=
  ∀ t ≤ B, ∀ s ∈ (machineRun false code (samplerOracle I U y) (levelInitial n r) t).support,
    ∀ dst a b, code[s.pc]? = some (.query dst 3 a b) →
      (decodeIndex U (s.natReg b)).card ≤ r

end ConstrainedCorrelationRepulsion.Main


