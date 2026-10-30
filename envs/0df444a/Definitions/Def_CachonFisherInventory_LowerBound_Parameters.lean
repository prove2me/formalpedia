-- Prove2me | Definitions.Def_CachonFisherInventory_LowerBound_Parameters
-- name    : CachonFisherInventory_LowerBound_Parameters
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T02:47:25.684245+00:00
-- url     : https://prove2.me/theorems/14ea5942-c29b-4079-aa42-14e874ee49b2
-- title:
--   Bounded integer demand and batch-inventory parameters
-- statement:
--   There are N≥1 identical retailers. Retailer batches contain Q_r≥1 units; supplier order lots contain Q_s≥1 such batches. L_r,L_s are arbitrary nonnegative integer lead times, including zero. One-period consumer demand has an arbitrary probability mass function on {0,…,d̄}, where d̄ is finite and Pr(D=1)>0. Its mean is μ_r. A period's retailer demand vector has the product of N copies of this law; the causal-law condition supplies independence across time. Deterministic unit demand is included. Mathlib's PMF is used directly, rather than defining a new probability distribution object.
--
--   Costs satisfy h_s>0, h_r≥0, p_r≥0. Nonnegativity of p_r is the convention for a backorder cost; no strict positivity is imposed. Positivity of d̄ follows from Pr(D=1)>0. Pipeline position k is scheduled to arrive k periods from now. At zero lead time the current order arrives immediately; otherwise the head arrives now, the remaining entries shift down, and the current order enters the last slot.
-- source:
--   Cachon and Fisher (2000), Supply Chain Inventory Management and the Value of Shared Information, Management Science 46(8), DOI 10.1287/mnsc.46.8.1032.12029, §3, pp. 1034–1035 (PDF pp. 3–4)

import Mathlib

open MeasureTheory

namespace CachonFisherInventory.LowerBound

/-- The standing data of §3; only source assumptions and nonnegative penalty costs. -/
structure Parameters where
  N : ℕ
  N_pos : 0 < N
  Qr : ℕ
  Qr_pos : 0 < Qr
  Qs : ℕ
  Qs_pos : 0 < Qs
  Lr : ℕ
  Ls : ℕ
  dbar : ℕ
  dbar_pos : 0 < dbar
  law : PMF (Fin (dbar + 1))
  unit_pos : 0 < law ⟨1, by omega⟩
  hs : ℝ
  hr : ℝ
  pr : ℝ
  hs_pos : 0 < hs
  hr_nonneg : 0 ≤ hr
  pr_nonneg : 0 ≤ pr

abbrev Demand (P : Parameters) := Fin P.N → Fin (P.dbar + 1)

noncomputable def demandLaw (P : Parameters) : Measure (Demand P) :=
  Measure.pi (fun _ : Fin P.N => P.law.toMeasure)

noncomputable def meanDemand (P : Parameters) : ℝ :=
  ∑ d : Fin (P.dbar + 1), (P.law d).toReal * d.val

/-- Pipeline entry k arrives k periods from now, at the receipt event. -/
def pipeAt {L : ℕ} (p : Fin L → ℕ) (k : ℕ) : ℕ :=
  if h : k < L then p ⟨k, h⟩ else 0

def pipeArrival {L : ℕ} (p : Fin L → ℕ) (q : ℕ) : ℕ :=
  if L = 0 then q else pipeAt p 0

def pipeShift {L : ℕ} (p : Fin L → ℕ) (q : ℕ) : Fin L → ℕ :=
  fun k => if k.val + 1 = L then q else pipeAt p (k.val + 1)

end CachonFisherInventory.LowerBound


