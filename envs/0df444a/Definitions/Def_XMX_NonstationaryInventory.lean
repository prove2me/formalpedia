-- Prove2me | Definitions.Def_XMX_NonstationaryInventory
-- name    : XMX_NonstationaryInventory
-- status  : Definition
-- author  : @visuddhi
-- created : 2026-10-08T17:02:18.224016+00:00
-- url     : https://prove2.me/theorems/edce8208-a16b-40dc-87cb-afaead88a36b
-- title:
--   Xie–Ma–Xin bounded inventory, shattering and risk definitions
-- statement:
--   Bounded trajectories and base-stock levels; finite maximum inventory formula with lead time; normalized inventory; average K=0 backlog loss; fat shattering; true and empirical risks; one-sided GE and expected EE over IID trajectories.
-- source:
--   Yaqi Xie, Will Ma, Linwei Xin, VC Theory for Inventory Policies, arXiv:2404.11509v3 (2026-02-01), Sections 3.1, 3.3 and 4.4

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory

namespace XMX

/-- A trajectory has T+L coordinates; coordinate 0 is period 1. -/
abbrev Demand (T L : ℕ) (U : ℝ) := Fin (T + L) → Set.Icc (0 : ℝ) U
abbrev Levels (T L : ℕ) (U : ℝ) := Fin (T + L) → Set.Icc (0 : ℝ) (((L : ℝ) + 1) * U)

/-- Formula for post-replenishment inventory in period L+k+1.
The maximum is nonempty because its index type is Fin (k+1).
For valid k<T the formula uses only the trajectory and level coordinates. -/
noncomputable def inventory (T L : ℕ) (U : ℝ)
    (S : Levels T L U) (d : Demand T L U) (k : ℕ) : ℝ :=
  let sv : ℕ → ℝ := fun j => if hj : j < T + L then (S ⟨j, hj⟩ : ℝ) else 0
  let dv : ℕ → ℝ := fun j => if hj : j < T + L then (d ⟨j, hj⟩ : ℝ) else 0
  (Finset.univ : Finset (Fin (k + 1))).sup'
    Finset.univ_nonempty
    (fun j => sv j - ∑ r ∈ Finset.Ico (j : ℕ) (k + L), dv r)

noncomputable def normalizedInventory (T L : ℕ) (U : ℝ)
    (k : ℕ) (S : Levels T L U) (d : Demand T L U) : ℝ :=
  inventory T L U S d k / (((L : ℝ) + 1) * U)

/-- Holding/backlog cost, with no fixed ordering cost. -/
def cost (h b x : ℝ) : ℝ := h * max x 0 + b * max (-x) 0

/-- Time average over periods L+1,...,T+L; not total cost. -/
noncomputable def loss (T L : ℕ) (U h b : ℝ)
    (S : Levels T L U) (d : Demand T L U) : ℝ :=
  (∑ k : Fin T,
    cost h b (inventory T L U S d k -
      (d ⟨L + k, by omega⟩ : ℝ))) / (T : ℝ)

/-- Witnessed fat shattering, using the paper's strict/non-strict convention. -/
def Shatters {P X : Type*} (f : P → X → ℝ) (γ : ℝ) (m : ℕ)
    (x : Fin m → X) (τ : Fin m → ℝ) : Prop :=
  ∀ A : Fin m → Bool, ∃ p : P, ∀ i,
    if A i then τ i + γ < f p (x i) else f p (x i) ≤ τ i - γ

noncomputable def risk {P X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : P → X → ℝ) (p : P) : ℝ := ∫ x, f p x ∂μ

noncomputable def empiricalRisk {P X : Type*}
    (N : ℕ) (f : P → X → ℝ) (data : Fin N → X) (p : P) : ℝ :=
  (∑ i, f p (data i)) / (N : ℝ)

/-- One-sided GE; this supremum is not the absolute uniform deviation. -/
noncomputable def generalizationError {P X : Type*} [MeasurableSpace X]
    (N : ℕ) (μ : Measure X) (f : P → X → ℝ) (data : Fin N → X) : ℝ :=
  ⨆ p, risk μ f p - empiricalRisk N f data p

noncomputable def expectedGE {P X : Type*} [MeasurableSpace X]
    (N : ℕ) (μ : Measure X) [IsProbabilityMeasure μ] (f : P → X → ℝ) : ℝ :=
  ∫ data, generalizationError N μ f data ∂Measure.pi (fun _ : Fin N => μ)

/-- Excess risk of an actual selected policy relative to a fixed comparison policy. -/
noncomputable def expectedEE {P X : Type*} [MeasurableSpace X]
    (N : ℕ) (μ : Measure X) [IsProbabilityMeasure μ] (f : P → X → ℝ)
    (select : (Fin N → X) → P) (pstar : P) : ℝ :=
  ∫ data, risk μ f (select data) - risk μ f pstar
    ∂Measure.pi (fun _ : Fin N => μ)

end XMX


