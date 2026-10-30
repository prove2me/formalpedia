-- Prove2me | Definitions.Def_CheungIBOL_General_Inventory
-- name    : CheungIBOL_General_Inventory
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T22:11:46.138183+00:00
-- url     : https://prove2.me/theorems/9e693b66-dbf7-47ea-8bad-4e0a46dbf186
-- title:
--   Observed histories, saturated consumption and physical revenue
-- statement:
--   A history is an ordered finite list of observed triples $(x_s,a_s,y_s)$. Its measurable structure is the disjoint union, over lengths, of finite product measurable spaces. This does not impose the discrete sigma-algebra on $A$. Starting from $N_i^0=0$, an observed outcome increments resource $i$ exactly when $y_i=1$ and $N_i<b_i$; otherwise that coordinate stays unchanged. All vector coordinates are updated simultaneously.
--
--   The discounted reward after history $h$ is $r_i(1-\Psi_\epsilon(N_i(h)/b_i))$. Physical revenue sums $r_i y_{t,i}\mathbf1\{N_i^{t-1}<b_i\}$ over the observed rounds and resources. The prefix of length $t$ supplies the inventory before zero-based round $t$. Depleted resources still generate observed feedback, but earn no revenue. The inventory counts consumed units, never remaining units.
-- source:
--   Cheung, Ma, Simchi-Levi and Wang, Inventory Balancing with Online Learning, arXiv:1810.05640v2 (30 August 2021), PDF/printed pp. 9–10 and 13–15, physical dynamics and Algorithm 1, equation (5), https://arxiv.org/abs/1810.05640v2

import Definitions.Def_CheungIBOL_General_Model
import Definitions.Def_CheungIBOL_General_Potential

open scoped BigOperators
noncomputable section

namespace CheungIBOL.General

abbrev History (n c : ℕ) (A : Type*) := List (Fin c × A × (Fin n → Bool))

/-- The usual disjoint-union measurable structure on finite histories: on length k,
it is the finite product measurable structure. No discrete sigma-algebra on A is imposed. -/
instance historyMeasurableSpace {n c : ℕ} {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (History n c A) :=
  MeasurableSpace.map
    (fun s : Σ k : ℕ, Fin k → (Fin c × A × (Fin n → Bool)) => List.ofFn s.2)
    inferInstance

/-- Counts consumed units; saturated coordinates do not change. -/
def inventoryStep {n : ℕ} (b : Fin n → ℕ+) (N : Fin n → ℕ)
    (y : Fin n → Bool) : Fin n → ℕ :=
  fun i => if y i && decide (N i < (b i : ℕ)) then N i + 1 else N i

/-- Iterate the physical updates from zero on exactly the observed outcomes. -/
def inventory {n c : ℕ} {A : Type*} (b : Fin n → ℕ+) (h : History n c A) :
    Fin n → ℕ :=
  h.foldl (fun N obs => inventoryStep b N obs.2.2) (fun _ => 0)

/-- Equation (5): rewards sent to the oracle before its next decision. -/
def discounted {n c : ℕ} {A : Type*} [MeasurableSpace A]
    (M : Model n c A) (ε : ℝ) (h : History n c A) (i : Fin n) : ℝ :=
  M.reward i * (1 - potential ε ((inventory M.capacity h i : ℝ) / (M.capacity i : ℕ)))

/-- Physical revenue: each observed one earns its resource reward only before depletion. -/
def revenue {n c : ℕ} {A : Type*} [MeasurableSpace A]
    (M : Model n c A) (h : History n c A) : ℝ :=
  (h.mapIdx fun t obs => ∑ i : Fin n,
    if obs.2.2 i && decide (inventory M.capacity (h.take t) i < (M.capacity i : ℕ))
    then M.reward i else 0).sum

end CheungIBOL.General


