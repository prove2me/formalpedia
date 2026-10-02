-- Prove2me | Definitions.Def_ProcessingNetworks_BackPressure_LeontiefNetwork
-- name    : ProcessingNetworks_BackPressure_LeontiefNetwork
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T18:18:51.704127+00:00
-- url     : https://prove2.me/theorems/09496cf4-2df0-4557-ac21-c09a0dffa294
-- title:
--   Assumptions 9.1-9.2, Leontief network, and the activity-basis vocabulary
-- statement:
--   **Assumption 9.1.** Each column of the input-output matrix $R$ has exactly one positive
--   element; $i(j)$ denotes the unique such buffer for column $j$ (`servesBuffer`).
--
--   **Assumption 9.2.** There is $x \ge 0$ with $Rx > 0$ (componentwise).
--
--   **Definition 9.5 (Leontief network).** An SPN whose data satisfy both assumptions.
--
--   A **basis** (used in Lemma 9.3/Prop. 9.4) is a choice of $I$ activities, one serving each
--   buffer; its **basis matrix** $\hat R$ is the corresponding $I\times I$ submatrix of $R$, and
--   Eq. (9.3) records that $\hat R = (I-Q)\Delta^{-1}$ for some nonnegative $Q$ and positive
--   diagonal $\Delta$.
--
--   **Formalization note.** "Basis" is named `ActivityBasis`, not `Basis`, to avoid colliding
--   with Mathlib's vector-space `Basis` type — the book's own remark that its usage is "slightly
--   narrower than [the] standard meaning in linear programming theory" is taken seriously here.
--   `servesBuffer` uses `Exists.choose` on the `∃!` of Assumption 9.1, matching "the unique buffer
--   $i$" exactly (well-defined precisely because uniqueness holds).
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 164-167, Assumptions 9.1-9.2, Definition 9.5, Eq. (9.3)

import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData

namespace ProcessingNetworks.BackPressure

/-- Assumption 9.1, Dai & Harrison p. 164 (PDF p. 180): each column of the input-output matrix
`R` contains exactly one positive element. -/
def SatisfiesAssumption91 {I J K : ℕ} (dat : SPNPlanningData I J K) : Prop :=
  ∀ j : Fin J, ∃! i : Fin I, 0 < dat.R i j

/-- `i(j)`, the unique buffer served by activity `j` under Assumption 9.1. -/
noncomputable def servesBuffer {I J K : ℕ} {dat : SPNPlanningData I J K}
    (h91 : SatisfiesAssumption91 dat) (j : Fin J) : Fin I :=
  (h91 j).choose

/-- Assumption 9.2, Dai & Harrison p. 164 (PDF p. 180): there exists a vector `x ≥ 0` such that
`Rx > 0` (componentwise). -/
def SatisfiesAssumption92 {I J K : ℕ} (dat : SPNPlanningData I J K) : Prop :=
  ∃ x : Fin J → ℝ, (∀ j, 0 ≤ x j) ∧ ∀ i : Fin I, 0 < (dat.R.mulVec x) i

/-- Definition 9.5 (Leontief network), Dai & Harrison p. 167 (PDF p. 183): an SPN whose data
satisfy both Assumption 9.1 and Assumption 9.2. -/
def IsLeontiefNetwork {I J K : ℕ} (dat : SPNPlanningData I J K) : Prop :=
  SatisfiesAssumption91 dat ∧ SatisfiesAssumption92 dat

/-- A **basis** (Dai & Harrison p. 165, PDF p. 181): a choice of `I` activities among the `J ≥ I`
available, one serving each buffer. `choice i` is the basic activity assigned to buffer `i`;
`serves` records that it genuinely serves buffer `i` (i.e. `R i (choice i) > 0`), consistent with
Assumption 9.1's `i(j)` map. Named `ActivityBasis`, not `Basis`, to avoid colliding with Mathlib's
vector-space `Basis` type — this is a narrower, SPN-specific notion. -/
structure ActivityBasis {I J K : ℕ} (dat : SPNPlanningData I J K) where
  choice : Fin I → Fin J
  injective : Function.Injective choice
  serves : ∀ i, 0 < dat.R i (choice i)

/-- The basis matrix `R̂` (Dai & Harrison p. 165, PDF p. 181): the `I × I` submatrix of `R` formed
from the basic activities' columns. -/
noncomputable def basisMatrix {I J K : ℕ} {dat : SPNPlanningData I J K} (basis : ActivityBasis dat) :
    Matrix (Fin I) (Fin I) ℝ :=
  fun i i' => dat.R i (basis.choice i')

/-- `R̂ = (I - Q)Δ⁻¹` (Eq. 9.3): `Q` is a nonnegative square matrix and `Δ` is diagonal with
positive diagonal elements. -/
def IsBasisDecomposition {I : ℕ} (Rhat Q : Matrix (Fin I) (Fin I) ℝ) (Δ : Fin I → ℝ) : Prop :=
  (∀ i, 0 < Δ i) ∧ (∀ i i', 0 ≤ Q i i') ∧ Rhat = (1 - Q) * Matrix.diagonal (fun i => (Δ i)⁻¹)

end ProcessingNetworks.BackPressure


