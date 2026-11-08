-- Prove2me | Definitions.Def_CompDesignBFM_tau
-- name    : CompDesignBFM_tau
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:32:36.880071+00:00
-- url     : https://prove2.me/theorems/74b1ddaa-d479-444a-bdc4-ea79d1cdbf9b
-- title:
--   Payment threshold
-- statement:
--   For an allocation rule $A$ and a fixed profile $b_{-i}$, the **payment threshold** is
--
--   $$\tau_i(b_{-i})=\sup\{z\ge0: i\in A(z,b_{-i})\}.$$
--
--   **Formalization Note** A real supremum, which is $0$ on an empty or unbounded set in Lean. It is used only at selected agents, where the set is nonempty, and every theorem using it assumes or proves boundedness.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, eq. (5), p.12 (PDF 14)

import Mathlib

namespace CompDesignBFM

/-- The payment threshold `τᵢ(b₋ᵢ) = sup {z ≥ 0 : i ∈ A(z, b₋ᵢ)}` (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, eq. (5), p.12, PDF 14).
**Formalization Note.** A real `sSup`, which is `0` on an empty or unbounded set. Only the value at a
selected agent is ever used (`thresholdMech`), where the set contains `b i`; every theorem using it
either assumes or proves that the set is bounded above. The value does not depend on `b i`. -/
noncomputable def tau {n : ℕ} (A : (Fin n → ℝ) → Finset (Fin n)) (b : Fin n → ℝ) (i : Fin n) : ℝ :=
  sSup {z : ℝ | 0 ≤ z ∧ i ∈ A (Function.update b i z)}

end CompDesignBFM


