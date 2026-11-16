-- Prove2me | Definitions.Def_CatalystQLB_Query_Supplement_unitaryChannel
-- name    : CatalystQLB_Query_Supplement_unitaryChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:57:32.40739+00:00
-- url     : https://prove2.me/theorems/772af153-b1bc-4420-8c91-f552ab6dbbb1
-- title:
--   The unitary channel $C_V(\rho)=V\rho V^\dagger$
-- statement:
--   For a unitary $V\in\mathcal U(n)$ on $n$ qubits, the **unitary channel** is
--   $$C_V(\rho) := V\rho V^\dagger .$$
--   Theorems 64 and 136 compare catalytic channels $C^\eta_U$ with channels of this form.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Notation 59 and Example 60, pp.36–37 (PDF 39–40); proof of Theorem 64, p.40 (PDF 43)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

open scoped Matrix

namespace CatalystQLB.Query.Supplement

open QAlgorithms

/-- The unitary channel `C_V(ρ) := V ρ V†` of `V ∈ U(n)` (Arora, Chakraborty, Cojocaru,
Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*,
arXiv:2609.40323 (version of 2026-11-03), Notation 59 and Example 60, pp.36–37 (PDF 39–40);
proof of Theorem 64, p.40 (PDF 43): `C_{V_η}(ρ) = V_η ρ V_η†`). -/
noncomputable def unitaryChannel {n : ℕ} (V : Matrix.unitaryGroup (Qubits n) ℂ)
    (ρ : Matrix (Qubits n) (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ :=
  (V : Matrix _ _ ℂ) * ρ * (V : Matrix _ _ ℂ)ᴴ

end CatalystQLB.Query.Supplement


