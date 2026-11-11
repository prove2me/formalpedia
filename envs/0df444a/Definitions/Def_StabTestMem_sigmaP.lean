-- Prove2me | Definitions.Def_StabTestMem_sigmaP
-- name    : StabTestMem_sigmaP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:11:18.511142+00:00
-- url     : https://prove2.me/theorems/23a0dd37-d2ea-4538-a4d8-ee401effd518
-- title:
--   Operator $\sigma_P=2^{-nt}\sum_{O\in\mathcal O_t}R(O)$
-- statement:
--   $$\sigma_P=\frac1{2^{nt}}\sum_{O\in\mathcal O_t}R(O).$$
--
--   It is not normalized (its trace is $\sum_{O}2^{-n\,\mathrm{rank}(I+O)}$), and it approximates $\rho_P$ in trace norm when $t<n$ (Theorem 5.5).
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Eq. (80), p. 39

import Definitions.Def_StabTestMem_IsStochOrth
import Definitions.Def_StabTestMem_ROp

namespace StabTestMem

open QAlgorithms

open Classical in
/-- **The operator `σ_P = 2^{−nt} Σ_{O ∈ O_t} R(O)`.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Eq. (80), p. 39: "σ_P := (1/2^{nt})
Σ_{O∈O_t} R(O) … Observe that σ_P is unnormalized and, in particular, not equal to ρ_P". -/
noncomputable def sigmaP (n t : ℕ) : Matrix (Fin t → Qubits n) (Fin t → Qubits n) ℂ :=
  ((2 : ℂ) ^ (n * t))⁻¹ •
    ∑ O ∈ Finset.univ.filter (fun O : Matrix (Fin t) (Fin t) (ZMod 2) => IsStochOrth O), ROp O

end StabTestMem


