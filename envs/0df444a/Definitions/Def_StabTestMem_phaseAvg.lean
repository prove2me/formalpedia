-- Prove2me | Definitions.Def_StabTestMem_phaseAvg
-- name    : StabTestMem_phaseAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:10:11.943889+00:00
-- url     : https://prove2.me/theorems/4cab00dd-4cdb-4a36-a5f8-b8ae57813633
-- title:
--   Expectation over a uniformly random upper-triangular $A$
-- statement:
--   For a real function $f$ on $\mathbb F_2^{n\times n}$, $\mathbb E_A[f(A)]$ is the average of $f$ over the $2^{n(n+1)/2}$ upper-triangular matrices. Applied to the acceptance probability of a protocol on $|\psi_A\rangle$, it is the acceptance probability on a uniformly random degree-2 phase state.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), §3.2, p. 19; §5.2, p. 38

import Definitions.Def_StabTestMem_IsUpperTri

namespace StabTestMem

open Classical in
/-- **Expectation over a uniformly random upper-triangular `A`, `E_A[f(A)]`.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), §3.2, p. 19,
and §5.2, p. 38 ("Uniformly random degree two phase states ρ_P := E_A[ψ_A^{⊗t}]").

`phaseAvg f = (#upper-triangular A)⁻¹ Σ_{A upper triangular} f(A)`. Used for the acceptance
probability of a protocol on a uniformly random degree-2 phase state. -/
noncomputable def phaseAvg {n : ℕ} (f : Matrix (Fin n) (Fin n) (ZMod 2) → ℝ) : ℝ :=
  ((Finset.univ.filter fun A : Matrix (Fin n) (Fin n) (ZMod 2) => IsUpperTri A).card : ℝ)⁻¹ *
    ∑ A ∈ Finset.univ.filter (fun A : Matrix (Fin n) (Fin n) (ZMod 2) => IsUpperTri A), f A

end StabTestMem


