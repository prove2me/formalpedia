-- Prove2me | Definitions.Def_KTUnitary_Synth_placeState
-- name    : KTUnitary_Synth_placeState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:29:57.264204+00:00
-- url     : https://prove2.me/theorems/733fd5da-ee1e-4812-958a-5c80ab0d8e07
-- title:
--   Loading an input state onto chosen wires
-- statement:
--   For an $m$-qubit matrix $\rho$ and distinct input wires among $N$, the $N$-qubit matrix $\rho\otimes|0\rangle\langle0|$ with $\rho$ on the input wires and every other wire in $|0\rangle$. It is how a distinguisher $D_n$ receives the state $\rho_{b,n}$.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 7.13, p. 38

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace KTUnitary.Synth

open Classical in
/-- **Loading an input state into a circuit** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 7.13, p. 38: `D_n(ρ_{b,n})`): the
`N`-qubit matrix `ρ ⊗ |0⟩⟨0|` with the `m`-qubit matrix `ρ` on the distinct wires `inp : Fin m ↪ Fin N`
(qubit `r` of `ρ` on wire `inp r`) and every other wire in `|0⟩`. -/
noncomputable def placeState {m N : ℕ} (inp : Fin m ↪ Fin N) (ρ : Matrix (Bits m) (Bits m) ℂ) :
    Matrix (Bits N) (Bits N) ℂ :=
  Matrix.of fun z z' =>
    if ∀ q, q ∉ Set.range inp → z q = false ∧ z' q = false
    then ρ (fun r => z (inp r)) (fun r => z' (inp r)) else 0

end KTUnitary.Synth


