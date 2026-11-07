-- Prove2me | Definitions.Def_KTUnitary_Synth_embedGate
-- name    : KTUnitary_Synth_embedGate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:27:59.96319+00:00
-- url     : https://prove2.me/theorems/e5ad0cfb-f1b3-492a-9879-bf516385c4e7
-- title:
--   A gate acting on chosen wires
-- statement:
--   For distinct wires $w_0,\dots,w_{k-1}$ among $N$ qubits and a $2^k\times 2^k$ matrix $G$, the $2^N\times 2^N$ matrix that applies $G$ to those wires (in that order) and the identity to the others:
--   $$(G\otimes I)_{ij}=\begin{cases}G_{i|_w,\,j|_w}&\text{if }i,j\text{ agree off }w,\\0&\text{otherwise.}\end{cases}$$
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definitions 4.2–4.3, p. 14

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace KTUnitary.Synth

open Classical in
/-- **A `k`-qubit gate acting on chosen wires of `N` qubits** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definitions 4.2–4.3, p. 14:
"each gate is specified by the list of `k` qubits it acts on"): for distinct wires
`w : Fin k ↪ Fin N` and a `2^k × 2^k` matrix `G`, the `2^N × 2^N` matrix `G ⊗ I` with `G` on the wires
`w 0, …, w (k − 1)` (in that order) and the identity on the other wires. Entry `(i, j)` is
`G (i ∘ w) (j ∘ w)` if `i` and `j` agree off the range of `w`, and `0` otherwise. -/
noncomputable def embedGate {k N : ℕ} (w : Fin k ↪ Fin N) (G : Matrix (Bits k) (Bits k) ℂ) :
    Matrix (Bits N) (Bits N) ℂ :=
  Matrix.of fun i j =>
    if ∀ q, q ∉ Set.range w → i q = j q then G (fun r => i (w r)) (fun r => j (w r)) else 0

end KTUnitary.Synth


