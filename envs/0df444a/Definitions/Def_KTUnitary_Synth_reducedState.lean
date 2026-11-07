-- Prove2me | Definitions.Def_KTUnitary_Synth_reducedState
-- name    : KTUnitary_Synth_reducedState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:29:52.95831+00:00
-- url     : https://prove2.me/theorems/e5532483-9772-4ccc-bbce-57c9b4e8f4ca
-- title:
--   Reduced state on output wires
-- statement:
--   For an $N$-qubit matrix $\rho$ and distinct output wires $o_0,\dots,o_{m-1}$, the partial trace of $\rho$ over all other wires, as an $m$-qubit matrix whose qubit $r$ is wire $o_r$.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 7.13, p. 38

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace KTUnitary.Synth

open Classical in
/-- **Reduced state on output wires** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 7.13, p. 38: the circuits' "outputs on
security parameter `n` are mixed states"): the partial trace of an `N`-qubit matrix `ρ` over every
wire outside the distinct wires `out : Fin m ↪ Fin N`, as an `m`-qubit matrix whose qubit `r` is
wire `out r`. Entry `(u, v)` is `Σ ρ_{zz'}` over the pairs `z`, `z'` that agree off the range of `out`
and restrict to `u` and `v` on it. -/
noncomputable def reducedState {m N : ℕ} (out : Fin m ↪ Fin N) (ρ : Matrix (Bits N) (Bits N) ℂ) :
    Matrix (Bits m) (Bits m) ℂ :=
  Matrix.of fun u v => ∑ z : Bits N, ∑ z' : Bits N,
    if (fun r => z (out r)) = u ∧ (fun r => z' (out r)) = v ∧ ∀ q, q ∉ Set.range out → z q = z' q
    then ρ z z' else 0

end KTUnitary.Synth


