-- Prove2me | Definitions.Def_KempeCloning_initState
-- name    : KempeCloning_initState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:23:15.694527+00:00
-- url     : https://prove2.me/theorems/46dbbba7-1f21-43b7-8fa8-bc927cc358f9
-- title:
--   The initial state $|\Psi_{in}\rangle = |m,0,0,0,N\rangle$ (13)
-- statement:
--   For $m, N\in\mathbb N$, the initial state of Eq. (13) is the number state
--
--   $$|\Psi_{in}\rangle = \frac{(a_1^\dagger)^m}{\sqrt{m!}}\frac{(c^\dagger)^N}{\sqrt{N!}}|0\rangle = |m_{a_1}, 0_{a_2}, 0_{b_1}, 0_{b_2}, N_c\rangle \equiv |m,0,0,0,N\rangle :$$
--
--   $m$ photons in the correct mode $a_1$, and all $N$ atoms in the excited level (mode $c$ holds $N$ quanta).
--
--   **Formalization Note** Defined directly as the basis vector $|m,0,0,0,N\rangle$ with amplitude $1$.
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II B, (13), p.4; Sec. II C, p.5

import Definitions.Def_KempeCloning_occ
import Definitions.Def_KempeCloning_FockVec

namespace KempeCloning

/-- **The initial state (13): `|Ψ_in⟩ = |m, 0, 0, 0, N⟩`.**
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1, Sec. II B, (13), p.4: "the initial state (2) is
now given by |ψi⟩ = (a†1)^m/√m! (c†)^N/√N! |0⟩ = |m_{a1}, 0_{a2}, 0_{b1}, 0_{b2}, N_c⟩ ≡ |m, 0, 0, 0, N⟩."
Sec. II C, p.5, calls the same state `|Ψ_in⟩`.

`m` photons in the good mode `a₁`, and `N` excitations in mode `c` (all `N` atoms excited).

**Formalization Note.** Defined directly as the normalized number state `Finsupp.single n 1`
with `n = occ m 0 0 0 N`; the paper's middle expression `(a₁†)^m/√m! (c†)^N/√N! |0⟩` equals it. -/
noncomputable def initState (m N : ℕ) : FockVec :=
  Finsupp.single (occ m 0 0 0 N) 1

end KempeCloning


