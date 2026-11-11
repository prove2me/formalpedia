-- Prove2me | Definitions.Def_LindbladShallow_gen
-- name    : LindbladShallow_gen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:18:43.639736+00:00
-- url     : https://prove2.me/theorems/7eb59b09-c66a-47ed-9f0a-23dbd41e8718
-- title:
--   The Lindblad generator $\mathcal L$ of an input and the target channel $e^{T\mathcal L}$
-- statement:
--   For an input with lifted local Hamiltonians $H_e$ and lifted jump operators $L_{e\mu}$, the **Lindblad generator** is
--   $$\mathcal L(\rho)=-i[H,\rho]+\sum_{e,\mu}\Big(L_{e\mu}\rho L_{e\mu}^\dagger-\tfrac12\{L_{e\mu}^\dagger L_{e\mu},\rho\}\Big),\qquad H=\sum_e H_e,$$
--   and the **target channel** is $e^{T\mathcal L}$, with $T$ the input time.
--
--   This is Eq. (1) of the paper, the dynamics that Theorem 2.1 simulates.
--
--   **Formalization Note** The sums run over all supplied terms; removed (empty-support or exactly zero) terms contribute nothing, so this is the generator of the retained decomposition.
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Eq. (1), p.1; Theorem 2.1, p.10

import Mathlib
import Definitions.Def_LindbladShallow_Instance

open scoped Matrix ComplexOrder

namespace LindbladShallow

/-- The system Hamiltonian `H := Σ_e H_e`, each local `H_e` lifted from its support by the
identity (arXiv:2610.05362, held version sha256 8f4637ef…, Eq. (1), p.1). -/
noncomputable def hamTotal {P : Params} (I : Instance P) : Matrix (Sys I) (Sys I) ℂ :=
  ∑ e : Fin I.nT, liftSys I (I.term e).supp (I.term e).hamC

/-- All lifted jump operators `L_eµ` (`e ∈ I_J`, `1 ≤ µ ≤ µ_e`), in term order. -/
noncomputable def jumpsTotal {P : Params} (I : Instance P) : List (Matrix (Sys I) (Sys I) ℂ) :=
  (List.finRange I.nT).flatMap fun e => (I.term e).jumpsC.map (liftSys I (I.term e).supp)

/-- The Lindblad generator of the input (arXiv:2610.05362, Eq. (1), p.1):
`ℒ(ρ) := −i[H, ρ] + Σ_{e,µ} (L_eµ ρ L_eµ† − ½{L_eµ†L_eµ, ρ})`, `H := Σ_e H_e`.

**Formalization Note** The sum runs over all supplied terms. A removed term contributes nothing:
an exact-zero term lifts to `0`, an empty-support Hamiltonian term is a real scalar (zero
commutator) and an empty-support jump `c·I` has `|c|²(ρ − ρ) = 0`; so this equals the generator of
the retained decomposition. -/
noncomputable def gen {P : Params} (I : Instance P) :
    Matrix (Sys I) (Sys I) ℂ →ₗ[ℂ] Matrix (Sys I) (Sys I) ℂ :=
  gksl (hamTotal I) (jumpsTotal I)

/-- The target channel `e^{Tℒ}` (arXiv:2610.05362, Eq. (1), p.1; Theorem 2.1, p.10), with `T`
the input's rational time. -/
noncomputable def target {P : Params} (I : Instance P) :
    Matrix (Sys I) (Sys I) ℂ →ₗ[ℂ] Matrix (Sys I) (Sys I) ℂ :=
  supExp (I.T : ℝ) (gen I)

end LindbladShallow


