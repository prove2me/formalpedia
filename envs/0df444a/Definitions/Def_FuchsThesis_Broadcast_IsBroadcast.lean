-- Prove2me | Definitions.Def_FuchsThesis_Broadcast_IsBroadcast
-- name    : FuchsThesis_Broadcast_IsBroadcast
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:39.881307+00:00
-- url     : https://prove2.me/theorems/0dbd4666-2fda-4086-ab1d-cc89160e5e30
-- title:
--   The pair $\{\rho_0,\rho_1\}$ can be broadcast (eqs. 4.48–4.51)
-- statement:
--   A quantum system $AB$ consists of two parts $A$ and $B$, each with an $N$-dimensional Hilbert space. System $A$ is prepared in one of two states $\rho_0, \rho_1$; system $B$ is in a standard state $\Sigma$. The set $\{\rho_0,\rho_1\}$ **can be broadcast** if there is a single physical process $E$, the same for $s = 0$ and $s = 1$, such that the state
--
--   $$
--   \tilde\rho_s = E(\rho_s \otimes \Sigma)
--   $$
--
--   of $AB$ has both marginals equal to the input state:
--
--   $$
--   \mathrm{tr}_A(\tilde\rho_s) = \rho_s \quad\text{and}\quad \mathrm{tr}_B(\tilde\rho_s) = \rho_s, \qquad s = 0, 1 .
--   $$
--
--   Physical processes are those of the form $E(X) = \mathrm{tr}_C\big(U(X\otimes\Upsilon)U^\dagger\big)$ for some auxiliary system $C$ of finite dimension, some standard state $\Upsilon$ of $C$ and some unitary operator $U$ on $ABC$.
--
--   The joint state $\tilde\rho_s$ is not required to be a product: it may be correlated or entangled, as long as each subsystem receives the original state.
--
--   **Formalization Note** $A$ and $B$ are indexed by the same finite type, $AB$ by its square (first factor $A$, second $B$), and $C$ by $\{0,\dots,k-1\}$ for some natural number $k$, so every finite-dimensional auxiliary system is allowed; $k\ge1$ follows from $\mathrm{tr}\,\Upsilon = 1$. $\Sigma$ and $\Upsilon$ are density matrices, $U$ is unitary, and the same $k,\Sigma,\Upsilon,U$ serve both states.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §4.3, eqs. (4.48), (4.49), (4.51), pp.113–114 (PDF pp.122–123)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_FuchsThesis_Broadcast_ancillaProcess

open scoped Kronecker

namespace FuchsThesis.Broadcast

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §4.3, eqs. (4.48), (4.49), (4.51), pp.113–114 (PDF pp.122–123): the set
`{ρ₀, ρ₁}` of states of an `N`-dimensional system `A` **can be broadcast** if there is one physical
process `E`, fixed independently of `s`, with a standard state `Σ` of `B` (also `N`-dimensional),
such that `ρ̃ₛ = E(ρₛ ⊗ Σ)` satisfies `tr_A ρ̃ₛ = ρₛ` and `tr_B ρ̃ₛ = ρₛ` for `s = 0, 1`. By (4.51)
`E(ρₛ ⊗ Σ) = tr_C (U (ρₛ ⊗ Σ ⊗ Υ) U†)` for some auxiliary system `C`, standard state `Υ` of `C` and
unitary `U` on `ABC`.

**Formalization Note.** `A` and `B` are both indexed by the finite type `n`; `AB` by `n × n` (first
factor `A`, second `B`); `C` by `Fin k` for some `k : ℕ` (every finite-dimensional auxiliary
system; `k ≥ 1` is forced by `tr Υ = 1`). `Σ`, `Υ` are density matrices, `U` a unitary on
`(n × n) × Fin k`, and the same `k, Σ, Υ, U` serve both states. `tr_A` is
`WildeQIT.partialTraceLeft` and `tr_B` is `WildeQIT.partialTraceRight`. -/
def IsBroadcast {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ) : Prop :=
  ∃ (k : ℕ) (Sig : Matrix n n ℂ) (Ups : Matrix (Fin k) (Fin k) ℂ)
    (U : Matrix ((n × n) × Fin k) ((n × n) × Fin k) ℂ),
    WildeQIT.IsDensityOperator Sig ∧ WildeQIT.IsDensityOperator Ups ∧
    U ∈ Matrix.unitaryGroup ((n × n) × Fin k) ℂ ∧
    ∀ ρ ∈ ({ρ0, ρ1} : Set (Matrix n n ℂ)),
      WildeQIT.partialTraceLeft (ancillaProcess U Ups (ρ ⊗ₖ Sig)) = ρ ∧
      WildeQIT.partialTraceRight (ancillaProcess U Ups (ρ ⊗ₖ Sig)) = ρ

end FuchsThesis.Broadcast


