-- Prove2me | Definitions.Def_FuchsThesis_Broadcast_IsClone
-- name    : FuchsThesis_Broadcast_IsClone
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:28.901841+00:00
-- url     : https://prove2.me/theorems/d75e96b6-71c7-470b-908f-085e452cd02d
-- title:
--   The pair $\{\rho_0,\rho_1\}$ is clonable (eq. 4.50)
-- statement:
--   In the setting of broadcasting (an $N$-dimensional system $A$ prepared in $\rho_0$ or $\rho_1$, an $N$-dimensional system $B$ in a standard state $\Sigma$), the set $\{\rho_0,\rho_1\}$ is **clonable** if there is a single physical process $E$, the same for both states, with
--
--   $$
--   E(\rho_s \otimes \Sigma) = \rho_s \otimes \rho_s, \qquad s = 0, 1 .
--   $$
--
--   As for broadcasting, $E(X) = \mathrm{tr}_C\big(U(X\otimes\Upsilon)U^\dagger\big)$ for some finite-dimensional auxiliary system $C$, standard state $\Upsilon$ of $C$ and unitary $U$ on $ABC$. Cloning is the strong form of broadcasting in which the output is the product of two copies.
--
--   **Formalization Note** Same encoding as the broadcasting predicate: $A$, $B$ indexed by one finite type, $C$ by $\{0,\dots,k-1\}$ for some $k$; $\Sigma$, $\Upsilon$ density matrices, $U$ unitary, the same data for both states.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §4.3, eqs. (4.50), (4.51), p.114 (PDF p.123)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsThesis_Broadcast_ancillaProcess

open scoped Kronecker

namespace FuchsThesis.Broadcast

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §4.3, eqs. (4.50), (4.51), p.114 (PDF p.123): the set `{ρ₀, ρ₁}` is
**clonable** if there is one physical process `E` of the form (4.51), with a standard state `Σ` of
`B`, such that `E(ρₛ ⊗ Σ) = ρₛ ⊗ ρₛ` for `s = 0, 1` ("We reserve the word cloning for this strong
form of broadcasting").

**Formalization Note.** Same encoding as `IsBroadcast`: `A`, `B` indexed by `n`, `AB` by `n × n`,
the auxiliary system `C` by `Fin k` for some `k : ℕ`; `Σ`, `Υ` density matrices, `U` unitary on
`(n × n) × Fin k`, the same `k, Σ, Υ, U` for both states. -/
def IsClone {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ) : Prop :=
  ∃ (k : ℕ) (Sig : Matrix n n ℂ) (Ups : Matrix (Fin k) (Fin k) ℂ)
    (U : Matrix ((n × n) × Fin k) ((n × n) × Fin k) ℂ),
    WildeQIT.IsDensityOperator Sig ∧ WildeQIT.IsDensityOperator Ups ∧
    U ∈ Matrix.unitaryGroup ((n × n) × Fin k) ℂ ∧
    ∀ ρ ∈ ({ρ0, ρ1} : Set (Matrix n n ℂ)), ancillaProcess U Ups (ρ ⊗ₖ Sig) = ρ ⊗ₖ ρ

end FuchsThesis.Broadcast


