-- Prove2me | Definitions.Def_FuchsThesis_Broadcast_ancillaProcess
-- name    : FuchsThesis_Broadcast_ancillaProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:21.367241+00:00
-- url     : https://prove2.me/theorems/6c4ae7bd-d713-47ca-a6bd-8bc01bc5986b
-- title:
--   Physical process with an auxiliary system, $E(X) = \mathrm{tr}_C\big(U(X\otimes\Upsilon)U^\dagger\big)$ (eq. 4.51)
-- statement:
--   Let a quantum system with a finite-dimensional Hilbert space interact with an auxiliary system $C$ of dimension $k$. Given an operator $\Upsilon$ on $C$ (the standard state of the auxiliary system) and an operator $U$ on the joint system, the associated process maps an operator $X$ of the system to
--
--   $$
--   E(X) = \mathrm{tr}_C\big( U (X \otimes \Upsilon) U^\dagger \big),
--   $$
--
--   where $X\otimes\Upsilon$ is the tensor (Kronecker) product and $\mathrm{tr}_C$ is the partial trace over the auxiliary system.
--
--   In §4.3 of Fuchs's thesis this is "the most general action $E$ on AB consistent with quantum theory": the system (there the composite $AB$) interacts unitarily with an auxiliary system $C$ prepared in a standard state $\Upsilon$, after which $C$ is ignored. The broadcasting and cloning predicates and the fidelity bounds of this mission are all stated through this map.
--
--   **Formalization Note** The system is indexed by an arbitrary finite type and $C$ by $\{0,\dots,k-1\}$, which covers every finite-dimensional auxiliary system. The map is defined for every matrix $U$ and $\Upsilon$; the statements that use it assume $U$ unitary and $\Upsilon$ a density matrix.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §4.3, eq. (4.51), p.114 (PDF p.123)

import Mathlib
import Definitions.Def_WildeQIT_partialTrace

open scoped Kronecker Matrix

namespace FuchsThesis.Broadcast

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §4.3, eq. (4.51), p.114 (PDF p.123): the most general physical process
on a system `X` lets it interact unitarily with an auxiliary system `C` in a standard state `Υ` and
then ignores `C`:
`E(X) = tr_C (U (X ⊗ Υ) U†)`.

**Formalization Note.** The system is indexed by an arbitrary finite type `m` (in §4.3, `m = n × n`
is the composite system `AB`); the auxiliary system `C` is indexed by `Fin k`, which covers every
finite-dimensional `C`. `X ⊗ Υ` is the Kronecker product, indexed by `m × Fin k`, and `tr_C` is the
partial trace over the right factor (`WildeQIT.partialTraceRight`). `U` is any matrix here; the
statements that use this map require `U ∈ Matrix.unitaryGroup (m × Fin k) ℂ` and `Υ` a density
matrix. -/
noncomputable def ancillaProcess {m : Type} [Fintype m] {k : ℕ}
    (U : Matrix (m × Fin k) (m × Fin k) ℂ) (Υ : Matrix (Fin k) (Fin k) ℂ)
    (X : Matrix m m ℂ) : Matrix m m ℂ :=
  WildeQIT.partialTraceRight (U * (X ⊗ₖ Υ) * Uᴴ)

end FuchsThesis.Broadcast


