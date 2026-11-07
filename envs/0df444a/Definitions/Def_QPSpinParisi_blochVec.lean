-- Prove2me | Definitions.Def_QPSpinParisi_blochVec
-- name    : QPSpinParisi_blochVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:02:23.449095+00:00
-- url     : https://prove2.me/theorems/241a56ec-dcaf-4e46-936a-42a53f7d9974
-- title:
--   The Bloch vector of a qubit, (2.6)
-- statement:
--   The Bloch vector of a pure one-qubit state $|\phi\rangle$ is $s=(s^1,s^2,s^3)$ with
--   $$s^a=\langle\phi|\sigma^a|\phi\rangle.$$
--   It lies on the unit sphere $S^2$, and it turns optimization over product states into optimization over $(S^2)^n$.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (2.6), p.6 (PDF p.6)

import Mathlib
import Definitions.Def_QPSpinParisi_E3
import Definitions.Def_CollectiveDFS_pauli
import Definitions.Def_QPSpinParisi_energy

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The Bloch vector of a one-qubit ket, with coordinates `s^a = ⟨ϕ|σ^a|ϕ⟩` (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (2.6), p.6, PDF p.6).

**Formalization Note** `σ^a` is the published `CollectiveDFS.pauli`, indexed by `Fin 3` (`0 = σ¹ = X`, `1 = σ² = Y`,
`2 = σ³ = Z`), with `false : Bool` the basis vector `|0⟩`, as on p.3. -/
noncomputable def blochVec (f : Bool → ℂ) : E3 :=
  WithLp.toLp 2 fun a : Fin 3 => energy (CollectiveDFS.pauli a) f

end QPSpinParisi


