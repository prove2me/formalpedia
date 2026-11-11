-- Prove2me | Definitions.Def_QNatProofs_haar
-- name    : QNatProofs_haar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:59:15.28083+00:00
-- url     : https://prove2.me/theorems/71b9caf9-3c65-4379-8eb4-9c9a08235be7
-- title:
--   The unit sphere of $n$-qubit states and the Haar measure $\mathrm{Haar}_n$
-- statement:
--   For $n\in\mathbb N$, $S(\mathbb C^{2^n})$ is the unit sphere of $\mathbb C^{2^n}$, whose coordinates are indexed by $x\in\{0,1\}^n$: the normalized $n$-qubit state vectors.
--
--   $\mathrm{Haar}_n$ is "the Haar probability measure on the unit sphere in $\mathbb C^{2^n}$, so its samples are normalized state vectors" (p.10). It is the unique probability measure on the sphere that is invariant under all unitaries.
--
--   **Formalization Note** $\mathrm{Haar}_n$ is Mathlib's surface measure `toSphere` of an additive Haar measure on $\mathbb C^{2^n}$, viewed as a real vector space of dimension $2^{n+1}$, divided by its total mass.
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Definition 2.2, p.9; p.10

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

set_option autoImplicit false

namespace QNatProofs

open QAlgorithms MeasureTheory

/-- The set of normalized `n`-qubit state vectors, the unit sphere `S(ℂ^{2ⁿ})` of
`ℂ^{2ⁿ} = EuclideanSpace ℂ (Qubits n)` (Li, Parham, arXiv:2610.06826 (held copy sha256 b604fa11…),
Definition 2.2, p.9). -/
abbrev sphere (n : ℕ) : Type :=
  Metric.sphere (0 : EuclideanSpace ℂ (Qubits n)) 1

/-- **`Haar_n`**, "the Haar probability measure on the unit sphere in `ℂ^{2ⁿ}`, so its samples are
normalized state vectors" (Li, Parham, arXiv:2610.06826 (held copy sha256 b604fa11…), p.10).

**Formalization Note** It is Mathlib's surface measure `toSphere` of an additive Haar measure on
`ℂ^{2ⁿ}` (as a real vector space of dimension `2^{n+1}`), divided by its total mass: the unique
rotation-invariant probability measure on the sphere. -/
noncomputable def haar (n : ℕ) : Measure (sphere n) :=
  ((Measure.addHaar : Measure (EuclideanSpace ℂ (Qubits n))).toSphere Set.univ)⁻¹ •
    (Measure.addHaar : Measure (EuclideanSpace ℂ (Qubits n))).toSphere

end QNatProofs


