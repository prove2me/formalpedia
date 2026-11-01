-- Prove2me | Definitions.Def_TucciCIT_metaDensity
-- name    : TucciCIT_metaDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:29:10.481987+00:00
-- url     : https://prove2.me/theorems/705f1f8b-ec79-4103-ae8a-8d5174c65ce3
-- title:
--   Meta density matrix $\mu = |\psi_{meta}\rangle\langle\psi_{meta}|$
-- statement:
--   For an amplitude $\psi$ on $S_x \times S_y$, the meta density matrix of the net of Fig. 3 is the projector
--
--   $$
--   \mu = |\psi_{meta}\rangle\langle\psi_{meta}| ,\qquad \mu_{i,j} = \psi_{meta}(i)\,\overline{\psi_{meta}(j)},
--   $$
--
--   on $\mathcal H_e \otimes \mathcal H_x \otimes \mathcal H_y$, where $\psi_{meta}$ is the meta amplitude of eq. (4.2) and $i, j$ range over basis indices $(e, x, y)$ with $e \in S_x \times S_y$.
--
--   All quantities $S_\mu(\cdot)$ of the paper's §4 are von Neumann entropies of reduced density matrices of $\mu$. It is a density matrix exactly when $\sum_{x,y}|\psi(x,y)|^2 = 1$.
--
--   **Formalization Note** The register order is $e$, then $x$, then $y$; the definition does not normalize $\psi$.
-- source:
--   Tucci, Quantum Entanglement and Conditional Information Transmission, arXiv:quant-ph/9909041v2, eq. (4.1), p.8

import Mathlib
import Definitions.Def_TucciCIT_metaAmplitude

namespace TucciCIT

/-- Tucci, *Quantum Entanglement and Conditional Information Transmission*,
arXiv:quant-ph/9909041v2, eq. (4.1), p.8 (PDF p.8).

The meta density matrix `μ = |ψ_meta⟩⟨ψ_meta|` of the QB net of Fig. 3, acting on
`H_e ⊗ H_x ⊗ H_y` with basis `(e, x, y) ∈ (S_x × S_y) × S_x × S_y`:
`μ_{i,j} = ψ_meta(i) · conj(ψ_meta(j))`, where `ψ_meta` is `metaAmplitude ψ` (eq. (4.2)).

**Formalization Note.** The register order is `e`, then `x`, then `y`. `μ` is the unnormalized
projector onto `ψ_meta`; it is a density matrix exactly when `Σ_{x,y} |ψ(x,y)|² = 1`. -/
def metaDensity {X Y : Type*} [DecidableEq X] [DecidableEq Y] (ψ : Matrix X Y ℂ) :
    Matrix ((X × Y) × X × Y) ((X × Y) × X × Y) ℂ :=
  Matrix.of fun i j => metaAmplitude ψ i * star (metaAmplitude ψ j)

end TucciCIT


