-- Prove2me | Definitions.Def_ChenMaxEnt_expectations
-- name    : ChenMaxEnt_expectations
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:20:31.538186+00:00
-- url     : https://prove2.me/theorems/167580d6-2ac2-40e8-b492-31247933fa59
-- title:
--   The data map $\rho \mapsto \alpha = (\operatorname{tr}(\rho F_1), \dots, \operatorname{tr}(\rho F_r))$
-- statement:
--   Let $\mathcal H = \mathbb C^n$ be the finite-dimensional Hilbert space of a quantum system and let $F = (F_1, \dots, F_r)$ be a tuple of observables (Hermitian $n\times n$ matrices). The tuple defines the **data map**
--
--   $$
--   \rho \;\longmapsto\; \alpha = \bigl(\operatorname{tr}(\rho F_1), \dots, \operatorname{tr}(\rho F_r)\bigr) \in \mathbb R^r ,
--   $$
--
--   which sends a state $\rho$ to the vector $\alpha$ of expectation values of the observables, the "measurement results" of the paper.
--
--   The data map is the basic object of the maximum entropy inference: the attainable data $D_F$, the linear family $L(\alpha)$ and the inference $\rho^*(\alpha)$ are all defined through it.
--
--   **Formalization Note** The observables are indexed by a finite type $\iota$ (the paper's $\{1,\dots,r\}$). For Hermitian $F_i$ and a state $\rho$ the trace is real; the definition takes its real part, so the map lands in $\mathbb R^\iota$. It is total on matrices; the statements apply it to states.
-- source:
--   Chen et al., Discontinuity of Maximum Entropy Inference and Quantum Phase Transitions, arXiv:1406.5046v2, §2.1, eq. (1), p.4

import Mathlib

namespace ChenMaxEnt

/-- Chen et al., *Discontinuity of Maximum Entropy Inference and Quantum Phase Transitions*,
arXiv:1406.5046v2, §2.1, eq. (1), p.4: "Any tuple F = (F1, F2, . . . , Fr) of r observables
defines a mapping ρ ↦ α = (tr(ρF1), tr(F2ρ), . . . , tr(ρFr)), (1) from states ρ in D to points α
in the set DF". `expectations F ρ` is the data `α` of the matrix `ρ`: `α_i = tr(ρ F_i)`.

**Formalization Note.** The Hilbert space `H` of dimension `d` is `ℂ^n` for a finite index type
`n`; the tuple `F = (F_1, …, F_r)` is a family `F : ι → Matrix n n ℂ` indexed by a finite type
`ι` (`Fin r` in the paper). For a state `ρ` and a Hermitian `F_i` the trace `tr(ρ F_i)` is real;
the map takes its real part, so that the data are points of `ℝ^ι` as on the page. The map is
total on matrices; the theorems apply it to states. -/
noncomputable def expectations {n ι : Type*} [Fintype n] (F : ι → Matrix n n ℂ)
    (ρ : Matrix n n ℂ) : ι → ℝ :=
  fun i => (ρ * F i).trace.re

end ChenMaxEnt


