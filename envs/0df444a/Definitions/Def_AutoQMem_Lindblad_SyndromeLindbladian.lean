-- Prove2me | Definitions.Def_AutoQMem_Lindblad_SyndromeLindbladian
-- name    : AutoQMem_Lindblad_SyndromeLindbladian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:55:20.479597+00:00
-- url     : https://prove2.me/theorems/0a2bdf49-e6e8-4e44-8869-9d2d029c4d84
-- title:
--   Syndrome-based Lindbladian $\mathcal L(t)$ (representation data, rate condition, time regularity)
-- statement:
--   A **syndrome-based Lindbladian** for a CSS code is given by a Hamiltonian $H(t)$ and syndrome functions $f_{P,i,\alpha}(t)$ ($P\in\{I,X,Y,Z\}$, qubit $i$, $\alpha$ in a finite index set) such that, for every $t\ge0$:
--
--   1. $H(t)$ is a Hermitian element of the stabilizer algebra $\mathcal A$;
--   2. every $f_{P,i,\alpha}(t)$ is an element of $\mathcal A$;
--   3. the **rate condition** holds: $\Gamma^{(X)}_i(t)\in\mathcal A_X$ and $\Gamma^{(Z)}_i(t)\in\mathcal A_Z$ for every qubit $i$.
--
--   The generator is $\mathcal L(t)(\rho)=-i[H(t),\rho]+\sum_i\sum_P\sum_\alpha\mathcal D[P_if_{P,i,\alpha}(t)](\rho)$ (see `SyndromeLindbladian.gen`).
--
--   4. (time regularity) $t\mapsto H(t)$ and $t\mapsto f_{P,i,\alpha}(t)$ are measurable on $[0,\infty)$ and bounded on every interval $[0,T]$.
--
--   The rate condition is imposed on the total flip rates, not on the individual syndrome functions, and the Hamiltonian may be any Hermitian element of $\mathcal A$.
--
--   **Formalization Note** Condition 4 is Reading R1: Definition 2.22 leaves the time dependence open, and the paper's Remark 2.26 ("measurable and locally bounded in $t$ are covered verbatim") is adopted so that the propagators (40) and (51) exist. No continuity and no time independence is required. One finite index type is shared by all $(P,i)$; families on $(P,i)$-dependent finite sets are covered by padding with zero operators.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.22, eqs. (31)–(33), p. 20 (PDF p. 22); Remark 2.26, p. 21

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_CSSCode
import Definitions.Def_AutoQMem_Lindblad_flipRateX
open Matrix

namespace AutoQMem.Lindblad

/-- **Syndrome-based Lindbladian (its representation data).** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.22, eqs. (31)–(33),
p. 20 (PDF 22): "L(t)(ρ) = −i[H(t), ρ] + Σ_{i=1}^n Σ_{P∈{I,X,Y,Z}} Σ_α D[P_i f_{P,i,α}(t)](ρ), where α
ranges over a finite index set, the Hamiltonian H(t) is a Hermitian element of A, each syndrome
function f_{P,i,α}(t) is an element of A, and, for every qubit i and every t ≥ 0, the flip-rate
operators [(32)] satisfy the rate condition Γ^{(X)}_i(t) ∈ A_X, Γ^{(Z)}_i(t) ∈ A_Z. (33)"

**Formalization Note.**
* `ham t = H(t)`, `jump t i P α = f_{P,i,α}(t)`; the jump operator is `P_i f_{P,i,α}(t)`. The
  generator itself is `SyndromeLindbladian.gen`.
* The index set `ι` is one finite type shared by all `(P, i)`; families indexed by
  `(P, i)`-dependent finite sets are covered by padding with zero operators.
* The rate condition is on `Γ`, not on each `f`; the Hamiltonian is any Hermitian element of
  `A` (not of `A_X + A_Z`). All conditions are for `t ≥ 0` only.
* **Reading R1 (time regularity).** Definition 2.22 does not say how `L(t)` depends on `t`, and
  for some dependences (e.g. rate `1/t`) the propagator (40) does not exist. Following the paper's
  Remark 2.26 ("measurable and locally bounded in t are covered verbatim"), `H(t)` and every
  `f_{P,i,α}(t)` are required to be measurable on `[0, ∞)` (entrywise) and bounded on every
  `[0, T]`. Continuity or time independence is **not** required. -/
structure SyndromeLindbladian {n mX mZ : ℕ} (C : CSSCode n mX mZ) (ι : Type) [Fintype ι] :
    Type where
  /-- The Hamiltonian `H(t)`. -/
  ham : ℝ → Op n
  /-- The syndrome functions `f_{P,i,α}(t)`. -/
  jump : ℝ → Fin n → Pauli1 → ι → Op n
  /-- `H(t)` is a Hermitian element of `A` for `t ≥ 0`. -/
  ham_mem : ∀ t : ℝ, 0 ≤ t → ham t ∈ C.alg ∧ (ham t).IsHermitian
  /-- Each `f_{P,i,α}(t)` is an element of `A` for `t ≥ 0`. -/
  jump_mem : ∀ t : ℝ, 0 ≤ t → ∀ i P α, jump t i P α ∈ C.alg
  /-- Rate condition (33), X part: `Γ^{(X)}_i(t) ∈ A_X` for `t ≥ 0`. -/
  rateX_mem : ∀ t : ℝ, 0 ≤ t → ∀ i, flipRateX (jump t) i ∈ C.algX
  /-- Rate condition (33), Z part: `Γ^{(Z)}_i(t) ∈ A_Z` for `t ≥ 0`. -/
  rateZ_mem : ∀ t : ℝ, 0 ≤ t → ∀ i, flipRateZ (jump t) i ∈ C.algZ
  /-- R1: `t ↦ H(t)` is measurable on `[0, ∞)`, entrywise. -/
  ham_meas : ∀ x y, Measurable fun t : Set.Ici (0 : ℝ) => ham t x y
  /-- R1: `t ↦ f_{P,i,α}(t)` is measurable on `[0, ∞)`, entrywise. -/
  jump_meas : ∀ i P α x y, Measurable fun t : Set.Ici (0 : ℝ) => jump t i P α x y
  /-- R1: `H(t)` is bounded on every `[0, T]`. -/
  ham_bdd : ∀ T : ℝ, ∃ B : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x y, ‖ham t x y‖ ≤ B
  /-- R1: every `f_{P,i,α}(t)` is bounded on every `[0, T]`. -/
  jump_bdd : ∀ T : ℝ, ∃ B : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i P α x y, ‖jump t i P α x y‖ ≤ B

end AutoQMem.Lindblad


