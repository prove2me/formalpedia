-- Prove2me | Definitions.Def_AutoQMem_Lindblad_Supplement_IsQuantumMemoryThrough
-- name    : AutoQMem_Lindblad_Supplement_IsQuantumMemoryThrough
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:39:32.225398+00:00
-- url     : https://prove2.me/theorems/44ff0462-c7cc-45b9-b8a5-812a37e853b2
-- title:
--   Quantum $\epsilon$-memory and $q$-remembering through round $m$
-- statement:
--   Let $W_r$ be the physical channel at the $r$-th time point of a discrete schedule (for instance $W_r=Q_*^r$ after $r$ synchronous rounds, or the evolution up to the $r$-th cycle boundary). The encoded system is a **quantum $\epsilon$-memory through round $m$** if
--   $$\min_{0\le r\le m}F_{\min}[W_r]\ \ge\ 1-\epsilon ,$$
--   where $F_{\min}$ is the worst-case encoded fidelity of the designated logical qubit with the given readout decoders. A classical process **$q$-remembers** $b$ through round $m$ if
--   $$\max_{0\le r\le m}\Pr\big[b(\xi_r)\neq b(\xi_0)\big]\ \le\ q .$$
--
--   These are Definitions 2.20 and 2.21 on the index set $I=\{0,\dots,m\}$, used by Theorems 8, 3 and 4.
--
--   **Formalization Note** The minimum and maximum over the finite index set are written as pointwise bounds for every $r\le m$; $F_{\min}$ is the base mission's `LogicalQubit.Fmin`.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.20, eq. (28), and Definition 2.21, eq. (29), p. 19 (PDF p. 21); eq. (70), p. 27 (PDF p. 29)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_Fmin
open Matrix

namespace AutoQMem.Lindblad.Supplement

open AutoQMem.Lindblad

variable {n' mX mZ : ℕ} {C : CSSCode (n' + 1) mX mZ}

/-- **Quantum ε-memory through round m (on a discrete index set).** Drechsler, Oreg, Aharonov,
*Autonomous Quantum Memories from Classical Stochastic Processes*, arXiv:2610.05589 (PDF of
2026-11-03), Definition 2.20, eq. (28), p. 19 (PDF 21): "The encoded system is a quantum
ϵ_mem-memory on I if inf_{a∈I} F_min[W_{*,a}] ≥ 1 − ϵ_mem." Through round m: I = {0, …, m} with
W_{*,r} = Q_*^r (eq. (70), p. 27); at cycle boundaries through cycle m: I = {t_0, …, t_m},
t_r = rΔ (Theorem 4, p. 31; proof of Theorem 4, p. 61).

**Formalization Note.** `W r` is the physical channel at the r-th index point (`Q_*^[r]` for
synchronous dynamics, the register-reduced propagator at `rΔ` for Theorem 4). The infimum over the
finite set `{0, …, m}` is written as the equivalent pointwise bound `∀ r ≤ m`. -/
def IsQuantumMemoryThrough (Q : LogicalQubit C) (DX : Decoder C.HX) (DZ : Decoder C.HZ)
    (W : ℕ → Op (n' + 1) → Op (n' + 1)) (m : ℕ) (ε : ℝ) : Prop :=
  ∀ r : ℕ, r ≤ m → 1 - ε ≤ Q.Fmin DX DZ (W r)

/-- **q-remembering through round m.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from
Classical Stochastic Processes*, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.21, eq. (29),
p. 19 (PDF 21): "the process q-remembers b on I if sup_{a∈I} Pr[b(ξ_a) ≠ b(ξ_{a_0})] ≤ q"; through
round m is I = {0, …, m}.

**Formalization Note.** `pr r` is `Pr[b(ξ_r) ≠ b(ξ_0)]`; the supremum over the finite set is the
pointwise bound `∀ r ≤ m`. -/
def RemembersThrough (pr : ℕ → ℝ) (m : ℕ) (q : ℝ) : Prop :=
  ∀ r : ℕ, r ≤ m → pr r ≤ q

end AutoQMem.Lindblad.Supplement


