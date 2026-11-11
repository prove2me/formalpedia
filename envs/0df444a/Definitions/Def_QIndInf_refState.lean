-- Prove2me | Definitions.Def_QIndInf_refState
-- name    : QIndInf_refState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:26:51.849544+00:00
-- url     : https://prove2.me/theorems/388400a7-7e1f-4fee-8b77-56cae413f717
-- title:
--   Reference state: uniform mixture over all programs of length $\le s$
-- statement:
--   For $s\in\mathbb N$ let $P_s=\{T\in\{0,1\}^*:|T|\le s\}$, the set of programs of length at most $s$; it has $2^{s+1}-1$ elements. For a source model $T\mapsto\rho^{T}$ (at fixed $n,t$) the **reference state** on $m$ registers is the uniform mixture
--
--   $$
--   \mu_{R_1\dots R_m}=\frac1{|P_s|}\sum_{T\in P_s}\rho^{T}_{R_1\dots R_m}.
--   $$
--
--   It depends only on the source model and on $(n,s,t)$: not on the program that generated the observed source, and not on $m$.
--
--   It plays the role of the paper's time-bounded universal density matrix $\mu^{U,p(s,t)}$ (Definition 3.5, Eq. (39), a uniform mixture over programs run on a universal machine) in the proof of Theorem 4.2, where the only property used is the domination (58).
--
--   **Formalization Note** $P_s$ is a `Finset (List Bool)` built from the strings of each length $0,\dots,s$. Since $|P_s|\ge1$ the coefficient is never a division by zero.
-- source:
--   Hiroka, Hsieh, Shirakawa, arXiv:2609.36912 (PDF of 2026-11-02), Definition 3.5, Eq. (39), p.16; Eq. (58), p.20

import Mathlib
import Definitions.Def_QIndInf_QuantumProcess

set_option autoImplicit false

namespace QIndInf

/-- The finite set of all programs (bit strings) of length at most `s`:
`{T ∈ {0,1}* : |T| ≤ s}`, which has `2^{s+1} − 1` elements.

arXiv:2609.36912 (PDF of 2026-11-02), Eq. (50), p.18 ("a classical Turing machine T with
|T| ≤ s"). -/
def programs (s : ℕ) : Finset (List Bool) :=
  (Finset.range (s + 1)).biUnion fun l =>
    (Finset.univ : Finset (Fin l → Bool)).image List.ofFn

/-- **Reference (universal) state of a source model.** For a source model `gen` and parameters
`n, s, t`, the `m`-register state
`μ_{R₁…R_m} = (1/|P_s|) ∑_{T ∈ P_s} ρ^{gen,n,t}_T(R₁…R_m)`, the uniform mixture, over all programs
`T` of length at most `s`, of the sources they generate.

arXiv:2609.36912 (PDF of 2026-11-02), Definition 3.5, Eq. (39), p.16
(`μ^{U,t}_n := 2^{−t} ∑_{Π ∈ {0,1}^t} ρ^{U,t}_n(Π)`, a uniform mixture over programs) and its use in
Eq. (58), p.20 (`μ_{R₁…R_m} ≥ 2^{−cs} ρ_{R₁…R_m}`).

**Formalization Note.** The paper mixes over the programs of length exactly `p(s,t)` run on a
universal machine `U`; this definition mixes over the programs of length at most `s` run in the
source model itself. It depends only on `(gen, n, s, t)`, not on the program that generated the
observed source and not on `m`. It plays the role of the paper's `μ` in the proof of Theorem 4.2.
The coefficient is `|P_s|⁻¹` with `|P_s| = 2^{s+1} − 1 ≥ 1`, so there is no division by zero. -/
noncomputable def refState (gen : SourceModel) (n s t m : ℕ) :
    Matrix (Regs n m) (Regs n m) ℂ :=
  ((programs s).card : ℂ)⁻¹ • ∑ T ∈ programs s, (gen n t T).state m

end QIndInf


