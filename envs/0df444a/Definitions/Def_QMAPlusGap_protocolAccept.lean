-- Prove2me | Definitions.Def_QMAPlusGap_protocolAccept
-- name    : QMAPlusGap_protocolAccept
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:07:39.263205+00:00
-- url     : https://prove2.me/theorems/d06008f3-d92a-4cd5-a535-efa1cb10ec48
-- title:
--   Acceptance probability of the two-proof protocol
-- statement:
--   Let $\mathcal H=\mathbb C^{\iota}$, $0\preceq B\preceq I$ on $\mathcal H$, $N\le M$, and let $|\Psi_1\rangle,|\Psi_2\rangle\in\mathcal H^{\otimes M}$ be the two proofs. The protocol (1) measures $\{P^{(M)}_{\mathrm{sym}},I-P^{(M)}_{\mathrm{sym}}\}$ on each proof and continues only on the symmetric outcomes, (2) keeps the first $N$ registers of each proof, and (3–4) accepts with the joint operator $P^{(2N)}_{\mathrm{sym}}B^{\otimes2N}$ on the $2N$ kept registers. Its acceptance probability is
--   $$
--   \operatorname{Tr}\Big[P^{(2N)}_{\mathrm{sym}}B^{\otimes2N}\big(X_1\otimes X_2\big)\Big],\qquad X_i=\big(P^{(M)}_{\mathrm{sym}}|\Psi_i\rangle\langle\Psi_i|P^{(M)}_{\mathrm{sym}}\big)_N ,
--   $$
--   where $(\cdot)_N$ is the reduction to the first $N$ registers.
--
--   **Formalization Note** The projectors are exact; the circuit implementation of §4.5 approximates them to inverse-exponential accuracy. The trace is real for positive semidefinite $B$, and the definition takes its real part.
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), §4.1, p.16

import Mathlib
import Definitions.Def_QMAPlusGap_symProj
import Definitions.Def_QMAPlusGap_reduce
import Definitions.Def_QMAPlusGap_tensorJoin
import Definitions.Def_WildeQIT_Schumacher_tensorPow
import Definitions.Def_DuanEP_Pure_pureKernel

set_option autoImplicit false

namespace QMAPlusGap

/-- The **acceptance probability of the two-proof protocol** of Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), §4.1, p.16, on proofs
`|Ψ₁⟩, |Ψ₂⟩ ∈ H^{⊗M}`, with ideal (exact) operators:
1. measure `{P_sym^{(M)}, I − P_sym^{(M)}}` on each proof and continue only on the outcomes `P_sym^{(M)}`;
2. keep the first `N` H-registers of each proof and discard the other `M − N`;
3. and 4. accept with the joint acceptance operator `P_sym^{(2N)} B^{⊗2N}` on the `2N` kept registers
("Since P_sym^{(2N)} commutes with B^{⊗2N}, steps 3 and 4 have joint acceptance operator P_sym^{(2N)} B^{⊗2N}").

The value is `Tr[P_sym^{(2N)} B^{⊗2N} (X₁ ⊗ X₂)]` with `X_i` the reduction to the first `N` registers of the
unnormalized post-measurement operator `P_sym^{(M)} |Ψ_i⟩⟨Ψ_i| P_sym^{(M)}`; this is the probability that steps
1–4 all accept.

**Formalization Note** `H = ℂ^ι`; `2N` registers are indexed by `Fin (N + N)`, the first `N` from proof 1. The
trace is real for PSD `B` (the two factors commute); the definition takes its real part. -/
noncomputable def protocolAccept {ι : Type} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℂ) (M N : ℕ)
    (Ψ₁ Ψ₂ : (Fin M → ι) → ℂ) : ℝ :=
  (Matrix.trace (symProj (N + N) * WildeQIT.Schumacher.tensorPow (N + N) B *
    tensorJoin (reduce N (symProj M * DuanEP.Pure.pureKernel Ψ₁ * symProj M))
      (reduce N (symProj M * DuanEP.Pure.pureKernel Ψ₂ * symProj M)))).re

end QMAPlusGap


