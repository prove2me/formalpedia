-- Prove2me | Definitions.Def_DimFreeShadow_labelEntropy
-- name    : DimFreeShadow_labelEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:37.98603+00:00
-- url     : https://prove2.me/theorems/db93503f-698e-4fec-ab38-880fba040d31
-- title:
--   §4.2, Lemma B.2 — marginals, $I(J:Q_{t+1}\mid Q^t)$, $I(J:Q^N)$ and $H(J)$
-- statement:
--   Let $\omega$ be an operator on $J\otimes Q_1\otimes\dots\otimes Q_N$. This module defines the marginal $\omega_{JQ_1\cdots Q_t}$ and, with $S(\omega)=-\operatorname{Tr}(\omega\log\omega)$ in natural logarithms,
--
--   $$
--   I(J:Q_{t+1}\mid Q^t)=S(\omega_{JQ^t})+S(\omega_{Q^{t+1}})-S(\omega_{Q^t})-S(\omega_{JQ^{t+1}}),
--   $$
--
--   $$
--   I(J:Q^N)=S(\omega_J)+S(\omega_{Q^N})-S(\omega_{JQ^N}),\qquad H(J)=-\sum_a q_a\log q_a,
--   $$
--
--   where $q$ is the marginal law of the classical register $J$. These are the quantities of the chain rule in Lemma B.2.
--
--   **Formalization Note** Registers may have different finite dimensions. Indices are 0-based: $Q^t$ is the coordinates $i<t$ of a configuration. The entropy is the published `P56.entropy`, in nats.
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), §4.2, p.17; Lemma B.2, p.37

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Defs_Measurement

namespace DimFreeShadow

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- **Marginal on the label and the first `t` registers** `ω_{J Q₁⋯Q_t}` (arXiv:2608.06345,
sha256 a1a42249…, §4.2, p.17 and Lemma B.2, p.37). The state `ω` lives on `J ⊗ Q₁ ⊗ ⋯ ⊗ Q_N`,
with `J` indexed by `A` and register `Q_i` by `Q i` (registers of possibly different finite
dimensions); the marginal traces out `Q_{t+1}, …, Q_N`.

**Formalization Note** Registers are 0-based: `Q₁ ⋯ Q_t` are the coordinates `i < t` of
`(i : Fin N) → Q i`. Entry `((a,x),(a',x'))` sums `ω_{(a,z),(a',z')}` over full configurations
`z, z'` that restrict to `x, x'` on the first `t` coordinates and agree on the others. At
`t = 0` the register part is the one-point space. -/
noncomputable def prefixMarginal {A : Type} {N : ℕ} {Q : Fin N → Type}
    [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)]
    (ω : Matrix (A × ((i : Fin N) → Q i)) (A × ((i : Fin N) → Q i)) ℂ) (t : ℕ) (ht : t ≤ N) :
    Matrix (A × ((i : Fin t) → Q (Fin.castLE ht i))) (A × ((i : Fin t) → Q (Fin.castLE ht i))) ℂ :=
  Matrix.of fun p q => ∑ z : (i : Fin N) → Q i, ∑ z' : (i : Fin N) → Q i,
    if (∀ i : Fin t, z (Fin.castLE ht i) = p.2 i) ∧ (∀ i : Fin t, z' (Fin.castLE ht i) = q.2 i) ∧
        (∀ i : Fin N, t ≤ (i : ℕ) → z i = z' i)
    then ω (p.1, z) (q.1, z') else 0

/-- **Conditional mutual information** `I(J : Q_{t+1} | Q₁ ⋯ Q_t)_ω` (arXiv:2608.06345, sha256
a1a42249…, §4.2, p.17: "I(J : C | K)ω := S(ωJK) + S(ωKC) − S(ωK) − S(ωJKC)", with
`K = Q₁⋯Q_t`, `C = Q_{t+1}`; Lemma B.2, p.37). Here `t : Fin N` is the 0-based index of
`ηt := I(J : Qt+1 | Qt)`, `0 ≤ t < N`.

**Formalization Note** `S(ω) = −Tr(ω log ω)` in nats is the published
`P56.entropy` ("We use natural logarithms in the entropy expressions", p.17).
`ω_{KC} = ω_{Q₁⋯Q_{t+1}}` is `traceLeft` (trace over `J`) of the `(t+1)`-prefix marginal. -/
noncomputable def prefixCondMI {A : Type} [Fintype A] [DecidableEq A] {N : ℕ} {Q : Fin N → Type}
    [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)]
    (ω : Matrix (A × ((i : Fin N) → Q i)) (A × ((i : Fin N) → Q i)) ℂ) (t : Fin N) : ℝ :=
  entropy (prefixMarginal ω t.val t.isLt.le) +
    entropy (QAlgorithms.traceLeft (prefixMarginal ω (t.val + 1) t.isLt)) -
    entropy (QAlgorithms.traceLeft (prefixMarginal ω t.val t.isLt.le)) -
    entropy (prefixMarginal ω (t.val + 1) t.isLt)

/-- **Mutual information between the label and all registers** `I(J : Q₁⋯Q_N)_ω =
S(ω_J) + S(ω_{Q₁⋯Q_N}) − S(ω_{JQ₁⋯Q_N})` (arXiv:2608.06345, sha256 a1a42249…, §4.2, p.17:
"I(U : V)ω := S(ωU) + S(ωV) − S(ωUV)"), in nats. -/
noncomputable def labelMutualInfo {A : Type} [Fintype A] [DecidableEq A] {N : ℕ}
    {Q : Fin N → Type} [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)]
    (ω : Matrix (A × ((i : Fin N) → Q i)) (A × ((i : Fin N) → Q i)) ℂ) : ℝ :=
  entropy (QAlgorithms.traceRight ω) + entropy (QAlgorithms.traceLeft ω) - entropy ω

/-- **Shannon entropy of the label** `H(J)_ω = −Σ_a q_a log q_a`, `q_a = Tr(⟨a| ω |a⟩)` the
marginal law of the classical register `J` (arXiv:2608.06345, sha256 a1a42249…, §4.2, p.17:
"For a classical law q, write H(q) = −Σa qa log qa. H(J)ω denotes the entropy of the marginal
law of a classical register J"). Natural logarithm, `0 log 0 = 0` (`Real.negMulLog`). -/
noncomputable def labelEntropy {A : Type} [Fintype A] {N : ℕ} {Q : Fin N → Type}
    [∀ i, Fintype (Q i)]
    (ω : Matrix (A × ((i : Fin N) → Q i)) (A × ((i : Fin N) → Q i)) ℂ) : ℝ :=
  ∑ a, Real.negMulLog (∑ z, ω (a, z) (a, z)).re

end DimFreeShadow


