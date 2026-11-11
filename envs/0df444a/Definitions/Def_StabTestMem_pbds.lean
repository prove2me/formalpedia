-- Prove2me | Definitions.Def_StabTestMem_pbds
-- name    : StabTestMem_pbds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:12:22.639643+00:00
-- url     : https://prove2.me/theorems/5183b8b4-f23c-4cd2-b54b-040ee7102a8b
-- title:
--   Partial Bell difference sampling distribution $Q^k_\psi$
-- statement:
--   **Partial Bell difference sampling** (Algorithm 2) runs partial Bell sampling twice on fresh pairs of copies and returns the sum $(a_1+a_2,\,r_1+r_2)$ of the two outcomes. Its output distribution is
--
--   $$Q^k_\psi(a,r)=\sum_{b\in\mathbb F_2^{2k}}\sum_{s\in\mathbb F_2^m}q^k_\psi(b,s)\,q^k_\psi(a+b,\,r+s).$$
--
--   It uses four copies and $k$ qubits of memory, and is the first step of each round of the paper's tester.
--
--   **Formalization Note** Defined operationally from Algorithm 1, never from the formula of Lemma 4.2 (which is a milestone about this definition).
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Algorithm 2, p. 24; p. 17; Eq. (28), p. 18

import Definitions.Def_StabTestMem_pbs

namespace StabTestMem

open QAlgorithms

/-- **Partial Bell difference sampling distribution `Q^k_ψ(a, r)` (Algorithm 2).** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026),
Algorithm 2, p. 24 ("for i = 0 to 1 do … return (a_0 + a_1, z_{0,0} + z_{0,1} + z_{1,0} + z_{1,1})"),
and p. 17: "partial Bell difference sampling (Algorithm 2) corresponds to partial Bell sampling
|ψ⟩ twice to obtain outcomes (a_1, r_1) and (a_2, r_2) and returns (a_1 + a_2, r_1 + r_2)".

`pbds ψ (a, r) = Σ_{b, s} q^k_ψ(b, s) q^k_ψ(a + b, r + s)`: the law of the sum of two independent
partial Bell samples (Eq. (28), p. 18).

**Formalization Note.** Defined operationally (two independent runs of Algorithm 1, outcomes
added), never by the formula of Lemma 4.2, which is a theorem about this definition. -/
noncomputable def pbds {k m : ℕ} (ψ : EuclideanSpace ℂ (Qubits (k + m)))
    (p : CutRankSched.Pauli k × (Fin m → ZMod 2)) : ℝ :=
  ∑ b : CutRankSched.Pauli k, ∑ s : Fin m → ZMod 2, pbs ψ (b, s) * pbs ψ (p.1 + b, p.2 + s)

end StabTestMem


