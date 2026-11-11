-- Prove2me | Definitions.Def_StabTestMem_prefixMass
-- name    : StabTestMem_prefixMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:13:44.042971+00:00
-- url     : https://prove2.me/theorems/ed13d110-8312-4e3e-ae1f-f920b06b92ce
-- title:
--   Probability $Q^k_\psi(H_M)$ of an $M$-good prefix
-- statement:
--   The probability that partial Bell difference sampling on $|\psi\rangle$ returns an $M$-good prefix:
--
--   $$Q^k_\psi(H_M)=\sum_{(a,r)\in H_M}Q^k_\psi(a,r).$$
--
--   The probability of an $M$-bad prefix is $1-Q^k_\psi(H_M)$.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Lemma 3.4, p. 18; Proposition 4.11 and Corollary 4.12, pp. 34–35

import Definitions.Def_StabTestMem_pbds
import Definitions.Def_StabTestMem_goodPrefixes

namespace StabTestMem

open QAlgorithms

open Classical in
/-- **Probability `Q^k_ψ(H_M)` that partial Bell difference sampling outputs an `M`-good prefix.**
Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Lemma 3.4 (p. 18: "The probability of observing an element of H from partial Bell difference
sampling is Q^k_ψ(H)"), Proposition 4.11 and Corollary 4.12, pp. 34–35 ("The M-good prefixes are
exactly the prefix projection H_M").

`prefixMass ψ M = Σ_{p ∈ H_M} Q^k_ψ(p)`, with `H_M` = `goodPrefixes M` and `Q^k_ψ` = `pbds ψ`. -/
noncomputable def prefixMass {k m : ℕ} (ψ : EuclideanSpace ℂ (Qubits (k + m)))
    (M : Set (CutRankSched.Pauli (k + m))) : ℝ :=
  ∑ p : CutRankSched.Pauli k × (Fin m → ZMod 2), if p ∈ goodPrefixes M then pbds ψ p else 0

end StabTestMem


