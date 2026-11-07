-- Prove2me | Definitions.Def_CertRandQROM_outProb
-- name    : CertRandQROM_outProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:31:55.904972+00:00
-- url     : https://prove2.me/theorems/cb114276-f392-4be8-9698-2ab342457f6e
-- title:
--   Output law $\Pr[X=o\mid H=h]$ of a query algorithm
-- statement:
--   After the $Q$ queries, $\mathcal A^h$ measures $|\psi^h_Q\rangle$ with its POVM $\{M_o\}$ and outputs the outcome. The probability of outcome $o$ given the oracle $h$ is
--
--   $$
--   \Pr[X=o\mid H=h]=\langle\psi^h_Q|\,M_o\,|\psi^h_Q\rangle .
--   $$
--
--   It is the conditional law of the adversary's output $X$ given the oracle, used in Lemma 7.3, in the acceptance probability and in the min-entropy of Definition 6.1.
--
--   **Formalization Note** Written as the real part of $\sum_{a,b}\overline{\psi(a)}\,(M_o)_{ab}\,\psi(b)$ with $\psi=|\psi^h_Q\rangle$; the sanity file proves $\sum_o \Pr[X=o\mid H=h]=1$.
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), §3.2, p.15 (PDF p.17): "A applies measurement M to |ψ_Q^H⟩ and outputs the measurement outcome"

import Mathlib
import Definitions.Def_CertRandQROM_QueryAlg

namespace CertRandQROM

/-- **Output law of a query algorithm** (§3.2, p.15: "A applies measurement `M` to `|ψ_Q^H⟩` and
outputs the measurement outcome"; Coladangelo et al., arXiv:2608.31112, sha256 b75095a2…):
`outProb A h o = Pr[X = o | H = h] = ⟨ψ_Q^h| M_o |ψ_Q^h⟩`, written
`Re Σ_{a,b} conj(ψ(a)) (M_o)_{a b} ψ(b)`. -/
noncomputable def outProb {U W O : Type} [Fintype U] [DecidableEq U] [Fintype W]
    [DecidableEq W] [Fintype O] {Q : ℕ} (A : QueryAlg U W O Q) (h : U → Bool) (o : O) : ℝ :=
  (∑ a, ∑ b, star (A.state h Q a) * A.meas o a b * A.state h Q b).re

end CertRandQROM


