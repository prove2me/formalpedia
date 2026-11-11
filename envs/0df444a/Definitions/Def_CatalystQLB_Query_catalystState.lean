-- Prove2me | Definitions.Def_CatalystQLB_Query_catalystState
-- name    : CatalystQLB_Query_catalystState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:21:18.700619+00:00
-- url     : https://prove2.me/theorems/0feb066c-73aa-4151-a877-7aaf513e42e8
-- title:
--   Catalyst state $\eta_{\ell,p}=((1-p)|0\rangle\langle0|+p|1\rangle\langle1|)^{\otimes\ell}$
-- statement:
--   The catalyst state on $\ell$ qubits is the product state
--   $$\eta_{\ell,p}=\big((1-p)|0\rangle\langle0|+p|1\rangle\langle1|\big)^{\otimes\ell}=\sum_{z\in\{0,1\}^\ell}\mu_p(z)\,|z\rangle\langle z|:$$
--   each catalyst qubit is independently $|1\rangle$ with probability $p$. Its purity is measured by $1-h_2(p)$ per qubit, and the mission's lower bound holds when $\ell(1-h_2(p))$ stays below $\lambda$.
--
--   **Formalization Note** A diagonal matrix in the computational basis, `true` $=|1\rangle$. This is the state the paper uses on p.7, in Theorem 117 and throughout §9. The preamble of Lemma 8 prints instead $(1-p)|0^\ell\rangle\langle0^\ell|+p|1^\ell\rangle\langle1^\ell|$, under which Lemma 8 is false; see the goal theorem.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), p.7 (PDF 10); Theorem 117, p.69 (PDF 72); §9.3, p.74 (PDF 77); Lemma 8 preamble, p.12 (PDF 15)

import Mathlib
import Definitions.Def_CatalystQLB_Query_catalystWeight

namespace CatalystQLB.Query

open QAlgorithms

/-- The catalyst state `η_{ℓ,p} = ((1 − p)|0⟩⟨0| + p|1⟩⟨1|)^{⊗ℓ} = Σ_z µ_p(z) |z⟩⟨z|`
(Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of 2026-11-03): p.7 (PDF 10), "η consisting of tensor products of `p|1⟩⟨1| + (1 − p)|0⟩⟨0|`";
Theorem 117, p.69 (PDF 72); §9.3, p.74 (PDF 77), before Eq. (93)). Each of the `ℓ` catalyst
qubits is independently `|1⟩` with probability `p`.

**Formalization Note** This is the product state, the reading the paper uses everywhere except
in the preamble of Lemma 8 (p.12), which prints `(1 − p)|0^ℓ⟩⟨0^ℓ| + p|1^ℓ⟩⟨1^ℓ|`; with that
state Lemma 8 is false (see the goal theorem). A diagonal matrix in the computational basis
`Qubits ℓ`, `true` = `|1⟩`. -/
noncomputable def catalystState (ℓ : ℕ) (p : ℝ) : Matrix (Qubits ℓ) (Qubits ℓ) ℂ :=
  Matrix.diagonal fun z => ((catalystWeight ℓ p z : ℝ) : ℂ)

end CatalystQLB.Query


