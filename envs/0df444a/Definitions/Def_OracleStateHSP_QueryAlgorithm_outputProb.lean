-- Prove2me | Definitions.Def_OracleStateHSP_QueryAlgorithm_outputProb
-- name    : OracleStateHSP_QueryAlgorithm_outputProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:31:41.302854+00:00
-- url     : https://prove2.me/theorems/5fa11157-d312-449f-aea0-ccfe7e36b402
-- title:
--   Output probability $\sum_{z : \mathrm{out}(z) = e} |\langle z | A^O \psi_0\rangle|^2$
-- statement:
--   Run the algorithm $A$ on the oracle $O$ from the initial vector $|\psi_0\rangle$, measure the final state $A^O|\psi_0\rangle$ in the computational basis, and report $\mathrm{out}(z)$ for the outcome $z$. The probability of output $e$ is
--   $$
--   \Pr[A \text{ outputs } e] = \sum_{z\,:\,\mathrm{out}(z) = e} \bigl|\langle z | A^O \psi_0\rangle\bigr|^2 .
--   $$
--
--   **Formalization Note** The paper measures "a designated output register". Measuring the whole register and applying the output map covers that case (the map reads the register), and conversely an algorithm can copy $\mathrm{out}(z)$ into an output register of an enlarged workspace by one final permutation unitary, so both readings give the same success probabilities and query counts.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Definition 4.3, p.35

import Mathlib
import Definitions.Def_OracleStateHSP_QueryAlgorithm

namespace OracleStateHSP

open QAlgorithms

namespace QueryAlgorithm

variable {Q S W : Type*} [Fintype Q] [Fintype S] [Fintype W] [DecidableEq Q] [DecidableEq S]
  [DecidableEq W] {T : ℕ}

/-- The probability that the algorithm, run on oracle `O` from `ψ₀`, outputs `e` (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656,
Definition 4.3, p.35): the final state `A^O|ψ₀⟩` is measured in the computational basis and the
outcome `z` is reported as `out z`, so the probability is `∑_{z : out z = e} |⟨z|A^O ψ₀⟩|²`.

**Formalization Note.** The paper measures "a designated output register". Here the whole register
is measured and the output map `out` is applied to the outcome. A register measurement is the
special case where `out` reads the register's coordinates; conversely an algorithm can write
`out z` into an output register of an enlarged workspace with one final permutation unitary, so
both readings give the same success probabilities and the same query counts. -/
noncomputable def outputProb {E : Type*} (A : QueryAlgorithm Q S W T) (O : Matrix Q Q ℂ)
    (ψ₀ : EuclideanSpace ℂ (S ⊕ (Q × W))) (out : S ⊕ (Q × W) → E) (e : E) : ℝ := by
  classical
  exact ∑ z ∈ Finset.univ.filter (fun z => out z = e), prob (A.finalState O ψ₀) z

end QueryAlgorithm

end OracleStateHSP


