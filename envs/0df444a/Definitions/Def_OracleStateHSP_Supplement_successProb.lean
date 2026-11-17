-- Prove2me | Definitions.Def_OracleStateHSP_Supplement_successProb
-- name    : OracleStateHSP_Supplement_successProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:12:22.420712+00:00
-- url     : https://prove2.me/theorems/e9aa35eb-1a0f-4bf3-80d3-9616f270d013
-- title:
--   Probability that a POVM returns a given answer
-- statement:
--   Let $\{M_z\}_{z}$ be a measurement with finitely many outcomes $z$ on a finite-dimensional Hilbert space, and let $\mathrm{out}$ map outcomes to answers. On the pure state $|\psi\rangle$ the probability that the reported answer is $a$ is
--   $$
--   \Pr[\text{answer} = a] = \sum_{z\,:\,\mathrm{out}(z) = a} \langle\psi| M_z |\psi\rangle = \sum_{z\,:\,\mathrm{out}(z) = a} \operatorname{Tr}\big(M_z |\psi\rangle\langle\psi|\big).
--   $$
--   A $t$-sample algorithm evaluates the answer function with bounded error if this probability is at least $2/3$ on every instance (Definition 5.2).
--
--   **Formalization Note** Outcomes are $\{0, \dots, e - 1\}$ for an arbitrary $e$, followed by an arbitrary output map; coarse-graining a POVM by the output map is again a POVM, so this covers every POVM with outcomes in the answer set. The real part of $\langle\psi|M_z|\psi\rangle$ is taken, which is the probability when $M_z$ is positive semidefinite.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Definition 5.2, p.41

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query

namespace OracleStateHSP

namespace Supplement

open QAlgorithms

/-- The probability that the measurement `{M_z}_z` with output map `out` returns the answer `a` on
the pure state `|ψ⟩` (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, Definition 5.2, p.41):
`∑_(z : out z = a) ⟨ψ|M_z|ψ⟩ = ∑_(z : out z = a) Tr(M_z |ψ⟩⟨ψ|)`.

**Formalization Note.** Outcomes are `Fin e` with an arbitrary output map `out` into the answer set
(coarse-graining a POVM by `out` is again a POVM, so this covers every POVM with outcomes in the
answer set). The real part is taken; it is the probability when `M_z ⪰ 0`. -/
noncomputable def successProb {Y A : Type*} [Fintype Y] {e : ℕ} (Mz : Fin e → Matrix Y Y ℂ)
    (out : Fin e → A) (ψ : EuclideanSpace ℂ Y) (a : A) : ℝ :=
  ∑ z, @ite ℝ (out z = a) (Classical.propDecidable _) (inner ℂ ψ (act (Mz z) ψ)).re 0

end Supplement

end OracleStateHSP


