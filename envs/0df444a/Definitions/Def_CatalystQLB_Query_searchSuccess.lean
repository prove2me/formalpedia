-- Prove2me | Definitions.Def_CatalystQLB_Query_searchSuccess
-- name    : CatalystQLB_Query_searchSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:22:57.931244+00:00
-- url     : https://prove2.me/theorems/ce2555d0-c035-451d-a41a-d39885ab998a
-- title:
--   Reversed-problem success $\mathrm{succ}_{\mathrm{search}}(\gamma)$
-- statement:
--   For an oracle circuit with unitary $U=U_{f,g}$ and an operator $\gamma$ on the catalyst register,
--   $$\mathrm{succ}_{\mathrm{search}}(\gamma)=\mathbb E_{f,g,x}\,\mathrm{tr}\Big[\Pi^{\mathrm{search}}_x\,U\big(|x,f(g(x))\rangle\langle x,f(g(x))|\otimes\gamma\big)U^\dagger\Big].$$
--   For $\gamma=|0^\ell\rangle\langle0^\ell|$ this is the success probability of mapping $|x,f(g(x)),0^\ell\rangle$ to $|x,0^\lambda\rangle$ (Eq. (41)). It is linear in $\gamma$ and lies in $[0,\mathrm{tr}\,\gamma]$ for $\gamma\succeq0$.
--
--   This reversed problem is what the paper's proofs bound; the forward problem of Lemma 8 follows by taking adjoints.
--
--   **Formalization Note** The real part of the trace; $\gamma$ is any matrix, and the theorems assume $0\preceq\gamma$, $\mathrm{tr}\,\gamma\le1$.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Eq. (83), p.72 (PDF 75); Eq. (41), p.44 (PDF 47)

import Mathlib
import Definitions.Def_CatalystQLB_Query_searchProj
import Definitions.Def_CatalystQLB_Query_expectFGX

open scoped Matrix

namespace CatalystQLB.Query

open QAlgorithms

/-- The success of the circuit on the **reversed** problem with catalyst operator `γ`
(Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of 2026-11-03), Eq. (83), p.72 (PDF 75)):
`succ_search(γ) := E_{f,g,x} tr[Π^search U (|x, f(g(x))⟩⟨x, f(g(x))| ⊗ γ) U†]`, `U = eval C f g`.
For `γ = |0^ℓ⟩⟨0^ℓ|` this is Eq. (41).

**Formalization Note** The real part of the trace; `γ` is any matrix on `C` (the paper takes
`0 ⪯ γ`, `tr γ ≤ 1`, and notes that the expression is linear in `γ`). This is the reversed map
`|x, f(g(x))⟩ ↦ |x, 0^λ⟩`; Lemma 8's forward problem is `forwardSuccess`. -/
noncomputable def searchSuccess {n ℓ : ℕ} (C : OracleCircuit n ℓ)
    (γ : Matrix (Qubits ℓ) (Qubits ℓ) ℂ) : ℝ :=
  expectFGX n fun f g x =>
    (Matrix.trace (searchProj x * C.eval f g *
      Matrix.kronecker (Matrix.single (x, f (g x)) (x, f (g x)) (1 : ℂ)) γ *
      (C.eval f g)ᴴ)).re

end CatalystQLB.Query


