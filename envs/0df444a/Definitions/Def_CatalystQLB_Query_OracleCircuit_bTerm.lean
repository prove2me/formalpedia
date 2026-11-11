-- Prove2me | Definitions.Def_CatalystQLB_Query_OracleCircuit_bTerm
-- name    : CatalystQLB_Query_OracleCircuit_bTerm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:23:45.635799+00:00
-- url     : https://prove2.me/theorems/d069e5a2-37b7-4376-b4ad-838b3142d991
-- title:
--   Branch weights $b_i$
-- statement:
--   For an operator $\gamma$ on the catalyst register and $1\le i\le q-1$,
--   $$b_i=\mathbb E_{f,g,x}\,\mathrm{tr}\Big[\Pi\,Z_i\big(|x,f(g(x))\rangle\langle x,f(g(x))|\otimes\gamma\big)Z_i^\dagger\Big],\qquad \Pi=|g(x)\rangle\langle g(x)|_Q\otimes I_{RC}:$$
--   the weight of the branch whose first query to $f$ at the point $g(x)$ is the $i$-th query.
--
--   **Formalization Note** Real part of the trace.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Eq. (84), p.72 (PDF 75)

import Mathlib
import Definitions.Def_CatalystQLB_Query_OracleCircuit_branchZ
import Definitions.Def_CatalystQLB_Query_expectFGX

open scoped Matrix

namespace CatalystQLB.Query

open QAlgorithms

namespace OracleCircuit

variable {n ℓ : ℕ}

/-- The branch weight `b_i := E_{f,g,x} tr[Π Z_i (|x, f(g(x))⟩⟨x, f(g(x))| ⊗ γ) Z_i†]`,
`1 ≤ i ≤ q − 1` (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of 2026-11-03), Eq. (84), p.72 (PDF 75)), with `Π = |g(x)⟩⟨g(x)|_Q ⊗ I_RC`.

**Formalization Note** Real part of the trace; `γ` is any matrix on `C`. -/
noncomputable def bTerm (C : OracleCircuit n ℓ) (γ : Matrix (Qubits ℓ) (Qubits ℓ) ℂ) (i : ℕ) :
    ℝ :=
  expectFGX n fun f g x =>
    (Matrix.trace (firstQueryProj (g x) * C.branchZ f g x i *
      Matrix.kronecker (Matrix.single (x, f (g x)) (x, f (g x)) (1 : ℂ)) γ *
      (C.branchZ f g x i)ᴴ)).re

end OracleCircuit

end CatalystQLB.Query


