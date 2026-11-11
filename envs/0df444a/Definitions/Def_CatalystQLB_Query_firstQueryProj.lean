-- Prove2me | Definitions.Def_CatalystQLB_Query_firstQueryProj
-- name    : CatalystQLB_Query_firstQueryProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:21:47.854322+00:00
-- url     : https://prove2.me/theorems/3beff213-ac9f-40ea-80ba-d0f3ccc6331d
-- title:
--   First-query projector $\Pi=|g(x)\rangle\langle g(x)|_Q\otimes I_{RC}$
-- statement:
--   For $z\in\{0,1\}^\lambda$,
--   $$\Pi=|z\rangle\langle z|_Q\otimes I_{RC},\qquad \Pi^\perp=I-\Pi.$$
--   The paper uses it with $z=g(x)$: $\Pi$ detects a query to $f$ at the point $g(x)$. Inserting $I=\Pi+\Pi^\perp$ before each query to $O_f$ splits a circuit by the first such query (Notation 74).
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), §5.3, p.45 (PDF 48)

import Mathlib
import Definitions.Def_CatalystQLB_Query_OracleCircuit

namespace CatalystQLB.Query

open QAlgorithms

/-- The projector `Π := |z⟩⟨z|_Q ⊗ I_{RC}` onto the query register holding `z`
(Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of 2026-11-03), §5.3, p.45 (PDF 48): "Define `Π := |g(x)⟩⟨g(x)|_Q ⊗ I_RC` and `Π^⊥ := I − Π`"). The
paper uses it with `z = g(x)`; `Π^⊥` is `1 - firstQueryProj z`. -/
noncomputable def firstQueryProj {n ℓ : ℕ} (z : Qubits n) : Matrix (Idx n ℓ) (Idx n ℓ) ℂ :=
  Matrix.kronecker
    (Matrix.kronecker (Matrix.single z z (1 : ℂ)) (1 : Matrix (Qubits n) (Qubits n) ℂ))
    (1 : Matrix (Qubits ℓ) (Qubits ℓ) ℂ)

end CatalystQLB.Query


