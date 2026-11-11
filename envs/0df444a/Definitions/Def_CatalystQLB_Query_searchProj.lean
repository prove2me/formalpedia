-- Prove2me | Definitions.Def_CatalystQLB_Query_searchProj
-- name    : CatalystQLB_Query_searchProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:22:02.3779+00:00
-- url     : https://prove2.me/theorems/d0228fd5-548c-4bbc-8251-ddfc9c5d354c
-- title:
--   Search projector $\Pi^{\mathrm{search}}_x=|x\rangle\langle x|_Q\otimes|0^\lambda\rangle\langle0^\lambda|_R\otimes I_C$
-- statement:
--   For $x\in\{0,1\}^\lambda$,
--   $$\Pi^{\mathrm{search}}_x=|x\rangle\langle x|_Q\otimes|0^\lambda\rangle\langle0^\lambda|_R\otimes I_C,$$
--   the projector onto the IO register holding $(x,0^\lambda)$, with the catalyst unconstrained. It has rank $2^\ell$ and measures success on the reversed problem $|x,f(g(x))\rangle\mapsto|x,0^\lambda\rangle$.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Eq. (41), p.44 (PDF 47)

import Mathlib
import Definitions.Def_CatalystQLB_Query_OracleCircuit

namespace CatalystQLB.Query

open QAlgorithms

/-- The search projector `Π^search_x := |x⟩⟨x|_Q ⊗ |0^λ⟩⟨0^λ|_R ⊗ I_C` (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of 2026-11-03), Eq. (41),
p.44 (PDF 47)): the IO register holds `(x, 0^n)`; the catalyst is unconstrained.

**Formalization Note** `n` is the paper's `λ`; `0 : Qubits n` is `0^n`. -/
noncomputable def searchProj {n ℓ : ℕ} (x : Qubits n) : Matrix (Idx n ℓ) (Idx n ℓ) ℂ :=
  Matrix.kronecker (Matrix.single (x, (0 : Qubits n)) (x, (0 : Qubits n)) (1 : ℂ))
    (1 : Matrix (Qubits ℓ) (Qubits ℓ) ℂ)

end CatalystQLB.Query


