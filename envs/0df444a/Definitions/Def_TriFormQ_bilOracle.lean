-- Prove2me | Definitions.Def_TriFormQ_bilOracle
-- name    : TriFormQ_bilOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:45:17.674025+00:00
-- url     : https://prove2.me/theorems/51aebf7d-30ca-4837-a330-854be0f7d6ec
-- title:
--   Evaluation oracle function of a bilinear form $x^\top My$
-- statement:
--   For a matrix $M\in M_n(\mathbb F_q)$, the bilinear form $f(x,y)=x^\top M y$ is accessed through the evaluation oracle
--
--   $$|x\rangle|y\rangle|b\rangle\ \mapsto\ |x\rangle|y\rangle|b+x^\top M y\rangle .$$
--
--   This definition is the function $(x,y)\mapsto x^\top My$ that this oracle evaluates. Bilinear forms and $n\times n$ matrices are identified, as in the paper's preliminaries.
--
--   **Formalization Note** An adaptive algorithm with oracle function `bilOracle M` queries `QAlgorithms.xorOracle (bilOracle M)`.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Corollary 4, p.11 (PDF p.14); Theorem 4, p.18 (PDF p.21)

import Definitions.Def_TriFormQ_TriForm
open Matrix

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Corollary 4, p.11 (PDF p.14),
Theorem 4, p.18 (PDF p.21): the bilinear form `f(x, y) = xᵀMy` "to which algorithm can only access
by making evaluation queries". The function `(x, y) ↦ xᵀMy` that the evaluation oracle
`|x⟩|y⟩|b⟩ ↦ |x⟩|y⟩|b + xᵀMy⟩` evaluates.

**Formalization Note.** An adaptive algorithm with oracle function `bilOracle M` queries
`QAlgorithms.xorOracle (bilOracle M)`; bilinear forms and `n × n` matrices are identified as in
§2, p.11. -/
def bilOracle {F : Type} [Field F] {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    Vec F n × Vec F n → F :=
  fun p => p.1 ⬝ᵥ (M *ᵥ p.2)

end TriFormQ


