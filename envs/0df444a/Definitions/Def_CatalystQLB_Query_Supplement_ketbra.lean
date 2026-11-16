-- Prove2me | Definitions.Def_CatalystQLB_Query_Supplement_ketbra
-- name    : CatalystQLB_Query_Supplement_ketbra
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:56:22.499657+00:00
-- url     : https://prove2.me/theorems/e92cd6c6-0a77-4093-b3a5-44942f474a80
-- title:
--   The rank-one operator $|v\rangle\langle v|$
-- statement:
--   For a vector $|v\rangle$ with coordinates $v_i$, the operator $|v\rangle\langle v|$ is the matrix with entries
--   $$\big(|v\rangle\langle v|\big)_{ij} = v_i\,\overline{v_j}.$$
--   For a unit vector it is the density operator of the pure state $|v\rangle$; the paper abbreviates it as $v$ (so $\phi\otimes\eta$ means $|\phi\rangle\langle\phi|\otimes\eta$).
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Notation 9, p.17 (PDF 20)

import Mathlib

namespace CatalystQLB.Query.Supplement

/-- The rank-one operator `|v⟩⟨v|` (Arora, Chakraborty, Cojocaru, Saminathan, Singh,
*Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of
2026-11-03), Notation 9, p.17 (PDF 20): "The pure states `|ψ⟩⟨ψ|, |ϕ⟩⟨ϕ|` are abbreviated as
`ψ, ϕ`"). Its `(i, j)` entry is `vᵢ · conj(vⱼ)`; for a unit vector `v` it is the density operator
of the pure state `|v⟩`. -/
def ketbra {m : Type} (v : m → ℂ) : Matrix m m ℂ :=
  Matrix.of fun i j => v i * star (v j)

end CatalystQLB.Query.Supplement


