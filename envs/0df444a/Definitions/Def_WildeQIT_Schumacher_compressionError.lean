-- Prove2me | Definitions.Def_WildeQIT_Schumacher_compressionError
-- name    : WildeQIT_Schumacher_compressionError
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:48.625743+00:00
-- url     : https://prove2.me/theorems/cd852712-c515-4145-836b-f8b1538ce93b
-- title:
--   Error of a quantum compression protocol, eq. (18.5)
-- statement:
--   The error of a quantum compression protocol $(W, \mathcal E_{A^n\to W}, \mathcal D_{W\to\hat A^n})$ for the source $\rho$ is the normalized trace distance between the purified i.i.d. source state and its compressed and decompressed version:
--
--   $$
--   \frac12\left\| (\phi^\rho_{RA})^{\otimes n} - (\mathcal D_{W\to\hat A^n}\circ\mathcal E_{A^n\to W})\big((\phi^\rho_{RA})^{\otimes n}\big) \right\|_1 ,
--   $$
--
--   where the channels act on $A^n$ (then $W$) only and $\|\cdot\|_1$ is the trace norm.
--
--   **Formalization Note** $\|\cdot\|_1$ is the published `WildeQIT.traceNorm`; the purified state is `purifiedSourceState ρ n`, and `idTensorApply` applies a channel to the second tensor factor.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §18.1, eq. (18.5), p. 523

import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_Schumacher_CompressionCode
import Definitions.Def_WildeQIT_Schumacher_purifiedSourceState
import Definitions.Def_WildeQIT_Schumacher_idTensorApply

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §18.1, eq. (18.5), p. 523.
-/

namespace WildeQIT.Schumacher

/-- **Error of a quantum compression protocol** (Wilde, arXiv:1106.1445v8, eq. (18.5), p. 523):
the normalized trace distance between the purified i.i.d. source state and its compressed and
decompressed version,
`½ ‖(ϕ^ρ_{RA})^{⊗n} − (D_{W→Âⁿ} ∘ E_{Aⁿ→W})((ϕ^ρ_{RA})^{⊗n})‖₁`,
where the channels act on `Aⁿ` only.

**Formalization Note.** `‖·‖₁` is the published `WildeQIT.traceNorm`; the purified state is
`purifiedSourceState ρ n` (canonical purification, systems grouped `Rⁿ Aⁿ`), and
`idTensorApply` applies a channel to the second system. -/
noncomputable def compressionError {a : Type} [Fintype a] [DecidableEq a] {n : ℕ}
    (ρ : Matrix a a ℂ) (C : CompressionCode a n) : ℝ :=
  (1 / 2) * WildeQIT.traceNorm (purifiedSourceState ρ n -
    idTensorApply C.dec (idTensorApply C.enc (purifiedSourceState ρ n)))

end WildeQIT.Schumacher


