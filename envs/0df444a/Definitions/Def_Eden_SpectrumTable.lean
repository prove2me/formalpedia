-- Prove2me | Definitions.Def_Eden_SpectrumTable
-- name    : Eden_SpectrumTable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:47:19.385243+00:00
-- url     : https://prove2.me/theorems/3abcb030-0d52-5ad4-a1f5-b60f25970f41
-- title:
--   Spectrum Table
-- statement:
--   Definitions and structural lemmas for Spectrum Table, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SpectrumTable.lean

import Definitions.Def_Eden_KaplanYorke
set_option autoImplicit true
noncomputable section
namespace Eden
def radiusPairSpectrum (c s₁ s₂ : ℝ) : Fin 5 → ℝ :=
  ![radialRate s₁, tangentialRate s₁, radialRate s₂, tangentialRate s₂, -c]
end Eden


