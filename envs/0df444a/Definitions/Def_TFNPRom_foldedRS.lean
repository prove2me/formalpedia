-- Prove2me | Definitions.Def_TFNPRom_foldedRS
-- name    : TFNPRom_foldedRS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:00:08.515971+00:00
-- url     : https://prove2.me/theorems/bccdfd00-391d-4cf1-8e64-b6b58d3386b0
-- title:
--   The folded Reed-Solomon code
-- statement:
--   $\mathrm{FoldedRS}^m_{F,\gamma,d}$ is the image of $\mathrm{ReedSolomon}_{F,\gamma,d}$ under folding into blocks of length $m$. It is a code of block length $n/m$ over the alphabet $\Gamma=F^m$.
-- source:
--   Fleming, Göös, Guan, Korten, Mitropolsky, Pitassi, Riazanov, Sokolov, Yang, Yuan, TFNP in the Random Oracle Model, arXiv:2611.05308 (held version, sha256 e11eb9c3…), §3.3, p.18

import Mathlib
import Definitions.Def_TFNPRom_reedSolomon
import Definitions.Def_TFNPRom_foldBlocks

namespace TFNPRom

/-- The folded Reed-Solomon code `FoldedRS^m_{F,γ,d}` (Fleming et al., *TFNP in the Random Oracle Model*, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), §3.3, p.18), a subset of `Γ^{n/m}` with `Γ
= F^m`: the image of `ReedSolomon_{F,γ,d}` under folding into blocks of length `m`. -/
noncomputable def foldedRS {F : Type} [Field F] [Fintype F] [DecidableEq F] (γ : F) (m d : ℕ) :
    Finset (Fin ((Fintype.card F - 1) / m) → Fin m → F) :=
  (reedSolomon γ d).image (foldBlocks m)

end TFNPRom


