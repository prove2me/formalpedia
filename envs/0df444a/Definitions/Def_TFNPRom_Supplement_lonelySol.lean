-- Prove2me | Definitions.Def_TFNPRom_Supplement_lonelySol
-- name    : TFNPRom_Supplement_lonelySol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:27:26.287287+00:00
-- url     : https://prove2.me/theorems/ce3b934d-0bb4-4c4c-aaff-d88553e86a80
-- title:
--   Solutions of Lonely (canonical PPA-complete problem)
-- statement:
--   An instance of **Lonely** on $2M+1$ nodes is a map $\mathrm{Mate}\in[2M+1]^{2M+1}$. Its solutions are the nodes $i$ with $\mathrm{Mate}_i=i$ (lonely node) and the nodes $i$ with $\mathrm{Mate}_{\mathrm{Mate}_i}\neq i$ (mismatch).
--
--   Since the number of nodes is odd, $\mathrm{Mate}$ cannot be a fixed-point-free involution, so every instance has a solution. Lonely is the complete problem defining PPA.
--
--   **Formalization Note** Nodes are `Fin (2 * M + 1)`; the paper's $N$ is called $M$ here.
-- source:
--   Fleming, Göös, Guan, Korten, Mitropolsky, Pitassi, Riazanov, Sokolov, Yang, Yuan, TFNP in the Random Oracle Model, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), App. A, p.41

import Mathlib

namespace TFNPRom.Supplement

/-- The solutions of Lonely, the canonical PPA-complete problem (Fleming et al., *TFNP in the Random Oracle Model*, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), App. A, p.41): "We are
given `Mate ∈ [2N + 1]^{2N+1}`; solutions are `i ∈ [2N + 1]` such that `Mate_i = i` (lonely node);
`i ∈ [2N + 1]` such that `Mate_{Mate_i} ≠ i` (mismatch)".

**Formalization Note** The node set `[2M + 1]` is `Fin (2 * M + 1)` (0-based); the paper's `N` is
called `M` here, to keep `N` for the input length of the source problem. -/
def lonelySol (M : ℕ) (mate : Fin (2 * M + 1) → Fin (2 * M + 1)) (i : Fin (2 * M + 1)) : Prop :=
  mate i = i ∨ mate (mate i) ≠ i

end TFNPRom.Supplement


