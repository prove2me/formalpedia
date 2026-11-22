-- Prove2me | Definitions.Def_Formalism_FockGram_StatementSymPos
-- name    : Formalism_FockGram_StatementSymPos
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:50.094212+00:00
-- url     : https://prove2.me/theorems/43a173b9-ddc6-486c-8e3f-31d636880a5a
-- title:
--   Statement Sym Pos
-- statement:
--   Definitions and structural lemmas for Statement Sym Pos, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FockGram/StatementSymPos.lean

import Definitions.Def_Formalism_FockGram_StatementFock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
noncomputable section
namespace Formalism.E
def SymGramPosSemidef : Prop :=
  ∀ (𝕜 σ : Type) [RCLike 𝕜] [Fintype σ] [DecidableEq σ] (a : ℕ) (G : Matrix σ σ 𝕜),
    G.PosSemidef → (symGram a G).PosSemidef
def SymGramPosDef : Prop :=
  ∀ (𝕜 σ : Type) [RCLike 𝕜] [Fintype σ] [DecidableEq σ] (a : ℕ) (G : Matrix σ σ 𝕜),
    G.PosDef → (symGram a G).PosDef
end Formalism.E


