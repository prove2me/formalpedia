-- Prove2me | Definitions.Def_TFNPRom_Supplement_LonelyReduction
-- name    : TFNPRom_Supplement_LonelyReduction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:27:58.38647+00:00
-- url     : https://prove2.me/theorems/e8b676cd-fbcc-404e-8f4d-65432b117b21
-- title:
--   Zero-error black-box reduction to Lonely
-- statement:
--   A **zero-error black-box reduction** of depth at most $d$ from a search problem $F\subseteq\Sigma^\iota\times O$ to Lonely on $2M+1$ nodes consists of decision trees over the input $u$ computing the cells $\mathrm{Mate}_j$ of a Lonely instance $f(u)$, and for every node $i$ a decoding tree $g_i$ over $u$ with output in $O$, all of depth at most $d$, such that for every input $u$ and every Lonely solution $i$ of $f(u)$, $g_i(u)$ is a solution of $u$.
--
--   Its complexity is $d+\log_2(2M+1)$. This is a public reduction with $\omega(u)=u$ and error $0$, and defines membership in PPA.
--
--   **Formalization Note** The same shape as the published `TFNPRom.EoLReduction`, with Lonely in place of End-of-Line.
-- source:
--   Fleming, Göös, Guan, Korten, Mitropolsky, Pitassi, Riazanov, Sokolov, Yang, Yuan, TFNP in the Random Oracle Model, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), §5, p.28; App. A, p.41

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_TFNPRom_Supplement_lonelySol

namespace TFNPRom.Supplement

/-- A zero-error black-box (public) reduction of depth at most `d` from a search problem
`rel ⊆ α^ι × O` to Lonely on `2M + 1` nodes (Fleming et al., *TFNP in the Random Oracle Model*, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), §5, p.28: "if `err(ω, f, g) = 0`, then we
recover the standard definition of a black-box reduction"; App. A, p.41: "`F′ ∈ C` iff there exists
a zero-error public reduction"). It consists of
1. decision trees `mateT j` over `u` computing the cells `Mate_j` of a Lonely instance `f(u)`;
2. for every node `i` a decision tree `dec i` over `u` computing a candidate solution `g_i(u) ∈ O`;
3. every tree makes at most `d` queries on every input;
4. zero error: for every input `u` and every Lonely solution `i` of `f(u)`, `g_i(u)` is a solution
   of `u`.

**Formalization Note** The same shape as the published `TFNPRom.EoLReduction`, with Lonely in place
of End-of-Line; the instance distribution is the identity. The Lonely instance has `m = 2M + 1`
cells, so the complexity is `d + log₂(2M + 1)` (used in `InPPAdt`). -/
structure LonelyReduction {ι α O : Type} (rel : (ι → α) → O → Prop) (M d : ℕ) where
  /-- the trees computing `Mate_j` -/
  mateT : Fin (2 * M + 1) → QAlgorithms.DecisionTree ι α (Fin (2 * M + 1))
  /-- the decoding trees `g_i` -/
  dec : Fin (2 * M + 1) → QAlgorithms.DecisionTree ι α O
  /-- depth bound for `Mate` -/
  mate_depth : ∀ j, (mateT j).MakesAtMost d
  /-- depth bound for the decoders -/
  dec_depth : ∀ i, (dec i).MakesAtMost d
  /-- zero error on every input -/
  correct : ∀ (u : ι → α) (i : Fin (2 * M + 1)),
    lonelySol M (fun j => (mateT j).eval u) i → rel u ((dec i).eval u)

end TFNPRom.Supplement


