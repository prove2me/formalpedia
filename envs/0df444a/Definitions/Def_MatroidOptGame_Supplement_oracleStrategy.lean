-- Prove2me | Definitions.Def_MatroidOptGame_Supplement_oracleStrategy
-- name    : MatroidOptGame_Supplement_oracleStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:54:01.257968+00:00
-- url     : https://prove2.me/theorems/767d895f-e98b-4354-8803-7a4c8682f44b
-- title:
--   Strategy induced by an oracle player on a hidden matroid
-- statement:
--   Let $\widetilde M$ be a matroid on $E=\{0,\dots,m-1\}$ and $P$ a deterministic oracle player with budget $s$ moving at positions of parity $p$. The **induced strategy** plays, at a history $h$ of parity $p$, the move $P$ makes in its current turn, after rebuilding its transcript from its earlier turns, with every query $F$ answered by the independence oracle of $\widetilde M$ ($1$ iff $F$ is independent). At histories of the other parity it plays nothing. The player depends on $\widetilde M$ only through these answers.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2, Theorems 11 and 14, pp.13, 15; the oracle O of p.4

import Mathlib
import Definitions.Def_MatroidOptGame_Strategy
import Definitions.Def_MatroidOptGame_indepOracle
import Definitions.Def_MatroidOptGame_Supplement_runTurn
import Definitions.Def_MatroidOptGame_Supplement_transcriptBefore

namespace MatroidOptGame.Supplement

/-- The strategy induced by the deterministic oracle player `P` with query budget `s` when the
hidden matroid is `M`: at a history `h` of its parity `p` (`0` for MAX, `1` for MIN) it rebuilds
its transcript from the earlier turns and plays out its current turn, every query answered by the
independence oracle of `M`. At histories of the other parity it returns `none` (they are not its
turns).
Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2, Theorems 11 and 14, pp.13, 15; the oracle `O(F) = true iff F ∈ I` of p.4.
**Formalization Note.** The player reaches `M` only through `MatroidOptGame.indepOracle M`
(`1` = independent, `0` = dependent). -/
noncomputable def oracleStrategy {m : ℕ} (M : Matroid (Fin m))
    (P : OraclePlayer (Fin m)) (p s : ℕ) : Strategy (Fin m) :=
  fun h =>
    if h.length % 2 = p then
      (runTurn (indepOracle M) P h (s + 1)
        (transcriptBefore (indepOracle M) P p s h)).2
    else none

end MatroidOptGame.Supplement


