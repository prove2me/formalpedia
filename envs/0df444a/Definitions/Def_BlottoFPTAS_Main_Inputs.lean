-- Prove2me | Definitions.Def_BlottoFPTAS_Main_Inputs
-- name    : BlottoFPTAS_Main_Inputs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:42:28.526887+00:00
-- url     : https://prove2.me/theorems/1160ea7f-ff8b-4b4d-a58f-683d4cd48ccb
-- title:
--   Input layouts of the construction programs in both models
-- statement:
--   The construction program is run once per player; the player ($A$ or $B$) is the last input entry, and the output of the run is that player's strategy description. In the real-RAM model the input is the list of reals $n,v_1,\dots,v_n,b,\varepsilon,\text{player}$; in the finite-bit model it is the bit string $\mathrm{enc}(n)\,\mathrm{enc}(v_1)\cdots\mathrm{enc}(v_n)\,\mathrm{enc}(b)\,\mathrm{enc}(\varepsilon)\,\text{player}$ in the self-delimiting code, of length $O(L_0+E)$. A sampler program receives only a description, never the game data.
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 6, §2.2 (input and output); p. 49, App. B

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_Game
import Definitions.Def_BlottoFPTAS_Main_RealRAM
import Definitions.Def_BlottoFPTAS_Main_BitRAM

namespace BlottoFPTAS.Main

/-!
# Input layouts of the construction programs (§2.2, p. 6; App. B, p. 49)

The construction program is run once per player; the player is the last input entry (`false`/`0`
for A, `true`/`1` for B), and the run's output is that player's strategy description. The
construction bounds of Theorem 5.1 are stated for the two runs together.

* Real RAM: the list of reals `n, v_1, …, v_n, b, ε, player`.
* Finite-bit model: the bit string `encNat n ++ encRat v_1 ++ ⋯ ++ encRat v_n ++ encRat b ++
  encRat ε ++ [player]`. Its length is at most a constant times `L0 + E` (every `ratSize` is at
  least `2`, so `L0 ≥ n`, and `Nat.size n ≤ n`).

A sampler program receives only a description: its input is the description itself, never the
game data.
-/

/-- The real-RAM input of the construction program for player `player` (`false` = A,
`true` = B). -/
noncomputable def realInput (I : Instance) (ε : ℚ) (player : Bool) : List ℝ :=
  [(I.n : ℝ)] ++ (List.ofFn fun i => (I.v i : ℝ)) ++
    [(I.b : ℝ), (ε : ℝ), if player then 1 else 0]

/-- The binary input of the construction program for player `player` (`false` = A,
`true` = B). -/
def bitInput (I : Instance) (ε : ℚ) (player : Bool) : List Bool :=
  BitRAM.encNat I.n ++ BitRAM.encRats (List.ofFn I.v) ++ BitRAM.encRat I.b ++
    BitRAM.encRat ε ++ [player]

end BlottoFPTAS.Main


