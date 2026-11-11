-- Prove2me | Definitions.Def_BlottoFPTAS_Main_Sizes
-- name    : BlottoFPTAS_Main_Sizes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:40:48.643201+00:00
-- url     : https://prove2.me/theorems/fefe79a1-d667-41ed-a490-8a5ff58fe475
-- title:
--   Binary input lengths L0 and E, n* = min{n, 1/ε}, and pow2ceil
-- statement:
--   A rational $p/q$ in lowest terms has binary length $\mathrm{size}(p/q)=\mathrm{size}|p|+\mathrm{size}(q)+1$, where $\mathrm{size}(k)$ is the number of binary digits of $k$ (`Nat.size`, with $\mathrm{size}(0)=0$) and the extra bit is the sign. For a game instance, $L_0=\sum_i\mathrm{size}(v_i)+\mathrm{size}(b)$ is the binary length of the game input, and $E=\mathrm{size}(\varepsilon)$ that of the approximation parameter; since every size is at least $2$, $L_0\ge n$. The quantity $n_*=\min\{n,1/\varepsilon\}$ is a real number. $\mathrm{pow2ceil}(a)$ is the least power of two that is at least $a$ (for natural $a$; $\mathrm{pow2ceil}(0)=1$).
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 2, p. 27, p. 49 (L0, E, n*), p. 55 (pow2ceil)

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_Game

open scoped BigOperators

namespace BlottoFPTAS.Main

/-!
# Input sizes `L0`, `E`, `n*` and `pow2ceil` (p. 2, p. 27, p. 49, p. 55)

* `ratSize q = size |p| + size q + 1` for the reduced fraction `q = p/q` (`Nat.size` is the
  number of binary digits, `Nat.size 0 = 0`); the extra bit is the sign.
* `L0 = ∑_i ratSize v_i + ratSize b`, the binary length of the game input; `E = ratSize ε`.
  Every `ratSize` is at least `2`, so `L0 ≥ n`.
* `nStar n ε = min{n, 1/ε}`, a real number (p. 27).
* `pow2ceil a` is the least power of two that is at least `a` (p. 55), for natural `a`
  (`pow2ceil 0 = pow2ceil 1 = 1`).
-/

/-- The binary encoding length of a rational in lowest terms: numerator magnitude, denominator,
and one sign bit. -/
def ratSize (q : ℚ) : ℕ :=
  Nat.size q.num.natAbs + Nat.size q.den + 1

/-- `L0`, the binary length of the game input `(v_1, …, v_n, b)` (p. 27, p. 49). -/
def L0 (I : Instance) : ℕ :=
  (∑ i, ratSize (I.v i)) + ratSize I.b

/-- `E`, the binary length of the approximation parameter `ε` (p. 27, p. 49). -/
def Elen (ε : ℚ) : ℕ :=
  ratSize ε

/-- `n* = min{n, 1/ε}` (p. 27). -/
noncomputable def nStar (n : ℕ) (ε : ℝ) : ℝ :=
  min (n : ℝ) (1 / ε)

/-- `pow2ceil a`, the least power of two that is at least `a` (p. 55). -/
def pow2ceil (a : ℕ) : ℕ :=
  2 ^ Nat.clog 2 a

end BlottoFPTAS.Main


