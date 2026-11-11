-- Prove2me | Definitions.Def_BlottoFPTAS_Main_LearnIO
-- name    : BlottoFPTAS_Main_LearnIO
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:42:29.380808+00:00
-- url     : https://prove2.me/theorems/2cab7e22-3bb6-4047-9813-afa317f47776
-- title:
--   Input and output layouts of the learning computation of Lemma 5.6
-- statement:
--   The learning computation receives the reduced game: $m$, $a$ ($e=2^{-a}$), the integer weights $\hat w_1,\dots,\hat w_m$ of the second rounding ($\hat v_j=\hat w_j/Q_v$, $Q_v=\sum_j\hat w_j$), the auxiliary ratio $\rho$, and a flag for the player's budget $c\in\{1,\rho\}$. In the real-RAM model the input is the list of these numbers and the output list of $Tm$ reals is read as $T$ allocations (allocation $t$ is entries $tm,\dots,tm+m-1$); in the finite-bit model the input is their self-delimiting binary code and the output string is decoded as $Tm$ rationals read in the same order.
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 35, Lemma 5.6; p. 56, App. C.2

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_RealRAM
import Definitions.Def_BlottoFPTAS_Main_BitRAM

namespace BlottoFPTAS.Main

/-!
# Input and output layouts of the learning computation (Lemma 5.6, p. 35)

The computation of §5.2 receives the reduced game: the number `m` of battlefields, `a`
(`e = 2^{-a}`), the integer weights `ŵ_1, …, ŵ_m` of the second rounding (the values are
`v̂_j = ŵ_j / Q_v`, `Q_v = ∑_j ŵ_j`), the auxiliary ratio `ρ`, and the player's budget `c ∈ {1, ρ}`
as a flag (`false` for `c = 1`, `true` for `c = ρ`).

* Real RAM: input list `m, a, ŵ_1, …, ŵ_m, ρ, flag`; the output list of `T m` reals is read as
  `T` allocations, allocation `t` being entries `t m, …, t m + m − 1` (`realAllocs`).
* Finite-bit model: input `encNat m ++ encNat a ++ encNat ŵ_1 ++ ⋯ ++ encNat ŵ_m ++ encRat ρ ++
  [flag]`; the output string is the code of `T m` rationals, read in the same order
  (`bitAllocs`; `none` if it does not decode).
-/

/-- The real-RAM input of the learning computation. -/
noncomputable def learnRealInput (m a : ℕ) (wh : Fin m → ℕ) (ρ : ℚ) (flag : Bool) : List ℝ :=
  [(m : ℝ), (a : ℝ)] ++ (List.ofFn fun j => (wh j : ℝ)) ++ [(ρ : ℝ), if flag then 1 else 0]

/-- The binary input of the learning computation. -/
def learnBitInput (m a : ℕ) (wh : Fin m → ℕ) (ρ : ℚ) (flag : Bool) : List Bool :=
  BitRAM.encNat m ++ BitRAM.encNat a ++ (List.ofFn fun j => BitRAM.encNat (wh j)).flatten ++
    BitRAM.encRat ρ ++ [flag]

/-- The `T` allocations read from a real output list. -/
def realAllocs (m T : ℕ) (out : List ℝ) : List (Fin m → ℝ) :=
  List.ofFn fun t : Fin T => fun j : Fin m => out.getD (t.val * m + j.val) 0

/-- The `T` allocations read from a binary output string (`none` if it is not the code of
exactly `T m` rationals). -/
noncomputable def bitAllocs (m T : ℕ) (bits : List Bool) : Option (List (Fin m → ℝ)) :=
  (BitRAM.decodeAlloc (T * m) bits).map fun y =>
    List.ofFn fun t : Fin T => fun j : Fin m => (((List.ofFn y).getD (t.val * m + j.val) 0 : ℚ) : ℝ)

end BlottoFPTAS.Main


