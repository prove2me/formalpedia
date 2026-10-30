-- Prove2me | Definitions.Def_JailletLu_mi
-- name    : JailletLu_mi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:21:46.072353+00:00
-- url     : https://prove2.me/theorems/dd09bca9-7323-417e-8996-a47e1baceeb3
-- title:
--   List numbers $m^i_{b,c}$
-- statement:
--   For a type $i$ and $b,c\in A^*$, $m^i_{b,c}$ is the expected number of requests of type $i$ whose list is $\langle b,c\rangle$: $b$ first ($x\in J_i(b)$) and $c$ second ($\mathrm{rot}_{r_i}(x)\in J_i(c)$), with $x$ uniform on $[0,r_i]$. With $n$ requests, each of type $i$ with probability $r_i/n$, this equals the Lebesgue measure
--   $$
--   m^i_{b,c}=\big|\{x\in[0,r_i]:\ x\in J_i(b),\ \mathrm{rot}_{r_i}(x)\in J_i(c)\}\big|.
--   $$
--   The list $\langle b,b\rangle$ is the singleton $\langle b\rangle$.
--
--   **Formalization Note** The measure is Lebesgue measure on $\mathbb R$ converted to a real number; the set lies in $[0,r_i]$, so it is finite. The probability space is not built.
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.3, p. 13

import Mathlib
import Definitions.Def_JailletLu_J
import Definitions.Def_JailletLu_rot

namespace JailletLu

/-- **The list numbers `m^i_{b,c}`.**
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.3, p. 13: "Let m^i_{a_j,a_k} be the expected number of requests for impressions of type i
and corresponding lists given by ⟨a_j, a_k⟩."

`mi r f ord i b c` is the Lebesgue measure of the set of `x ∈ [0, r_i]` with `x ∈ J_i(b)` (so `b`
is first in the list) and `rot(x) ∈ J_i(c)` (so `c` is second). The list `⟨b, b⟩` is the
singleton `⟨b⟩`.

**Formalization Note.** With `n` requests, each of type `i` with probability `r_i/n`, and `x`
uniform on `[0, r_i]`, the expected number is `n · (r_i/n) · |{x …}|/r_i = |{x …}|`, the Lebesgue
measure; the probability space is not built. The set lies in `[0, r_i]`, so its measure is finite
and `toReal` loses nothing. -/
noncomputable def mi {A I : Type*} [Fintype A] [DecidableEq A] (r : I → ℝ) (f : A → I → ℝ)
    (ord : I → List (Option A)) (i : I) (b c : Option A) : ℝ :=
  (MeasureTheory.volume {x : ℝ | x ∈ Set.Icc 0 (r i) ∧ x ∈ J r f ord i b ∧
      rot (r i) x ∈ J r f ord i c}).toReal

end JailletLu


