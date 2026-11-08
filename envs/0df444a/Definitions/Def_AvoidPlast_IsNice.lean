-- Prove2me | Definitions.Def_AvoidPlast_IsNice
-- name    : AvoidPlast_IsNice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:47:34.045132+00:00
-- url     : https://prove2.me/theorems/4596a890-1e86-455a-ac5d-3fa8781c5fd1
-- title:
--   Nice functions
-- statement:
--   A function $f:\mathbb N\to\mathbb N$ is **nice** if there is a deterministic algorithm that given $n$ outputs $f(n)$ in time $\mathrm{polylog}(n,f(n))$: here a machine with $n$ on its input tape in binary, writing $f(n)$ in binary, within $a(\log_2(n+f(n)+2)+1)^a$ steps.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 3, p.14

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_lg

namespace AvoidPlast

/-- A *nice* function (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §3, p.14): "there is a deterministic algorithm that given `n` as
input, outputs `f(n)` in time `polylog(n, f(n))`". Here `n` is on the input tape in binary and the
algorithm writes `f(n)` in binary. -/
def IsNice (f : ℕ → ℕ) : Prop :=
  ∃ (M : Machine 1) (a : ℕ), ∀ n : ℕ,
    HaltsWithin M ![Nat.bits n] ⌈(a : ℝ) * (lg (n + f n) + 1) ^ a⌉₊ ∧
      output M ![Nat.bits n] = Nat.bits (f n)

end AvoidPlast


