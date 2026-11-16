-- Prove2me | Definitions.Def_VAS5Reach_Supplement_reachLang
-- name    : VAS5Reach_Supplement_reachLang
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:47:12.602654+00:00
-- url     : https://prove2.me/theorems/0002d0c1-877e-4171-9a05-2a4c83ec427a
-- title:
--   Reachability in $D$-VAS as a language under binary and unary encoding
-- statement:
--   The **reachability problem for $D$-VAS** asks, given a finite set $T\subseteq\mathbb Z^D$ of transitions and configurations $s,t\in\mathbb N^D$, whether $t$ is reachable from $s$ by a run of the VAS. As a language over $\{0,1\}$ it is the set of codes of yes-instances.
--
--   An instance is coded as a sequence of self-delimiting **fields**: every data bit $b$ is written as the pair $0b$ and every field is closed by the separator $10$. The code lists one field for every coordinate of every listed transition, then the $D$ coordinates of $s$, then those of $t$.
--
--   1. Under **binary encoding** an integer $z$ is written as a sign bit ($1$ iff $z<0$) followed by the binary digits of $|z|$, and a natural number by its binary digits. The code length is polynomially related to
--   $$\mathrm{SIZE}_{\mathrm{BIN}}(V,s,t)=1+d|T|\lceil\log_2(\|T\|+2)\rceil+d\lceil\log_2(\|s\|+2)\rceil+d\lceil\log_2(\|t\|+2)\rceil .$$
--   2. Under **unary encoding** $z$ is written as a sign bit followed by $|z|$ ones, so the code length is polynomially related to the unary size $\mathrm{SIZE}(V,s,t)$.
--
--   A word is in the language iff it is the code of an instance $(T,s,t)$ with $s\xrightarrow{*}t$; words that code no instance are not in it. These are the languages of Theorems 1.1 and 1.5.
--
--   **Formalization Note** The transitions are given as a list $L$ (the VAS is `L.toFinset`; a listed transition may repeat). The code is injective in $(L,s,t)$ for $D\ge1$, since fields parse uniquely and there are $D|L|+2D$ of them.
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), §3 'Size and Reachability Problems', p.14 (PDF p.16); SIZE_BIN, App. A.1, p.44 (PDF p.46); Theorem 1.1, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_VAS5Reach_IsVASRun

namespace VAS5Reach.Supplement

open VAS5Reach

/-- A self-delimiting field: every data bit `b` is written as the pair `0b`, and the field is
closed by the separator pair `10`. Concatenations of fields therefore parse uniquely. -/
def fieldCode (bs : List Bool) : List Bool :=
  (bs.flatMap fun b => [false, b]) ++ [true, false]

/-- Binary code of a natural number: its binary digits, least significant first
(`Nat.bits`, empty for `0`). -/
def binNat (n : ℕ) : List Bool := Nat.bits n

/-- Binary code of an integer: a sign bit (`true` iff negative) followed by the binary digits of
its absolute value. -/
def binInt (z : ℤ) : List Bool := decide (z < 0) :: Nat.bits z.natAbs

/-- Unary code of a natural number `n`: `n` ones. -/
def unNat (n : ℕ) : List Bool := List.replicate n true

/-- Unary code of an integer `z`: a sign bit (`true` iff negative) followed by `|z|` ones. -/
def unInt (z : ℤ) : List Bool := decide (z < 0) :: List.replicate z.natAbs true

/-- The encoding of a `D`-VAS reachability instance `(V, s, t)` whose transitions are listed as
`L`: one field per coordinate of every listed transition, then the `D` coordinates of `s`, then
the `D` coordinates of `t`, each number written with `encZ` (integers) or `encN` (naturals). -/
def encodeInstance {D : ℕ} (encZ : ℤ → List Bool) (encN : ℕ → List Bool)
    (L : List (Fin D → ℤ)) (s t : Fin D → ℕ) : List Bool :=
  (L.flatMap fun a => (List.finRange D).flatMap fun i => fieldCode (encZ (a i))) ++
    ((List.finRange D).flatMap fun i => fieldCode (encN (s i))) ++
    ((List.finRange D).flatMap fun i => fieldCode (encN (t i)))

/-- The reachability problem for `D`-VAS as a language over `{0,1}` (W. Chen, B. Fu, Y. Fu,
*Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete*, arXiv:2610.40012,
held version, sha256 a74d76f9…, §3 "Size and Reachability Problems", printed p. 14, PDF p. 16:
"Input: A VASS (V, s, t). Question: Does s −∗→ t hold in V?"; a `d`-VAS is a finite `T ⊆ ℤ^d`,
p. 14). A word is in the language iff it is the encoding of an instance `(T, s, t)` — with `T`
listed as `L` — such that `t` is reachable from `s` (`VASReach`). Words that encode no instance
are not in the language.

**Formalization Note** The list `L` may repeat a transition (the instance's transition set is
`L.toFinset`); the encoding is injective in `(L, s, t)` for `D ≥ 1`, since fields parse uniquely
and the number of fields is `D·|L| + 2D`. -/
def reachLang (D : ℕ) (encZ : ℤ → List Bool) (encN : ℕ → List Bool) : Set (List Bool) :=
  {w | ∃ (L : List (Fin D → ℤ)) (s t : Fin D → ℕ),
    w = encodeInstance encZ encN L s t ∧ VASReach L.toFinset s t}

/-- `D`-VAS reachability **under binary encoding**: every integer is written in binary with a sign
bit, so the length of the code of `(V, s, t)` is `Θ(Σ log(|n| + 2))` over its numbers, polynomially
related to `SIZE_BIN(V, s, t) := 1 + d|T|⌈log₂(∥T∥ + 2)⌉ + d⌈log₂(∥s∥ + 2)⌉ + d⌈log₂(∥t∥ + 2)⌉`
(arXiv:2610.40012, App. A.1, printed p. 44, PDF p. 46). -/
def reachLangBin (D : ℕ) : Set (List Bool) := reachLang D binInt binNat

/-- `D`-VAS reachability **under unary encoding**: every integer `n` is written as a sign bit and
`|n|` ones, so the length of the code is polynomially related to the unary size `SIZE(V, s, t)`
(arXiv:2610.40012, §3, printed p. 14, PDF p. 16). -/
def reachLangUnary (D : ℕ) : Set (List Bool) := reachLang D unInt unNat

end VAS5Reach.Supplement


