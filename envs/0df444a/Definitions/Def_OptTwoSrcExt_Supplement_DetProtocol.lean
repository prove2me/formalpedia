-- Prove2me | Definitions.Def_OptTwoSrcExt_Supplement_DetProtocol
-- name    : OptTwoSrcExt_Supplement_DetProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:36:59.370061+00:00
-- url     : https://prove2.me/theorems/aea3ba40-9e5e-4428-bbf8-bd5f9bcd64d6
-- title:
--   Deterministic two-party communication protocols and the whole-word odd-power hash $H_J$
-- statement:
--   1. A **deterministic two-party protocol** between an $X$-side holding $x$ and a $Y$-side holding $y$ runs a fixed number of rounds. Before each round the bits sent so far decide who speaks; the speaker sends one bit computed from its own input and the bits sent so far. The **transcript** $Z(x,y)$ is the list of all bits sent.
--   2. Fix integers $m,t,J\ge1$, fields $F=\mathbb F_{2^m}\subset K=\mathbb F_{2^{4m}}\subset E=\mathbb F_{2^w}$ with $w=4mt$, and a $K$-basis of $E$ with coordinate maps $c_a:E\to K$, $0\le a<t$. The **whole-word odd-power hash** is
--   $$H_J(z;u,v)=\mathrm{Tr}_{K/F}\Big(v\sum_{j=1}^J\sum_{a=0}^{t-1}c_a\big(z^{2j-1}\big)\,u^{(j-1)t+a}\Big)\qquad(z\in E,\ (u,v)\in K^2),\tag{3.62}$$
--   the powers $z^{2j-1}$ being taken in the whole-word field $E$ before the $K$-coordinates.
--
--   These are the objects of Theorem 3.62, which bounds the binary rank of hash characters after a short deterministic exposure.
--
--   **Formalization Note** Messages of several bits and protocols of history-dependent length are protocols of this form after splitting messages into bits and padding with constant bits. In Lean the basis is indexed by $t$ coordinates and the fields are any fields with the stated algebra structures.
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Theorem 3.62, p.67 (PDF p.69); (3.62), p.65 (PDF p.67)

import Mathlib

namespace OptTwoSrcExt.Supplement

/-- **Deterministic two-party communication protocol (bit messages).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Theorem 3.62, printed p.67 (PDF p.69): "Z and then P are
transcripts of deterministic communication between the X and Y sides".

A protocol runs `rounds` rounds. Before each round the history `h` of earlier message bits decides
the speaker (`speaker h = true`: the `X` side); the speaker sends one bit, `msgX h x` or `msgY h y`,
a function of its own input and of `h` only.

**Formalization Note.** Messages of several bits, and protocols whose length depends on the history,
are protocols of this form after splitting messages into bits and padding with constant bits. -/
structure DetProtocol (α β : Type*) where
  rounds : ℕ
  speaker : List Bool → Bool
  msgX : List Bool → α → Bool
  msgY : List Bool → β → Bool

/-- The transcript of the first `r` rounds on inputs `(x, y)`. -/
def DetProtocol.runFor {α β : Type*} (π : DetProtocol α β) (x : α) (y : β) : ℕ → List Bool
  | 0 => []
  | r + 1 =>
    let h := π.runFor x y r
    h ++ [if π.speaker h then π.msgX h x else π.msgY h y]

/-- **The full transcript** `Z(x, y)` of the protocol on inputs `(x, y)`. -/
def DetProtocol.transcript {α β : Type*} (π : DetProtocol α β) (x : α) (y : β) : List Bool :=
  π.runFor x y π.rounds

/-- **The whole-word odd-power hash `H_J(z; u, v)`.**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), (3.62), printed p.65 (PDF p.67): "Fix integers m, t, J ⩾ 1
and fields F = F_{2^m} ⊂ K = F_{2^{4m}} ⊂ E = F_{2^w}, w = 4mt. Fix a K-basis of E, and write
ca : E → K, 0 ⩽ a < t, for its coordinate functions. Put B∗ = Jt and define …
HJ(z; u, v) = Tr_{K/F}(v Σ_{j=1}^J Σ_{a=0}^{t−1} ca(z^{2j−1}) u^{(j−1)t+a})."

`oddPowerHash b J z (u, v)` with `b` a `K`-basis of `E` indexed by `Fin t` (`c_a = b.repr · a`); the
powers `z^{2j−1}` are taken in the whole-word field `E` before the `K`-coordinates. -/
noncomputable def oddPowerHash {F K E : Type*} [Field F] [Field K] [Field E] [Algebra F K]
    [Algebra K E] {t : ℕ} (b : Module.Basis (Fin t) K E) (J : ℕ) (z : E) (s : K × K) : F :=
  Algebra.trace F K (s.2 * ∑ j ∈ Finset.range J, ∑ a : Fin t,
    b.repr (z ^ (2 * (j + 1) - 1)) a * s.1 ^ (j * t + (a : ℕ)))

end OptTwoSrcExt.Supplement


