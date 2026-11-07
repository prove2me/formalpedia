-- Prove2me | Definitions.Def_MMSDelta2_instCode
-- name    : MMSDelta2_instCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:59.684739+00:00
-- url     : https://prove2.me/theorems/0bee93f4-4b68-4a78-906f-41a3dc23a0c5
-- title:
--   Binary codes of naturals, rationals and additive instances
-- statement:
--   The paper represents instances explicitly, with rational values written in binary; it fixes no particular encoding. This item fixes one.
--
--   1. A natural number $k$ is encoded by its binary digits, least significant first, with every bit written twice, followed by the end marker $01$. This code is prefix-free and has length $2\lceil\log_2(k+1)\rceil+2$.
--   2. A rational number $q$ is encoded by the code of its sign bit ($1$ if $q<0$, else $0$), then of $|\mathrm{num}(q)|$, then of $\mathrm{den}(q)$, where $q=\mathrm{num}(q)/\mathrm{den}(q)$ is in lowest terms.
--   3. An additive instance with $n$ agents, $m$ goods and item values $v_i(g)\in\mathbb Q$ is encoded by the code of $n$, the code of $m$, and then the codes of the values $v_i(g)$, agent by agent and, for each agent, good by good.
--
--   The code is injective and can be decoded in polynomial time; any other encoding with these two properties would serve equally well.
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), §4, pp.11–12 (PDF pp.13–14): explicit representation; rational values, p.11

import Mathlib

namespace MMSDelta2

/-!
# Binary codes of naturals, rationals and additive instances

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…), §4, pp.11–12 (PDF pp.13–14): "In our inputs,
the valuations are represented explicitly"; values are rationals (`v_i : 2^M → ℚ`, p.11).

**Formalization Note.** The paper fixes no encoding. A natural `k` is written by its binary digits
(least significant first), every bit doubled, followed by the end marker `01`: a prefix-free code
of length `2⌈log₂(k+1)⌉ + 2`. A rational `q` is the code of its sign bit, of `|num q|` and of
`den q`. An additive instance `(n, m, v)` is the code of `n`, of `m`, then of the values `v i g`
agent by agent and, for each agent, good by good. The code is injective and decodable in polynomial
time; any other such code is equally faithful.
-/

/-- The prefix-free binary code of a natural number: doubled binary digits, then `01`. -/
def natCode (k : ℕ) : List Bool :=
  (Nat.digits 2 k).flatMap (fun d => [decide (d = 1), decide (d = 1)]) ++ [false, true]

/-- The binary code of a rational number: sign bit, `|numerator|`, denominator. -/
def ratCode (q : ℚ) : List Bool :=
  natCode (if q < 0 then 1 else 0) ++ natCode q.num.natAbs ++ natCode q.den

/-- The binary code of an additive instance with `n` agents, `m` goods and item values `v i g`. -/
def instCode (n m : ℕ) (v : Fin n → Fin m → ℚ) : List Bool :=
  natCode n ++ natCode m ++
    (List.ofFn fun i => (List.ofFn fun g => ratCode (v i g)).flatten).flatten

end MMSDelta2


