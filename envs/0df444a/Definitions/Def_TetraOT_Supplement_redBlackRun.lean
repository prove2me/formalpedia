-- Prove2me | Definitions.Def_TetraOT_Supplement_redBlackRun
-- name    : TetraOT_Supplement_redBlackRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:38:47.050197+00:00
-- url     : https://prove2.me/theorems/d0a0e3c8-116b-4f9d-9f73-78a3d5ed2a44
-- title:
--   One run of the Red-Black Protocol (Fig. 21)
-- statement:
--   The Red-Black Protocol (Fig. 21) runs on a permutation $\rho$ of $\{0,1,2,3\} = \{L0,L1,R0,R1\}$:
--
--   1. Alice receives $(\rho(0),\rho(1))$ and Bob receives $\rho(2)$;
--   2. if Alice's two cards are on the same side ($\{L0,L1\}$ or $\{R0,R1\}$) she announces "reject" and both parties quit;
--   3. otherwise she announces "ok" and outputs $m_0m_1$ from her table (Fig. 22), and Bob outputs $(s, m_s)$ from his table (Fig. 24).
--
--   Alice's only message is ok/reject. Alice's view is her ordered hand; Bob's view is his card together with the ok/reject message. Each party's output is "none" on reject and the table value otherwise.
--
--   This is the real protocol of Theorem 9.1; its transcripts are listed in Fig. 26.
--
--   **Formalization Note** The message is a Boolean ($\texttt{true}$ = "ok"); outputs are optional pairs of Booleans.
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), Figs. 21, 22, 24, 26, pp.10–11 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib
import Definitions.Def_TetraOT_Supplement_redBlackAliceTable
import Definitions.Def_TetraOT_Supplement_redBlackBobTable

set_option autoImplicit false

namespace TetraOT.Supplement

/-- **One run of the Red-Black Protocol** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), Fig. 21, p.10, with Figs. 22 and 24 and the
transcripts of Fig. 26, pp.10–11; p. = PDF page, the PDF has no printed page numbers). Fig. 21:
1. Randomly sample `ρ ← S₄`.
2. Deal `(ρ(0), ρ(1))` to Alice, `ρ(2)` to Bob.
3. If Alice receives `(L0, L1)` or `(R0, R1)`, she sends reject and quits.
4. Alice determines `m₀, m₁` according to her table (Fig. 22).
5. Bob determines `s, m_s` according to his table (Fig. 24).

`redBlackRun ρ = (ok, Alice's output, Bob's output)`, where `ok` is Alice's only message (`true` = "ok",
`false` = "rej", Fig. 26), Alice's output is `some (m₀, m₁)` or `none` on reject, and Bob's output is
`some (s, m_s)` or `none` on reject.

**Formalization Note.** `ρ : Equiv.Perm (Fin 4)` with `ρ i` the card dealt to position `i`, as in the
published `TetraOT.tetrahedralRun`; cards `0, 1, 2, 3` are `L0, L1, R0, R1` (Fig. 20). On reject both
parties quit, which is encoded by the output `none` for both. -/
def redBlackRun (ρ : Equiv.Perm (Fin 4)) : Bool × Option (Bool × Bool) × Option (Bool × Bool) :=
  ((redBlackAliceTable (ρ 0) (ρ 1)).isSome, redBlackAliceTable (ρ 0) (ρ 1),
    if (redBlackAliceTable (ρ 0) (ρ 1)).isSome then some (redBlackBobTable (ρ 2)) else none)

/-- Alice's public message: `true` = "ok", `false` = "rej". -/
def rbAccept (ρ : Equiv.Perm (Fin 4)) : Bool := (redBlackRun ρ).1

/-- Alice's output: `some (m₀, m₁)` on acceptance, `none` on reject. -/
def rbAliceOut (ρ : Equiv.Perm (Fin 4)) : Option (Bool × Bool) := (redBlackRun ρ).2.1

/-- Bob's output: `some (s, m_s)` on acceptance, `none` on reject. -/
def rbBobOut (ρ : Equiv.Perm (Fin 4)) : Option (Bool × Bool) := (redBlackRun ρ).2.2

/-- Alice's view: her ordered hand `(ρ(0), ρ(1))`. She receives no message and is deterministic, so her
message and output are functions of it. -/
def rbViewA (ρ : Equiv.Perm (Fin 4)) : Fin 4 × Fin 4 := (ρ 0, ρ 1)

/-- Bob's view: his card `ρ(2)` and Alice's accept/reject message. -/
def rbViewB (ρ : Equiv.Perm (Fin 4)) : Fin 4 × Bool := (ρ 2, rbAccept ρ)

end TetraOT.Supplement


