-- Prove2me | Definitions.Def_TetraOT_tetrahedralRun
-- name    : TetraOT_tetrahedralRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:26:35.488699+00:00
-- url     : https://prove2.me/theorems/5b9c52c3-82a2-4fdf-97c7-a40e7d35f9ae
-- title:
--   One run of the Tetrahedral Protocol on a uniformly shuffled 4-card deck
-- statement:
--   A deck of four distinct cards $0,1,2,3$ is shuffled by a permutation $\rho \in S_4$, written as the sequence $\rho(0)\rho(1)\rho(2)\rho(3)$ of the cards in positions $0,1,2,3$. Alice receives the ordered hand $(\rho(0), \rho(1))$, Bob receives $\rho(2)$, and $\rho(3)$ stays face down.
--
--   1. Alice computes $(M, m_0, m_1) = A(\rho(0), \rho(1))$ from her table (Fig. 2) and sends $M$ to Bob.
--   2. Bob computes $(y_0, y_1) = B(M, \rho(2))$ from his table (Fig. 3), recorded as his selection bit $s$ and the bit $m_s$.
--
--   The **transcript** of the run is $(M, (m_0, m_1), (s, m_s))$; there is one per permutation, 24 in all (Fig. 5). The definition also names the pieces used in the security statements: the message $M$; Alice's output $(m_0, m_1)$; Bob's output $(s, m_s)$; the unselected bit $m_{s'}$ with $s' = 1 - s$; **Alice's view**, her ordered hand $(\rho(0), \rho(1))$; **Bob's view**, the pair $(\rho(2), M)$; and the **deal**, the uniform distribution of $\rho$ on $S_4$.
--
--   These objects are the real-world side of the security statement for the Tetrahedral Protocol (Theorem 4.1).
--
--   **Formalization Note** $\rho$ is an element of `Equiv.Perm (Fin 4)` and `ρ i` is the paper's $\rho(i)$ (for the example of Fig. 4, $\rho = (1,2,3,0)$, Alice holds $(1,2)$ and Bob holds $3$). Alice is deterministic and receives no message, so her message and output are functions of her ordered hand, which is taken as her view. Bits are Booleans with $\texttt{true} = 1$.
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), §3, Fig. 1, Fig. 4, Fig. 5, p.3 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib
import Definitions.Def_TetraOT_Msg
import Definitions.Def_TetraOT_aliceTable
import Definitions.Def_TetraOT_bobTable

set_option autoImplicit false

namespace TetraOT

/-- **One run of the Tetrahedral Protocol** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), §3 and Fig. 1, p.3; p. = PDF page, the PDF
has no printed page numbers). A 4-card deck `0, 1, 2, 3` is shuffled by a permutation `ρ ∈ S₄`.
Alice holds `ρ(0), ρ(1)` and computes `M, m₀, m₁ ← A(ρ(0), ρ(1))` (Fig. 2); she sends `M`. Bob holds
`ρ(2)` and computes `y₀, y₁ ← B(M, ρ(2))` (Fig. 3). The card `ρ(3)` is seen by nobody.
`tetrahedralRun ρ = (M, (m₀, m₁), (s, m_s))` is the transcript: the message, Alice's output and Bob's
output; it is the row of Fig. 5 (p.3) for `ρ`.

**Formalization Note.** `ρ : Equiv.Perm (Fin 4)` and `ρ i` is the paper's `ρ(i)`, the card dealt to
position `i`; the paper writes `ρ` as the sequence `ρ(0)ρ(1)ρ(2)ρ(3)` (Fig. 4: `ρ = (1, 2, 3, 0)`, Alice's
hand `(1, 2)`, Bob's hand `(3)`). Bob's output `(s, m_s)` encodes his `(y₀, y₁)` as in `bobTable`. -/
def tetrahedralRun (ρ : Equiv.Perm (Fin 4)) : Msg × (Bool × Bool) × (Bool × Bool) :=
  ((aliceTable (ρ 0) (ρ 1)).1, (aliceTable (ρ 0) (ρ 1)).2,
    bobTable (aliceTable (ρ 0) (ρ 1)).1 (ρ 2))

/-- Alice's message `M` in the run on `ρ` (Fig. 1, p.3). -/
def msg (ρ : Equiv.Perm (Fin 4)) : Msg := (tetrahedralRun ρ).1

/-- Alice's output `(m₀, m₁)` in the run on `ρ` (Fig. 1, p.3). -/
def aliceOut (ρ : Equiv.Perm (Fin 4)) : Bool × Bool := (tetrahedralRun ρ).2.1

/-- Bob's output `(s, m_s)` in the run on `ρ` (Fig. 1, p.3), encoding his `(y₀, y₁)`. -/
def bobOut (ρ : Equiv.Perm (Fin 4)) : Bool × Bool := (tetrahedralRun ρ).2.2

/-- The bit `m_{s′}`, `s′ = 1 − s`, that Bob does not learn (proof of Theorem 4.1, pp.3–4):
`m₀` if `s = 1`, `m₁` if `s = 0`. -/
def unchosen (ρ : Equiv.Perm (Fin 4)) : Bool :=
  if (bobOut ρ).1 then (aliceOut ρ).1 else (aliceOut ρ).2

/-- Alice's view: her ordered hand `(ρ(0), ρ(1))`. Alice is deterministic and receives no message, so
everything she sees (including `M` and her output) is a function of it. -/
def viewA (ρ : Equiv.Perm (Fin 4)) : Fin 4 × Fin 4 := (ρ 0, ρ 1)

/-- Bob's view: his card `ρ(2)` and the message `M` he receives ("Bob's view, produced by a particular
M and ρ(2)", proof of Theorem 4.1, p.3). -/
def viewB (ρ : Equiv.Perm (Fin 4)) : Fin 4 × Msg := (ρ 2, msg ρ)

/-- The deal: `ρ` uniform on `S₄` ("shuffled uniformly with a random permutation ρ ← S₄", §3, p.3). -/
noncomputable def deal : PMF (Equiv.Perm (Fin 4)) := PMF.uniformOfFintype (Equiv.Perm (Fin 4))

end TetraOT


