-- Prove2me | Definitions.Def_TetraOT_Supplement_reverseRun
-- name    : TetraOT_Supplement_reverseRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:36:44.594863+00:00
-- url     : https://prove2.me/theorems/25b07ce4-2501-4ec2-a8ba-5dbb38785db3
-- title:
--   The inverted Tetrahedral Protocol: one run from Alice's hand and one ½ROT (Figs. 7–10)
-- statement:
--   The inverted Tetrahedral Protocol (Fig. 10) produces a $(2,1;1)$ deal from one random 1-of-2 oblivious transfer. Its randomness is a pair $\omega = ((a,b), s)$:
--
--   1. Alice's ordered hand $(a,b)$, two distinct cards of $\{0,1,2,3\}$, uniform over the 12 ordered pairs (the 12 rows of Fig. 9);
--   2. the selection bit $s$ of the oblivious-transfer channel, uniform and independent of the hand.
--
--   On $\omega$, Alice computes $(M, m_0m_1) = A(a,b)$ from her Tetrahedral table (Fig. 2, equivalently Fig. 7), sends $M$ to Bob and feeds $(m_0,m_1)$ into the channel. The channel delivers $(s, m_s)$ to Bob, with $m_s = m_1$ if $s=1$ and $m_0$ if $s=0$, and nothing to Alice. Bob sets his card to
--   $$c = B^{-1}(M, (s, m_s))$$
--   (Fig. 8). Alice's view is her ordered hand; Bob's view is $(M, (s, m_s))$. Alice's output is her hand $(a,b)$; Bob's output is the pair $(c, M)$ of his card and the public message.
--
--   This object is the real protocol of Theorem 5.1.
--
--   **Formalization Note** The randomness space is the finite type of pairs (ordered pair of distinct cards, bit) with the uniform law. The oblivious-transfer channel is ideal (the OT-hybrid model). Bob's output carries $M$ in addition to the printed "Deal result: $\rho(2)$"; this is the correction of Theorem 5.1 explained there.
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), §5, Figs. 7–10, pp.4–5 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib
import Definitions.Def_TetraOT_Msg
import Definitions.Def_TetraOT_aliceTable
import Definitions.Def_TetraOT_Supplement_bobInvTable

set_option autoImplicit false

namespace TetraOT.Supplement

open TetraOT

/-- The randomness of the inverted Tetrahedral Protocol (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), §5 and Figs. 9–10, pp.4–5; p. = PDF
page, the PDF has no printed page numbers): Alice's ordered hand `(a, b)`, a pair of distinct cards of
`{0, 1, 2, 3}` ("Alice will simply choose a two-card hand ρ(0), ρ(1) for herself at random", p.4; the 12
ordered rows `ρ_A` of Fig. 9), together with the selection bit `s` of the ½ROT channel. -/
abbrev RevOmega : Type := {p : Fin 4 × Fin 4 // p.1 ≠ p.2} × Bool

instance : Nonempty RevOmega := ⟨(⟨((0 : Fin 4), (1 : Fin 4)), by decide⟩, false)⟩

/-- The law of the randomness: Alice's ordered hand uniform over the 12 ordered pairs of distinct
cards, and the OT channel's selection bit `s` uniform and independent of it (Fig. 9: "Alice randomly
selects ρ_A per one of 12 rows; two subsequent OT cases per row are shown"). -/
noncomputable def revRandomness : PMF RevOmega := PMF.uniformOfFintype RevOmega

/-- **One run of the inverted Tetrahedral Protocol** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), Fig. 10, p.5, with Figs. 7–9, pp.4–5;
p. = PDF page, the PDF has no printed page numbers). On randomness `ω = ((a, b), s)`:
1. Alice computes `(M, m₀m₁) ← A(a, b)` (the published table `TetraOT.aliceTable`, Fig. 2; equivalently
   Fig. 7's `A⁻¹`), sends `M` to Bob, and feeds `(m₀, m₁)` into the single ½ROT;
2. the ½ROT channel delivers to Bob `(y₀, y₁)`, i.e. `(s, m_s)` with `m_s = m₁` if `s = 1` and `m₀` if
   `s = 0`;
3. Bob computes his card `c = ρ(2) ← B⁻¹(M, y₀y₁)` (Fig. 8, `bobInvTable`).

`reverseRun ω = (M, (m₀, m₁), (s, m_s), c)`.

**Formalization Note.** The ½ROT channel is the ideal functionality of the OT-hybrid model: Alice
supplies `(m₀, m₁)`, the channel draws `s` uniformly (the `Bool` component of `ω`), and Bob receives
`(s, m_s)`; Alice receives nothing from it. Bits are `Bool` with `true` = 1. -/
def reverseRun (ω : RevOmega) : Msg × (Bool × Bool) × (Bool × Bool) × Fin 4 :=
  ((aliceTable ω.1.1.1 ω.1.1.2).1, (aliceTable ω.1.1.1 ω.1.1.2).2,
    (ω.2, if ω.2 then (aliceTable ω.1.1.1 ω.1.1.2).2.2 else (aliceTable ω.1.1.1 ω.1.1.2).2.1),
    bobInvTable (aliceTable ω.1.1.1 ω.1.1.2).1
      (ω.2, if ω.2 then (aliceTable ω.1.1.1 ω.1.1.2).2.2 else (aliceTable ω.1.1.1 ω.1.1.2).2.1))

/-- Alice's view in the OT-hybrid model: her ordered hand `(a, b)`. She receives nothing (neither from
Bob nor from the ½ROT), and `M`, `m₀, m₁` are functions of her hand. -/
def revViewA (ω : RevOmega) : Fin 4 × Fin 4 := ω.1.1

/-- Bob's view in the OT-hybrid model: Alice's message `M` and the ½ROT output `(s, m_s)`. -/
def revViewB (ω : RevOmega) : Msg × (Bool × Bool) := ((reverseRun ω).1, (reverseRun ω).2.2.1)

/-- Alice's deal result `ρ(0)ρ(1)` (Fig. 10): her ordered hand `(a, b)`. -/
def revAliceOut (ω : RevOmega) : Fin 4 × Fin 4 := ω.1.1

/-- Bob's output: his deal result `ρ(2) = c` (Fig. 10), paired with the public message `M`.

**Formalization Note.** Bob's output carries `M` in addition to the printed "Deal result: ρ(2)"; this is
the minimal correction of Theorem 5.1 (see `idealDealM`). -/
def revBobOut (ω : RevOmega) : Fin 4 × Msg := ((reverseRun ω).2.2.2, (reverseRun ω).1)

end TetraOT.Supplement


