-- Prove2me | Definitions.Def_TetraOT_idealROT
-- name    : TetraOT_idealROT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:25:02.684971+00:00
-- url     : https://prove2.me/theorems/6bde1a0b-1b8e-47e5-a370-f10ff2fb2d8a
-- title:
--   The ideal random 1-of-2 oblivious transfer $\binom{2}{1}\mathrm{ROT}$
-- statement:
--   In **random 1-of-2 oblivious transfer** (ROT), Alice receives two random bits $m_0, m_1$ and Bob receives a random selection bit $s$ together with $m_s$, learning nothing about the other bit $m_{s'}$, $s' = 1 - s$, while Alice learns nothing about $s$. As a functionality it is the joint law of the two outputs when $m_0, m_1, s$ are independent uniform bits:
--   $$
--   \mathcal F_{\mathrm{ROT}} = \text{law of } \big((m_0, m_1),\ (s, m_s)\big), \qquad (m_0, m_1, s) \sim \mathrm{Unif}(\{0,1\}^3).
--   $$
--   It puts mass $1/8$ on each pair $((m_0,m_1),(s,y))$ with $y = m_s$ and mass $0$ on every other pair.
--
--   This is the ideal functionality against which the Tetrahedral Protocol is compared.
--
--   **Formalization Note** Bits are Booleans with $\texttt{true} = 1$ and $m_s$ is `if s then m₁ else m₀`. The paper names this functionality both $\tfrac12\mathrm{ROT}$ (Fig. 1) and $\binom{2}{1}\mathrm{ROT}$ (Theorem 4.1); Definition 2.5 makes all three bits random in both.
-- source:
--   Beaver, Correlated Group Interactions: Founding Cryptography on S4 and Sn, STOC 2027 submission (preprint, sha256 3dc88c598213707cd4cd52311a9b058999deef19d5aa9eed05208ba8092d65b7), Definition 2.5, p.2 (p. = PDF page; the PDF has no printed page numbers)

import Mathlib

set_option autoImplicit false

namespace TetraOT

/-- **The ideal random 1-of-2 oblivious transfer `(²₁)ROT`** (Beaver, *Correlated Group Interactions: Founding Cryptography on S4 and Sn*, STOC 2027 submission (held preprint, sha256 3dc88c59…92d65b7), Definition 2.5, p.2; p. =
PDF page, the PDF has no printed page numbers): "Alice receives two random bits m₀, m₁ and Bob learns
a random selection bit s, and Bob learns m_s (but nothing about m_{s′}) while Alice learns nothing."
`idealROT` is the joint law of the two outputs `((m₀, m₁), (s, m_s))` when `m₀, m₁, s` are independent
uniform bits: the image of the uniform law on `Bool × Bool × Bool` under
`(m₀, m₁, s) ↦ ((m₀, m₁), (s, m_s))`. It gives mass `1/8` to each pair whose second component is
consistent with the first, and `0` elsewhere.

**Formalization Note.** Bits are `Bool` with `true` = 1, and `m_s` is `if s then m₁ else m₀`. The
paper's names `½ROT` (Fig. 1) and `(²₁)ROT` (Theorem 4.1) both denote this functionality here, since
Definition 2.5 makes all three bits random in both. -/
noncomputable def idealROT : PMF ((Bool × Bool) × (Bool × Bool)) :=
  (PMF.uniformOfFintype (Bool × Bool × Bool)).map
    (fun x => ((x.1, x.2.1), (x.2.2, if x.2.2 then x.2.1 else x.1)))

end TetraOT


