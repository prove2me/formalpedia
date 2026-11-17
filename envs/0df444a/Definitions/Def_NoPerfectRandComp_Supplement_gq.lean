-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_gq
-- name    : NoPerfectRandComp_Supplement_gq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:06:51.310726+00:00
-- url     : https://prove2.me/theorems/c2711d87-97a2-4a85-86f8-1cdab3915572
-- title:
--   The Blais–Brody block $g_q = \mathrm{PtrFcn}_{q,q}\circ\phi^{q^2}$
-- statement:
--   Let $\Gamma = \{0,1\}\times([q]\cup\{\bot\})^q\times([q]\cup\{\bot\})$ be the pointer-cell alphabet and $\phi : \{0,1\}^C \to \Gamma$ a cell map. The **Blais–Brody block** is the total Boolean function on $m_q = q^2 C$ bits
--   $$
--   g_q \;=\; \mathrm{PtrFcn}_{q,q}\circ\phi^{q^2}:
--   $$
--   the input is a $q\times q$ array of cells of $C$ bits each; every cell is decoded by $\phi$, and the pointer predicate $\mathrm{PtrFcn}_{q,q}$ (clauses (i)–(v) of §2.6: an all-ones special column, a special cell, null row pointers elsewhere in that column, linked zero cells, and exactly $\lfloor (q-1)/2\rfloor$ good linked cells) is applied. Its randomized complexity is $T_q := \mathrm{R}(g_q)$.
--
--   **Formalization Note** The pointer predicate is the base mission's published $\Pi_q$ (`PiQ`), the precise form of (i)–(v) given on p.18. The cell map $\phi$ and its length $C$ are parameters: the paper uses Blais–Brody's map, which it does not reprint. Bit $t$ of cell $(i,j)$ is coordinate $(i,j,t)$.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §2.6, p.7 and (5)

import Mathlib
import Definitions.Def_NoPerfectRandComp_PiQ

namespace NoPerfectRandComp

namespace Supplement

/-- The Blais–Brody block `g_q = PtrFcn_{q,q} ∘ ϕ^{q²}` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §2.6, p.7): decode
each of the `q²` cells of `C` bits through the cell map `ϕ : {0,1}^C → Γ` and apply the pointer
predicate `Π_q` (the published `PiQ`, clauses (i)–(v) of §2.6 in the form of §5.1, p.18). Its
input length is `m_q = q² C` ((5), p.7). Bit `t` of cell `(i, j)` is the coordinate `(i, j, t)`.

**Formalization Note** The paper takes Blais–Brody's `⌊C_q/3⌋`-resilient map with
`C_q = Θ(q log q)` and does not reprint it; here `C` and `ϕ` are parameters, and the theorems of
this supplement hypothesise `IsResilientMap (C / 3) ϕ` and `C ≤ K q log₂ q`. -/
def gq (q C : ℕ) (ϕ : (Fin C → Bool) → PtrCell q) (x : Fin q × Fin q × Fin C → Bool) : Bool :=
  PiQ q (fun c => ϕ (fun t => x (c.1, c.2, t)))

end Supplement

end NoPerfectRandComp


