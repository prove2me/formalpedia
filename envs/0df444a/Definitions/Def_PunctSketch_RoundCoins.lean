-- Prove2me | Definitions.Def_PunctSketch_RoundCoins
-- name    : PunctSketch_RoundCoins
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:13.947846+00:00
-- url     : https://prove2.me/theorems/c094f752-c269-4a38-8100-bdb62b3494f7
-- title:
--   The public coins of one round
-- statement:
--   Levels run over $l\in\{0,\dots,\lceil2\log n\rceil\}$. For each level, the coins of a round are a subsampling coin for each unordered pair and a nonzero field element $\boldsymbol r_{\{u,v\}}$ for each unordered pair. All are independent and uniform.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §5.1, p.15 (PDF p.16); proof of Theorem 5, p.13 (PDF p.14)

import Mathlib

namespace PunctSketch

/-- **The number of subsampling levels.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.1, p.15: `l ∈ {0, …, ⌈2 log n⌉}`. Here
`Nat.clog 2 (n ^ 2) = ⌈2 log₂ n⌉`. -/
def levelTop (n : ℕ) : ℕ := Nat.clog 2 (n ^ 2)

/-- **The public coins of one round.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.1, p.15, and proof of Theorem 5, p.13. For each
level `l ≤ L`: a coin uniform on `Fin (2^l)` per unordered pair, which subsamples the edges, and an
element of `𝔽_Q ∖ {0}` per unordered pair, which is the vector `𝒓` of that level.

**Formalization Note.** The coordinates on the diagonal of `Sym2` are never read. -/
abbrev RoundCoins (n Q L : ℕ) : Type :=
  ((l : Fin (L + 1)) → Sym2 (Fin n) → Fin (2 ^ (l : ℕ))) ×
    (Fin (L + 1) → Sym2 (Fin n) → (ZMod Q)ˣ)

/-- The coins of one round form a finite space. -/
noncomputable instance RoundCoins.instFintype (n Q L : ℕ) [Fact Q.Prime] :
    Fintype (RoundCoins n Q L) := inferInstance

end PunctSketch


