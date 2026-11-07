-- Prove2me | Definitions.Def_PunctSketch_coinList
-- name    : PunctSketch_coinList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:33.082402+00:00
-- url     : https://prove2.me/theorems/21610a91-8432-4f2e-bfc8-fdd54a5ad26e
-- title:
--   A coin string as a machine input
-- statement:
--   Public coins are a uniform $\omega$ in $\{0,\dots,M-1\}^N$, written as the list of the values $\omega_1,\dots,\omega_N$.
--
--   The alphabet is a finite set of arbitrary size and not $\{0,1\}$, because the paper draws uniform elements of $\mathbb F_Q\setminus\{0\}$, which a bounded number of fair bits cannot produce exactly when $Q-1$ is not a power of two.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §2, p.5 (PDF p.6); proof of Theorem 5, p.13 (PDF p.14)

import Mathlib

namespace PunctSketch

/-- **A coin string as a machine input.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §2, p.5 (public coins), §4.2, p.13.

The public coins are `ω : Fin N → Fin M`, drawn uniformly, written as the list of their values.

**Formalization Note.** A uniform finite alphabet rather than fair bits: the paper draws uniform
elements of `𝔽_Q ∖ {0}` (p.13), which a bounded number of fair bits cannot produce exactly when
`Q − 1` is not a power of two. -/
def coinList {N M : ℕ} (ω : Fin N → Fin M) : List ℕ := List.ofFn (fun i => (ω i : ℕ))

end PunctSketch


