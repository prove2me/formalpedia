-- Prove2me | Definitions.Def_AbelianCayleyHDX_cayleyGraph
-- name    : AbelianCayleyHDX_cayleyGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:25:28.891035+00:00
-- url     : https://prove2.me/theorems/53c19764-b6f0-47d9-913b-49446e290eb0
-- title:
--   The Cayley graph $\mathrm{Cay}(\mathbb F_2^n, S)$
-- statement:
--   For $S \subseteq \mathbb F_2^n$, the **Cayley graph** $\mathrm{Cay}(\mathbb F_2^n, S)$ has vertex set $\mathbb F_2^n$ and edge set
--   $$\big\{\{x, x+s\} : x \in \mathbb F_2^n,\ s \in S\big\}.$$
--   Since $y = x + s$ iff $s = x + y$ in characteristic two, two vertices $x \ne y$ are adjacent iff $x + y \in S$.
--
--   **Formalization Note** A simple graph on `Vec n`; the condition $x \neq y$ only removes loops, which do not occur under the paper's standing assumption $0 \notin S$.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.3, p.9

import Mathlib
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)

namespace AbelianCayleyHDX

/-- **The Cayley graph `Cay(𝔽₂ⁿ, S)`** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.3, p.9): vertex set `𝔽₂ⁿ`, edge set
`{{x, x + s} : x ∈ 𝔽₂ⁿ, s ∈ S}`.

**Formalization Note** In `𝔽₂ⁿ`, `y = x + s` iff `s = x + y`, so `x ~ y` iff `x ≠ y` and
`x + y ∈ S`. The clause `x ≠ y` only removes loops; under the standing assumption `0 ∉ S` it is
automatic. -/
def cayleyGraph {n : ℕ} (S : Finset (Vec n)) : SimpleGraph (Vec n) where
  Adj x y := x ≠ y ∧ x + y ∈ S
  symm := ⟨fun x y h => ⟨h.1.symm, by rw [add_comm]; exact h.2⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

end AbelianCayleyHDX


