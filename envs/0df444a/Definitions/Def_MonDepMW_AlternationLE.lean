-- Prove2me | Definitions.Def_MonDepMW_AlternationLE
-- name    : MonDepMW_AlternationLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:44.753458+00:00
-- url     : https://prove2.me/theorems/fa6694ed-047c-49ab-9ec7-88a931e29a92
-- title:
--   Alternation of a vertex ordering (Definition 5.11)
-- statement:
--   Let $\preccurlyeq$ be a vertex ordering of $G$. Its **alternation** is the least integer $\alpha$ such that for every vertex $u$ there are at most $\alpha$ pairs of vertices $w,w'$ consecutive in $\preccurlyeq$ with $u\in\Delta[w,w']$.
--
--   Orderings of low alternation replace the online $\varepsilon$-net in the proof of the Predamping Lemma.
--
--   **Formalization Note** An ordering is a bijection `Fin n ≃ Fin n` from positions to vertices; `AlternationLE G σ α` says that $\alpha$ has the property.
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), §5.3, p.21, Definition 5.11

import Mathlib
import Definitions.Def_MonDepMW_closedSymmDiff

set_option autoImplicit false

namespace MonDepMW

/-- **Alternation at most `α`.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), Definition 5.11, p.21: "Let G be a graph and ≼ be a vertex ordering of G. The
alternation of ≼ is the least integer α with the following property: For every vertex u of G, there are at most α pairs
of vertices w, w′ that are consecutive in ≼ and satisfy u ∈ ∆[w, w′]."

**Formalization Note.** A vertex ordering is `σ : Fin n ≃ Fin n`, position ↦ vertex; the consecutive pairs are
`(σ i, σ (i + 1))` for `i + 1 < n`, counted by their first position. -/
def AlternationLE {n : ℕ} (G : SimpleGraph (Fin n)) (σ : Fin n ≃ Fin n) (α : ℕ) : Prop :=
  ∀ u : Fin n,
    {i : Fin n | ∃ h : (i : ℕ) + 1 < n, u ∈ closedSymmDiff G (σ i) (σ ⟨(i : ℕ) + 1, h⟩)}.ncard ≤ α

end MonDepMW


