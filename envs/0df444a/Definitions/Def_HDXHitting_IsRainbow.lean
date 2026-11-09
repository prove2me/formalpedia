-- Prove2me | Definitions.Def_HDXHitting_IsRainbow
-- name    : HDXHitting_IsRainbow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:56:27.223149+00:00
-- url     : https://prove2.me/theorems/b67dd821-48b7-44d2-8191-f7d88646d406
-- title:
--   $d$-partite complex with a colouring
-- statement:
--   Let $c$ be a colouring of the vertices with colours in a set $\iota$, and $S\subseteq\iota$ a finite set of colours. A complex with top distribution $p$ is **$|S|$-partite with colouring $c$ and colour set $S$** if every top face $\sigma$ ($p(\sigma)\ne0$) has all its vertices coloured in $S$ and contains exactly one vertex of each colour $i\in S$.
--
--   With $A_i = c^{-1}(i)$ this is the paper's partition $X(1)=\bigsqcup_{i\in[d]}A_i$ with $|\tau\cap A_i|\le 1$ for every face $\tau$: a top face with $d$ vertices meeting each of the $d$ parts at most once meets each exactly once.
--
--   **Formalization Note** The colour set $S$ is explicit so that the link of a face $\tau$ is again of this form, on the colours $S\setminus c(\tau)$, with the same colouring $c$. Colours of vertices outside the complex are irrelevant.
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), Section 2.2.1, p.12 (partite complexes)

import Mathlib

namespace HDXHitting

/-- `d`-partiteness with a colouring (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), §2.2.1, p.12: `X(1) = ⊔_{i∈[d]} A_i` with
`|τ ∩ A_i| ≤ 1` for every face `τ`): every top face (`p σ ≠ 0`) has all its vertices coloured
in `S` and exactly one vertex of each colour `i ∈ S`. The parts are `A_i = c⁻¹(i)`.

**Formalization Note** For a pure complex with `|S| = d` and top faces of size `d` this is the
paper's condition (each top face meets each of the `d` parts in at most one vertex, hence in
exactly one). The colour set `S` is explicit so that the link of a colour-`i` vertex is again
of this form, on `S ∖ {i}`, with the same colouring `c` (p.12: "the link `X_τ` is
`k`-partite"). Colours of non-vertices are irrelevant. -/
def IsRainbow {V ι : Type*} [Fintype V] (p : Finset V → ℝ) (c : V → ι) (S : Finset ι) :
    Prop :=
  ∀ σ, p σ ≠ 0 → (∀ v ∈ σ, c v ∈ S) ∧ ∀ i ∈ S, ∃! v, v ∈ σ ∧ c v = i

end HDXHitting


