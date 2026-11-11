-- Prove2me | Definitions.Def_StabTestMem_AffineConsistent
-- name    : StabTestMem_AffineConsistent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:09:19.51346+00:00
-- url     : https://prove2.me/theorems/97957797-7b5c-4c0e-ac8e-79ca9f5cfc66
-- title:
--   Samples on the graph of an affine function $\mathbb F_2^m\to\mathbb F_2$
-- statement:
--   For $u\in\mathbb F_2^m$ and $c\in\mathbb F_2$ let $\chi_{u,c}(s)=u\cdot s\oplus c$. A list of samples $(s_1,b_1),\dots,(s_N,b_N)\in\mathbb F_2^m\times\mathbb F_2$ is **affine consistent** if some $\chi_{u,c}$ has all of them on its graph:
--
--   $$\exists u\in\mathbb F_2^m,\ c\in\mathbb F_2:\quad b_j=u\cdot s_j\oplus c\ \text{ for all } j\in[N].$$
--
--   The tester rejects when, for both phase guesses $\beta$, the hidden-shift samples are not affine consistent.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Eq. (43), p. 26; Lemma 4.5, p. 30

import Mathlib

namespace StabTestMem

/-- **Samples lying on the graph of an affine function `F₂^m → F₂`.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Eq. (43), p. 26
(`χ_{u,c}(s) := u·s ⊕ c`, `Graph(χ_{u,c})`), and Lemma 4.5, p. 30: "∃u ∈ F_2^m, c ∈ F_2 such that
b_j = u · s_j ⊕ c for all j ∈ [N]".

`AffineConsistent w` holds for a list `w = ((s_1, b_1), …, (s_N, b_N))` when some affine function
`χ_{u,c}` has all `N` samples on its graph. -/
def AffineConsistent {m N : ℕ} (w : Fin N → (Fin m → ZMod 2) × ZMod 2) : Prop :=
  ∃ (u : Fin m → ZMod 2) (c : ZMod 2), ∀ j, (w j).2 = (∑ i, u i * (w j).1 i) + c

end StabTestMem


