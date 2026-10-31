-- Prove2me | Definitions.Def_KempeCloning_Mode
-- name    : KempeCloning_Mode
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:21:05.76808+00:00
-- url     : https://prove2.me/theorems/fb839f57-63c0-444d-b512-a32ce25963d3
-- title:
--   The five oscillator modes $a_1, a_2, b_1, b_2, c$
-- statement:
--   The model of the paper has five bosonic (harmonic-oscillator) modes:
--
--   1. $a_1$ and $a_2$, the two photon modes (two polarizations); $a_1$ is the "correct" mode that carries the $m$ input photons, $a_2$ the orthogonal one;
--   2. $b_1$ and $b_2$, the Schwinger modes of the two atomic ground levels $g_1, g_2$;
--   3. $c$, the Schwinger mode of the excited atomic level $e$.
--
--   Kets $|n_{a_1}, n_{a_2}, n_{b_1}, n_{b_2}, n_c\rangle$ list the occupation numbers in this order, as in Eqs. (13) and (15) of the paper.
--
--   **Formalization Note** An inductive type with constructors `a1, a2, b1, b2, c`, in the paper's ket order.
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II B, sentence before (15), p.4

import Mathlib

namespace KempeCloning

/-- **The five harmonic-oscillator modes `a₁, a₂, b₁, b₂, c` of the Λ-atom cloner.**
Kempe, Simon, Weihs, *Λ's, V's, and optimal cloning with stimulated emission*,
arXiv:quant-ph/0003025v1, Sec. II B, sentence before (15), p.4: "We are now dealing with five
harmonic oscillator modes defined by the operators c, b1, b2, a1, and a2."

`a1`, `a2` are the two photon modes (the "good" mode `a1` carries the input photons, `a2` the
orthogonal polarization); `b1`, `b2` are the Schwinger modes of the two atomic ground levels
`g1`, `g2`; `c` is the Schwinger mode of the excited level `e`.

**Formalization Note.** The constructor order `a1, a2, b1, b2, c` is the order in which the paper
writes its kets `|n_{a1}, n_{a2}, n_{b1}, n_{b2}, n_c⟩` in (13) and (15). -/
inductive Mode
  | a1
  | a2
  | b1
  | b2
  | c
  deriving DecidableEq, Repr

end KempeCloning


