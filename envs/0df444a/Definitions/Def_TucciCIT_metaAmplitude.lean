-- Prove2me | Definitions.Def_TucciCIT_metaAmplitude
-- name    : TucciCIT_metaAmplitude
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:28:20.196147+00:00
-- url     : https://prove2.me/theorems/f697180b-3848-4452-95e4-9d52753f98f6
-- title:
--   Amplitude of the meta state $|\psi_{meta}\rangle$ of the two-listener QB net
-- statement:
--   Let $S_x$ and $S_y$ be finite sets and let $\psi : S_x \times S_y \to \mathbb C$ be an amplitude, viewed as a rectangular matrix with entries $\psi(x,y)$. The quantum Bayesian net of Fig. 3 has a speaker node $e$ with states $e = (e_1, e_2) \in S_x \times S_y$ and two listener nodes $x \in S_x$, $y \in S_y$; node $e$ carries the amplitude $\psi(e)$, node $x$ the amplitude $\delta(x, e_1)$ and node $y$ the amplitude $\delta(y, e_2)$. The resulting meta state on $\mathcal H_e \otimes \mathcal H_x \otimes \mathcal H_y$ is
--
--   $$
--   |\psi_{meta}\rangle = \sum_{x,y} \psi(x,y)\, |e = (x,y), x, y\rangle .
--   $$
--
--   This definition gives its amplitude at a basis index $(e, x, y)$: it is $\psi(e_1, e_2)$ if $x = e_1$ and $y = e_2$, and $0$ otherwise.
--
--   The meta state is the object on which all entropies of the paper's §4 are evaluated.
--
--   **Formalization Note** The amplitude is taken as given; for the a priori net of the first table on p. 8 it is the rotated amplitude $\psi = U\psi^0V^\dagger$. No normalization is imposed in the definition.
-- source:
--   Tucci, Quantum Entanglement and Conditional Information Transmission, arXiv:quant-ph/9909041v2, eq. (4.2) and the first table, p.8

import Mathlib

namespace TucciCIT

/-- Tucci, *Quantum Entanglement and Conditional Information Transmission*,
arXiv:quant-ph/9909041v2, eq. (4.2), p.8 (PDF p.8), and the first table on p.8.

The amplitude of the meta state `|ψ_meta⟩ = Σ_{x,y} ψ(x,y) |e = (x,y), x, y⟩` of the QB net of
Fig. 3 (p.7). A basis index of `H_e ⊗ H_x ⊗ H_y` is `(e, x, y)` with `e = (e₁, e₂) ∈ S_x × S_y`,
`x ∈ S_x`, `y ∈ S_y`. The amplitude is `ψ(e₁, e₂)` when `x = e₁` and `y = e₂` (the table's
`δ(x, e₁)` at node x and `δ(y, e₂)` at node y), and `0` otherwise.

**Formalization Note.** `X`, `Y` are the paper's finite sets `S_x`, `S_y`; the rectangular
matrix `ψ : Matrix X Y ℂ` has entries `ψ x y = ψ(x,y)`. For the a priori net of the first table
on p.8, `ψ` is the rotated amplitude `ψ = U ψ⁰ V†` (eq. (4.9)); the definition takes `ψ` as given.
No normalization is imposed here; the theorems that need `Σ|ψ(x,y)|² = 1` assume it. -/
def metaAmplitude {X Y : Type*} [DecidableEq X] [DecidableEq Y] (ψ : Matrix X Y ℂ)
    (i : (X × Y) × X × Y) : ℂ :=
  if i.1 = i.2 then ψ i.2.1 i.2.2 else 0

end TucciCIT


