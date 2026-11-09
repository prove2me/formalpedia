-- Prove2me | Definitions.Def_SelectiveDPT_phaseOracle
-- name    : SelectiveDPT_phaseOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:48:51.219544+00:00
-- url     : https://prove2.me/theorems/391607b2-bba1-45e6-9779-31cd4af45794
-- title:
--   $d$-ary phase oracle $O|i,p,w\rangle = \omega_d^{p x_i}|i,p,w\rangle$
-- statement:
--   Fix an alphabet $X$ of size $d$, identified with $\mathbb Z_d$, and write $\omega_d = e^{2\pi i/d}$. For an input $x \in X^\iota$ indexed by a finite set $\iota$ (positions), the **phase oracle** acts on the query register, spanned by $|i,p\rangle$ with $i \in \iota$ and $p \in \mathbb Z_d$, as the diagonal unitary
--   $$O_x\,|i,p\rangle = \omega_d^{\,p\,x_i}\,|i,p\rangle .$$
--   A query algorithm applies $O_x \otimes I_W$, the identity on its workspace $W$.
--
--   Auxiliary: $\omega_d^a := \exp(2\pi i\, a/d)$ for $a \in \mathbb Z_d$, read through the representative $a \in \{0, \dots, d-1\}$.
--
--   This is the oracle of every query complexity in the mission. For $m$ copies of an input in $X^n$ the index set is $[m] \times [n]$, so one query reads one position of one copy.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, §2.2, p.9 (definition of O and footnote 5)

import Mathlib

namespace SelectiveDPT

/-- The root-of-unity power `ω_d^a = exp(2πi·a/d)` for `a ∈ Z_d` (Beame–Kornerup–Whitmeyer,
*Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity*,
arXiv:2609.26678, §2.2, p.9: "`ω_d` is a primitive `d`-th root of unity").

**Formalization Note.** `a` is read through its canonical representative `a.val ∈ {0, …, d−1}`;
since `ω_d^d = 1` the value is the paper's `ω_d^a` for the fixed primitive root `ω_d = e^{2πi/d}`. -/
noncomputable def rootPow (d : ℕ) (a : ZMod d) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) / d)

/-- The `d`-ary phase oracle of arXiv:2609.26678, §2.2, p.9:
`O |i, p, w⟩ |x⟩ = ω_d^{p·x_i} |i, p, w⟩ |x⟩`, as the diagonal matrix on the query register
`ι × Z_d` (index `i`, phase `p`) for the input `x : ι → Z_d`. The workspace `w` is the workspace of
`QAlgorithms.QueryAlg`, on which the oracle acts as the identity.

**Formalization Note.** The input alphabet `X` with `|X| = d` is identified with `Z_d = ZMod d`
("via some fixed mapping identifying `X` with the elements of `Z_d`", p.9). For `m` copies the index
type is `Fin m × Fin n` (copy, position), footnote 5, p.9; one query reads one position of one
copy. -/
noncomputable def phaseOracle {ι : Type*} [DecidableEq ι] {d : ℕ} (x : ι → ZMod d) :
    Matrix (ι × ZMod d) (ι × ZMod d) ℂ :=
  Matrix.diagonal fun q => rootPow d (q.2 * x q.1)

end SelectiveDPT


