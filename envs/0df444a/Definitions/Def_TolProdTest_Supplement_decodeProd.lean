-- Prove2me | Definitions.Def_TolProdTest_Supplement_decodeProd
-- name    : TolProdTest_Supplement_decodeProd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:07:42.47921+00:00
-- url     : https://prove2.me/theorems/bda24458-8fc5-4259-bdca-3e9bdaad2eb0
-- title:
--   Fixed decoder from output bits to a pure product state
-- statement:
--   A learner outputs "a classical description of a pure product state". This definition fixes how such a description is read off the measured output string $y\in\{0,1\}^W$.
--
--   For a precision $p$ and an injective map $o$ assigning a wire to each site $i\in[n]$, level $j\in[d]$, part (real or imaginary) and bit index $l\in\{0,\dots,p\}$, the raw amplitude of level $j$ at site $i$ is
--
--   $$
--   \tilde u_i(j)=\mathrm{fp}\big(y_{o(i,j,\mathrm{re},\cdot)}\big)+\mathrm{i}\,\mathrm{fp}\big(y_{o(i,j,\mathrm{im},\cdot)}\big),\qquad \mathrm{fp}(b)=(-1)^{b_0}\sum_{l=1}^{p}b_l\,2^{-l},
--   $$
--
--   and the decoded site vector is $u_i=\tilde u_i/\|\tilde u_i\|_2$, with $u_i=|0\rangle$ when $\tilde u_i=0$. The output state is $|\hat u\rangle=|u_1\rangle\otimes\cdots\otimes|u_n\rangle$.
--
--   For $d\ge1$ every $u_i$ is a unit vector, so $|\hat u\rangle$ is always a pure product state.
--
--   **Formalization Note** The decoding rule is part of the definition; an algorithm chooses only $p$ and $o$. This keeps the computational-complexity bound meaningful: no arbitrary post-processing is hidden outside the circuit.
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Problem 1.2, p.2; Theorem 4.1, p.19; Theorem 4.2, p.20

import Mathlib
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace TolProdTest.Supplement

/-- The signed binary fixed-point number read from `p + 1` bits `b`: bit `0` is the sign (`true` = negative),
bits `1, …, p` are the binary fraction, `(-1)^{b_0} · Σ_{l=1}^{p} b_l 2^{-l}`. -/
noncomputable def fixedPoint {p : ℕ} (b : Fin (p + 1) → Bool) : ℝ :=
  (if b 0 then -1 else 1) * ∑ l : Fin p, if b l.succ then (2 : ℝ)⁻¹ ^ (l.val + 1) else 0

/-- Normalize a site vector `v : Fin d → ℂ`: divide by its Euclidean norm; the zero vector is sent to the
basis vector `|0⟩`. -/
noncomputable def normalizeSite {d : ℕ} (v : Fin d → ℂ) : Fin d → ℂ :=
  if ∑ j, ‖v j‖ ^ 2 = 0 then (fun j => if j.val = 0 then 1 else 0)
  else fun j => v j / (Real.sqrt (∑ j', ‖v j'‖ ^ 2) : ℂ)

/-- **The classical description of a pure product state read off the output wires of a learner**
(Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Problem 1.2, p.2; Theorem 4.1, p.19; Theorem 4.2, p.20: "outputs a classical description of a pure
product state |û⟩").

The decoder is fixed here and is not chosen by the algorithm. For a precision `p` and an injective wire map
`o : Fin n × Fin d × Bool × Fin (p+1) ↪ Fin W`, the raw amplitude of level `j` at site `i` is
`fixedPoint (bits at o (i, j, false, ·)) + i · fixedPoint (bits at o (i, j, true, ·))` (real part, then imaginary
part; each a sign bit and `p` binary-fraction bits), and each site vector is then normalized by
`normalizeSite` (zero vector ↦ `|0⟩`). The product state is `TolProdTest.prodVec (decodeProd p o y)`.

**Formalization Note** The algorithm chooses only `p` and `o`; the decoding rule (fixed point, normalization)
is part of this definition, so no unbounded computation is hidden outside the circuit. For `d ≥ 1` every
decoded site vector is a unit vector. Sites and levels are indexed from `0`. -/
noncomputable def decodeProd {n d W : ℕ} (p : ℕ) (o : Fin n × Fin d × Bool × Fin (p + 1) ↪ Fin W)
    (y : ShiShallow.Bits W) : Fin n → Fin d → ℂ :=
  fun i => normalizeSite fun j =>
    ((fixedPoint fun l => y (o (i, j, false, l)) : ℝ) : ℂ) +
      ((fixedPoint fun l => y (o (i, j, true, l)) : ℝ) : ℂ) * Complex.I

end TolProdTest.Supplement


