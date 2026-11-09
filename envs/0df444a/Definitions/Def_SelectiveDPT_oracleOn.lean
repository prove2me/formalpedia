-- Prove2me | Definitions.Def_SelectiveDPT_oracleOn
-- name    : SelectiveDPT_oracleOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:37.570893+00:00
-- url     : https://prove2.me/theorems/d3a37a77-f5da-48d1-8817-2f4c685e3cc8
-- title:
--   Fixed-query oracle $O_{i,p} = \sum_{x\in D}\omega_d^{p x_i}|x\rangle\langle x|$
-- statement:
--   For a domain $D \subseteq X^\iota$, an index $i \in \iota$ and a phase $p \in \mathbb Z_d$, the **fixed-query oracle** is the diagonal unitary on the input space $\mathbb C^D$
--   $$O_{i,p} = \sum_{x \in D} \omega_d^{\,p\,x_i}\, |x\rangle\langle x| .$$
--   It is the action of the phase oracle on the input register once the query $(i,p)$ is fixed, and it enters the per-query progress rate of the multiplicative adversary method.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, §2.2, p.9 (definition of O_{i,p})

import Mathlib
import Definitions.Def_SelectiveDPT_phaseOracle

namespace SelectiveDPT

/-- The fixed-query oracle `O_{i,p} := Σ_{x ∈ D} ω_d^{p·x_i} |x⟩⟨x|` on the input register `ℂ^D`
(arXiv:2609.26678, §2.2, p.9: "We will sometimes fix the index `i` and phase `p` and consider
`O_{i,p} := Σ_x ω_d^{p x_i} |x⟩⟨x|`"), a diagonal unitary on the inputs of the domain `D`.

**Formalization Note.** The index type of the matrix is the subtype `↥D` of the domain
`D ⊆ X^n`; adversary matrices of §2.4 are `|D| × |D|` matrices on the same index. -/
noncomputable def oracleOn {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (D : Finset (ι → ZMod d)) (i : ι) (p : ZMod d) : Matrix D D ℂ :=
  Matrix.diagonal fun x => rootPow d (p * x.1 i)

end SelectiveDPT


