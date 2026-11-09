-- Prove2me | Definitions.Def_AbelianCayleyHDX_character
-- name    : AbelianCayleyHDX_character
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:25:32.644414+00:00
-- url     : https://prove2.me/theorems/9c0b678d-59ab-4aae-8784-9f0523416ccb
-- title:
--   Character $\chi_\xi(x) = (-1)^{\langle \xi, x\rangle}$ of $\mathbb F_2^n$
-- statement:
--   For $\xi \in \mathbb F_2^n$, the **character** $\chi_\xi : \mathbb F_2^n \to \{\pm 1\} \subset \mathbb R$ is
--   $$\chi_\xi(x) = (-1)^{\langle \xi, x \rangle}, \qquad \langle \xi, x\rangle = \sum_i \xi_i x_i \in \mathbb F_2 .$$
--   The characters diagonalize every Cayley graph on $\mathbb F_2^n$ (Lemma 2.1).
--
--   **Formalization Note** The exponent is the representative $0$ or $1$ of $\langle \xi, x\rangle$.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 2.1, p.9

import Mathlib
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)

namespace AbelianCayleyHDX

/-- **The character `χ_ξ` of `𝔽₂ⁿ`** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 2.1, p.9): `χ_ξ(x) = (−1)^{⟨ξ, x⟩}` with
`⟨ξ, x⟩ = ∑ᵢ ξᵢ xᵢ ∈ 𝔽₂`.

**Formalization Note** The exponent is the representative `0` or `1` of `⟨ξ, x⟩ ∈ ZMod 2`. -/
def character {n : ℕ} (ξ x : Vec n) : ℝ :=
  (-1 : ℝ) ^ (∑ i, ξ i * x i).val

end AbelianCayleyHDX


