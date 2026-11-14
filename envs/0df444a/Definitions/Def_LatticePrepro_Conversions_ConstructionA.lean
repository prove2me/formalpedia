-- Prove2me | Definitions.Def_LatticePrepro_Conversions_ConstructionA
-- name    : LatticePrepro_Conversions_ConstructionA
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:19:53.040202+00:00
-- url     : https://prove2.me/theorems/4239cd11-6d55-4503-986c-bac167cdd4d3
-- title:
--   Integer lift $\tilde y\in\{0,\dots,\mathsf p-1\}^M$ of a word over $\mathbb F_{\mathsf p}$ (Lemma B.1, Construction A)
-- statement:
--   For a prime $\mathsf p$ and a coordinate set $M$, the map `liftZMod` sends a word $y\in\mathbb F_{\mathsf p}^M$ to the integer vector
--   $$\tilde y\in\mathbb Z^M,\qquad \tilde y_i\in\{0,1,\dots,\mathsf p-1\},\qquad \tilde y_i\equiv y_i\pmod{\mathsf p},$$
--   replacing each coordinate by its least nonnegative integer representative, so that $\tilde y\bmod\mathsf p=y$.
--
--   This is the vector $\tilde y$ of Lemma B.1 (From codes to lattices). There a code $\mathcal C\subseteq\mathbb F_{\mathsf p}^M$ gives the Construction A lattice $\mathcal L_{\mathcal C}=\{v\in\mathbb Z^M: v\bmod\mathsf p\in\mathcal C\}$, and a target $y$ gives the lattice target $\tilde y$. The lattice reduction of Lemma 3.12 uses the lifted code targets $\tilde y_x$, directly for norm exponents $1\le p\le2$ and after the block Hadamard map for $p>2$; the lift of a binary error vector $e$ is its $\{0,1\}$-valued integer copy.
--
--   **Formalization Note.** The lift is `fun i => ((y i).val : ℤ)`, using `ZMod.val`; the coordinate set $M$ is an arbitrary type, and Lean writes the prime as `p`. The source module also defines the Construction A lattice (`constructionA`, a $\mathbb Z$-submodule of $\mathbb Z^M$) and coordinatewise reduction modulo $\mathsf p$ (`redMod`) with their properties; these do not occur in the published statements and are not part of this bundle.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Lemma B.1 (\label{lem:construction-a-gap}), the lift of a target; Lean: LatticePrepro/Conversions/ConstructionA.lean, LatticePrepro.liftZMod

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks

/-!
# Construction A (Lemma B.1)

For a prime `p` and a code `𝒞 ⊆ 𝔽_p^M`, the lattice `Λ_𝒞 = {v ∈ ℤ^M : v mod p ∈ 𝒞}`.
We also define the lift `liftZMod y ∈ {0, …, p-1}^M` of a word `y ∈ 𝔽_p^M`, and prove the
residual bounds used in the lattice reduction: for `v ∈ Λ_𝒞`, the reduction of `t - v` modulo
`p` lies in `y - 𝒞`, and its Hamming weight is at most the number of nonzero coordinates of
`t - v`.
-/

namespace LatticePrepro

open Finset

variable {p : ℕ} [Fact p.Prime] {M : Type*}

/-- The lift `y ↦ (y_i.val)_i ∈ {0, …, p-1}^M`. -/
def liftZMod (y : M → ZMod p) : M → ℤ := fun i => ((y i).val : ℤ)

end LatticePrepro


