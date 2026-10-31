-- Prove2me | Definitions.Def_ObliviousRSP_povmElement
-- name    : ObliviousRSP_povmElement
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:21:44.483899+00:00
-- url     : https://prove2.me/theorems/d57f9b15-13c9-4402-8eea-a2b4d437f0a2
-- title:
--   Elements $M_m$ of the modified measurement, eq. (4)
-- statement:
--   Given Bob's isometries $V_m$, the message probabilities $p_m$ and the extra outputs $b_m$, the paper's modified measurement $\mathcal M$ has the elements
--   $$
--   M_m = d\,d'\,p_m\,\big(I_1\otimes V_m^{T}\big)\big(|\Phi_d\rangle\langle\Phi_d|_{12}\otimes b_m^{T}\big)\big(I_1\otimes \overline{V_m}\big),
--   $$
--   operators on $\mathbb C^\iota\otimes\mathbb C^\sigma$ (the specimen and Alice's half). Here $d = |\iota|$, $d' = |\sigma|$, $V^T$ is the transpose and $\overline V$ the entrywise complex conjugate, and $V_m$ acts on registers 2 and 3.
--
--   The construction depends on the protocol only through $V_m$, $p_m$ and $b_m$, never on the state to be prepared.
--
--   **Formalization Note** The paper writes $U_m^T$, $U_m^*$ and a $\operatorname{Tr}_3$ over the one-dimensional leftover of the ancilla $|0\rangle$; with the isometry $V_m = U_m(\cdot\otimes|0\rangle)$ there is no leftover and no $\operatorname{Tr}_3$. $|\Phi_d\rangle\langle\Phi_d|\otimes b_m^T$ is indexed by $(\iota\times\iota)\times K_m$ and regrouped as $\iota\times(\iota\times K_m)$ along `Equiv.prodAssoc`.
-- source:
--   Leung–Shor, Oblivious remote state preparation, arXiv:quant-ph/0201008v1, eq. (4), p.3

import Mathlib
import Definitions.Def_ObliviousRSP_maxEnt

open scoped Kronecker Matrix

namespace ObliviousRSP

/-- Leung–Shor, *Oblivious remote state preparation*, arXiv:quant-ph/0201008v1, eq. (4), p.3: the POVM element of Alice's `φ`-independent measurement `𝓜`,
`M_m = d d′ p_m Tr_3 (I_1 ⊗ U_m23^T)(|Φ_d⟩⟨Φ_d|_12 ⊗ b_m3^{(out) T})(I_1 ⊗ U_m23^*)`,
an operator on `ℂ^ι ⊗ ℂ^σ` (the specimen and Alice's half).

**Formalization Note.** Bob's `U_m(· ⊗ |0⟩)` is the isometry `V m : Matrix (ι × K m) σ ℂ`, so
`U_m^T` is `(V m)ᵀ`, `U_m^*` is the entrywise conjugate `(V m).map star` (not `ᴴ`), and
`b_m^T` is `(b m)ᵀ`. `|Φ_d⟩⟨Φ_d| ⊗ b_mᵀ` is indexed by `(ι × ι) × K m` and is reindexed to
`ι × (ι × K m)` along `Equiv.prodAssoc ι ι (K m)`, so `V m` acts on registers 2, 3. The
paper's `Tr_3` traces a one-dimensional leftover of `U_m^T` (the ancilla `|0⟩`); with the
isometry there is no leftover and no `Tr_3`. `d = Fintype.card ι`, `d′ = Fintype.card σ`. -/
noncomputable def povmElement {ι σ M : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
    {K : M → Type} [∀ m, Fintype (K m)] [∀ m, DecidableEq (K m)]
    (V : (m : M) → Matrix (ι × K m) σ ℂ) (p : M → ℝ) (b : (m : M) → Matrix (K m) (K m) ℂ)
    (m : M) : Matrix (ι × σ) (ι × σ) ℂ :=
  ((Fintype.card ι : ℂ) * (Fintype.card σ : ℂ) * (p m : ℂ)) •
    (((1 : Matrix ι ι ℂ) ⊗ₖ (V m)ᵀ) *
      Matrix.reindex (Equiv.prodAssoc ι ι (K m)) (Equiv.prodAssoc ι ι (K m))
        (maxEnt ι ⊗ₖ (b m)ᵀ) *
      ((1 : Matrix ι ι ℂ) ⊗ₖ (V m).map star))

end ObliviousRSP


