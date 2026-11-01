-- Prove2me | Definitions.Def_WildeQIT_Schumacher_idTensorApply
-- name    : WildeQIT_Schumacher_idTensorApply
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:14.971985+00:00
-- url     : https://prove2.me/theorems/90429a3f-b261-44bf-a1a1-b07b1751823a
-- title:
--   A channel acting on the second system, $(\mathrm{id}_R\otimes\mathcal N)(X_{RB})$
-- statement:
--   Let $\mathcal N_{B\to C}$ be a quantum channel with Kraus operators $\{V_l\}$, $\sum_l V_l^\dagger V_l = I_B$. For an operator $X_{RB}$ on $\mathcal H_R\otimes\mathcal H_B$,
--
--   $$
--   (\mathrm{id}_R\otimes\mathcal N_{B\to C})(X_{RB}) = \sum_l (I_R\otimes V_l)\,X_{RB}\,(I_R\otimes V_l)^\dagger .
--   $$
--
--   In Schumacher compression the encoder and decoder act on $A^n$ and $W$ only, the reference system $R^n$ being untouched; this is how $(\mathcal D\circ\mathcal E)((\phi^\rho_{RA})^{\otimes n})$ in (18.5) is read.
--
--   **Formalization Note** The channel is the published `WildeQIT.QChannel` (Choi–Kraus form, which by Theorem 4.4.1 represents every quantum channel). $\mathcal H_R\otimes\mathcal H_B$ is indexed by `r × b` with Mathlib's Kronecker product.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §18.1, eq. (18.5), p. 523

import Definitions.Def_WildeQIT_QChannel
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §18.1, eq. (18.5), p. 523:
the encoding and decoding channels act on the systems `Aⁿ` (resp. `W`) only, the reference system
`Rⁿ` being untouched: `(D_{W→Âⁿ} ∘ E_{Aⁿ→W})((ϕ^ρ_{RA})^{⊗n})` means `(id_{Rⁿ} ⊗ (D ∘ E))(…)`.
-/

open Matrix

namespace WildeQIT.Schumacher

/-- **A channel acting on the second system** `(id_R ⊗ 𝒩_{B→C})(X_{RB})` (Wilde,
arXiv:1106.1445v8, §18.1, eq. (18.5), p. 523; channels in Choi–Kraus form, Theorem 4.4.1).
For a quantum channel `𝒩` with Kraus operators `{V_l}`,
`(id_R ⊗ 𝒩)(X) = ∑_l (I_R ⊗ V_l) X (I_R ⊗ V_l)†`.

**Formalization Note.** The channel is the published `WildeQIT.QChannel` (Choi–Kraus form, which
by Theorem 4.4.1 represents every quantum channel); `ℋ_R ⊗ ℋ_B` is indexed by `r × b`, with
Mathlib's Kronecker product `⊗ₖ`. -/
noncomputable def idTensorApply {r b c : Type} [Fintype r] [DecidableEq r] [Fintype b]
    [DecidableEq b] [Fintype c] (N : WildeQIT.QChannel b c)
    (X : Matrix (r × b) (r × b) ℂ) : Matrix (r × c) (r × c) ℂ :=
  ∑ l, Matrix.kronecker (1 : Matrix r r ℂ) (N.K l) * X *
    (Matrix.kronecker (1 : Matrix r r ℂ) (N.K l))ᴴ

end WildeQIT.Schumacher


