-- Prove2me | Definitions.Def_WildeQIT_Activation_omegaState
-- name    : WildeQIT_Activation_omegaState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T19:12:00.098811+00:00
-- url     : https://prove2.me/theorems/fb75cdee-7622-4064-8f6c-b64469c38200
-- title:
--   The output state $\omega_{RB_1B_2E_1E_2}=(U^{\mathcal N_1}\otimes U^{\mathcal N_2})(\phi_{RA_1A_2})$
-- statement:
--   For channels $\mathcal N_1$, $\mathcal N_2$ with isometric extensions $U^{\mathcal N_1}_{A_1\to B_1E_1}$, $U^{\mathcal N_2}_{A_2\to B_2E_2}$ and a pure state $|\phi\rangle_{RA_1A_2}$,
--
--   $$
--   \omega_{RB_1B_2E_1E_2}\equiv\left(U^{\mathcal N_1}_{A_1\to B_1E_1}\otimes U^{\mathcal N_2}_{A_2\to B_2E_2}\right)(\phi_{RA_1A_2}),
--   $$
--
--   the pure state $|\omega\rangle\langle\omega|$ with $|\omega\rangle=(I_R\otimes U^{\mathcal N_1}\otimes U^{\mathcal N_2})|\phi\rangle$. This is (24.164).
--
--   **Formalization Note** The output systems are ordered as $R$, then $B_1B_2$, then $E_1E_2$, so $H(B_1B_2)_\omega$ and $H(E_1E_2)_\omega$ are entropies of iterated partial traces. The isometric extensions are the Kraus-built ones; any other choice gives the same entropies.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 24.8.1, eq. (24.164), p. 684

import Definitions.Def_WildeQIT_Degradable_isometricExtension
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 24.8.1, p. 684, eq. (24.164).
-/

open Matrix
open scoped Kronecker

namespace WildeQIT.Activation

/-- **The output state `ω_{RB1B2E1E2}`** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, (24.164), p. 684):
`ω ≡ (U^{N1}_{A1→B1E1} ⊗ U^{N2}_{A2→B2E2})(ϕ_{RA1A2})` for a pure state `|ϕ⟩_{RA1A2}`, that is
`|ω⟩⟨ω|` with `|ω⟩ = (I_R ⊗ U^{N1} ⊗ U^{N2})|ϕ⟩`.

**Formalization Note.** `U^{N1} ⊗ U^{N2}` is the Kronecker product of the canonical isometric
extensions, an operator from `a1 × a2` to `(b1 × ι1) × (b2 × ι2)`; its output is regrouped by
`Equiv.prodProdProdComm` as `(b1 × b2) × (ι1 × ι2)`, i.e. `B1B2E1E2`. The reference `R` is the
left factor. So `H(B1B2)_ω` is the entropy of `Tr_{E1E2}(Tr_R ω)` and `H(E1E2)_ω` that of
`Tr_{B1B2}(Tr_R ω)`. -/
noncomputable def omegaState {r a1 b1 a2 b2 : Type} [Fintype r] [Fintype a1] [Fintype b1]
    [Fintype a2] [Fintype b2] [DecidableEq a1] [DecidableEq a2]
    (N1 : QChannel a1 b1) (N2 : QChannel a2 b2) (ϕ : r × (a1 × a2) → ℂ) :
    Matrix (r × ((b1 × b2) × (N1.ι × N2.ι))) (r × ((b1 × b2) × (N1.ι × N2.ι))) ℂ :=
  let U : Matrix ((b1 × b2) × (N1.ι × N2.ι)) (a1 × a2) ℂ :=
    Matrix.reindex (Equiv.prodProdProdComm b1 N1.ι b2 N2.ι) (Equiv.refl _)
      (WildeQIT.Degradable.isometricExtension N1 ⊗ₖ WildeQIT.Degradable.isometricExtension N2)
  let w : r × ((b1 × b2) × (N1.ι × N2.ι)) → ℂ := fun ry => ∑ x, U ry.2 x * ϕ (ry.1, x)
  vecMulVec w (star w)

end WildeQIT.Activation


