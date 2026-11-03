-- Prove2me | Definitions.Def_WildeQIT_EntBreaking_qcChannel
-- name    : WildeQIT_EntBreaking_qcChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:13.861958+00:00
-- url     : https://prove2.me/theorems/22997582-3d85-4d84-88de-52d715104fda
-- title:
--   Quantum–classical (measurement) channel $\rho\mapsto\sum_x\mathrm{Tr}\{\Lambda^x\rho\}|x\rangle\langle x|$ (Definition 4.6.7)
-- statement:
--   Let $\{\Lambda^x_A\}_{x}$ be a family of operators on $\mathcal H_A$ indexed by a finite set, and let $\{|x\rangle_X\}$ be the standard orthonormal basis of the classical system $\mathcal H_X$. The **quantum–classical channel** of the family is the linear map
--
--   $$
--   \mathcal M_{A\to X}(X_A)=\sum_x \operatorname{Tr}\{\Lambda^x_AX_A\}\,|x\rangle\langle x|_X ,
--   $$
--
--   the diagonal matrix with entries $\operatorname{Tr}\{\Lambda^x_AX_A\}$. When $\{\Lambda^x_A\}$ is a POVM this is the measurement channel (4.288) of Definition 4.6.7; the POVM condition is a hypothesis of the statements that use it.
--
--   **Formalization Note** The book defines the map on density operators; it is identified with its linear extension (p. 149), which is the same formula on all operators.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 4.6.7, eq. (4.288), p. 166

import Mathlib

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §4.6.6,
Definition 4.6.7 (Quantum–Classical Channels), (4.288), p. 166.
-/

namespace WildeQIT.EntBreaking

open scoped Matrix

/-- **Definition 4.6.7 (Quantum–Classical Channel)**, Wilde, *From Classical to Quantum Shannon
Theory*, arXiv:1106.1445v8, p. 166: given a POVM `{Λ^x_A}` on system `A` and an orthonormal basis
`{|x⟩_X}` of `ℋ_X`, the quantum–classical channel acts as `ρ_A ↦ ∑_x Tr{Λ^x_A ρ_A} |x⟩⟨x|_X` (4.288).

`qcChannel Λ` is this map, extended linearly to all operators: `X ↦ ∑_x Tr{Λ^x X} |x⟩⟨x|`, the
diagonal matrix with entries `Tr{Λ^x X}`. That `Λ` is a POVM is a hypothesis of the statements
that use it (`FuchsVdGraaf.IsPOVM`, Definition 4.2.1).

**Formalization Note.** The classical system `X` has the finite outcome set `x` as its index type
and `{|x⟩}` is its standard basis. The linear extension of (4.288) from density operators to
`L(ℋ_A)` is the same formula (the book identifies a channel with its linear extension, p. 149). -/
def qcChannel {a x : Type} [Fintype a] [DecidableEq x] (Λ : x → Matrix a a ℂ) :
    Matrix a a ℂ →ₗ[ℂ] Matrix x x ℂ where
  toFun X := Matrix.diagonal fun k => (Λ k * X).trace
  map_add' X Y := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.mul_add, Matrix.trace_add]
  map_smul' c X := by
    ext i j
    by_cases h : i = j <;> simp [h]

end WildeQIT.EntBreaking


