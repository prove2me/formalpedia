-- Prove2me | Definitions.Def_TolProdTest_blockMarginal
-- name    : TolProdTest_blockMarginal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:25:31.300144+00:00
-- url     : https://prove2.me/theorems/dd453d9e-c407-4c7c-94f1-6f4d406dc6a1
-- title:
--   Block marginal $\rho_c=\mathrm{Tr}_{-c}\,\rho$
-- statement:
--   For a coloring $C$ and a colour $c$, the **block marginal** $\rho_c=\mathrm{Tr}_{-c}\rho$ is the operator on $\mathcal H_c=\bigotimes_{i\in B_c}\mathbb C^d$ obtained by tracing out all other blocks:
--
--   $$
--   (\rho_c)_{x,y}=\sum_{z}\rho_{(x,z),(y,z)},
--   $$
--
--   the sum running over basis strings $z$ of the sites outside $B_c$. The module also defines the extension $A\otimes I$ of a block operator $A$ to the whole space.
--
--   The spectral projectors of these marginals drive the blockwise compression of Lemma 3.6.
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), §2.1, p.8; Lemma 3.6, p.14

import Mathlib

set_option autoImplicit false

namespace TolProdTest

/-- Glue a basis string `x` of block `B_c = C⁻¹(c)` and a basis string `z` of the other sites into a global basis
string. -/
def glue {S ι : Type} [DecidableEq ι] {d : ℕ} (C : S → ι) (c : ι) (x : {i // C i = c} → Fin d)
    (z : {i // C i ≠ c} → Fin d) : S → Fin d :=
  fun i => if h : C i = c then x ⟨i, h⟩ else z ⟨i, h⟩

/-- **Block marginal** `ρ_c = Tr_{−c} ρ`, Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), §2.1, p.8: "For a block B_c, we write ρ_c = Tr_{−c} ρ for its
marginal, where Tr_{−c} traces out all blocks other than c." It is the operator on `H_c` (basis
`{i // C i = c} → Fin d`) with entries `(ρ_c)_{xy} = Σ_z ρ_{(x,z),(y,z)}`. -/
def blockMarginal {S ι : Type} [Fintype S] [DecidableEq S] [DecidableEq ι] {d : ℕ} (C : S → ι) (c : ι)
    (ρ : Matrix (S → Fin d) (S → Fin d) ℂ) :
    Matrix ({i // C i = c} → Fin d) ({i // C i = c} → Fin d) ℂ :=
  Matrix.of fun x y => ∑ z : {i // C i ≠ c} → Fin d, ρ (glue C c x z) (glue C c y z)

/-- The operator `A ⊗ I` on the whole space for an operator `A` on block `B_c` ("we … omit identity tensor
factors when the registers are clear from context", p.8): entry `(x, y)` is `A_{x|_c, y|_c}` if `x` and `y`
agree outside `B_c`, and `0` otherwise. -/
def liftBlock {S ι : Type} [Fintype S] [DecidableEq S] [DecidableEq ι] {d : ℕ} (C : S → ι) (c : ι)
    (A : Matrix ({i // C i = c} → Fin d) ({i // C i = c} → Fin d) ℂ) :
    Matrix (S → Fin d) (S → Fin d) ℂ :=
  Matrix.of fun x y =>
    if (∀ i, C i ≠ c → x i = y i) then A (fun i => x i.1) (fun i => y i.1) else 0

end TolProdTest


