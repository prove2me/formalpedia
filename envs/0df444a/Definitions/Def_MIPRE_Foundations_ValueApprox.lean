-- Prove2me | Definitions.Def_MIPRE_Foundations_ValueApprox
-- name    : MIPRE_Foundations_ValueApprox
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:06:29.446987+00:00
-- url     : https://prove2.me/theorems/116e80ed-adda-4d72-a077-16a135b3bbf4
-- title:
--   The perturbation split of Born expectations, groundwork for approximating the quantum value from below
-- statement:
--   This bundle is the groundwork module of `lem:value-lower-approx` (the $\mathrm{MIP}^{*} \subseteq \mathrm{RE}$ direction). It contributes no definition and three exact algebraic identities about Born expectations $\langle\psi, M\psi\rangle = \psi^{*}\cdot(M\psi)$ (`star ψ ⬝ᵥ (M *ᵥ ψ)`) on $\mathbb{C}^{d}$, with no norms and no estimates, which let the two players' operators and the state of a candidate strategy be perturbed one at a time (blueprint `lem:perturbation-split`).
--
--   `MIPRE.ValueApprox.kronecker_sub_kronecker`: for square matrices $A, A'$ indexed by $d_A$ and $B, B'$ indexed by $d_B$ (arbitrary index types), $A \otimes B - A' \otimes B' = (A - A') \otimes B + A' \otimes (B - B')$.
--
--   `MIPRE.ValueApprox.dotProduct_mulVec_perturb`: for $M, N$ square matrices over a finite index type $d$ and vectors $\psi, \varphi : d \to \mathbb{C}$,
--   $$\langle\psi, M\psi\rangle - \langle\varphi, N\varphi\rangle = \langle\psi, (M-N)\psi\rangle + \langle\psi-\varphi, N\psi\rangle + \langle\varphi, N(\psi-\varphi)\rangle,$$
--   an operator term in which only $M - N$ appears plus two state terms in which only $\psi - \varphi$ appears.
--
--   `MIPRE.ValueApprox.dotProduct_kronecker_perturb`, the split a candidate strategy needs: for $d_A, d_B$ finite, $\langle\psi,(A\otimes B)\psi\rangle - \langle\varphi,(A'\otimes B')\varphi\rangle$ equals the sum of the four terms $\langle\psi,((A-A')\otimes B)\psi\rangle$, $\langle\psi,(A'\otimes(B-B'))\psi\rangle$, $\langle\psi-\varphi,(A'\otimes B')\psi\rangle$ and $\langle\varphi,(A'\otimes B')(\psi-\varphi)\rangle$, each moving exactly one of $A$, $B$ and $\psi$.
--
--   **Formalization Note**. `⬝ᵥ` is Mathlib's dot product and `*ᵥ` matrix-vector multiplication, so $\langle\psi, M\psi\rangle$ is `star ψ ⬝ᵥ (M *ᵥ ψ)` and no inner-product-space structure is involved; `⊗ₖ` is the Kronecker product on matrices indexed by the product type. The identities are equalities in $\mathbb{C}$ and in matrices respectively, with no hypotheses on the matrices or vectors. The decidability statements of the module docstring (operator-norm constraints as positive-semidefiniteness tests) are not among the declarations of this bundle.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/ValueApprox.lean; blueprint lem:perturbation-split

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/ValueApprox.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games

/-!
# Approximating the quantum value from below

Groundwork for `lem:value-lower-approx`, the `MIP* ⊆ RE` direction: a machine that,
given a game `G` and a rational `t`, halts if and only if `val*(G) > t`. It enumerates
candidate strategies with Gaussian-rational entries, computes their values exactly, and
halts on a certificate; `val*` is by definition a supremum over finite-dimensional
tensor-product strategies (`MIPRE.quantumValue`), so no infinite-dimensional truncation
and no semidefinite programming enter.

The decomposition followed here is the one validated in the adversarial campaign
recorded in `vidick/mipre-proof` (ledger nodes `1.1.7.2.1` to `1.1.7.2.6`); see
`planning/ledger-informed-plan.md`. This file carries the part of node `1.1.7.2.1`
that makes the candidate set decidable: an operator-norm constraint on a Hermitian
matrix is equivalent to two positive-semidefiniteness tests, and positive
semidefiniteness of a Gaussian-rational Hermitian matrix is decidable.

Everything is stated through the quadratic form `⟨x| M |x⟩` rather than a matrix norm.
That is faithful — for Hermitian `M` the operator norm *is* the supremum of
`|⟨x| M |x⟩|` over unit `x` — and it keeps the statements independent of which of
Mathlib's several matrix-norm instances is in scope.
-/

namespace MIPRE.ValueApprox

open Matrix
open scoped ComplexOrder Kronecker

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ### Perturbing a candidate

Nodes `1.1.7.2.3` (stability) and `1.1.7.2.4` (density) both compare the value of an
approximate candidate with the value of an exact strategy nearby, and both do it by the
same algebra: split the difference of two Born expectations into a part where only the
operators moved and a part where only the state moved. The identities below are that
split, exactly and with no estimates in them; the analytic bounds of those two nodes are
obtained by bounding each term separately. -/

/-- A difference of Kronecker products splits over the two factors. This is what lets the
two players' operators be perturbed one at a time. -/
theorem kronecker_sub_kronecker {dA dB : Type*} (A A' : Matrix dA dA ℂ) (B B' : Matrix dB dB ℂ) :
    A ⊗ₖ B - A' ⊗ₖ B' = (A - A') ⊗ₖ B + A' ⊗ₖ (B - B') := by
  ext p q
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.kroneckerMap_apply]
  ring

omit [DecidableEq d] in
/-- **The perturbation split.** The difference of the Born expectations of `(M, ψ)` and
`(N, φ)` is an operator term, in which only `M - N` appears, plus two state terms, in which
only `ψ - φ` appears. Exact: no norms and no estimates. -/
theorem dotProduct_mulVec_perturb (M N : Matrix d d ℂ) (ψ φ : d → ℂ) :
    star ψ ⬝ᵥ (M *ᵥ ψ) - star φ ⬝ᵥ (N *ᵥ φ)
      = star ψ ⬝ᵥ ((M - N) *ᵥ ψ) + star (ψ - φ) ⬝ᵥ (N *ᵥ ψ)
        + star φ ⬝ᵥ (N *ᵥ (ψ - φ)) := by
  simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, star_sub]
  ring

/-- The split a candidate strategy actually needs: a bipartite Born expectation with both
players' operators and the state perturbed at once decomposes into four terms, each moving
exactly one of `A`, `B` and `ψ`. Combining `kronecker_sub_kronecker` with
`dotProduct_mulVec_perturb`. -/
theorem dotProduct_kronecker_perturb {dA dB : Type*} [Fintype dA] [Fintype dB]
    (A A' : Matrix dA dA ℂ) (B B' : Matrix dB dB ℂ) (ψ φ : dA × dB → ℂ) :
    star ψ ⬝ᵥ ((A ⊗ₖ B) *ᵥ ψ) - star φ ⬝ᵥ ((A' ⊗ₖ B') *ᵥ φ)
      = star ψ ⬝ᵥ (((A - A') ⊗ₖ B) *ᵥ ψ) + star ψ ⬝ᵥ ((A' ⊗ₖ (B - B')) *ᵥ ψ)
        + star (ψ - φ) ⬝ᵥ ((A' ⊗ₖ B') *ᵥ ψ)
        + star φ ⬝ᵥ ((A' ⊗ₖ B') *ᵥ (ψ - φ)) := by
  rw [dotProduct_mulVec_perturb (A ⊗ₖ B) (A' ⊗ₖ B') ψ φ, kronecker_sub_kronecker,
    Matrix.add_mulVec, dotProduct_add]

end MIPRE.ValueApprox


