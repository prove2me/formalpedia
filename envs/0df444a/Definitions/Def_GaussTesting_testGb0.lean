-- Prove2me | Definitions.Def_GaussTesting_testGb0
-- name    : GaussTesting_testGb0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:41.46743+00:00
-- url     : https://prove2.me/theorems/eaef537a-c9b5-4421-893f-b39a0c913208
-- title:
--   The zero-mean bosonic Gaussian test $\Pi_{\mathrm{sym}}\Pi_{\ker\Gamma}$
-- statement:
--   The two-copy operator of Girardi et al. is
--
--   $$
--   \Gamma=i\sum_{i=1}^n\big(a_i\otimes a_i^\dagger-a_i^\dagger\otimes a_i\big)\qquad(7.1),
--   $$
--
--   and the zero-mean bosonic Gaussian test is $\Pi^{(1,2)}_{\mathrm{test},G_{b,0}}=\Pi^{(1,2)}_{\mathrm{sym}}\Pi_{\ker\Gamma}$. Since $\mathrm{SWAP}\,\Gamma\,\mathrm{SWAP}=-\Gamma$, the kernel of $\Gamma$ is swap-invariant, the two projectors commute, and their product is the projector onto $\ker\Gamma\cap\mathrm{Sym}^2(\mathcal H)$.
--
--   **Formalization Note** $\ker\Gamma=\{f\in\ell^2:\ (\Gamma f)(x)=0\ \forall x\}$, with $\Gamma$ applied to coefficient functions (the kernel of the closure of the unbounded $\Gamma$). The Lean subspace is $\ker\Gamma\cap\mathrm{Sym}^2(\mathcal H)$.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), §7, eq. (7.1), p.64

import Definitions.Def_GaussTesting_quadrature
import Definitions.Def_GaussTesting_symSub

namespace GaussTesting

/-- The two-copy operator `Γ = i ∑ᵢ (aᵢ ⊗ aᵢ† − aᵢ† ⊗ aᵢ)` (7.1), acting on coefficient functions of
`ℋ^{⊗2}` (register `0` = first factor). -/
noncomputable def gammaOp {n : ℕ} (F : (Fin 2 → Fin n → ℕ) → ℂ) : (Fin 2 → Fin n → ℕ) → ℂ :=
  fun x => Complex.I * ∑ j, (onReg 0 (lower j) (onReg 1 (raise j) F) x -
    onReg 0 (raise j) (onReg 1 (lower j) F) x)

/-- The zero-mean bosonic Gaussian test subspace `ker Γ ∩ Sym²(ℋ)`; its projector is
`Π^{(1,2)}_test,G_{b,0} = Π^{(1,2)}_sym Π_{ker Γ}`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), §7, eq. (7.1) and p.64 ("Let `Π_{ker Γ}` be the projector onto the
`0`-eigenspace of `Γ`. Our property tester for zero-mean bosonic Gaussian states will be the projector
onto the symmetrization of `Π_{ker Γ}`: `Π^{(1,2)}_test,G_{b,0} = Π^{(1,2)}_sym Π_{ker Γ(1,2)}`").

**Formalization Note.**
* `ker Γ` is `{f ∈ ℓ² : (Γf)(x) = 0 for all x}` with `Γ` applied to coefficients (`Γ` is unbounded; this
  is the kernel of its closure).
* `SWAP · Γ · SWAP = −Γ`, so `ker Γ` is swap-invariant, `Π_sym` and `Π_{ker Γ}` commute, and their
  product is the projector onto `ker Γ ∩ Sym²(ℋ)`, the subspace used here.
* The set is a closed subspace; span and closure only package it as a `ClosedSubmodule`. -/
noncomputable def testGb0 (n : ℕ) : ClosedSubmodule ℂ (Ell2 (Fin 2 → Fin n → ℕ)) :=
  (Submodule.span ℂ {f : Ell2 (Fin 2 → Fin n → ℕ) | (∀ x, gammaOp (fun y => f y) x = 0) ∧
      ∀ σ : Equiv.Perm (Fin 2), permVec σ f = f}).closure

end GaussTesting


