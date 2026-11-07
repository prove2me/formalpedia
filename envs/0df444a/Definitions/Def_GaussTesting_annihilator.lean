-- Prove2me | Definitions.Def_GaussTesting_annihilator
-- name    : GaussTesting_annihilator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:28.802403+00:00
-- url     : https://prove2.me/theorems/99108366-687c-4c68-b6d0-db2fcdb557f7
-- title:
--   Fermionic annihilation operators $c_j$, two-copy tensor products and the number operator
-- statement:
--   On the $n$-mode fermionic Fock space (Jordan–Wigner qubits, occupation $1$ = occupied), the annihilation operator of mode $j$ is
--
--   $$
--   c_j=\tfrac12\big(\gamma_{2j-1}+i\gamma_{2j}\big)=Z\otimes\cdots\otimes Z\otimes|0\rangle\langle1|\otimes I\otimes\cdots\otimes I,
--   $$
--
--   where $\gamma_{2j-1}=c_j+c_j^\dagger$ and $\gamma_{2j}=-i(c_j-c_j^\dagger)$ are the Majorana operators. The module also defines the two-copy tensor product $A\otimes B$ of matrices, the number operator $N=\sum_j c_j^\dagger c_j$, and the kernel $\ker M$ of a matrix as a closed subspace.
--
--   With these conventions the occupation basis $|x\rangle$ is the paper's Fock basis $|S\rangle=c^\dagger_{S_1}\cdots c^\dagger_{S_{|S|}}|0^n\rangle$, $S_1<\dots<S_{|S|}$.
--
--   **Formalization Note** Modes and Majoranas are $0$-based: the paper's $\gamma_{2i-1},\gamma_{2i}$ are `majorana n (2j)`, `majorana n (2j+1)` with $j=i-1$, from the published definition `FermiCap.Gaussian.majorana`. Two copies are combined by the plain tensor product of the Jordan–Wigner qubit spaces, as in (4.1) and §5.4.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), §2.2, p.17; eq. (4.1), p.28; Definition 5.2, p.41

import Definitions.Def_FermiCap_Gaussian_Majorana
import Definitions.Def_GaussTesting_Ell2

namespace GaussTesting

/-- The fermionic annihilation operator `c_j` on `n` modes, `c_j = (γ_{2j−1} + iγ_{2j})/2` in the
paper's 1-based Majorana labels; in Jordan–Wigner form `c_j = Z ⊗ ⋯ ⊗ Z ⊗ |0⟩⟨1| ⊗ I ⊗ ⋯ ⊗ I`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), §2.2, p.17 (`γ_{2i−1} = cᵢ + cᵢ†`, `γ_{2i} = −i(cᵢ − cᵢ†)`, Fock states
`|x₁,…,x_n⟩ = ∏ᵢ (cᵢ†)^{xᵢ}|0ⁿ⟩`).

**Formalization Note.** Modes and Majoranas are 0-based: the paper's mode `i` is `j = i − 1`, and its
`γ_{2i−1}`, `γ_{2i}` are `majorana n (2j)`, `majorana n (2j+1)` of the published definition
`FermiCap.Gaussian.majorana` (Jordan–Wigner strings `Z…Z X` and `Z…Z Y`). The occupation basis
`x : Fin n → Fin 2` (`1` = occupied) is the paper's Fock basis with its sign convention
`|S⟩ = c†_{S₁}⋯c†_{S_|S|}|0ⁿ⟩`, `S₁ < ⋯`, since each `c†` acts while all lower modes are empty. -/
noncomputable def annihilator (n : ℕ) (j : Fin n) : FermiCap.Gaussian.Op n :=
  (1 / 2 : ℂ) • (FermiCap.Gaussian.majorana n ⟨2 * j.val, by omega⟩ +
    Complex.I • FermiCap.Gaussian.majorana n ⟨2 * j.val + 1, by omega⟩)

/-- The two-copy tensor product `A ⊗ B` of matrices, on basis labels `Fin 2 → α`
(copy `0` = first tensor factor, copy `1` = second). -/
def kron2 {α : Type*} (A B : Matrix α α ℂ) : Matrix (Fin 2 → α) (Fin 2 → α) ℂ :=
  fun x y => A (x 0) (y 0) * B (x 1) (y 1)

/-- The number operator `N = ∑ⱼ cⱼ† cⱼ`. -/
noncomputable def numberOp (n : ℕ) : FermiCap.Gaussian.Op n :=
  ∑ j, (annihilator n j).conjTranspose * annihilator n j

/-- The kernel of a matrix `M` on a finite basis, as a closed subspace of `ℓ²`; its projector is "the
projector onto `ker M`" (onto the `0`-eigenspace of `M`).

**Formalization Note.** On a finite index type `{f | M f = 0}` is already a closed subspace; span and
closure add nothing. -/
noncomputable def matKer {α : Type*} [Fintype α] (M : Matrix α α ℂ) :
    ClosedSubmodule ℂ (Ell2 α) :=
  (Submodule.span ℂ {f : Ell2 α | M.mulVec (fun x => f x) = 0}).closure

end GaussTesting


