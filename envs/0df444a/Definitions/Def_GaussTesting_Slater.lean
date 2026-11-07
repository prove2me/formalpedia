-- Prove2me | Definitions.Def_GaussTesting_Slater
-- name    : GaussTesting_Slater
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:01:26.570052+00:00
-- url     : https://prove2.me/theorems/0e65460c-cb25-4f0f-b3cd-34dced3974c3
-- title:
--   Slater determinants $\mathcal S\subset G_f$
-- statement:
--   The **Slater determinants** on $n$ modes are the pure fermionic Gaussian states that are eigenstates of the number operator $N=\sum_{i=1}^n c_i^\dagger c_i$:
--
--   $$
--   \mathcal S=\{\psi\in G_f:\ N\psi=\eta\,\psi \text{ for some }\eta\}.
--   $$
--
--   They are the mean-field states of Hartree–Fock theory.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), §2.2, p.18

import Definitions.Def_GaussTesting_Gf

namespace GaussTesting

/-- The Slater determinants `𝒮 ⊂ G_f`: pure fermionic Gaussian states that are eigenstates of the number
operator `N = ∑ᵢ cᵢ†cᵢ`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), §2.2, p.18 ("Slater determinants `𝒮 ⊂ G_f` are the subset of pure fermionic
Gaussian states that are also eigenstates of the number operator `N = ∑ⁿᵢ₌₁ c†ᵢcᵢ`").

**Formalization Note.** Elements of `G_f` are nonzero, so the eigenvector condition `Nψ = ηψ` is the
eigenstate condition. The class is closed under global phase. -/
noncomputable def Slater (n : ℕ) : Set (Ell2 (FermiCap.Gaussian.Qubits n)) :=
  {ψ | ψ ∈ Gf n ∧ ∃ η : ℂ, (numberOp n).mulVec (fun x => ψ x) = η • (fun x => ψ x)}

end GaussTesting


