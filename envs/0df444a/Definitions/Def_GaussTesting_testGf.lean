-- Prove2me | Definitions.Def_GaussTesting_testGf
-- name    : GaussTesting_testGf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:49.693214+00:00
-- url     : https://prove2.me/theorems/bee72b98-e822-43cd-a1bb-9bb6d09831f7
-- title:
--   The fermionic Gaussian test $\Pi_{\mathrm{test},G_f}$: the kernel of $\Lambda$
-- statement:
--   Tsirel'son's two-copy operator is
--
--   $$
--   \Lambda=2\sum_{i=1}^n\big(c_i\otimes c_i^\dagger+c_i^\dagger\otimes c_i\big)\qquad(4.1),
--   $$
--
--   which equals $\sum_{p=1}^{2n}\gamma_p\otimes\gamma_p$. The fermionic Gaussian test $\Pi_{\mathrm{test},G_f}$ is the projector onto $\ker\Lambda\subseteq(\bigwedge\mathbb C^n)^{\otimes2}$; by Bravyi, $|\psi\rangle^{\otimes2}\in\ker\Lambda$ exactly for fermionic Gaussian $\psi$.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), eq. (4.1), p.28; p.29

import Definitions.Def_GaussTesting_annihilator

namespace GaussTesting

/-- Tsirel'son's two-copy operator `Λ = 2 ∑ᵢ (cᵢ ⊗ cᵢ† + cᵢ† ⊗ cᵢ)` (4.1), equal to `∑_p γ_p ⊗ γ_p`. -/
noncomputable def lambdaOp (n : ℕ) :
    Matrix (Fin 2 → FermiCap.Gaussian.Qubits n) (Fin 2 → FermiCap.Gaussian.Qubits n) ℂ :=
  (2 : ℂ) • ∑ i, (kron2 (annihilator n i) (annihilator n i).conjTranspose +
    kron2 (annihilator n i).conjTranspose (annihilator n i))

/-- The fermionic Gaussian test subspace `ker Λ ⊆ (⋀ℂⁿ)^{⊗2}`; its projector is `Π_test,G_f`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), eq. (4.1), p.28, and p.29 ("we define `Π_test,G_f` to be the two-copy projector
onto the kernel of `Λ`").

**Formalization Note.** The two copies are combined by the plain tensor product of the Jordan–Wigner
qubit spaces, as in (4.1) and §5.4 of the paper (`kron2`). -/
noncomputable def testGf (n : ℕ) :
    ClosedSubmodule ℂ (Ell2 (Fin 2 → FermiCap.Gaussian.Qubits n)) :=
  matKer (lambdaOp n)

end GaussTesting


