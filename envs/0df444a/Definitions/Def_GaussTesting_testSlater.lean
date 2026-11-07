-- Prove2me | Definitions.Def_GaussTesting_testSlater
-- name    : GaussTesting_testSlater
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:47.435003+00:00
-- url     : https://prove2.me/theorems/47cae292-6545-4beb-8ee2-cb3aca67e3b9
-- title:
--   The Slater test: the kernel of $K=G^\dagger G$
-- statement:
--   With $G=\sum_{j=1}^n c_j\otimes c_j^\dagger$, the two-copy operator of Definition 5.2 is $K=G^\dagger G$. Given two copies of a state, the Slater tester measures $K$ and accepts iff $0$ is obtained, i.e. it is the projective test $\Pi_{\mathrm{test},\mathcal S}=\Pi_{\ker K}$.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), Definition 5.2, p.41

import Definitions.Def_GaussTesting_annihilator

namespace GaussTesting

/-- `G = ∑ⱼ cⱼ ⊗ cⱼ†`. -/
noncomputable def gOp (n : ℕ) :
    Matrix (Fin 2 → FermiCap.Gaussian.Qubits n) (Fin 2 → FermiCap.Gaussian.Qubits n) ℂ :=
  ∑ j, kron2 (annihilator n j) (annihilator n j).conjTranspose

/-- The two-copy operator `K = G†G` of Definition 5.2. -/
noncomputable def kOp (n : ℕ) :
    Matrix (Fin 2 → FermiCap.Gaussian.Qubits n) (Fin 2 → FermiCap.Gaussian.Qubits n) ℂ :=
  (gOp n).conjTranspose * gOp n

/-- The Slater test subspace `ker K`: the tester measures `K` on two copies and accepts iff `0` is
obtained, i.e. it is the projective test `Π_test,𝒮 = Π_{ker K}`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), Definition 5.2, p.41 ("Define the two-copy operator `K := G†G`, where
`G := ∑ⁿⱼ₌₁ cⱼ ⊗ c†ⱼ`. Given two copies of the state `ρ`, the tester measures the observable `K` and
accepts if and only if `0` is obtained").

**Formalization Note.** Plain tensor product of the Jordan–Wigner qubit spaces (`kron2`), as in §5.4. -/
noncomputable def testSlater (n : ℕ) :
    ClosedSubmodule ℂ (Ell2 (Fin 2 → FermiCap.Gaussian.Qubits n)) :=
  matKer (kOp n)

end GaussTesting


