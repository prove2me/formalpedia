-- Prove2me | Definitions.Def_GaussTesting_Supplement_slaterSwapOp
-- name    : GaussTesting_Supplement_slaterSwapOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:27:04.375451+00:00
-- url     : https://prove2.me/theorems/f52d8681-7992-47a2-be36-2b6b515d3a07
-- title:
--   The operator $P=\Pi^{(1,2)}_{\mathrm{test},\mathcal S}\,\mathrm{SWAP}^{(2,3)}\,\Pi^{(1,2)}_{\mathrm{test},\mathcal S}$ and the $\eta$-particle three-copy sector
-- statement:
--   Let $\mathcal H=\bigwedge\mathbb C^n$ be the fermionic Fock space of $n$ modes, with occupation basis $|x\rangle$, $x\in\{0,1\}^n$. On three copies $\mathcal H^{\otimes3}$ define
--
--   $$
--   P=\Pi^{(1,2)}_{\mathrm{test},\mathcal S}\cdot\mathrm{SWAP}^{(2,3)}\cdot\Pi^{(1,2)}_{\mathrm{test},\mathcal S},
--   $$
--
--   where $\Pi_{\mathrm{test},\mathcal S}$ is the orthogonal projector onto the kernel of the two-copy operator $K=G^\dagger G$, $G=\sum_{j=1}^n c_j\otimes c_j^\dagger$ (the Slater tester), $\Pi^{(1,2)}_{\mathrm{test},\mathcal S}=\Pi_{\mathrm{test},\mathcal S}\otimes I$ acts on the first two copies, and $\mathrm{SWAP}^{(2,3)}:|S_1\rangle\otimes|S_2\rangle\otimes|S_3\rangle\mapsto|S_1\rangle\otimes|S_3\rangle\otimes|S_2\rangle$ exchanges the second and third copies.
--
--   The **$\eta$-particle three-copy sector** is $(\bigwedge^\eta\mathbb C^n)^{\otimes3}\subseteq\mathcal H^{\otimes3}$, spanned by the basis vectors $|x_1\rangle\otimes|x_2\rangle\otimes|x_3\rangle$ in which every $x_s$ has exactly $\eta$ occupied modes.
--
--   The operator $P$ governs the spectral-gap analysis of the Slater tester: the symmetrized test operator equals $(\Pi^{(1,2)}_{\mathrm{test},\mathcal S}+2P)/3$ on the symmetric subspace, so the spectrum of $P$ on each sector determines the soundness of the tester.
--
--   **Formalization Note** $\mathcal H^{\otimes3}$ is $\ell^2(\mathrm{Fin}\,3\to(\mathrm{Fin}\,n\to\mathrm{Fin}\,2))$ with the plain (ungraded) tensor product of the Jordan–Wigner qubit spaces, as in the published `testSlater`; registers are 0-based, so the paper's copies $(1,2)$ are registers $0,1$ and $\mathrm{SWAP}^{(2,3)}$ is the register permutation `permVec (Equiv.swap 1 2)`, with no fermionic sign. $P$ is given as a function on vectors (`slaterSwapOp`); the sector is the submodule `particleSector n η`.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), §5.2, p.42 (the sector ⋀^η ℂⁿ and P); p.43 (SWAP^(2,3) and |S₁| = |S₂| = |S₃| = η); Definition 5.2, p.41

import Definitions.Def_GaussTesting_testSlater
import Definitions.Def_GaussTesting_amplSub
import Definitions.Def_GaussTesting_proj
import Definitions.Def_GaussTesting_symSub

namespace GaussTesting

namespace Supplement

/-- The `η`-particle three-copy sector `(⋀^η ℂⁿ)^{⊗3} ⊆ (⋀ℂⁿ)^{⊗3}`: the vectors supported on
occupation configurations `x : Fin 3 → (Fin n → Fin 2)` with exactly `η` occupied modes in every
register. -/
noncomputable def particleSector (n η : ℕ) :
    Submodule ℂ (Ell2 (Fin 3 → FermiCap.Gaussian.Qubits n)) where
  carrier := {f | ∀ x, f x ≠ 0 → ∀ s : Fin 3, (Finset.univ.filter (fun j => x s j = 1)).card = η}
  add_mem' := by
    intro f g hf hg x hx s
    by_cases h : f x = 0
    · have hg' : g x ≠ 0 := by
        intro h'
        apply hx
        simp [h, h']
      exact hg x hg' s
    · exact hf x h s
  zero_mem' := by
    intro x hx
    exact absurd (by simp) hx
  smul_mem' := by
    intro c f hf x hx s
    have : f x ≠ 0 := by
      intro h
      apply hx
      simp [lp.coeFn_smul, h]
    exact hf x this s

/-- The operator `P = Π^{(1,2)}_{test,𝒮} · SWAP^{(2,3)} · Π^{(1,2)}_{test,𝒮}` on three copies of the
fermionic Fock space, where `Π^{(1,2)}_{test,𝒮}` is the projector onto `ker K` (`K = G†G`,
`G = ∑ⱼ cⱼ ⊗ cⱼ†`) acting on the first two registers and the identity on the third, and
`SWAP^{(2,3)}` exchanges the second and third registers.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian
states*, arXiv:2609.39113 (sha256 6683e57b…), §5.2, p.42 ("`P = Π^{(1,2)}_{test,𝒮} · SWAP^{(2,3)} ·
Π^{(1,2)}_{test,𝒮}`"), p.43 ("`SWAP^{(2,3)} : |S₁⟩ ⊗ |S₂⟩ ⊗ |S₃⟩ ↦ |S₁⟩ ⊗ |S₃⟩ ⊗ |S₂⟩`"); `particleSector`:
§5.2, p.42 ("we will work in the fixed particle sector `ℋ = ⋀^η ℂⁿ`"), p.43 ("`|S₁| = |S₂| = |S₃| = η`").

**Formalization Note.**
* `ℋ^{⊗3}` is `ℓ²(Fin 3 → (Fin n → Fin 2))` with the plain tensor product of the Jordan–Wigner qubit
  spaces (`kron2`), as in the published `testSlater`; occupation `1` = occupied.
* Registers are 0-based: the paper's registers `(1, 2)` are `0, 1`, and `SWAP^{(2,3)}` is the register
  permutation `permVec (Equiv.swap 1 2)` with no fermionic sign (the sign `(−1)^η` of eq. (5.3) belongs
  to the paper's auxiliary space `W`, not to `P`).
* `Π^{(1,2)}_{test,𝒮} = proj (amplSub (testSlater n) 1)` (`Π ⊗ I` with `Π` on the first two
  registers). `P` is given as a function; it is the composition of two projectors and a unitary. -/
noncomputable def slaterSwapOp (n : ℕ) (v : Ell2 (Fin 3 → FermiCap.Gaussian.Qubits n)) :
    Ell2 (Fin 3 → FermiCap.Gaussian.Qubits n) :=
  proj (amplSub (testSlater n) 1)
    (permVec (Equiv.swap (1 : Fin 3) 2) (proj (amplSub (testSlater n) 1) v))

end Supplement

end GaussTesting


