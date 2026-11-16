-- Prove2me | Definitions.Def_AutoQMem_Lindblad_Supplement_translation
-- name    : AutoQMem_Lindblad_Supplement_translation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:43:25.091276+00:00
-- url     : https://prove2.me/theorems/7b8e482a-2dba-419b-bc5c-0a7198396b7f
-- title:
--   Lattice translations of the 4D toric code acting on operators
-- statement:
--   For a permutation $\pi$ of the qubits, $U_\pi|x\rangle=|x\circ\pi^{-1}\rangle$, and conjugation acts on an operator by $(U_\pi\rho U_\pi^\dagger)(x,y)=\rho(x\circ\pi,y\circ\pi)$. A **lattice translation** by $y\in(\mathbb Z/L\mathbb Z)^4$ moves every plaquette $(x,S)$ to $(x+y,S)$ and so permutes the qubits of the 4D toric code.
--
--   These express the translation invariance of the 4D Toom channel in Theorem 3.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Theorem 3, p. 31 (PDF p. 33); Definition 6.1, p. 47 (PDF p. 49)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_Supplement_toricCode
open Matrix

namespace AutoQMem.Lindblad.Supplement

open AutoQMem.Lindblad

/-- **Conjugation of an n-qubit operator by a qubit permutation** `U_π ρ U_π†`, where
`U_π |x⟩ = |x ∘ π⁻¹⟩` (Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical
Stochastic Processes*, arXiv:2610.05589 (PDF of 2026-11-03), Theorem 3, p. 31, PDF 33: "translationally
invariant"; a lattice translation acts on the qubits by a permutation). -/
def permConj {n : ℕ} (π : Equiv.Perm (Fin n)) (ρ : Op n) : Op n :=
  Matrix.of fun x y => ρ (x ∘ π) (y ∘ π)

/-- **Lattice translation of the plaquettes** of the 4D toric code by `y ∈ (ℤ/Lℤ)⁴`:
`(x, S) ↦ (x + y, S)`, transported to the qubit labels `Fin n` by `encP` (Definition 6.1, p. 47). -/
noncomputable def plaqTransl (L : ℕ) [NeZero L] (y : Fin 4 → ZMod L) :
    Equiv.Perm (Fin (toricN' L + 1)) :=
  (encP L).trans ((Equiv.prodCongr (Equiv.addRight y) (Equiv.refl _)).trans (encP L).symm)

end AutoQMem.Lindblad.Supplement


