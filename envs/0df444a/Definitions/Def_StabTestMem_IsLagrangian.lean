-- Prove2me | Definitions.Def_StabTestMem_IsLagrangian
-- name    : StabTestMem_IsLagrangian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:09:27.85934+00:00
-- url     : https://prove2.me/theorems/69a3f87a-7ac0-4994-86cd-2a7485e716a6
-- title:
--   Lagrangian subspace of $\mathbb F_2^{2n}$
-- statement:
--   A subspace $M\le\mathbb F_2^{2n}$ is **Lagrangian** if
--
--   1. it is isotropic: $[x,y]=0$ for all $x,y\in M$;
--   2. $\dim M=n$.
--
--   Here $[u,v]=\langle u_X,v_Z\rangle+\langle u_Z,v_X\rangle \pmod 2$ is the symplectic inner product of Eq. (9). Equivalently $M=M^{\omega}$ (its own symplectic complement); a Lagrangian is a maximal isotropic subspace. The labels of the Paulis stabilizing a stabilizer state form a Lagrangian subspace (Definition 2.2).
--
--   **Formalization Note** Labels are the published `CutRankSched.Pauli n` and the symplectic form is the published `CutRankSched.symp` ($x\cdot z'+z\cdot x'$ mod 2), the same objects with the same conventions as Eq. (9).
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Definition 2.1, p. 13

import Definitions.Def_CutRankSched_symp

namespace StabTestMem

/-- **Lagrangian subspace.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Definition 2.1, p. 13: "A subspace M ≤ F_2^{2n} is said to be
Lagrangian if M = M^ω … Equivalently, • For all x, y ∈ M, [x, y] = 0. • dim(M) = n and hence M
is a maximal isotropic subspace."

`IsLagrangian M` holds when `M` is isotropic for the symplectic form `[u, v] = u_X·v_Z + u_Z·v_X`
(Eq. (9)) and has dimension `n` over `F₂` (the paper's "equivalently" form).

**Formalization Note.** Labels `(x, z) ∈ F₂ⁿ × F₂ⁿ` are the published `CutRankSched.Pauli n`
(X-part first) and the symplectic form is the published `CutRankSched.symp`
(`x · z' + z · x'` mod 2), both the same objects with the same conventions as Eq. (9). -/
def IsLagrangian {n : ℕ} (M : Submodule (ZMod 2) (CutRankSched.Pauli n)) : Prop :=
  (∀ u ∈ M, ∀ v ∈ M, CutRankSched.symp u v = 0) ∧ Module.finrank (ZMod 2) M = n

end StabTestMem


