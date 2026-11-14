-- Prove2me | Definitions.Def_LatticePrepro_Conversions_Hadamard
-- name    : LatticePrepro_Conversions_Hadamard
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:19:14.004773+00:00
-- url     : https://prove2.me/theorems/4dbe56ba-d1c8-4260-8b66-234164606a3c
-- title:
--   Walsh–Hadamard matrices and the block Hadamard map (Lemma B.2)
-- statement:
--   These definitions give the Hadamard matrices used for norm exponents $p>2$. Blocks have size $2^k$ and are indexed by $\mathbb F_2^k$.
--
--   1. **Signs** (`sgn`): $\mathbb F_2\to\mathbb Z$, $a\mapsto(-1)^a$, i.e. $0\mapsto1$ and $1\mapsto-1$.
--   2. **Block index set** (`Idx k`): $\mathbb F_2^k$, the functions $\{0,\dots,k-1\}\to\mathbb F_2$; it has $2^k$ elements.
--   3. **Inner product** (`ip k`): $\langle u,w\rangle=\sum_{i}u_iw_i\in\mathbb F_2$ for $u,w\in\mathbb F_2^k$.
--   4. **Entries** (`wh k`): $(-1)^{\langle u,w\rangle}\in\{1,-1\}$.
--   5. **The Walsh–Hadamard matrix** (`whMat k`): the integer matrix $H_{2^k}=\bigl((-1)^{\langle u,w\rangle}\bigr)_{u,w\in\mathbb F_2^k}$.
--   6. **The block Hadamard map** (`blockHad k`): for a set of blocks $\beta$ and an integer vector $v$ indexed by $\beta\times\mathbb F_2^k$,
--   $$(\mathcal Hv)_{(s,u)}=\sum_{w\in\mathbb F_2^k}(-1)^{\langle u,w\rangle}\,v_{(s,w)},$$
--   that is, $H_{2^k}$ applied separately to each block $\{s\}\times\mathbb F_2^k$.
--
--   $\mathcal H$ is the block-diagonal Sylvester–Hadamard matrix of Lemma B.2 (Hadamard blocks). In the lattice reduction of Lemma 3.12 for $2<p\le\infty$, the lattice and the targets are multiplied by $\mathcal H$ after the blocks have been padded to a power-of-two size.
--
--   **Formalization Note.** Indexing rows and columns by $\mathbb F_2^k$ instead of $\{1,\dots,2^k\}$ identifies $H_{2^k}$ with Sylvester's matrix $H_{2b}=\bigl(\begin{smallmatrix}H_b&H_b\\H_b&-H_b\end{smallmatrix}\bigr)$ through the binary expansions of the indices. The bundle also contains the simp lemma `sgn_zero` ($\operatorname{sgn}(0)=1$). The source module proves the properties used later (symmetry, $H_{2^k}^2=2^kI$, Parseval's identity for $\mathcal H$).
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Lemma B.2 (\label{lem:embeddings}); Lean: LatticePrepro/Conversions/Hadamard.lean, LatticePrepro.Hadamard.sgn, LatticePrepro.Hadamard.Idx, LatticePrepro.Hadamard.ip, LatticePrepro.Hadamard.wh, LatticePrepro.Hadamard.whMat, LatticePrepro.Hadamard.blockHad

import Mathlib

/-!
# Walsh–Hadamard matrices and the block Hadamard map (Lemma B.2)

The Walsh–Hadamard matrix of order `2^k` is indexed by `Idx k = Fin k → ZMod 2`, with entries
`wh u w = (-1)^{⟨u, w⟩}`. It is symmetric with `H * H = 2^k • 1`. The block Hadamard map
`blockHad` applies `H` to every block of a vector indexed by `β × Idx k`; it is `ℤ`-linear,
satisfies `blockHad (blockHad v) = 2^k • v` and Parseval's identity
`∑ (blockHad v)² = 2^k ∑ v²`, and has entries bounded by the `ℓ_1` norm of the block.
-/

namespace LatticePrepro

namespace Hadamard

/-- The sign character `ZMod 2 → ℤ`, `0 ↦ 1`, `1 ↦ -1`. -/
def sgn (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

@[simp] lemma sgn_zero : sgn 0 = 1 := rfl

variable (k : ℕ)

/-- The index set of a Hadamard block of size `2^k`. -/
abbrev Idx : Type := Fin k → ZMod 2

/-- The inner product `⟨u, w⟩ = ∑ u_i w_i` over `ZMod 2`. -/
def ip (u w : Idx k) : ZMod 2 := ∑ i, u i * w i

/-- Entries `(-1)^{⟨u, w⟩}` of the Walsh–Hadamard matrix. -/
def wh (u w : Idx k) : ℤ := sgn (ip k u w)

/-- The Walsh–Hadamard matrix. -/
def whMat : Matrix (Idx k) (Idx k) ℤ := Matrix.of fun u w => wh k u w

section Block

variable {β : Type*}

/-- The block Hadamard map: apply the Walsh–Hadamard matrix to every block. -/
def blockHad (v : β × Idx k → ℤ) : β × Idx k → ℤ :=
  fun su => (whMat k).mulVec (fun w => v (su.1, w)) su.2

end Block

end Hadamard

end LatticePrepro


