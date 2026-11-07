-- Prove2me | Definitions.Def_QLocalCert_swapOp
-- name    : QLocalCert_swapOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:12.604161+00:00
-- url     : https://prove2.me/theorems/eaf9cd34-7f82-4843-bc33-b10b032fbabc
-- title:
--   SWAP operator $S$, projectors $\Pi_\pm=(I\pm S)/2$, and partial traces
-- statement:
--   For two registers $\mathsf A,\mathsf B$ of the same dimension $d$, the **SWAP operator** is $S(|a\rangle\otimes|b\rangle)=|b\rangle\otimes|a\rangle$, and
--   $$
--   \Pi_\pm=\tfrac12(I\pm S)
--   $$
--   are the projectors onto the symmetric and antisymmetric subspaces. The SWAP test accepts on $\Pi_+$ and rejects on $\Pi_-$; on a joint state $\rho$ its rejection probability is $\operatorname{tr}(\Pi_-\rho)$. The **reduced states** of $\rho$ are $\rho_{\mathsf A}=\operatorname{tr}_{\mathsf B}\rho$ and $\rho_{\mathsf B}=\operatorname{tr}_{\mathsf A}\rho$, with entries $\rho_{\mathsf A}(i,j)=\sum_k\rho((i,k),(j,k))$ and $\rho_{\mathsf B}(i,j)=\sum_k\rho((k,i),(k,j))$.
--
--   These are the objects of Lemma 8 and of the tests of Protocol 1.
--
--   **Formalization Note** Both registers are indexed by one finite type `d`; `ptrB ρ` is $\rho_{\mathsf A}$ (the register $\mathsf B$ is traced out) and `ptrA ρ` is $\rho_{\mathsf B}$.
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), §2, p.15 (SWAP, Π±, SWAP test); Lemma 8, p.18 (reduced states)

import Mathlib

set_option autoImplicit false

namespace QLocalCert

open Matrix

/-- The SWAP operator `S(|a⟩ ⊗ |b⟩) = |b⟩ ⊗ |a⟩` on two registers of the same dimension, together
with the symmetric and antisymmetric projectors `Π± = (I ± S)/2` and the two partial traces.

B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), §2, p.15 ("The SWAP operator is
S(|a⟩⊗|b⟩) = |b⟩⊗|a⟩, and Π± := (I±S)/2 project onto the symmetric and antisymmetric subspaces.
The SWAP test accepts on Π+ and rejects on Π−") and Lemma 8, p.18 (reduced states ρ_A, ρ_B).

**Formalization Note.** Both registers are indexed by the same finite type `d` (this is
`dim A = dim B`); the joint register is indexed by `d × d`, first component `A`, second `B`.
The matrix entry is `S((a,b),(a',b')) = ⟨a,b|S|a',b'⟩ = [a = b'][b = a']`. -/
def swapOp (d : Type) [DecidableEq d] : Matrix (d × d) (d × d) ℂ :=
  fun x y => if x.1 = y.2 ∧ x.2 = y.1 then 1 else 0

/-- `Π+ = (I + S)/2`, the projector onto the symmetric subspace (the accepting projector of the
SWAP test), §2, p.15. -/
noncomputable def symProj (d : Type) [Fintype d] [DecidableEq d] : Matrix (d × d) (d × d) ℂ :=
  (1 / 2 : ℂ) • (1 + swapOp d)

/-- `Π− = (I − S)/2`, the projector onto the antisymmetric subspace (the rejecting projector of
the SWAP test), §2, p.15. -/
noncomputable def antisymProj (d : Type) [Fintype d] [DecidableEq d] :
    Matrix (d × d) (d × d) ℂ :=
  (1 / 2 : ℂ) • (1 - swapOp d)

/-- The reduced state `ρ_A = tr_B ρ` on the first register:
`ρ_A(i, j) = ∑_k ρ((i,k),(j,k))`. -/
def ptrB {a b : Type} [Fintype b] (ρ : Matrix (a × b) (a × b) ℂ) : Matrix a a ℂ :=
  fun i j => ∑ k, ρ (i, k) (j, k)

/-- The reduced state `ρ_B = tr_A ρ` on the second register:
`ρ_B(i, j) = ∑_k ρ((k,i),(k,j))`. -/
def ptrA {a b : Type} [Fintype a] (ρ : Matrix (a × b) (a × b) ℂ) : Matrix b b ℂ :=
  fun i j => ∑ k, ρ (k, i) (k, j)

end QLocalCert


