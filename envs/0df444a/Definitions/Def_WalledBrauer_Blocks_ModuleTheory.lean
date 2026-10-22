-- Prove2me | Definitions.Def_WalledBrauer_Blocks_ModuleTheory
-- name    : WalledBrauer_Blocks_ModuleTheory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:42:27.817993+00:00
-- url     : https://prove2.me/theorems/b405734a-b59c-4618-9a34-4af44ff020b8
-- title:
--   Radical and head of a module, the block relation, composition factors
-- statement:
--   Let $A$ be a ring and $M$ an $A$-module. This file fixes three standard notions.
--
--   1. The **radical** of $M$ is the intersection of its maximal submodules, and the **head** of $M$ is $M/\operatorname{rad} M$. For a finite-dimensional cell module, the head is the simple module the cell module defines (p. 8).
--   2. Two modules $M$ and $N$ lie in the **same block** if no central idempotent of $A$ separates them: for every $e\in A$ with $e^2=e$ and $ea=ae$ for all $a\in A$,
--   $$
--   e \text{ acts as the identity on } M \iff e \text{ acts as the identity on } N .
--   $$
--   For simple modules of a finite-dimensional algebra this is the usual block relation. Each simple module lies in the block of the unique primitive central idempotent that acts on it as $1$.
--   3. $S$ is a **composition factor** of $M$, written $[M:S]\neq 0$, if $S\cong P/Q$ for submodules $Q\le P\le M$.
--
--   These notions turn the paper's block statements into statements about modules.
--
--   **Formalization Note** The radical is `sInf {N | IsCoatom N}` in the submodule lattice; if there are no coatoms it is the whole module. Same block is stated with an explicit commutation condition `∀ a, a * e = e * a` and `IsIdempotentElem e`.
-- source:
--   Cox, De Visscher, Doty & Martin, On the blocks of the walled Brauer algebra, arXiv:0709.0851v1, p. 8 (simple modules as heads of cell modules) and p. 17 (weights in the same block)

import Mathlib

namespace WalledBrauer.Blocks

universe u v w

/-- The radical of a module: the intersection of its maximal submodules (the coatoms of the
submodule lattice; the whole module if there are none). -/
def moduleRadical (A : Type u) [Ring A] (M : Type v) [AddCommGroup M] [Module A M] :
    Submodule A M :=
  sInf {N : Submodule A M | IsCoatom N}

/-- The head of a module: the module modulo its radical. -/
abbrev Head (A : Type u) [Ring A] (M : Type v) [AddCommGroup M] [Module A M] : Type v :=
  M ⧸ moduleRadical A M

/-- `M` and `N` lie in the same block: no central idempotent of `A` separates them, i.e. every
central idempotent `e` acts as the identity on `M` exactly when it acts as the identity on `N`. -/
def SameBlock (A : Type u) [Ring A] (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] : Prop :=
  ∀ e : A, (∀ a : A, a * e = e * a) → IsIdempotentElem e →
    ((∀ m : M, e • m = m) ↔ (∀ n : N, e • n = n))

/-- `S` is a composition factor of `M` (`[M : S] ≠ 0`): `S ≅ P / Q` for submodules
`Q ≤ P ≤ M`. -/
def IsCompositionFactor (A : Type u) [Ring A] (S : Type v) [AddCommGroup S] [Module A S]
    (M : Type w) [AddCommGroup M] [Module A M] : Prop :=
  ∃ P Q : Submodule A M, Q ≤ P ∧ Nonempty ((↥P ⧸ Q.comap P.subtype) ≃ₗ[A] S)

end WalledBrauer.Blocks


