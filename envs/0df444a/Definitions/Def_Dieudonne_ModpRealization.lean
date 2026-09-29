-- Prove2me | Definitions.Def_Dieudonne_ModpRealization
-- name    : Dieudonne_ModpRealization
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/d3a50001-d976-5fac-af44-1a8f7a4026d2
-- title:
--   Mod-p Dieudonné realisations of finite Hopf algebras
-- statement:
--   Fix a field $k$ of characteristic $p$ (for a prime $p$) and a commutative $k$-algebra $A$ with a Hopf algebra structure over $k$. Two submodule-level invariants of $A$ are defined. First, [`primitives`](../def/Dieudonne_ModpRealization.html#L16) is the $k$-submodule of $A$ given as the kernel of the $k$-linear map $a \mapsto \Delta a - a \otimes 1 - 1 \otimes a$, where $\Delta$ is the comultiplication; that is, the space of primitive elements $P(A)$. Second, [`cotangentSpace`](../def/Dieudonne_ModpRealization.html#L20) is `Ideal.Cotangent` of the kernel of the counit algebra map $\varepsilon \colon A \to k$, i.e. the $k$-module $I_\varepsilon/I_\varepsilon^2$; for $A = \mathcal O(G)$ this is the cotangent space $\omega_G$ at the identity.
--
--   The structure [`ModpDieudonneRealization`](../def/Dieudonne_ModpRealization.html#L23) is then defined for $A$ finite and free as a $k$-module with cocommutative comultiplication, and for a $k$-module $D$ that is finite as a $k$-module. Its data consist of a field `datum`, a `DieudonneDatum` over the base ring $k$ at the scalar $\ell = (p : k)$ on $D$: a pair of $k$-linear endomorphisms $F, V$ of $D$ with $F \circ V = V \circ F = \ell \cdot \mathrm{id}$; since $k$ has characteristic $p$, the scalar $\ell$ is $0$, so both composites vanish. Three further fields are numerical constraints carried as part of the data: $\dim_k A = p^{\dim_k D}$; $\dim_k \ker F = \dim_k (I_\varepsilon/I_\varepsilon^2)$; and $\dim_k \ker V = \dim_k P(A)$.
--
--   Thus a realisation is a choice of module $D$ with $F$ and $V$ on it, pinned only by these three dimension identities; the definition asserts neither functoriality in $A$ nor uniqueness of $D$.
--
--   **Relation to Mathlib.** The Hopf/coalgebra interface used here (`HopfAlgebra`, `Coalgebra.comul`, `Coalgebra.IsCocomm`, `Bialgebra.counitAlgHom`) and the cotangent module `Ideal.Cotangent` are Mathlib's; Mathlib has no Dieudonné theory, so [`primitives`](../def/Dieudonne_ModpRealization.html#L16) and [`ModpDieudonneRealization`](../def/Dieudonne_ModpRealization.html#L23) are the project's own, built on the project's `DieudonneDatum`.
--
--   **Where it is used.** These definitions provide the mod-$p$ interface for Dieudonné modules of finite commutative $p$-group schemes, used in the classification of group schemes of order $p$ by the $F$–$V$ type of their realisation and, through it, in the mod-$p$ layer of the flatness and finite-flat conditions imposed on the Galois deformation problems.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Dieudonne_ModpRealization.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open Deformation

universe u v w

section Realization

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
variable (A : Type v) [CommRing A] [HopfAlgebra k A]

noncomputable def primitives : Submodule k A :=
  LinearMap.ker (Coalgebra.comul (R := k) (A := A)
    - (TensorProduct.mk k A A).flip 1 - TensorProduct.mk k A A 1)

abbrev cotangentSpace : Type v :=
  (RingHom.ker (Bialgebra.counitAlgHom k A)).Cotangent

structure ModpDieudonneRealization
    [Module.Finite k A] [Module.Free k A] [Coalgebra.IsCocomm k A]
    (D : Type w) [AddCommGroup D] [Module k D] [Module.Finite k D] where

  datum : DieudonneDatum ((p : ℕ) : k) D

  order_eq : Module.finrank k A = p ^ Module.finrank k D

  finrank_kerFrob : Module.finrank k (LinearMap.ker datum.F)
    = Module.finrank k (cotangentSpace k A)

  finrank_kerVer : Module.finrank k (LinearMap.ker datum.V)
    = Module.finrank k (primitives k A)

end Realization


