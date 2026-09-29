-- Prove2me | Definitions.Def_GaloisRep_DeligneOrdinaryShape
-- name    : GaloisRep_DeligneOrdinaryShape
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/da519271-3c5b-56e3-9153-b99bb5458566
-- title:
--   The ordinary shape of a local two-dimensional representation
-- statement:
--   Fixed throughout are a commutative ring $A$ and a group $H$. The single declaration [`GaloisRep.DeligneOrdinaryShape`](../def/GaloisRep_DeligneOrdinaryShape.html#L14) is a predicate in the data of a homomorphism $\rho_{\mathrm{loc}} : H \to \mathrm{GL}_2(A)$, a subgroup $I \le H$ (the inertia subgroup in the intended application), a distinguished element $\mathrm{frob} \in H$, a homomorphism $\chi : H \to A^{\times}$ in the form of a monoid homomorphism $H \to A$, a natural number $k$, and two ring elements $a_p, \varepsilon_p \in A$. It asserts the existence of one matrix $g \in \mathrm{GL}_2(A)$ such that the conjugated representation $\sigma \mapsto g\,\rho_{\mathrm{loc}}(\sigma)\,g^{-1}$ satisfies five entrywise equations, the indices being those of `Fin 2`, namely $0$ and $1$: the $(1,0)$ entry vanishes for every $\sigma \in H$, so the conjugate is upper triangular; the $(1,1)$ entry equals $1$ for every $\sigma \in I$, and equals $a_p$ at $\sigma = \mathrm{frob}$; the $(0,0)$ entry equals $\chi(\sigma)^{k-1}$ for every $\sigma \in I$; and the product of $a_p$ with the $(0,0)$ entry at $\mathrm{frob}$ equals $\chi(\mathrm{frob})^{k-1}\varepsilon_p$, a determinant-type normalisation at $\mathrm{frob}$.
--
--   Thus the predicate records, in the language of matrix entries after a single change of basis, that $\rho_{\mathrm{loc}}$ is reducible with unramified quotient character taking the value $a_p$ on $\mathrm{frob}$ and with sub-character agreeing with $\chi^{k-1}$ on $I$. The exponent $k-1$ is natural-number subtraction, so the case $k = 0$ reads as $k = 1$; consumers bind $k$ subject to their own weight conditions. No structure or instance is introduced: the content is a plain existential statement about a chosen basis, not an isomorphism of representations.
--
--   **Relation to Mathlib.** Mathlib supplies the general linear group `GL (Fin 2) A` used here; the notion of an ordinary shape for a two-dimensional representation is the project's own.
--
--   **Where it is used.** This predicate is the shape in which the local behaviour at $p$ of the Galois representation attached to a weight-$k$ eigenform with non-vanishing $T_p$-eigenvalue is recorded, and it is the form in which ordinarity enters the local conditions imposed on deformations in the modularity lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GaloisRep_DeligneOrdinaryShape.lean

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace GaloisRep

section Shapes

variable {A : Type*} [CommRing A] {H : Type*} [Group H]

open Matrix

def DeligneOrdinaryShape (ρloc : H →* GL (Fin 2) A) (I : Subgroup H) (frob : H)
    (χ : H →* A) (k : ℕ) (ap εp : A) : Prop :=
  ∃ g : GL (Fin 2) A,
    (∀ σ : H, (g * ρloc σ * g⁻¹).val 1 0 = 0) ∧
    (∀ σ ∈ I, (g * ρloc σ * g⁻¹).val 1 1 = 1) ∧
    (g * ρloc frob * g⁻¹).val 1 1 = ap ∧
    (∀ σ ∈ I, (g * ρloc σ * g⁻¹).val 0 0 = χ σ ^ (k - 1)) ∧
    ap * (g * ρloc frob * g⁻¹).val 0 0 = χ frob ^ (k - 1) * εp

end Shapes

end GaloisRep


