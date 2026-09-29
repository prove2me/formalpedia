-- Prove2me | Definitions.Def_GroupCohomology_IsGradedCupProduct
-- name    : GroupCohomology_IsGradedCupProduct
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/a9879c5f-5152-5696-aa85-e7bd04313d15
-- title:
--   Predicate characterising a graded cup product on group cohomology
-- statement:
--   Throughout, $k$ is a commutative ring, $G$ a group, and $A$, $B$ are objects of `Rep k G`, i.e. $k$-linear representations of $G$. The abbreviation `GradedCupFamily A B` names the type of families $\cup_{p,q}$, indexed by natural numbers $p,q$, of $k$-bilinear maps $H^p(G,A) \to H^q(G,B) \to H^{p+q}(G, A \otimes B)$, where the cohomology groups are Mathlib's `groupCohomology` of the indicated representations and the target is the cohomology of the tensor product representation $A \otimes B$ in degree $p+q$ (no degree cast is needed, the index being literally $p+q$).
--
--   The structure `IsGradedCupProduct A B cup` is a `Prop`-valued predicate on such a family with a single field `compat`: for all $p,q$, all $p$-cocycles $x$ and $q$-cocycles $y$ (elements of Mathlib's `cocycles`), and every proof $h$ that the inhomogeneous-cochain differential in degree $p+q$ annihilates the cochain-level cup product of the underlying cochains $i(x)$ and $i(y)$, the value $\cup_{p,q}([x],[y])$ on the classes obtained by the projections $\pi$ equals the class of the cocycle cut out by that cochain together with $h$. Here the cochain-level product is the one defined in the imported module: for $f \colon (\mathrm{Fin}\,p \to G) \to A$ and $g \colon (\mathrm{Fin}\,q \to G) \to B$, its value at $\sigma \colon \mathrm{Fin}(p+q) \to G$ is $f(\sigma_{<p}) \otimes_k \rho_B(g_1 \cdots g_p)\, g(\sigma_{\ge p})$, where $\sigma_{<p}$ and $\sigma_{\ge p}$ are the first $p$ and last $q$ arguments and $g_1\cdots g_p$ is the corresponding partial product.
--
--   Thus nothing is constructed here: `IsGradedCupProduct` is a specification, pinning a family down on cocycle classes by the standard inhomogeneous formula, and the cocycle condition on the product appears as a hypothesis rather than being derived.
--
--   **Relation to Mathlib.** The predicate is the project's own, stated in terms of Mathlib's inhomogeneous cochain complex for group cohomology (`inhomogeneousCochains.d`, `cocycles`, `iCocycles`, `π`, `cocyclesMk`) and of the cochain-level cup product defined in the imported module `GroupCohomology_CochainCup`.
--
--   **Where it is used.** Downstream statements about the cup product in group cohomology are formulated as theorems quantified over a family `cup` together with a hypothesis `IsGradedCupProduct A B cup`, so that its properties may be developed and used in the Galois-cohomological parts of the argument without fixing a particular construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_IsGradedCupProduct.lean

import Mathlib
import Definitions.Def_GroupCohomology_CochainCup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G)

abbrev GradedCupFamily : Type u :=
  (p q : ℕ) → (groupCohomology A p →ₗ[k] groupCohomology B q →ₗ[k] groupCohomology (A ⊗ B) (p + q))

structure IsGradedCupProduct (cup : GradedCupFamily A B) : Prop where
  compat : ∀ (p q : ℕ) (x : cocycles A p) (y : cocycles B q)
    (h : (inhomogeneousCochains.d (A ⊗ B) (p + q)).hom
      (cochainCup A B p q ((iCocycles A p).hom x) ((iCocycles B q).hom y)) = 0),
    cup p q ((groupCohomology.π A p).hom x) ((groupCohomology.π B q).hom y)
      = (groupCohomology.π (A ⊗ B) (p + q)).hom
          (cocyclesMk (cochainCup A B p q ((iCocycles A p).hom x) ((iCocycles B q).hom y)) h)

end groupCohomology


