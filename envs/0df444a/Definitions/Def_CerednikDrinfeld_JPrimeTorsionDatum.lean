-- Prove2me | Definitions.Def_CerednikDrinfeld_JPrimeTorsionDatum
-- name    : CerednikDrinfeld_JPrimeTorsionDatum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/babb494d-6e81-57a7-a374-2683ee997f57
-- title:
--   Čerednik–Drinfeld p-torsion datum on a degeneracy graph
-- statement:
--   For a natural number $p$, finite types $E$, $V$ and a valuation subring $A$ of $\overline{\mathbb{Q}}$, [`CerednikDrinfeld.JPrimeTorsionDatum p E V A`](../def/CerednikDrinfeld_JPrimeTorsionDatum.html#L11) is a structure bundling the combinatorial and arithmetic data by which the $p$-torsion of a Jacobian with purely toric reduction is handled. Its fields are: a `DegeneracyData E V`, i.e. two maps $a,b : E \to V$ and widths $w : E \to \mathbb{N}_{>0}$; a `HeckeData` on it, i.e. commuting integer matrices $T_\ell$ on $\mathbb{Z}^E$ and $T_{v,\ell}$ on $\mathbb{Z}^V$ indexed by the primes, a finite exceptional set $S$ outside which $T_\ell$ intertwines the two degeneracy pushforwards $\mathbb{Z}^E \to \mathbb{Z}^V$ with $T_{v,\ell}$, and stability of the joint kernel of these pushforwards under every $T_\ell$; a type $T$ that is a finite abelian group, together with the requirement $p\,t = 0$ for all $t \in T$; a ring homomorphism from `HeckeAlg` $= \mathbb{Z}[X_\ell : \ell \text{ prime}]$ to $\mathrm{End}_{\mathbb{Z}}(T)$; a homomorphism $\mathrm{gal}$ from the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$ to the additive automorphisms of $T$, commuting with the Hecke action elementwise; the condition that $\mathrm{gal}$ be trivial on the automorphisms fixing pointwise some intermediate field $L$ with $\mathbb{Q} \subseteq L \subseteq \overline{\mathbb{Q}}$ finite over $\mathbb{Q}$; a subgroup $\mathrm{toric} \le T$ together with an isomorphism of it onto the group of $\mathbb{Z}$-linear maps $\mathrm{ribbonKernel}\,D \to \mathbb{Z}/p$; and an additive map $\mathrm{sp}$ from the subgroup of elements fixed by every $\sigma$ in the inertia subgroup of $A$ over $\mathbb{Q}$ (the intersection over such $\sigma$ of the kernels of $\mathrm{gal}\,\sigma - \mathrm{id}$) to $\mathrm{ribbonComponentGroup}\,D$, the quotient of $\mathrm{Hom}_{\mathbb{Z}}(\mathrm{ribbonKernel}\,D, \mathbb{Z})$ by the image of the Gram map of the width pairing $\sum_e w_e x_e y_e$. No property relating these data is asserted beyond the listed fields. Two subgroups of $T$ are then named: `invariants`, the inertia invariants at $A$ just described, and `W Dm 𝔪`, the intersection over $x \in \mathfrak{m}$ of the kernels of $\mathrm{hecke}\,x$, i.e. the $\mathfrak{m}$-torsion of $T$ for an ideal $\mathfrak{m}$ of `HeckeAlg`.
--
--   **Relation to Mathlib.** Mathlib has no notion of degeneracy data, ribbon (joint) kernel, width pairing or component group of a toric reduction, nor of the abstract Hecke algebra as a polynomial ring on the primes; these are the project's own. The inertia subgroup used here is the project's [`ValuationSubring.inertiaSubgroupIn`](../def/FLTPrelim_Ramification.html#L21), the image in the full automorphism group of Mathlib's inertia subgroup of a valuation subring.
--
--   **Where it is used.** The structure is the interface through which the $p$-torsion of the Jacobian of a Shimura curve at a place of purely toric (Čerednik–Drinfeld) reduction enters the argument: the character-lattice side is recorded by the ribbon kernel with its width Gram pairing, the arithmetic side by a finite $p$-torsion module with commuting Hecke and Galois actions, and the two are linked by the toric isomorphism and the specialisation map to the component group. It is consumed by the modules that compare Hecke modules at different levels in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_JPrimeTorsionDatum.lean

import Definitions.Def_CerednikDrinfeld_Ribbon
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace CerednikDrinfeld

open ModularCurve

structure JPrimeTorsionDatum (p : ℕ) (E V : Type) [Fintype E] [Fintype V] [DecidableEq V]
    (A : ValuationSubring (AlgebraicClosure ℚ)) : Type 1 where

  D : DegeneracyData E V

  H : HeckeData D

  T : Type
  [instAddCommGroup : AddCommGroup T]
  [instFinite : Finite T]

  pTorsion : ∀ t : T, p • t = 0

  hecke : HeckeAlg →+* Module.End ℤ T

  gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* AddAut T

  comm : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : HeckeAlg) (t : T),
    gal σ (hecke x t) = hecke x (gal σ t)

  finiteLevel : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ y ∈ L, σ y = y) → gal σ = 1

  toric : AddSubgroup T

  toricEquiv : ↥toric ≃+ (↥(ribbonKernel D) →ₗ[ℤ] ZMod p)

  sp : ↥(⨅ σ ∈ A.inertiaSubgroupIn ℚ, ((gal σ).toAddMonoidHom - AddMonoidHom.id T).ker) →+
    ribbonComponentGroup D

attribute [instance] JPrimeTorsionDatum.instAddCommGroup JPrimeTorsionDatum.instFinite

namespace JPrimeTorsionDatum

variable {p : ℕ} {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]
  {A : ValuationSubring (AlgebraicClosure ℚ)}

noncomputable def invariants (Dm : JPrimeTorsionDatum p E V A) : AddSubgroup Dm.T :=
  ⨅ σ ∈ A.inertiaSubgroupIn ℚ, ((Dm.gal σ).toAddMonoidHom - AddMonoidHom.id Dm.T).ker

noncomputable def W (Dm : JPrimeTorsionDatum p E V A) (𝔪 : Ideal HeckeAlg) : AddSubgroup Dm.T :=
  ⨅ x ∈ 𝔪, (Dm.hecke x).toAddMonoidHom.ker

end JPrimeTorsionDatum

end CerednikDrinfeld


