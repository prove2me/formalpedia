-- Prove2me | Definitions.Def_HeckeGalois_MazurCase1BundleNoBT1
-- name    : HeckeGalois_MazurCase1BundleNoBT1
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/7ca37444-1287-56b1-9e0d-7b5eb3cbcabe
-- title:
--   Mazur Case-1 bundle without the identity ker F = im V
-- statement:
--   Throughout, $\mathbb{T}$ is a commutative ring, $J$ a $\mathbb{T}$-module, $\mathfrak m \subseteq \mathbb{T}$ an ideal, and the carrier vocabulary is the one of the imported module: a `VerFrobPair k M` is a pair of $k$-linear endomorphisms `frob`, `ver` of $M$ whose two composites both vanish; `SelfDual` is a structure carrying a $k$-linear isomorphism $M \to \operatorname{Dual}_k M$ that takes `frob` to the dual map of `ver` and `ver` to the dual map of `frob`; `Stable N` means $N$ is mapped into itself by `frob` and by `ver`, with `quotientPair` and `kernelPair` the induced pairs on a stable quotient and on the kernel of an equivariant map.
--
--   `OdaDictionaryNoBT1 𝕋 J 𝔪 k Vrep HDR MV H0Ω H1O`, for a field $k$, a $\mathbb{T}/\mathfrak m$-module `Vrep` and $k$-vector spaces `HDR`, `MV`, `H0Ω`, `H1O`, is a structure with fields: pairs `DHDR` on `HDR` and `DMV` on `MV`; $k$-linear isomorphisms $\mathrm{H0\Omega} \cong \ker(\mathtt{DHDR.frob})$ and $\mathrm{H1O} \cong \mathrm{HDR}/\operatorname{range}(\mathtt{DHDR.ver})$; a surjective $k$-linear map `pi : HDR → MV` intertwining the two `ver`s and the two `frob`s; and two rank identities, $\dim_{\mathbb{T}/\mathfrak m}$ of the $\mathfrak m$-torsion submodule `Submodule.torsionBySet 𝕋 J 𝔪` equals $\dim_k \mathrm{HDR}$, and $\dim_{\mathbb{T}/\mathfrak m}\mathrm{Vrep} = \dim_k \mathrm{MV}$. It is the structure `OdaDictionary` of the imported module with the field asserting $\ker(\mathtt{frob}) = \operatorname{range}(\mathtt{ver})$ on `HDR` deleted: on `HDR` only the vanishing of the two composites is assumed, so no exactness is available there, while the Hodge sub- and quotient identifications still refer to $\ker(\mathtt{frob})$ and to the cokernel of `ver` separately.
--
--   Two derived items accompany it. `kernelPair` is the pair obtained on $\ker(\mathtt{pi})$ by restricting `DHDR`. `FontaineLayer` is the proposition that if $\ker(\mathtt{pi})$ is nontrivial then there exist a submodule $N$ of $\ker(\mathtt{pi})$ stable for that pair and a $k$-linear isomorphism $\ker(\mathtt{pi})/N \cong \mathrm{MV}$ intertwining the induced `ver` with `DMV.ver` — a condition on `ver` alone, with no requirement on `frob`.
--
--   `Case1GeometryNoBT1 𝕋 J 𝔪`, for $\mathfrak m$ maximal, bundles five types `Vrep`, `HDR`, `MV`, `H0Ω`, `H1O` in one universe, each a module over the residue field $\mathbb{T}/\mathfrak m$, a dictionary `pkt` of the above kind over $k = \mathbb{T}/\mathfrak m$ with `HDR` finite-dimensional, a self-duality structure for `pkt.DMV`, and a proof of `pkt.FontaineLayer`. `Case1BundleNoBT1` extends this by the two numerical fields $\dim_{\mathbb{T}/\mathfrak m}\mathrm{H1O} \le 1$ and $\dim_{\mathbb{T}/\mathfrak m}\mathrm{Vrep} = 2$.
--
--   **Relation to Mathlib.** Mathlib has no Frobenius–Verschiebung (Dieudonné) pair, no Oda-style de Rham/Dieudonné dictionary and no such bundle; these are the project's own structures, built on Mathlib's `Submodule.torsionBySet`, `Module.Dual`, `Module.finrank` and `Ideal.Quotient.field`. The structures here duplicate those of the imported module with one field of the dictionary removed.
--
--   **Where it is used.** These bundles axiomatise the mod-$\mathfrak m$ Dieudonné-theoretic input attached to a maximal ideal of a Hecke algebra acting on a Jacobian: the comparison between the $\mathfrak m$-torsion of $J$, its de Rham realisation, and the two-dimensional residual Galois module, together with self-duality and the Fontaine-type layer condition. They serve as the hypotheses of the downstream statements that bound the dimension of the $\mathfrak m$-torsion, the multiplicity-one type input used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_HeckeGalois_MazurCase1BundleNoBT1.lean

import Definitions.Def_HeckeGalois_MazurCase1Bundle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open Module

namespace ModularCurve

namespace MazurII142

structure OdaDictionaryNoBT1
    (𝕋 : Type*) [CommRing 𝕋] (J : Type*) [AddCommGroup J] [Module 𝕋 J] (𝔪 : Ideal 𝕋)
    (k : Type*) [Field k]
    (Vrep : Type*) [AddCommGroup Vrep] [Module (𝕋 ⧸ 𝔪) Vrep]
    (HDR : Type*) [AddCommGroup HDR] [Module k HDR]
    (MV : Type*) [AddCommGroup MV] [Module k MV]
    (H0Ω : Type*) [AddCommGroup H0Ω] [Module k H0Ω]
    (H1O : Type*) [AddCommGroup H1O] [Module k H1O] : Type _ where

  DHDR : VerFrobPair k HDR

  DMV : VerFrobPair k MV

  hodgeSub : H0Ω ≃ₗ[k] LinearMap.ker DHDR.frob

  hodgeQuot : H1O ≃ₗ[k] (HDR ⧸ LinearMap.range DHDR.ver)

  pi : HDR →ₗ[k] MV

  pi_surjective : Function.Surjective pi

  pi_ver : pi ∘ₗ DHDR.ver = DMV.ver ∘ₗ pi

  pi_frob : pi ∘ₗ DHDR.frob = DMV.frob ∘ₗ pi

  rank_J : Module.finrank (𝕋 ⧸ 𝔪) (Submodule.torsionBySet 𝕋 J 𝔪) = finrank k HDR

  rank_V : Module.finrank (𝕋 ⧸ 𝔪) Vrep = finrank k MV

namespace OdaDictionaryNoBT1

section Derived

variable {𝕋 : Type*} [CommRing 𝕋] {J : Type*} [AddCommGroup J] [Module 𝕋 J] {𝔪 : Ideal 𝕋}
  {k : Type*} [Field k]
  {Vrep : Type*} [AddCommGroup Vrep] [Module (𝕋 ⧸ 𝔪) Vrep]
  {HDR : Type*} [AddCommGroup HDR] [Module k HDR]
  {MV : Type*} [AddCommGroup MV] [Module k MV]
  {H0Ω : Type*} [AddCommGroup H0Ω] [Module k H0Ω]
  {H1O : Type*} [AddCommGroup H1O] [Module k H1O]
  (P : OdaDictionaryNoBT1 𝕋 J 𝔪 k Vrep HDR MV H0Ω H1O)

abbrev kernelPair : VerFrobPair k (LinearMap.ker P.pi) :=
  P.DHDR.kernelPair P.DMV P.pi P.pi_ver P.pi_frob

abbrev FontaineLayer : Prop :=
  Nontrivial (LinearMap.ker P.pi) →
    ∃ (N : Submodule k (LinearMap.ker P.pi)) (hN : P.kernelPair.Stable N)
      (e : ((LinearMap.ker P.pi) ⧸ N) ≃ₗ[k] MV),
      ∀ z, e ((P.kernelPair.quotientPair N hN).ver z) = P.DMV.ver (e z)

end Derived

end OdaDictionaryNoBT1

universe u v

attribute [local instance] Ideal.Quotient.field

structure Case1GeometryNoBT1 (𝕋 : Type u) [CommRing 𝕋] (J : Type v) [AddCommGroup J] [Module 𝕋 J]
    (𝔪 : Ideal 𝕋) [𝔪.IsMaximal] where

  Vrep : Type u
  [hVrepACG : AddCommGroup Vrep]
  [hVrepMod : Module (𝕋 ⧸ 𝔪) Vrep]

  HDR : Type u
  [hHDRACG : AddCommGroup HDR]
  [hHDRMod : Module (𝕋 ⧸ 𝔪) HDR]

  MV : Type u
  [hMVACG : AddCommGroup MV]
  [hMVMod : Module (𝕋 ⧸ 𝔪) MV]

  H0Ω : Type u
  [hH0ACG : AddCommGroup H0Ω]
  [hH0Mod : Module (𝕋 ⧸ 𝔪) H0Ω]

  H1O : Type u
  [hH1ACG : AddCommGroup H1O]
  [hH1Mod : Module (𝕋 ⧸ 𝔪) H1O]

  pkt : OdaDictionaryNoBT1 𝕋 J 𝔪 (𝕋 ⧸ 𝔪) Vrep HDR MV H0Ω H1O
  [hFD : FiniteDimensional (𝕋 ⧸ 𝔪) HDR]

  hsd : pkt.DMV.SelfDual

  hlayer : pkt.FontaineLayer

attribute [instance] Case1GeometryNoBT1.hVrepACG Case1GeometryNoBT1.hVrepMod
  Case1GeometryNoBT1.hHDRACG Case1GeometryNoBT1.hHDRMod Case1GeometryNoBT1.hMVACG Case1GeometryNoBT1.hMVMod
  Case1GeometryNoBT1.hH0ACG Case1GeometryNoBT1.hH0Mod Case1GeometryNoBT1.hH1ACG Case1GeometryNoBT1.hH1Mod
  Case1GeometryNoBT1.hFD

structure Case1BundleNoBT1 (𝕋 : Type u) [CommRing 𝕋] (J : Type v) [AddCommGroup J] [Module 𝕋 J]
    (𝔪 : Ideal 𝕋) [𝔪.IsMaximal] extends Case1GeometryNoBT1 𝕋 J 𝔪 where

  h94 : finrank (𝕋 ⧸ 𝔪) H1O ≤ 1

  hdimV : finrank (𝕋 ⧸ 𝔪) Vrep = 2

end MazurII142

end ModularCurve

end


