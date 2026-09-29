-- Prove2me | Definitions.Def_HeckeGalois_MazurCase1Bundle
-- name    : HeckeGalois_MazurCase1Bundle
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/5cbc1aae-e97a-5a6c-aac2-58366484998f
-- title:
--   Frobenius–Verschiebung pairs and the Mazur II (14.2) Case-1 bundle
-- statement:
--   Over a field $k$ and a $k$-vector space $M$, `VerFrobPair k M` is the structure consisting of two $k$-linear endomorphisms `frob` and `ver` of $M$ whose two composites in either order vanish; the two accompanying lemmas record the pointwise consequences $V(Fx)=0$ and $F(Vx)=0$. `SelfDual D` is a structure carrying a $k$-linear isomorphism of $M$ with its dual $\mathrm{Dual}_k M$ that converts $F$ into the transpose of $V$ and $V$ into the transpose of $F$. A submodule $N$ is `Stable` for $D$ when it is carried into itself by both $F$ and $V$; `quotientPair` is the induced pair on $M/N$, and `kernelPair` produces, from pairs $D_2$ on $M_2$ and $D_3$ on $M_3$ and a $k$-linear map $\pi$ with $\pi\circ V_2=V_3\circ\pi$ and $\pi\circ F_2=F_3\circ\pi$, the pair obtained by restricting $F_2,V_2$ to $\ker\pi$.
--
--   `OdaDictionary 𝕋 J 𝔪 k Vrep HDR MV H0Ω H1O` bundles: pairs $D_{HDR}$ on `HDR` and $D_{MV}$ on `MV`; the equality $\ker F_{HDR}=\operatorname{im} V_{HDR}$; isomorphisms `H0Ω` $\cong\ker F_{HDR}$ and `H1O` $\cong HDR/\operatorname{im}V_{HDR}$; a surjection $\pi\colon HDR\to MV$ commuting with $V$ and with $F$; and two equalities of dimensions, $\dim_{𝕋/𝔪}\,J[𝔪]=\dim_k HDR$, where $J[𝔪]$ is the $𝔪$-torsion `Submodule.torsionBySet 𝕋 J 𝔪`, and $\dim_{𝕋/𝔪} Vrep=\dim_k MV$. `FontaineLayer P` is the proposition: if $\ker\pi$ is nontrivial then it has a submodule $N$, stable for the restricted pair, together with a $k$-linear isomorphism $(\ker\pi)/N\cong MV$ intertwining the induced `ver` with $V_{MV}$ (the condition is imposed on `ver` only).
--
--   For $𝔪$ a maximal ideal of $𝕋$, so that $𝕋/𝔪$ is a field, `Case1Geometry 𝕋 J 𝔪` is the data of five $𝕋/𝔪$-modules `Vrep`, `HDR`, `MV`, `H0Ω`, `H1O` with `HDR` finite-dimensional, an `OdaDictionary` on them taken with $k=𝕋/𝔪$, and, as fields, self-duality of $D_{MV}$ and the `FontaineLayer` clause. `Case1Bundle` extends this by two numerical fields: $\dim_{𝕋/𝔪} H1O\le 1$ and $\dim_{𝕋/𝔪} Vrep=2$.
--
--   **Relation to Mathlib.** Mathlib has no notion of Dieudonné module or of a Frobenius–Verschiebung pair; these structures are the project's own, built on Mathlib's `Module.Dual`, `LinearMap.dualMap`, `Submodule.mapQ`, `LinearMap.restrict` and `Submodule.torsionBySet`.
--
--   **Where it is used.** The structures provide the abstract Dieudonné-side vocabulary for Mazur's Case 1 analysis ($p\nmid N$) of the $𝔪$-torsion of the Jacobian of a modular curve: the carriers stand for $H^1_{\mathrm{DR}}/𝔪$, the Dieudonné module of the residual representation space, and the two Hodge pieces $H^0(\Omega)/𝔪$ and $H^1(\mathcal O)/𝔪$, with the rank fields tying $J[𝔪]$ and the representation space to them. A `Case1Bundle` is the hypothesis package from which the multiplicity-one style dimension conclusions on $J[𝔪]$ are drawn.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_HeckeGalois_MazurCase1Bundle.lean

import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Ideal.Quotient.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open Module

namespace ModularCurve

namespace MazurII142

section Carrier

variable (k : Type*) [Field k] (M : Type*) [AddCommGroup M] [Module k M]

structure VerFrobPair where

  frob : M →ₗ[k] M

  ver : M →ₗ[k] M

  ver_comp_frob : ver ∘ₗ frob = 0

  frob_comp_ver : frob ∘ₗ ver = 0

end Carrier

namespace VerFrobPair

section Basic

variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M]
variable (D : VerFrobPair k M)

theorem ver_frob_apply (x : M) : D.ver (D.frob x) = 0 := by
  simpa using LinearMap.congr_fun D.ver_comp_frob x

theorem frob_ver_apply (x : M) : D.frob (D.ver x) = 0 := by
  simpa using LinearMap.congr_fun D.frob_comp_ver x

end Basic

section Duality

variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M]

structure SelfDual (D : VerFrobPair k M) where

  equiv : M ≃ₗ[k] Module.Dual k M

  frob_comm : ∀ x : M, equiv (D.frob x) = D.ver.dualMap (equiv x)

  ver_comm : ∀ x : M, equiv (D.ver x) = D.frob.dualMap (equiv x)

end Duality

section StableQuotient

variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M]
variable (D : VerFrobPair k M)

def Stable (N : Submodule k M) : Prop :=
  (∀ x ∈ N, D.frob x ∈ N) ∧ (∀ x ∈ N, D.ver x ∈ N)

def quotientPair (N : Submodule k M) (hN : D.Stable N) : VerFrobPair k (M ⧸ N) where
  frob := Submodule.mapQ N N D.frob (fun x hx => hN.1 x hx)
  ver := Submodule.mapQ N N D.ver (fun x hx => hN.2 x hx)
  ver_comp_frob := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N z
    simp only [LinearMap.comp_apply, Submodule.mapQ_apply, D.ver_frob_apply,
      Submodule.Quotient.mk_zero, LinearMap.zero_apply]
  frob_comp_ver := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N z
    simp only [LinearMap.comp_apply, Submodule.mapQ_apply, D.frob_ver_apply,
      Submodule.Quotient.mk_zero, LinearMap.zero_apply]

end StableQuotient

section Kernel

variable {k : Type*} [Field k] {M₂ M₃ : Type*}
  [AddCommGroup M₂] [Module k M₂] [AddCommGroup M₃] [Module k M₃]

def kernelPair (D₂ : VerFrobPair k M₂) (D₃ : VerFrobPair k M₃) (π : M₂ →ₗ[k] M₃)
    (hπ_ver : π ∘ₗ D₂.ver = D₃.ver ∘ₗ π) (hπ_frob : π ∘ₗ D₂.frob = D₃.frob ∘ₗ π) :
    VerFrobPair k (LinearMap.ker π) where
  frob := D₂.frob.restrict (p := LinearMap.ker π) (q := LinearMap.ker π) (fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    have h := LinearMap.congr_fun hπ_frob x
    simp only [LinearMap.comp_apply] at h
    rw [h, hx, map_zero])
  ver := D₂.ver.restrict (p := LinearMap.ker π) (q := LinearMap.ker π) (fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    have h := LinearMap.congr_fun hπ_ver x
    simp only [LinearMap.comp_apply] at h
    rw [h, hx, map_zero])
  ver_comp_frob := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    show D₂.ver (D₂.frob (x : M₂)) = ((0 : LinearMap.ker π →ₗ[k] LinearMap.ker π) x : M₂)
    rw [D₂.ver_frob_apply]
    rfl
  frob_comp_ver := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    show D₂.frob (D₂.ver (x : M₂)) = ((0 : LinearMap.ker π →ₗ[k] LinearMap.ker π) x : M₂)
    rw [D₂.frob_ver_apply]
    rfl

end Kernel

end VerFrobPair

structure OdaDictionary
    (𝕋 : Type*) [CommRing 𝕋] (J : Type*) [AddCommGroup J] [Module 𝕋 J] (𝔪 : Ideal 𝕋)
    (k : Type*) [Field k]
    (Vrep : Type*) [AddCommGroup Vrep] [Module (𝕋 ⧸ 𝔪) Vrep]
    (HDR : Type*) [AddCommGroup HDR] [Module k HDR]
    (MV : Type*) [AddCommGroup MV] [Module k MV]
    (H0Ω : Type*) [AddCommGroup H0Ω] [Module k H0Ω]
    (H1O : Type*) [AddCommGroup H1O] [Module k H1O] : Type _ where

  DHDR : VerFrobPair k HDR

  DMV : VerFrobPair k MV

  frobKer_eq_verRange : LinearMap.ker DHDR.frob = LinearMap.range DHDR.ver

  hodgeSub : H0Ω ≃ₗ[k] LinearMap.ker DHDR.frob

  hodgeQuot : H1O ≃ₗ[k] (HDR ⧸ LinearMap.range DHDR.ver)

  pi : HDR →ₗ[k] MV

  pi_surjective : Function.Surjective pi

  pi_ver : pi ∘ₗ DHDR.ver = DMV.ver ∘ₗ pi

  pi_frob : pi ∘ₗ DHDR.frob = DMV.frob ∘ₗ pi

  rank_J : Module.finrank (𝕋 ⧸ 𝔪) (Submodule.torsionBySet 𝕋 J 𝔪) = finrank k HDR

  rank_V : Module.finrank (𝕋 ⧸ 𝔪) Vrep = finrank k MV

namespace OdaDictionary

section Derived

variable {𝕋 : Type*} [CommRing 𝕋] {J : Type*} [AddCommGroup J] [Module 𝕋 J] {𝔪 : Ideal 𝕋}
  {k : Type*} [Field k]
  {Vrep : Type*} [AddCommGroup Vrep] [Module (𝕋 ⧸ 𝔪) Vrep]
  {HDR : Type*} [AddCommGroup HDR] [Module k HDR]
  {MV : Type*} [AddCommGroup MV] [Module k MV]
  {H0Ω : Type*} [AddCommGroup H0Ω] [Module k H0Ω]
  {H1O : Type*} [AddCommGroup H1O] [Module k H1O]
  (P : OdaDictionary 𝕋 J 𝔪 k Vrep HDR MV H0Ω H1O)

abbrev kernelPair : VerFrobPair k (LinearMap.ker P.pi) :=
  P.DHDR.kernelPair P.DMV P.pi P.pi_ver P.pi_frob

abbrev FontaineLayer : Prop :=
  Nontrivial (LinearMap.ker P.pi) →
    ∃ (N : Submodule k (LinearMap.ker P.pi)) (hN : P.kernelPair.Stable N)
      (e : ((LinearMap.ker P.pi) ⧸ N) ≃ₗ[k] MV),
      ∀ z, e ((P.kernelPair.quotientPair N hN).ver z) = P.DMV.ver (e z)

end Derived

end OdaDictionary

universe u v

attribute [local instance] Ideal.Quotient.field

structure Case1Geometry (𝕋 : Type u) [CommRing 𝕋] (J : Type v) [AddCommGroup J] [Module 𝕋 J]
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

  pkt : OdaDictionary 𝕋 J 𝔪 (𝕋 ⧸ 𝔪) Vrep HDR MV H0Ω H1O
  [hFD : FiniteDimensional (𝕋 ⧸ 𝔪) HDR]

  hsd : pkt.DMV.SelfDual

  hlayer : pkt.FontaineLayer

attribute [instance] Case1Geometry.hVrepACG Case1Geometry.hVrepMod
  Case1Geometry.hHDRACG Case1Geometry.hHDRMod Case1Geometry.hMVACG Case1Geometry.hMVMod
  Case1Geometry.hH0ACG Case1Geometry.hH0Mod Case1Geometry.hH1ACG Case1Geometry.hH1Mod
  Case1Geometry.hFD

structure Case1Bundle (𝕋 : Type u) [CommRing 𝕋] (J : Type v) [AddCommGroup J] [Module 𝕋 J]
    (𝔪 : Ideal 𝕋) [𝔪.IsMaximal] extends Case1Geometry 𝕋 J 𝔪 where

  h94 : finrank (𝕋 ⧸ 𝔪) H1O ≤ 1

  hdimV : finrank (𝕋 ⧸ 𝔪) Vrep = 2

end MazurII142

end ModularCurve

end


