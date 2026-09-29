-- Prove2me | Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
-- name    : CerednikDrinfeld_DrinfeldQuadrupleRelations
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/93c9353b-2995-5afc-8392-2e79c6dc609b
-- title:
--   Base change and translation relations for Drinfeld data
-- statement:
--   Throughout, $\mathcal O$ is a commutative ring with an algebra map to a field $K$, $\pi\in\mathcal O$, and $B$ a commutative $\mathcal O$-algebra; $\mathtt{DrinfeldDatum}\ \pi\ B$ is the rigidified datum consisting of lattice functions $N_0(x)\le N_1(x)$ on $\operatorname{Spec} B$, invertible $B$-modules $T_0,T_1$ with maps $\Pi_0:T_0\to T_1$, $\Pi_1:T_1\to T_0$ satisfying $\Pi_1\Pi_0=\pi=\Pi_0\Pi_1$, and stalkwise surjections $u_i$ from $B_x\otimes_{\mathcal O}N_i(x)$ to the localisation of $T_i$ at $x$. Since such a datum carries its own modules, the operations of base change and of translation by $\mathrm{GL}_2(K)$ are formalised here not as constructions but as relations between two given data, witnessed by structures whose fields are the required identities.
--
--   For an $\mathcal O$-algebra map $f:B\to B'$, `pointUnder f x'` is the image of $x'$ under the map on prime spectra induced by $f$, and `BaseChangeAlong f Q Q'` records: $N'_i(x')=N_i(\mathtt{pointUnder}\ f\ x')$ for $i=0,1$; $f$-semilinear maps $\tau_i:T_i\to T'_i$ whose images span $T'_i$ over $B'$; the intertwining relations $\tau_1\Pi_0=\Pi'_0\tau_0$ and $\tau_0\Pi_1=\Pi'_1\tau_1$; and, for each $x'$, each $v$ lying in both $N_i(\mathtt{pointUnder}\ f\ x')$ and $N'_i(x')$, each $t\in T_i$ and $s\in B$ with $f(s)\notin x'$, the implication that if $u_i(1\otimes v)$ is the fraction $t/s$ then $u'_i(1\otimes v)=\tau_i(t)/f(s)$. `IsBaseChangeAlong` is the assertion that such a structure exists.
--
--   For $g\in\mathrm{GL}_2(K)$ and $c\in K^\times$, `TranslateEven g c Q Q'` requires $N'_i(x)=(c\,g^{-1})N_i(x)$, $B$-linear equivalences $\tau_i:T_i\to T'_i$ intertwining the $\Pi$'s as above, and $u'_i(1\otimes (c\,g^{-1})v)$ equal to the image of $u_i(1\otimes v)$ under the localisation of $\tau_i$. `TranslateOdd g c_0 c_1 Q Q'` imposes $c_0=\pi c_1$ in $K$ and interchanges the indices: $N'_0(x)=(c_0g^{-1})N_1(x)$, $N'_1(x)=(c_1g^{-1})N_0(x)$, equivalences $\sigma_0:T_1\to T'_0$, $\sigma_1:T_0\to T'_1$ with $\sigma_1\Pi_1=\Pi'_0\sigma_0$, $\sigma_0\Pi_0=\Pi'_1\sigma_1$, and the corresponding index-swapped compatibilities for $u_0,u_1$. `IsTranslateEven` and `IsTranslateOdd` are the existence statements. Finally, `Iso.toTranslateEven` turns an isomorphism of Drinfeld data over $B$ into a translation relation with $g=1$, $c=1$.
--
--   **Relation to Mathlib.** Mathlib has no notion of Drinfeld datum or of Drinfeld's functor on $\mathcal O$-algebras; these relations are the project's own. The only Mathlib ingredient reused directly is `PrimeSpectrum.comap`, wrapped here as `pointUnder`, together with localisations of rings and modules and semilinear maps.
--
--   **Where it is used.** These relations express the functoriality in $B$ and the $\mathrm{GL}_2(K)$-equivariance of the quadruple description of Drinfeld's functor, on the side of Drinfeld data rather than of Deligne data, and thus feed into the Čerednik–Drinfeld uniformisation used for Shimura curves in the formalisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_DrinfeldQuadrupleRelations.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped TensorProduct MatrixGroups
open LT.LatticeTree TensorProduct Matrix

namespace CerednikDrinfeld
namespace FormalOmega
namespace DrinfeldDatum

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

section BaseChange

variable {B' : Type} [CommRing B'] [Algebra 𝒪 B']

abbrev pointUnder (f : B →ₐ[𝒪] B') (x' : PrimeSpectrum B') : PrimeSpectrum B :=
  PrimeSpectrum.comap (f : B →+* B') x'

structure BaseChangeAlong (f : B →ₐ[𝒪] B') (Q : DrinfeldDatum (K := K) π B) (Q' : DrinfeldDatum (K := K) π B') :
    Type where

  N₀_eq : ∀ x' : PrimeSpectrum B', Q'.N₀ x' = Q.N₀ (pointUnder f x')

  N₁_eq : ∀ x' : PrimeSpectrum B', Q'.N₁ x' = Q.N₁ (pointUnder f x')

  τ₀ : Q.T₀ →ₛₗ[(f : B →+* B')] Q'.T₀

  τ₁ : Q.T₁ →ₛₗ[(f : B →+* B')] Q'.T₁

  span_range_τ₀ : Submodule.span B' (Set.range τ₀) = ⊤

  span_range_τ₁ : Submodule.span B' (Set.range τ₁) = ⊤

  τ₁_Pi₀ : ∀ t, τ₁ (Q.Pi₀ t) = Q'.Pi₀ (τ₀ t)

  τ₀_Pi₁ : ∀ t, τ₀ (Q.Pi₁ t) = Q'.Pi₁ (τ₁ t)

  u₀_eq : ∀ (x' : PrimeSpectrum B') (v : Fin 2 → K) (hv : v ∈ Q.N₀ (pointUnder f x')) (hv' : v ∈ Q'.N₀ x')
    (t : Q.T₀) (s : B) (hs : f s ∉ x'.asIdeal),
    Q.u₀ (pointUnder f x') ((1 : locRing B (pointUnder f x')) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(Q.N₀ (pointUnder f x')))) =
      LocalizedModule.mk t (⟨s, hs⟩ : (pointUnder f x').asIdeal.primeCompl) →
    Q'.u₀ x' ((1 : locRing B' x') ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(Q'.N₀ x'))) =
      LocalizedModule.mk (τ₀ t) (⟨f s, hs⟩ : x'.asIdeal.primeCompl)

  u₁_eq : ∀ (x' : PrimeSpectrum B') (v : Fin 2 → K) (hv : v ∈ Q.N₁ (pointUnder f x')) (hv' : v ∈ Q'.N₁ x')
    (t : Q.T₁) (s : B) (hs : f s ∉ x'.asIdeal),
    Q.u₁ (pointUnder f x') ((1 : locRing B (pointUnder f x')) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(Q.N₁ (pointUnder f x')))) =
      LocalizedModule.mk t (⟨s, hs⟩ : (pointUnder f x').asIdeal.primeCompl) →
    Q'.u₁ x' ((1 : locRing B' x') ⊗ₜ[𝒪] (⟨v, hv'⟩ : ↥(Q'.N₁ x'))) =
      LocalizedModule.mk (τ₁ t) (⟨f s, hs⟩ : x'.asIdeal.primeCompl)

def IsBaseChangeAlong (f : B →ₐ[𝒪] B') (Q : DrinfeldDatum (K := K) π B) (Q' : DrinfeldDatum (K := K) π B') : Prop :=
  Nonempty (BaseChangeAlong f Q Q')

end BaseChange

section Translate

structure TranslateEven (g : GL (Fin 2) K) (c : Kˣ) (Q Q' : DrinfeldDatum (K := K) π B) : Type where

  N₀_eq : ∀ x : PrimeSpectrum B, Q'.N₀ x = latticeMap (scalarGL c * g⁻¹) (Q.N₀ x)

  N₁_eq : ∀ x : PrimeSpectrum B, Q'.N₁ x = latticeMap (scalarGL c * g⁻¹) (Q.N₁ x)

  τ₀ : Q.T₀ ≃ₗ[B] Q'.T₀

  τ₁ : Q.T₁ ≃ₗ[B] Q'.T₁
  τ₁_Pi₀ : ∀ t, τ₁ (Q.Pi₀ t) = Q'.Pi₀ (τ₀ t)
  τ₀_Pi₁ : ∀ t, τ₀ (Q.Pi₁ t) = Q'.Pi₁ (τ₁ t)

  τ₀_u₀ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → K) (hv : v ∈ Q.N₀ x)
    (hv' : ((scalarGL c * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈ Q'.N₀ x),
    Q'.u₀ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨_, hv'⟩ : ↥(Q'.N₀ x))) =
      LocalizedModule.map x.asIdeal.primeCompl τ₀.toLinearMap (Q.u₀ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(Q.N₀ x))))

  τ₁_u₁ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → K) (hv : v ∈ Q.N₁ x)
    (hv' : ((scalarGL c * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈ Q'.N₁ x),
    Q'.u₁ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨_, hv'⟩ : ↥(Q'.N₁ x))) =
      LocalizedModule.map x.asIdeal.primeCompl τ₁.toLinearMap (Q.u₁ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(Q.N₁ x))))

def IsTranslateEven (g : GL (Fin 2) K) (c : Kˣ) (Q Q' : DrinfeldDatum (K := K) π B) : Prop :=
  Nonempty (TranslateEven g c Q Q')

structure TranslateOdd (g : GL (Fin 2) K) (c₀ c₁ : Kˣ) (Q Q' : DrinfeldDatum (K := K) π B) : Type where

  c₀_eq : (c₀ : K) = algebraMap 𝒪 K π * c₁

  N₀_eq : ∀ x : PrimeSpectrum B, Q'.N₀ x = latticeMap (scalarGL c₀ * g⁻¹) (Q.N₁ x)

  N₁_eq : ∀ x : PrimeSpectrum B, Q'.N₁ x = latticeMap (scalarGL c₁ * g⁻¹) (Q.N₀ x)

  σ₀ : Q.T₁ ≃ₗ[B] Q'.T₀

  σ₁ : Q.T₀ ≃ₗ[B] Q'.T₁
  σ₁_Pi₁ : ∀ t, σ₁ (Q.Pi₁ t) = Q'.Pi₀ (σ₀ t)
  σ₀_Pi₀ : ∀ t, σ₀ (Q.Pi₀ t) = Q'.Pi₁ (σ₁ t)

  σ₀_u₀ : ∀ (x : PrimeSpectrum B) (w : Fin 2 → K) (hw : w ∈ Q.N₁ x)
    (hw' : ((scalarGL c₀ * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w ∈ Q'.N₀ x),
    Q'.u₀ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨_, hw'⟩ : ↥(Q'.N₀ x))) =
      LocalizedModule.map x.asIdeal.primeCompl σ₀.toLinearMap (Q.u₁ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨w, hw⟩ : ↥(Q.N₁ x))))

  σ₁_u₁ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → K) (hv : v ∈ Q.N₀ x)
    (hv' : ((scalarGL c₁ * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈ Q'.N₁ x),
    Q'.u₁ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨_, hv'⟩ : ↥(Q'.N₁ x))) =
      LocalizedModule.map x.asIdeal.primeCompl σ₁.toLinearMap (Q.u₀ x ((1 : locRing B x) ⊗ₜ[𝒪] (⟨v, hv⟩ : ↥(Q.N₀ x))))

def IsTranslateOdd (g : GL (Fin 2) K) (c₀ c₁ : Kˣ) (Q Q' : DrinfeldDatum (K := K) π B) : Prop :=
  Nonempty (TranslateOdd g c₀ c₁ Q Q')

def Iso.toTranslateEven {Q Q' : DrinfeldDatum (K := K) π B} (e : Iso Q Q') : TranslateEven 1 1 Q Q' where
  N₀_eq x := by rw [scalarGL_one, one_mul, inv_one, latticeMap_one]; exact (e.N₀_eq x).symm
  N₁_eq x := by rw [scalarGL_one, one_mul, inv_one, latticeMap_one]; exact (e.N₁_eq x).symm
  τ₀ := e.τ₀
  τ₁ := e.τ₁
  τ₁_Pi₀ := e.τ₁_Pi₀
  τ₀_Pi₁ := e.τ₀_Pi₁
  τ₀_u₀ x v hv hv' := by
    have h1 : ((scalarGL (1 : Kˣ) * (1 : GL (Fin 2) K)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v := by
      rw [scalarGL_one, one_mul, inv_one, Units.val_one, Matrix.one_mulVec]
    have hv'' : v ∈ Q'.N₀ x := by rw [← h1]; exact hv'
    have key := e.τ₀_u₀ x v hv hv''
    have hsub : (⟨_, hv'⟩ : ↥(Q'.N₀ x)) = ⟨v, hv''⟩ := Subtype.ext h1
    rw [hsub]; exact key
  τ₁_u₁ x v hv hv' := by
    have h1 : ((scalarGL (1 : Kˣ) * (1 : GL (Fin 2) K)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v := by
      rw [scalarGL_one, one_mul, inv_one, Units.val_one, Matrix.one_mulVec]
    have hv'' : v ∈ Q'.N₁ x := by rw [← h1]; exact hv'
    have key := e.τ₁_u₁ x v hv hv''
    have hsub : (⟨_, hv'⟩ : ↥(Q'.N₁ x)) = ⟨v, hv''⟩ := Subtype.ext h1
    rw [hsub]; exact key

end Translate

end DrinfeldDatum
end FormalOmega
end CerednikDrinfeld

end


