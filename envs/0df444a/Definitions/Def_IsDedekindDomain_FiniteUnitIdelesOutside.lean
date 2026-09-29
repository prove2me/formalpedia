-- Prove2me | Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
-- name    : IsDedekindDomain_FiniteUnitIdelesOutside
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/12c84a90-b0c1-5fb9-b40e-963b050bf730
-- title:
--   S-unit idèle subgroups of the finite and full adèle rings
-- statement:
--   Throughout, $R$ is a Dedekind domain with fraction field $K$ (via an algebra structure making $K$ the fraction field of $R$), and $v$ ranges over `HeightOneSpectrum R`, the height-one primes of $R$. For a set $S$ of such primes, [`IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K S`](../def/IsDedekindDomain_FiniteUnitIdelesOutside.html#L10) is the subgroup of the unit group $(\mathbb{A}_K^f)^\times$ of the finite adèle ring consisting of those units $\delta$ such that for every $v \notin S$ both the $v$-component of $\delta$ and the $v$-component of the adèle underlying $\delta^{-1}$ lie in the valuation ring $\mathcal{O}_v$ of the $v$-adic completion. Thus no condition is imposed at places in $S$, while outside $S$ the pair of integrality conditions expresses that the local component is a unit of $\mathcal{O}_v$; the group axioms are verified componentwise. The membership criterion `mem_unitIdelesOutside_iff` records this carrier description verbatim. Three further lemmas fix the elementary behaviour: for $S = \varnothing$ the subgroup coincides with `unitIdeles R K`, the subgroup of units integral together with their inverses at every place (`unitIdelesOutside_empty`); the assignment $S \mapsto$ `unitIdelesOutside R K S` is monotone for inclusion of sets of primes (`unitIdelesOutside_mono`); and `unitIdeles R K` is contained in every such subgroup (`unitIdeles_le_unitIdelesOutside`).
--
--   The second half, [`NumberField.AdeleRing.unitIdelesOutside R K S`](../def/IsDedekindDomain_FiniteUnitIdelesOutside.html#L51), is the corresponding subgroup of $(\mathbb{A}_K)^\times$, defined as the preimage of [`IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K S`](../def/IsDedekindDomain_FiniteUnitIdelesOutside.html#L10) under the map on unit groups induced by the second projection $\mathbb{A}_K^\infty \times \mathbb{A}_K^f \to \mathbb{A}_K^f$. Hence a unit idèle lies in it exactly when its finite part satisfies the local unit conditions outside $S$, with the infinite components unconstrained; this is again recorded as a membership criterion.
--
--   **Relation to Mathlib.** Mathlib supplies the finite adèle ring, the adèle ring as a product of its infinite and finite parts, and the local integers `v.adicCompletionIntegers K`, but no $S$-unit idèle subgroups; these are the project's own, extending the imported `unitIdeles` (the case $S = \varnothing$).
--
--   **Where it is used.** These subgroups are the standard $S$-idèle groups $J_{K,S} = \prod_{v \in S} K_v^\times \times \prod_{v \notin S} \mathcal{O}_v^\times$ used in the idèlic treatment of class groups and class field theory, which enters the arithmetic of the number fields occurring in the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_IsDedekindDomain_FiniteUnitIdelesOutside.lean

import Mathlib
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace IsDedekindDomain.FiniteAdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

def unitIdelesOutside (S : Set (HeightOneSpectrum R)) : Subgroup (FiniteAdeleRing R K)ˣ where
  carrier := {δ | ∀ v : HeightOneSpectrum R, v ∉ S →
    (δ : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K ∧
      ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K}
  one_mem' v _ := ⟨by rw [Units.val_one]; exact one_mem _, by rw [inv_one, Units.val_one]; exact one_mem _⟩
  mul_mem' := by
    rintro x y hx hy v hv
    obtain ⟨hx1, hx2⟩ := hx v hv
    obtain ⟨hy1, hy2⟩ := hy v hv
    exact ⟨by rw [Units.val_mul]; exact mul_mem hx1 hy1, by rw [mul_inv, Units.val_mul]; exact mul_mem hx2 hy2⟩
  inv_mem' := by
    rintro x hx v hv
    obtain ⟨hx1, hx2⟩ := hx v hv
    exact ⟨hx2, by rw [inv_inv]; exact hx1⟩

variable {R K} in
theorem mem_unitIdelesOutside_iff (S : Set (HeightOneSpectrum R)) (δ : (FiniteAdeleRing R K)ˣ) :
    δ ∈ unitIdelesOutside R K S ↔
      ∀ v : HeightOneSpectrum R, v ∉ S →
        (δ : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K ∧
          ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K :=
  Iff.rfl

theorem unitIdelesOutside_empty : unitIdelesOutside R K (∅ : Set (HeightOneSpectrum R)) = unitIdeles R K :=
  Subgroup.ext fun _ =>
    ⟨fun h => ⟨fun v => (h v fun hv => hv).1, fun v => (h v fun hv => hv).2⟩, fun h v _ => ⟨h.1 v, h.2 v⟩⟩

theorem unitIdelesOutside_mono {S T : Set (HeightOneSpectrum R)} (h : S ⊆ T) :
    unitIdelesOutside R K S ≤ unitIdelesOutside R K T :=
  fun _ hx v hv => hx v fun hvS => hv (h hvS)

theorem unitIdeles_le_unitIdelesOutside (S : Set (HeightOneSpectrum R)) :
    unitIdeles R K ≤ unitIdelesOutside R K S :=
  fun _ hx v _ => ⟨hx.1 v, hx.2 v⟩

end IsDedekindDomain.FiniteAdeleRing

namespace NumberField.AdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

noncomputable def unitIdelesOutside (S : Set (IsDedekindDomain.HeightOneSpectrum R)) : Subgroup (AdeleRing R K)ˣ :=
  (IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K S).comap
    (Units.map (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing R K)).toMonoidHom)

variable {R K} in
theorem mem_unitIdelesOutside_iff (S : Set (IsDedekindDomain.HeightOneSpectrum R)) (x : (AdeleRing R K)ˣ) :
    x ∈ unitIdelesOutside R K S ↔
      Units.map (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing R K)).toMonoidHom x ∈
        IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K S :=
  Iff.rfl

end NumberField.AdeleRing


