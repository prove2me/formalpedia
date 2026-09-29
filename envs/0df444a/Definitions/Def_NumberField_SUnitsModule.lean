-- Prove2me | Definitions.Def_NumberField_SUnitsModule
-- name    : NumberField_SUnitsModule
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/f4a2660d-6770-544f-81c6-49e798cac396
-- title:
--   Galois-stable S-units of a number field as a Z-representation
-- statement:
--   Throughout, $E \subseteq K$ are number fields with $K$ an $E$-algebra, $G = K \simeq_{\mathrm{alg}[E]} K$ is the group of $E$-algebra automorphisms of $K$, and $S$ is a finite set of finite places of $E$, i.e. a `Finset` of height-one primes of $\mathcal{O}_E$. For such a prime $v$, [`NumberField.PlaceAbove.above E K v`](../def/NumberField_PlaceAbove.html#L27) is a chosen height-one prime of $\mathcal{O}_K$ whose contraction along $\mathcal{O}_E \to \mathcal{O}_K$ is $v$; `under_above` records that the place of $E$ under the chosen place above $v$ is again $v$. `placesAbove E K S` is the set of finite places $w$ of $K$ with $w \cap \mathcal{O}_E \in S$.
--
--   The group `sUnits E K S` is defined as the intersection, over all $\sigma \in G$, of the preimages under $\sigma$ of Mathlib's $S$-unit subgroup attached to `placesAbove E K S`; concretely (`mem_sUnits_iff`) $x \in K^\times$ lies in it exactly when $w(\sigma x) = 1$ for every $\sigma \in G$ and every finite place $w$ of $K$ whose restriction to $E$ is outside $S$. Being cut out by all conjugates, it is visibly $G$-stable (`smul_mem_sUnits`), and `valuation_eq_one_of_mem_sUnits` specialises this to the chosen places above $v \notin S$. `sUnitsSubmodule` is the same group viewed as a $\mathbb{Z}$-submodule of `Additive Kˣ`, and `sUnitsRep E K S : Rep ℤ G` is the corresponding subrepresentation of the representation of $G$ on `Additive Kˣ`, with `toUnitsRep` the inclusion morphism.
--
--   For a place $v$ of $E$, `loc E K v` is the localisation map $K \to K_{w(v)}$ into the adic completion at the chosen place above $v$; `smul_loc` says it is equivariant for the decomposition group of that place, and `valued_loc` that it transports the valuation. Finally `diagFun E K S v` is the $\mathbb{Z}$-linear map sending an $S$-unit $x$ to the family $g \mapsto \iota_{w(v)}(g \cdot x)$ of units of $K_{w(v)}$, written additively; `val` and its lemmas provide the multiplicative avatar of an element of `sUnitsSubmodule`.
--
--   **Relation to Mathlib.** The underlying $S$-unit subgroup of $K^\times$ is Mathlib's (`Set.unit` for a set of finite places); the project notion intersects all of its $G$-translates, so that $G$-stability, and hence the representation structure, holds by construction. The representation-theoretic wrappers (`Rep.ofMulDistribMulAction`, `Representation.subrepresentation`) and the adic completions are Mathlib's; the decomposition-group action on the completion comes from the project's place-decomposition module.
--
--   **Where it is used.** These definitions provide the $S$-unit group of $K$ as a $\mathbb{Z}[G]$-module together with the localisation maps underlying its diagonal embedding into the finite $S$-idèles, the starting data for the $S$-class modules and Herbrand-quotient computations used in the class field theoretic input to the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_SUnitsModule.lean

import Mathlib
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_NumberField_PlaceDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField CategoryTheory
open scoped NumberField.PlaceDecomp

namespace NumberField.SUnits

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

omit [NumberField K] in

theorem under_above (v : HeightOneSpectrum (𝓞 E)) : (NumberField.PlaceAbove.above E K v).under (𝓞 E) = v :=
  HeightOneSpectrum.ext (NumberField.PlaceAbove.comap_above E K v)

def placesAbove (S : Finset (HeightOneSpectrum (𝓞 E))) : Set (HeightOneSpectrum (𝓞 K)) := {w | w.under (𝓞 E) ∈ S}

omit [NumberField E] [NumberField K] in
theorem mem_placesAbove (S : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 K)) : w ∈ placesAbove E K S ↔ w.under (𝓞 E) ∈ S :=
  Iff.rfl

noncomputable def sUnits (S : Finset (HeightOneSpectrum (𝓞 E))) : Subgroup Kˣ :=
  ⨅ σ : K ≃ₐ[E] K, (Set.unit (placesAbove E K S) K).comap (Units.map (σ : K →* K))

omit [NumberField E] in
theorem mem_sUnits_iff (S : Finset (HeightOneSpectrum (𝓞 E))) (x : Kˣ) :
    x ∈ sUnits E K S ↔ ∀ σ : K ≃ₐ[E] K, ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∉ S → w.valuation K (σ (x : K)) = 1 := by
  simp only [sUnits, Subgroup.mem_iInf, Subgroup.mem_comap]
  exact forall_congr' fun σ => Iff.rfl

omit [NumberField E] in
theorem smul_mem_sUnits (S : Finset (HeightOneSpectrum (𝓞 E))) (τ : K ≃ₐ[E] K) {x : Kˣ} (hx : x ∈ sUnits E K S) : τ • x ∈ sUnits E K S := by
  rw [mem_sUnits_iff] at hx ⊢
  intro σ w hw
  exact hx (σ * τ) w hw

theorem valuation_eq_one_of_mem_sUnits (S : Finset (HeightOneSpectrum (𝓞 E))) {x : Kˣ} (hx : x ∈ sUnits E K S) (σ : K ≃ₐ[E] K)
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∉ S) :
    (NumberField.PlaceAbove.above E K v).valuation K (σ (x : K)) = 1 :=
  (mem_sUnits_iff E K S x).1 hx σ _ (by rwa [under_above])

noncomputable def sUnitsSubmodule (S : Finset (HeightOneSpectrum (𝓞 E))) : Submodule ℤ (Additive Kˣ) :=
  (Subgroup.toAddSubgroup (sUnits E K S)).toIntSubmodule

omit [NumberField E] in
theorem mem_sUnitsSubmodule (S : Finset (HeightOneSpectrum (𝓞 E))) (x : Additive Kˣ) :
    x ∈ sUnitsSubmodule E K S ↔ Additive.toMul x ∈ sUnits E K S := Iff.rfl

noncomputable abbrev sUnitsRep (S : Finset (HeightOneSpectrum (𝓞 E))) : Rep ℤ (K ≃ₐ[E] K) :=
  Rep.of (Representation.subrepresentation (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ).ρ (sUnitsSubmodule E K S)
    fun σ _ hx => smul_mem_sUnits E K S σ hx)

noncomputable def toUnitsRep (S : Finset (HeightOneSpectrum (𝓞 E))) : sUnitsRep E K S ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ :=
  Rep.ofHom ⟨Submodule.subtype _, fun _ => rfl⟩

section diag
variable (S : Finset (HeightOneSpectrum (𝓞 E)))

noncomputable abbrev loc (v : HeightOneSpectrum (𝓞 E)) : K →+* (NumberField.PlaceAbove.above E K v).adicCompletion K :=
  algebraMap K _

theorem smul_loc (v : HeightOneSpectrum (𝓞 E)) (σ : NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)) (x : K) :
    σ • loc E K v x = loc E K v ((σ : K ≃ₐ[E] K) x) := by
  rw [NumberField.PlaceDecomp.smul_def, show loc E K v = algebraMap K _ from rfl,
    IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply, WithVal.equiv_symm_apply]
  rw [NumberField.PlaceDecomp.actRingEquiv_coe, WithVal.congr_apply]
  rfl

theorem valued_loc (v : HeightOneSpectrum (𝓞 E)) (x : K) :
    Valued.v (loc E K v x) = (NumberField.PlaceAbove.above E K v).valuation K x := by
  rw [show loc E K v = algebraMap K _ from rfl, IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' _ x

abbrev val (x : sUnitsSubmodule E K S) : Kˣ := Additive.toMul x.1

omit [NumberField E] in
@[simp] theorem val_add (x y : sUnitsRep E K S) : val E K S (x + y) = val E K S x * val E K S y := rfl
omit [NumberField E] in
@[simp] theorem val_zsmul (n : ℤ) (x : sUnitsRep E K S) : val E K S (n • x) = val E K S x ^ n := rfl
omit [NumberField E] in
theorem val_mem (x : sUnitsRep E K S) : val E K S x ∈ sUnits E K S := Subtype.property (x : sUnitsSubmodule E K S)
omit [NumberField E] in
theorem val_rho (σ : K ≃ₐ[E] K) (x : sUnitsRep E K S) : val E K S ((sUnitsRep E K S).ρ σ x) = σ • val E K S x := rfl

noncomputable def diagFun (v : HeightOneSpectrum (𝓞 E)) :
    sUnitsRep E K S →ₗ[ℤ] ((K ≃ₐ[E] K) → Additive ((NumberField.PlaceAbove.above E K v).adicCompletion K)ˣ) where
  toFun x g := Additive.ofMul (Units.map (loc E K v).toMonoidHom (g • val E K S x))
  map_add' x y := by
    funext g
    change Additive.ofMul (Units.map (loc E K v).toMonoidHom (g • (val E K S x * val E K S y))) = _
    rw [smul_mul', map_mul, ofMul_mul]
    rfl
  map_smul' n x := by
    funext g
    change Additive.ofMul (Units.map (loc E K v).toMonoidHom (g • (val E K S x ^ n))) = _
    rw [smul_zpow', map_zpow, ofMul_zpow]
    rfl

theorem diagFun_apply (v : HeightOneSpectrum (𝓞 E)) (x : sUnitsRep E K S) (g : K ≃ₐ[E] K) :
    diagFun E K S v x g = Additive.ofMul (Units.map (loc E K v).toMonoidHom (g • val E K S x)) := rfl

end diag

end NumberField.SUnits


