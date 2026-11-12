-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CliffordCorrespondence
-- name    : OddOrder_GroupTheory_RepresentationTheory_CliffordCorrespondence
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:43:35.324852+00:00
-- url     : https://prove2.me/theorems/8ed97e00-81fd-4fea-b34c-c8ebe99b387a
-- title:
--   The Clifford correspondence (toward Isaacs 6.11)
-- statement:
--   Isaacs, *Character Theory of Finite Groups*, Theorem 6.11 (Clifford correspondence), irreducibility half: let $H\trianglelefteq G$, $\theta\in\mathrm{Irr}(H)$ with inertia group $T=I_G(\theta)$ and $\psi\in\mathrm{Irr}(T)$ lying over $\theta$. Then $\mathrm{Ind}_T^G\psi$ is irreducible.
--
--   Key results: `isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq` (the correspondence), `induce_eq_coe_of_inner_eq_one_of_apply_one_eq` (degree exhaustion for an induced character) and supporting facts on restriction in stages and the $\theta$-part lower bound.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CliffordCorrespondence.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CliffordCorrespondence.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CliffordSingleOrbit
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InflationCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedTransport

namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- **Restriction in stages**: restricting to `T` and then to `H ≤ T` is restriction to `H`,
up to the transport `↥(H.subgroupOf T) ≃* ↥H`.  All three functions evaluate `φ` at the same
underlying element of `G`. -/
theorem ClassFunction.restrict_subgroupOf_restrict {k : Type*} [CommRing k]
    {H T : Subgroup G} (hHT : H ≤ T) (φ : ClassFunction G k) :
    ClassFunction.restrict (H.subgroupOf T) (ClassFunction.restrict T φ)
      = ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom
          (ClassFunction.restrict H φ) := by
  ext y
  rw [ClassFunction.restrict_apply, ClassFunction.restrict_apply, ClassFunction.compHom_apply,
    ClassFunction.restrict_apply]
  rfl

/-- **The multiplicity of `η` in `Ind_I^G ψ` is the restriction multiplicity `⟨Res_I η, ψ⟩`**
(Frobenius reciprocity, with the conjugation stripped by the real-valuedness of the
multiplicity). -/
theorem inner_induce_coe_eq_restrictionMultiplicity
    {I : Subgroup G} [Fintype ↥I] [Invertible (Nat.card ↥I : ℂ)]
    (ψ : IrreducibleCharacter ↥I) (η : IrreducibleCharacter G) :
    ClassFunction.inner (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
        (η : ClassFunction G ℂ)
      = ClassFunction.restrictionMultiplicity I (η : ClassFunction G ℂ)
          (ψ : ClassFunction ↥I ℂ) := by
  obtain ⟨k, hk⟩ := IrreducibleCharacter.restrictionMultiplicity_natCast (H := I) η ψ
  rw [ClassFunction.inner_induce_eq_inner_restrict I (ψ : ClassFunction ↥I ℂ)
      (η : ClassFunction G ℂ),
    inner_conj_symm (ClassFunction.restrict I (η : ClassFunction G ℂ))
      (ψ : ClassFunction ↥I ℂ)]
  change star (ClassFunction.restrictionMultiplicity I (η : ClassFunction G ℂ)
      (ψ : ClassFunction ↥I ℂ)) = _
  rw [hk, star_natCast]

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- **The transported character has full inertia group**: if `θ` is invariant under
conjugation by every element of `T`, then its transport `θ' = θ ∘ e` along
`e : ↥(H.subgroupOf T) ≃* ↥H` is invariant under all of `↥T`, i.e. `I_T(θ') = ⊤`.
In the Clifford correspondence `T = I_G(θ)`, so this applies verbatim. -/
theorem inertia_compHom_subgroupOfEquivOfLe_eq_top
    {H T : Subgroup G} [H.Normal] [(H.subgroupOf T).Normal] (hHT : H ≤ T)
    {θ : ClassFunction ↥H ℂ}
    (hinv : ∀ t : ↥T, ClassFunction.conjBy ((t : G)) θ = θ) :
    ClassFunction.inertia (G := ↥T)
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro t
  rw [ClassFunction.mem_inertia]
  ext h'
  have key := congrFun (congrArg (fun f : ClassFunction ↥H ℂ => (f : ↥H → ℂ)) (hinv t))
    (⟨((h' : ↥T) : G), h'.2⟩ : ↥H)
  calc (ClassFunction.conjBy t
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ)) h'
      = θ ⟨(t : G) * ((h' : ↥T) : G) * (t : G)⁻¹,
          ‹H.Normal›.conj_mem _ h'.2 (t : G)⟩ := by
        exact congrArg θ (Subtype.ext rfl)
    _ = θ ⟨((h' : ↥T) : G), h'.2⟩ := by
        exact (congrArg θ (Subtype.ext rfl)).trans key
    _ = (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ) h' := by
        exact congrArg θ (Subtype.ext rfl)

open scoped ComplexOrder in
/-- **Degree exhaustion for an induced character**: if `χ ∈ Irr(G)` occurs in `Ind_I^G ψ`
with multiplicity exactly `1` and `(Ind_I^G ψ)(1) = χ(1)`, then `Ind_I^G ψ = χ` — in
particular the induced character is irreducible.

Expanding `Ind ψ = ∑_η ⟨Ind ψ, η⟩ • η` (Fourier), every coefficient is a non-negative
integer (`⟨Ind ψ, η⟩ = ⟨Res η, ψ⟩` by Frobenius reciprocity); evaluating at `1`, the
`χ`-term already accounts for the full degree, so all other coefficients vanish.  This is
the final step of the Clifford correspondence irreducibility (Isaacs 6.11). -/
theorem induce_eq_coe_of_inner_eq_one_of_apply_one_eq
    {I : Subgroup G} [Invertible (Nat.card ↥I : ℂ)]
    (ψ : IrreducibleCharacter ↥I) (χ : IrreducibleCharacter G)
    (h1 : ClassFunction.inner (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
        (χ : ClassFunction G ℂ) = 1)
    (hdeg : ClassFunction.induce I (ψ : ClassFunction ↥I ℂ) (1 : G)
        = (χ : ClassFunction G ℂ) (1 : G)) :
    ClassFunction.induce I (ψ : ClassFunction ↥I ℂ) = (χ : ClassFunction G ℂ) := by
  classical
  let : Fintype ↥I := Fintype.ofFinite _
  have : Finite (IrreducibleCharacter G) := finite_irreducibleCharacter (G := G)
  let : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  -- every Fourier coefficient of `Ind ψ` is a (real, non-negative) restriction multiplicity
  have hcoeff : ∀ η : IrreducibleCharacter G,
      ClassFunction.inner (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
          (η : ClassFunction G ℂ)
        = ClassFunction.restrictionMultiplicity I (η : ClassFunction G ℂ)
            (ψ : ClassFunction ↥I ℂ) :=
    fun η => inner_induce_coe_eq_restrictionMultiplicity ψ η
  -- Fourier expansion of `Ind ψ`, evaluated at `1`
  have hsumapp : ∀ (s : Finset (IrreducibleCharacter G))
      (F : IrreducibleCharacter G → ClassFunction G ℂ),
      (∑ η ∈ s, F η) (1 : G) = ∑ η ∈ s, (F η) (1 : G) := by
    intro s F
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.add_apply, ih]
  have hexp := sum_inner_irreducibleCharacter_smul (G := G)
    (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
  have key := congrArg (fun f : ClassFunction G ℂ => f (1 : G)) hexp
  simp only [hsumapp, ClassFunction.smul_apply] at key
  -- split off the `χ`-term: it already equals the full degree
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ χ), h1, one_mul, hdeg] at key
  have hrest : ∑ η ∈ Finset.univ.erase χ,
      ClassFunction.inner (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
          (η : ClassFunction G ℂ) * (η : ClassFunction G ℂ) (1 : G) = 0 := by
    have := key
    linear_combination this
  -- each remaining summand is non-negative, so each vanishes
  have hnn : ∀ η ∈ Finset.univ.erase χ,
      (0 : ℂ) ≤ ClassFunction.inner (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
          (η : ClassFunction G ℂ) * (η : ClassFunction G ℂ) (1 : G) := by
    intro η _
    have h0 : (0 : ℂ) ≤ ClassFunction.inner
        (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ)) (η : ClassFunction G ℂ) := by
      rw [hcoeff η]
      exact ClassFunction.restrictionMultiplicity_nonneg I η.isIrreducible ψ.isIrreducible
    obtain ⟨dη, _, hdη⟩ := irreducibleCharacter_apply_one_eq_pos_natCast η
    rw [hdη]
    exact mul_nonneg h0 (by positivity)
  have hzero : ∀ η ∈ Finset.univ.erase χ,
      ClassFunction.inner (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
          (η : ClassFunction G ℂ) * (η : ClassFunction G ℂ) (1 : G) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hrest
  have hcoeff_zero : ∀ η ∈ Finset.univ.erase χ,
      ClassFunction.inner (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
          (η : ClassFunction G ℂ) = 0 := by
    intro η hη
    obtain ⟨dη, hdpos, hdη⟩ := irreducibleCharacter_apply_one_eq_pos_natCast η
    have h0 := hzero η hη
    rw [hdη] at h0
    exact (mul_eq_zero.mp h0).resolve_right
      (Nat.cast_ne_zero.mpr hdpos.ne')
  -- collapse the expansion to the `χ`-term
  conv_lhs => rw [← hexp]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ χ), h1, one_smul,
    Finset.sum_eq_zero fun η hη => by rw [hcoeff_zero η hη, zero_smul], add_zero]

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
open scoped ComplexOrder in
/-- **The θ-part lower bound**: the multiplicity of `θ` in `Res_H χ` is at least
`⟨Res_T χ, ψ⟩ · ⟨Res_H ψ, θ⟩` for any `ψ ∈ Irr(T)` (with `H ≤ T` and the inner restriction
transported along `↥(H.subgroupOf T) ≃* ↥H`).

Expand `Res_T χ` into irreducibles of `T` and restrict once more: by
`ClassFunction.restrict_subgroupOf_restrict` and `inner_compHom_of_mulEquiv` the θ-multiplicity
of `χ` is `∑_ρ ⟨Res_T χ, ρ⟩·⟨Res ρ, θ'⟩`, a sum of products of non-negative integers, and the
`ψ`-term alone is the claimed bound.  This is the counting heart of Isaacs 6.11. -/
theorem restrictionMultiplicity_mul_le_restrictionMultiplicity
    {H T : Subgroup G} (hHT : H ≤ T)
    [Fintype ↥T] [Invertible (Nat.card ↥T : ℂ)]
    [Fintype ↥(H.subgroupOf T)] [Invertible (Nat.card ↥(H.subgroupOf T) : ℂ)]
    [Fintype ↥H] [Invertible (Nat.card ↥H : ℂ)]
    (χ : IrreducibleCharacter G) (ψ : IrreducibleCharacter ↥T)
    {θ : ClassFunction ↥H ℂ} (hθ : IsIrreducibleCharacter θ) :
    ClassFunction.restrictionMultiplicity T (χ : ClassFunction G ℂ) (ψ : ClassFunction ↥T ℂ)
        * ClassFunction.restrictionMultiplicity (H.subgroupOf T) (ψ : ClassFunction ↥T ℂ)
            (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ)
      ≤ ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ) θ := by
  classical
  have : Finite (IrreducibleCharacter ↥T) := finite_irreducibleCharacter (G := ↥T)
  let : Fintype (IrreducibleCharacter ↥T) := Fintype.ofFinite _
  set θ' : ClassFunction ↥(H.subgroupOf T) ℂ :=
    ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ with hθ'
  have hθ'irr : IsIrreducibleCharacter θ' :=
    IsIrreducibleCharacter.compHom_of_surjective (Subgroup.subgroupOfEquivOfLe hHT).surjective hθ
  -- the H-level multiplicity, transported to `H.subgroupOf T`
  have h1 : ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ) θ
      = ClassFunction.inner (ClassFunction.restrict (H.subgroupOf T)
          (ClassFunction.restrict T (χ : ClassFunction G ℂ))) θ' := by
    rw [ClassFunction.restrict_subgroupOf_restrict hHT, hθ']
    exact (inner_compHom_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHT)
      (ClassFunction.restrict H (χ : ClassFunction G ℂ)) θ).symm
  -- expand `Res_T χ` into irreducibles of `T` and push through
  have hres_sum : ∀ (s : Finset (IrreducibleCharacter ↥T))
      (F : IrreducibleCharacter ↥T → ClassFunction ↥T ℂ),
      ClassFunction.restrict (H.subgroupOf T) (∑ ρ ∈ s, F ρ)
        = ∑ ρ ∈ s, ClassFunction.restrict (H.subgroupOf T) (F ρ) := by
    intro s F
    induction s using Finset.induction_on with
    | empty =>
        ext y
        simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.restrict_add, ih]
  have h2 : ClassFunction.inner (ClassFunction.restrict (H.subgroupOf T)
        (ClassFunction.restrict T (χ : ClassFunction G ℂ))) θ'
      = ∑ ρ : IrreducibleCharacter ↥T,
          ClassFunction.inner (ClassFunction.restrict T (χ : ClassFunction G ℂ))
              (ρ : ClassFunction ↥T ℂ)
            * ClassFunction.inner (ClassFunction.restrict (H.subgroupOf T)
                (ρ : ClassFunction ↥T ℂ)) θ' := by
    conv_lhs => rw [← sum_inner_irreducibleCharacter_smul (G := ↥T)
      (ClassFunction.restrict T (χ : ClassFunction G ℂ))]
    rw [hres_sum, inner_sum_left]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [ClassFunction.restrict_smul, ClassFunction.inner_smul_left]
  -- every summand is a product of non-negative integers
  have hnn : ∀ ρ ∈ (Finset.univ : Finset (IrreducibleCharacter ↥T)),
      (0 : ℂ) ≤ ClassFunction.inner (ClassFunction.restrict T (χ : ClassFunction G ℂ))
          (ρ : ClassFunction ↥T ℂ)
        * ClassFunction.inner (ClassFunction.restrict (H.subgroupOf T)
            (ρ : ClassFunction ↥T ℂ)) θ' := by
    intro ρ _
    refine mul_nonneg ?_ ?_
    · exact ClassFunction.restrictionMultiplicity_nonneg T χ.isIrreducible ρ.isIrreducible
    · exact ClassFunction.restrictionMultiplicity_nonneg (H.subgroupOf T) ρ.isIrreducible hθ'irr
  -- the `ψ`-term is the claimed product
  calc ClassFunction.restrictionMultiplicity T (χ : ClassFunction G ℂ)
          (ψ : ClassFunction ↥T ℂ)
        * ClassFunction.restrictionMultiplicity (H.subgroupOf T) (ψ : ClassFunction ↥T ℂ) θ'
      ≤ ∑ ρ : IrreducibleCharacter ↥T,
          ClassFunction.inner (ClassFunction.restrict T (χ : ClassFunction G ℂ))
              (ρ : ClassFunction ↥T ℂ)
            * ClassFunction.inner (ClassFunction.restrict (H.subgroupOf T)
                (ρ : ClassFunction ↥T ℂ)) θ' :=
        Finset.single_le_sum hnn (Finset.mem_univ ψ)
    _ = ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ) θ :=
        (h1.trans h2).symm

open scoped ComplexOrder in
/-- **The Clifford correspondence, irreducibility half** (Isaacs, *Character Theory*,
Theorem 6.11; issue 9002 (G3)).  Let `H ⊴ G` and let `θ ∈ Irr(H)` have inertia group
exactly `T` (so `H ≤ T`), and let `ψ ∈ Irr(T)` lie over `θ` (transported along
`↥(H.subgroupOf T) ≃* ↥H`).  Then `Ind_T^G ψ` is **irreducible**.

θ-part counting (no Mackey formula): any irreducible constituent `χ` of `Ind_T^G ψ` with
multiplicity `m ≥ 1` satisfies `⟨Res_H χ, θ⟩ ≥ m·e` for `e = ⟨Res ψ, θ'⟩`
(`restrictionMultiplicity_mul_le_restrictionMultiplicity`), so by the single-orbit degree
formulas at `(G, H)` and `(T, H.subgroupOf T)`,
`χ(1) = ⟨Res_H χ, θ⟩·[G:T]·θ(1) ≥ m·[G:T]·ψ(1)`; against `χ(1) ≤ (Ind ψ)(1) = [G:T]·ψ(1)`
this forces `m = 1` with equal degrees, and `Ind ψ = χ` by degree exhaustion
(`induce_eq_coe_of_inner_eq_one_of_apply_one_eq`).

Combined with the extension theorem (Isaacs 8.16, `CanonicalCharacterExtension`) and the
Gallagher decomposition (`GallagherDecomposition`) this completes the constructive Clifford
decomposition of `Ind_H^G θ` for an abelian coprime inertia quotient (Peterfalvi
(1.7)(c) -- the coprimality is exactly what distinguishes it from the multiplicity-`e`
(1.7)(b)). -/
theorem isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq
    {H T : Subgroup G} [H.Normal] [(H.subgroupOf T).Normal] (hHT : H ≤ T)
    [Invertible (Nat.card ↥T : ℂ)]
    [Fintype ↥(H.subgroupOf T)] [Invertible (Nat.card ↥(H.subgroupOf T) : ℂ)]
    {θ : ClassFunction ↥H ℂ} (hθ : IsIrreducibleCharacter θ)
    (hinertia : ClassFunction.inertia (G := G) θ = T)
    (ψ : IrreducibleCharacter ↥T)
    (hover : ClassFunction.restrictionMultiplicity (H.subgroupOf T)
        (ψ : ClassFunction ↥T ℂ)
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ) ≠ 0) :
    IsIrreducibleCharacter (ClassFunction.induce T (ψ : ClassFunction ↥T ℂ)) := by
  classical
  let : Fintype ↥T := Fintype.ofFinite _
  let : Fintype ↥H := Fintype.ofFinite _
  let : Invertible (Nat.card ↥H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : Finite (IrreducibleCharacter G) := finite_irreducibleCharacter (G := G)
  let : Fintype (IrreducibleCharacter G) := Fintype.ofFinite _
  have : Finite (IrreducibleCharacter ↥H) := finite_irreducibleCharacter (G := ↥H)
  let : Fintype (IrreducibleCharacter ↥H) := Fintype.ofFinite _
  have : Finite (IrreducibleCharacter ↥(H.subgroupOf T)) :=
    finite_irreducibleCharacter (G := ↥(H.subgroupOf T))
  let : Fintype (IrreducibleCharacter ↥(H.subgroupOf T)) := Fintype.ofFinite _
  -- bundled forms, with definitional coercion bridges
  set θb : IrreducibleCharacter ↥H := ⟨θ, hθ⟩ with hθb
  have hθ'irr : IsIrreducibleCharacter (ClassFunction.compHom
      (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ) :=
    IsIrreducibleCharacter.compHom_of_surjective
      (Subgroup.subgroupOfEquivOfLe hHT).surjective hθ
  set θ'b : IrreducibleCharacter ↥(H.subgroupOf T) :=
    ⟨ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ, hθ'irr⟩
    with hθ'b
  have hcoeθ : (θb : ClassFunction ↥H ℂ) = θ := rfl
  have hcoeθ' : (θ'b : ClassFunction ↥(H.subgroupOf T) ℂ)
      = ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom θ := rfl
  -- the ℕ-valued degrees and multiplicities
  obtain ⟨dθ, hdθpos, hdθ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θb
  rw [hcoeθ] at hdθ
  obtain ⟨dψ, hdψpos, hdψ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ψ
  obtain ⟨eψ, heψ⟩ :=
    IrreducibleCharacter.restrictionMultiplicity_natCast (H := H.subgroupOf T) ψ θ'b
  rw [hcoeθ'] at heψ
  have heψ1 : 1 ≤ eψ := by
    rcases Nat.eq_zero_or_pos eψ with h | h
    · exact absurd (by rw [heψ, h, Nat.cast_zero]) hover
    · exact h
  -- Step 1: `ψ(1) = eψ·θ(1)`, since `θ'` has full inertia in `T`
  have hoverψ : IrreducibleCharacter.LiesOver (H := H.subgroupOf T) ψ θ'b := by
    change ClassFunction.restrictionMultiplicity (H.subgroupOf T) (ψ : ClassFunction ↥T ℂ)
        (θ'b : ClassFunction ↥(H.subgroupOf T) ℂ) ≠ 0
    rw [hcoeθ']
    exact hover
  have hstep1 := apply_one_eq_restrictionMultiplicity_mul_index_inertia
    (G := ↥T) (H := H.subgroupOf T) ψ θ'b hoverψ
  have hinvT : ∀ t : ↥T, ClassFunction.conjBy ((t : G)) θ = θ := fun t => by
    have hmem : (t : G) ∈ ClassFunction.inertia (G := G) θ := by
      rw [hinertia]
      exact t.2
    exact (ClassFunction.mem_inertia).mp hmem
  have hinertia' : IrreducibleCharacter.inertia (G := ↥T) (H := H.subgroupOf T) θ'b = ⊤ :=
    inertia_compHom_subgroupOfEquivOfLe_eq_top hHT hinvT
  rw [hcoeθ', hinertia', Subgroup.index_top, Nat.cast_one, mul_one, heψ,
    ClassFunction.compHom_apply, map_one, hdθ, hdψ] at hstep1
  have hstep1N : dψ = eψ * dθ := by exact_mod_cast hstep1
  -- some irreducible constituent `χ` of `Ind_T^G ψ` exists
  have hEx : ∃ χ : IrreducibleCharacter G,
      ClassFunction.restrictionMultiplicity T (χ : ClassFunction G ℂ)
        (ψ : ClassFunction ↥T ℂ) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hzero : ClassFunction.induce T (ψ : ClassFunction ↥T ℂ) = 0 := by
      rw [induce_eq_sum_inner_restrict_smul (N := T) (ψ : ClassFunction ↥T ℂ)]
      refine Finset.sum_eq_zero fun η _ => ?_
      have h0 : ClassFunction.inner (ψ : ClassFunction ↥T ℂ)
          (ClassFunction.restrict T (η : ClassFunction G ℂ)) = 0 := by
        rw [inner_conj_symm (ClassFunction.restrict T (η : ClassFunction G ℂ))
            (ψ : ClassFunction ↥T ℂ),
          ← ClassFunction.restrictionMultiplicity_def, hcon η, star_zero]
      rw [h0, zero_smul]
    have hdeg1 := ClassFunction.induce_apply_one T (ψ : ClassFunction ↥T ℂ)
    rw [hzero, hdψ] at hdeg1
    have h00 : ((0 : ClassFunction G ℂ)) (1 : G) = 0 := rfl
    rw [h00] at hdeg1
    have hTne : T.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact (mul_ne_zero (Nat.cast_ne_zero.mpr hTne)
      (Nat.cast_ne_zero.mpr hdψpos.ne' : ((dψ : ℕ) : ℂ) ≠ 0)) hdeg1.symm
  obtain ⟨χ, hmne⟩ := hEx
  obtain ⟨m, hm⟩ := IrreducibleCharacter.restrictionMultiplicity_natCast (H := T) χ ψ
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exact absurd (by rw [hm, h, Nat.cast_zero]) hmne
    · exact h
  obtain ⟨eχ, heχ⟩ := IrreducibleCharacter.restrictionMultiplicity_natCast (H := H) χ θb
  rw [hcoeθ] at heχ
  -- the θ-part lower bound `m·eψ ≤ eχ`
  have hlow := restrictionMultiplicity_mul_le_restrictionMultiplicity (G := G) hHT χ ψ hθ
  rw [hm, heψ, heχ] at hlow
  have hlowN : m * eψ ≤ eχ := by exact_mod_cast hlow
  have heχ1 : 1 ≤ eχ := le_trans (Nat.mul_pos hm1 heψ1) hlowN
  -- the (G, H) degree formula: `χ(1) = eχ·[G:T]·θ(1)`
  have hoverχ : IrreducibleCharacter.LiesOver (H := H) χ θb := by
    change ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ)
        (θb : ClassFunction ↥H ℂ) ≠ 0
    rw [hcoeθ, heχ]
    exact Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp heχ1)
  have hdegχ := apply_one_eq_restrictionMultiplicity_mul_index_inertia
    (G := G) (H := H) χ θb hoverχ
  have hinertiaχ : IrreducibleCharacter.inertia (G := G) (H := H) θb = T := hinertia
  obtain ⟨dχ, hdχpos, hdχ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
  rw [hcoeθ, hinertiaχ, heχ, hdθ, hdχ] at hdegχ
  have hdegχN : dχ = eχ * T.index * dθ := by exact_mod_cast hdegχ
  -- the constituent degree bound: `χ(1) ≤ (Ind ψ)(1) = [G:T]·ψ(1)`
  have hoverχψ : IrreducibleCharacter.LiesOver (H := T) χ ψ := hmne
  have hupper := apply_one_le_induce_apply_one_of_liesOver (I := T) χ ψ hoverχψ
  rw [ClassFunction.induce_apply_one, hdχ, hdψ] at hupper
  have hupperN : dχ ≤ T.index * dψ := by exact_mod_cast hupper
  -- the squeeze: `m = 1` and the degrees agree
  have hTpos : 0 < T.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have heχeψ : eχ ≤ eψ := by
    have h2 : eχ * (T.index * dθ) ≤ eψ * (T.index * dθ) := by
      calc eχ * (T.index * dθ) = eχ * T.index * dθ := by ring
        _ = dχ := hdegχN.symm
        _ ≤ T.index * dψ := hupperN
        _ = T.index * (eψ * dθ) := by rw [hstep1N]
        _ = eψ * (T.index * dθ) := by ring
    exact Nat.le_of_mul_le_mul_right h2 (Nat.mul_pos hTpos hdθpos)
  have hmeq : m = 1 := by
    have h1 : m * eψ ≤ 1 * eψ := by
      rw [one_mul]
      exact le_trans hlowN heχeψ
    have h2 : m ≤ 1 := Nat.le_of_mul_le_mul_right h1 heψ1
    omega
  have hdeqN : dχ = T.index * dψ := by
    have h1 : eψ ≤ eχ := by
      have h0 := hlowN
      rw [hmeq, one_mul] at h0
      exact h0
    rw [hdegχN, Nat.le_antisymm heχeψ h1, hstep1N]
    ring
  -- conclude by degree exhaustion
  have h1 : ClassFunction.inner (ClassFunction.induce T (ψ : ClassFunction ↥T ℂ))
      (χ : ClassFunction G ℂ) = 1 := by
    rw [inner_induce_coe_eq_restrictionMultiplicity, hm, hmeq, Nat.cast_one]
  have hdeg : ClassFunction.induce T (ψ : ClassFunction ↥T ℂ) (1 : G)
      = (χ : ClassFunction G ℂ) (1 : G) := by
    rw [ClassFunction.induce_apply_one, hdψ, hdχ, ← Nat.cast_mul, ← hdeqN]
  have hfinal := induce_eq_coe_of_inner_eq_one_of_apply_one_eq ψ χ h1 hdeg
  rw [hfinal]
  exact χ.isIrreducible

end OddOrder.RepresentationTheory


