-- Prove2me | Definitions.Def_RPLib_S4_SwanGlobS
-- name    : RPLib_S4_SwanGlobS
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:35:00.935376+00:00
-- url     : https://prove2.me/theorems/0a07b156-c0c3-492d-a91b-bbab05f9f5ed
-- title:
--   Towers of Galois extensions of Dedekind domains and restriction of inertia
-- statement:
--   Let $B' / B / A$ be a tower of Dedekind domains with finite groups $G'$ and $G$ acting so that $A = B^G$, $B = B'^{\,\ker}$ for a surjection $G' \to G$. For a prime $\mathfrak{P}'$ of $B'$ over $\mathfrak{P}$ of $B$, the file proves that restriction maps the inertia group $I(\mathfrak{P}')$ onto $I(\mathfrak{P})$ with kernel the inertia group of $\mathfrak{P}'$ in the kernel, $$|I(\mathfrak{P}')| = |I(\mathfrak{P}' \mid B)|\,|I(\mathfrak{P})|,$$ and assembles the resulting tower of local data.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Neukirch, Algebraic Number Theory, Grundlehren 322, Springer (1999), Chapter I, Section 9 (Hilbert's ramification theory); J.-P. Serre, Local Fields, GTM 67, Springer (1979), doi:10.1007/978-1-4757-5673-9, Chapter I, Section 7

import Mathlib
import Definitions.Def_RPLib_S4_SwanGlobVal

/-!
# S4-Swan (K2), part 18: towers of Galois extensions of Dedekind domains, inertia restriction

Let `R → S → S'` be finite extensions of Dedekind domains, `G` a Galois group of `S / R`, `G'` one of `S' / R`,
and `r : G' →* G` compatible with `S → S'`. Then

* `ker r` is a Galois group of `S' / S` (`isGaloisGroup_ker`; Galois theory of the fraction fields, as in
  Mathlib's `IsGaloisGroup.restrictHom`);
* for a height-one prime `Q'` of `S'` with finite residue field, `r` maps the inertia group of `Q'` onto the
  inertia group of `Q = Q' ∩ S` (`inertiaRes`, `inertiaRes_surjective`): orders of inertia groups are
  ramification indices (`GlobE`), which multiply in towers (`Ideal.ramificationIdx_tower`);
* the inertia local data of `Q` and `Q'` form a `LocData.Tower` along `L → L'` and `inertiaRes`
  (`inertiaTower`), so Serre's quotient formula, Herbrand's theorem and the Swan conductor are compatible with
  passing to a bigger level (`Tower.quotFormula`, `Tower.map_upper`, `Tower.swan_comp`).
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain

namespace RamanujanPetersson.Swan

section KerGalois

variable {R S S' : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
  [CommRing S'] [IsDomain S'] [Algebra R S] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
  [FaithfulSMul R S] [FaithfulSMul S S'] [Algebra.IsIntegral S S']
  {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G'] [MulSemiringAction G S]
  [MulSemiringAction G' S'] [IsGaloisGroup G R S] [IsGaloisGroup G' R S']
  {r : G' →* G} (hr : ∀ (σ : G') (s : S), σ • algebraMap S S' s = algebraMap S S' (r σ • s))

omit [Finite G] in
include R hr in
attribute [local instance] FractionRing.liftAlgebra in
/-- The kernel of a compatible `r : G' →* G` is a Galois group of `S' / S`. -/
theorem isGaloisGroup_ker : IsGaloisGroup r.ker S S' := by
  have : FaithfulSMul R S' := FaithfulSMul.trans R S S'
  let : MulSemiringAction G' (FractionRing S') :=
    IsFractionRing.mulSemiringAction G' S' (FractionRing S')
  let N := fixingSubgroup G' (Set.range (algebraMap (FractionRing S) (FractionRing S')))
  have hN : IsGaloisGroup N (FractionRing S) (FractionRing S') :=
    IsGaloisGroup.of_isScalarTower G' (FractionRing R) (FractionRing S') (FractionRing S)
  have hfS : FaithfulSMul G S := IsGaloisGroup.faithful R
  have key : ∀ (σ : G') (s : S), σ • algebraMap (FractionRing S) (FractionRing S')
      (algebraMap S (FractionRing S) s) =
      algebraMap S' (FractionRing S') (algebraMap S S' (r σ • s)) := by
    intro σ s
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply S S' (FractionRing S'),
      ← algebraMap.smul', hr]
  have heq : r.ker = N := by
    ext σ
    rw [MonoidHom.mem_ker]
    show r σ = 1 ↔ σ ∈ fixingSubgroup G' _
    rw [mem_fixingSubgroup_iff]
    constructor
    · rintro hσ _ ⟨x, rfl⟩
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := S) x
      have k2 : ∀ s : S, σ • algebraMap (FractionRing S) (FractionRing S')
          (algebraMap S (FractionRing S) s) =
          algebraMap (FractionRing S) (FractionRing S') (algebraMap S (FractionRing S) s) := by
        intro s
        rw [key, hσ, one_smul, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
      rw [map_div₀, smul_div₀', k2, k2]
    · intro h
      apply eq_of_smul_eq_smul (α := S)
      intro s
      rw [one_smul]
      apply FaithfulSMul.algebraMap_injective S S'
      apply IsFractionRing.injective S' (FractionRing S')
      rw [← key, h _ ⟨_, rfl⟩, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
  have : SMulDistribClass N S' (FractionRing S') :=
    ⟨fun g b x => smul_distrib_smul (g : G') b x⟩
  have : IsGaloisGroup N S S' :=
    IsGaloisGroup.of_isFractionRing N S S' (FractionRing S) (FractionRing S')
  exact IsGaloisGroup.of_mulEquiv (MulEquiv.subgroupCongr heq) (fun _ _ => rfl)

end KerGalois

section Inertia

variable {R S S' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  [CommRing S'] [IsDedekindDomain S'] [Algebra R S] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
  [FaithfulSMul R S] [FaithfulSMul S S'] [Module.Finite R S] [Module.Finite R S'] [Module.Finite S S']
  [Module.IsTorsionFree R S] [Module.IsTorsionFree R S'] [Module.IsTorsionFree S S']
  {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G'] [MulSemiringAction G S]
  [MulSemiringAction G' S'] [IsGaloisGroup G R S] [IsGaloisGroup G' R S']
  {r : G' →* G} (hr : ∀ (σ : G') (s : S), σ • algebraMap S S' s = algebraMap S S' (r σ • s))
  (Q' : HeightOneSpectrum S')

omit [FaithfulSMul S S'] [Module.IsTorsionFree S S'] [Finite G] [Finite G'] in
include hr in
theorem map_mem_inertia {σ : G'} (hσ : σ ∈ Q'.asIdeal.inertia G') :
    r σ ∈ (Q'.under S).asIdeal.inertia G := by
  intro s
  show algebraMap S S' (r σ • s - s) ∈ Q'.asIdeal
  rw [map_sub, ← hr]
  exact hσ (algebraMap S S' s)

/-- Restriction of inertia groups along the tower: `I(Q') → I(Q' ∩ S)`. -/
def inertiaRes : Q'.asIdeal.inertia G' →* (Q'.under S).asIdeal.inertia G :=
  (r.comp (Q'.asIdeal.inertia G').subtype).codRestrict _ fun σ => map_mem_inertia hr Q' σ.2

omit [FaithfulSMul S S'] [Module.IsTorsionFree S S'] [Finite G] [Finite G'] in
theorem inertiaRes_coe (σ : Q'.asIdeal.inertia G') : (inertiaRes hr Q' σ : G) = r σ := rfl

/-- The kernel of the inertia restriction is the inertia group of `Q'` in `ker r`. -/
def inertiaResKerEquiv : Q'.asIdeal.inertia r.ker ≃ (inertiaRes hr Q').ker where
  toFun τ := ⟨⟨τ.1.1, fun x => τ.2 x⟩, by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext τ.1.2⟩
  invFun σ := ⟨⟨σ.1.1, by
    have h := σ.2
    rw [MonoidHom.mem_ker] at h
    exact congrArg Subtype.val h⟩, fun x => σ.1.2 x⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Finite (S' ⧸ Q'.asIdeal)] [Finite (S ⧸ (Q'.under S).asIdeal)]

include R hr in
/-- `|I(Q')| = |I(Q)| · |I(Q') ∩ ker r|` (ramification indices multiply in the tower `R → S → S'`). -/
theorem card_inertia_eq :
    Nat.card (Q'.asIdeal.inertia G') =
      Nat.card ((Q'.under S).asIdeal.inertia G) * Nat.card (Q'.asIdeal.inertia r.ker) := by
  have : IsGaloisGroup r.ker S S' := isGaloisGroup_ker (R := R) hr
  have h1l := liesOver_under (A := R) Q'
  have h2l := liesOver_under (A := R) (Q'.under S)
  have h3l := liesOver_under (A := S) Q'
  have h1 := ramificationIdx'_under_eq_card (A := R) G' Q'
  have h2 := ramificationIdx'_under_eq_card (A := R) G (Q'.under S)
  have h3 := ramificationIdx'_under_eq_card (A := S) r.ker Q'
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (Q'.under R).ne_bot] at h1
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ ((Q'.under S).under R).ne_bot] at h2
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (Q'.under S).ne_bot] at h3
  rw [← h1, ← h2, ← h3]
  exact Ideal.ramificationIdx_tower (R := R) (Q'.under S).asIdeal Q'.asIdeal

include R hr in
/-- Inertia groups surject along the tower. -/
theorem inertiaRes_surjective : Function.Surjective (inertiaRes hr Q') := by
  rw [← MonoidHom.range_eq_top]
  apply Subgroup.eq_top_of_card_eq
  have h := card_inertia_eq (R := R) hr Q'
  have hk : Nat.card (inertiaRes hr Q').ker = Nat.card (Q'.asIdeal.inertia r.ker) :=
    (Nat.card_congr (inertiaResKerEquiv hr Q')).symm
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (inertiaRes hr Q').ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (inertiaRes hr Q')).toEquiv, hk, h] at hq
  have hpos : 0 < Nat.card (Q'.asIdeal.inertia r.ker) := Nat.card_pos
  exact (Nat.eq_of_mul_eq_mul_right hpos hq).symm

variable {L L' : Type*} [Field L] [Field L'] [Algebra S L] [IsFractionRing S L] [Algebra S' L']
  [IsFractionRing S' L'] [Algebra L L'] [Algebra S L'] [IsScalarTower S L L'] [IsScalarTower S S' L']
  [MulSemiringAction G L] [MulSemiringAction G' L']
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
  (hc' : ∀ (σ : G') (s : S'), σ • algebraMap S' L' s = algebraMap S' L' (σ • s))

omit [IsDedekindDomain S] [IsDedekindDomain S'] [FaithfulSMul S S'] [Module.Finite S S']
  [Module.IsTorsionFree S S'] [Finite G] [Finite G'] [IsFractionRing S' L'] in
include hr hc hc' in
/-- The fields `L ⊆ L'` are compatible with `r`. -/
theorem smul_algebraMap_field (σ : G') (x : L) :
    σ • algebraMap L L' x = algebraMap L L' (r σ • x) := by
  have key : ∀ (τ : G') (s : S), τ • algebraMap L L' (algebraMap S L s) =
      algebraMap L L' (r τ • algebraMap S L s) := by
    intro τ s
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply S S' L', hc', hr, hc]
    exact (IsScalarTower.algebraMap_apply S S' L' _).symm.trans (IsScalarTower.algebraMap_apply S L L' _)
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  rw [map_div₀, smul_div₀', key, key, smul_div₀', map_div₀]

include hr hc hc' in
/-- The inertia local data at `Q = Q' ∩ S` and at `Q'` form a tower along `L → L'` and `inertiaRes`. -/
theorem inertiaTower [Fintype (inertiaRes hr Q').ker] :
    LocData.Tower (inertiaLocData (R := R) hc (Q'.under S)) (inertiaLocData (R := R) hc' Q')
      (algebraMap L L') (inertiaRes hr Q') where
  surj := inertiaRes_surjective (R := R) hr Q'
  compat σ x := smul_algebraMap_field hr hc hc' (σ : G') x
  v_iota x m hm := by
    have : IsGaloisGroup r.ker S S' := isGaloisGroup_ker (R := R) hr
    rw [inertiaLocData_v, adicAdd_algebraMap_eq (A := S) r.ker Q' x m hm,
      Nat.card_congr (inertiaResKerEquiv hr Q'), Nat.card_eq_fintype_card]
  val x hx hx0 := inertiaLocData_val (R := R) hc' Q' (inertiaRes hr Q').ker x hx hx0

end Inertia

end RamanujanPetersson.Swan


