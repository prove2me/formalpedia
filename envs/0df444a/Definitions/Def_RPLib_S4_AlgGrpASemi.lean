-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpASemi
-- name    : RPLib_S4_AlgGrpASemi
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T02:33:01.482438+00:00
-- url     : https://prove2.me/theorems/5668ef29-3316-4c2f-a2d8-66e95f071d31
-- title:
--   Larsen's alternative library: identity component of a Noetherian semitopological group
-- statement:
--   A group `X` with a topology in which left translations, right translations and inversion are
--   continuous (no joint continuity: this is the situation of the Zariski topology on the points of
--   a linear algebraic group). We prove:
--   * the closure of a subgroup is a subgroup (`closureSubgroup`);
--   * the closure of `S * T` is irreducible for irreducible `S`, `T`;
--   * the irreducible component `G0 X` of `1` contains every irreducible set through `1`, and is a
--     normal, closed, irreducible subgroup (`idComp X`), of finite index when `X` is Noetherian, and
--     open; it lies in every closed subgroup of finite index;
--   * `Finite X ↔ idComp X = ⊥` for Noetherian T1 spaces.
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib

/-!
# S4-AlgGrpA, file Semi: identity component of a Noetherian semitopological group

A group `X` with a topology in which left translations, right translations and inversion are
continuous (no joint continuity: this is the situation of the Zariski topology on the points of
a linear algebraic group). We prove:
* the closure of a subgroup is a subgroup (`closureSubgroup`);
* the closure of `S * T` is irreducible for irreducible `S`, `T`;
* the irreducible component `G0 X` of `1` contains every irreducible set through `1`, and is a
  normal, closed, irreducible subgroup (`idComp X`), of finite index when `X` is Noetherian, and
  open; it lies in every closed subgroup of finite index;
* `Finite X ↔ idComp X = ⊥` for Noetherian T1 spaces.
-/

set_option autoImplicit false

namespace RamanujanPetersson.AlgGrpA

/-- Left translations, right translations and inversion are continuous. -/
class SemiTopGroup (X : Type*) [Group X] [TopologicalSpace X] : Prop where
  cont_mul_left : ∀ a : X, Continuous (fun x : X => a * x)
  cont_mul_right : ∀ a : X, Continuous (fun x : X => x * a)
  cont_inv : Continuous (fun x : X => x⁻¹)

namespace SemiTopGroup

variable {X : Type*} [Group X] [TopologicalSpace X] [SemiTopGroup X]

theorem cont_conj (g : X) : Continuous (fun x : X => g * x * g⁻¹) :=
  (cont_mul_right g⁻¹).comp (cont_mul_left g)

/-- The subspace topology on a subgroup is again semitopological. -/
instance subgroup (H : Subgroup X) : SemiTopGroup H where
  cont_mul_left a := continuous_induced_rng.2 ((cont_mul_left (a : X)).comp continuous_subtype_val)
  cont_mul_right a := continuous_induced_rng.2 ((cont_mul_right (a : X)).comp continuous_subtype_val)
  cont_inv := continuous_induced_rng.2 ((cont_inv (X := X)).comp continuous_subtype_val)

/-! ### Closure of a subgroup -/

theorem mul_mem_closure {H : Subgroup X} {x y : X} (hx : x ∈ closure (H : Set X))
    (hy : y ∈ closure (H : Set X)) : x * y ∈ closure (H : Set X) := by
  have h1 : ∀ h ∈ (H : Set X), h * y ∈ closure (H : Set X) := by
    intro h hh
    have hsub : (H : Set X) ⊆ (fun z => h * z) ⁻¹' closure (H : Set X) :=
      fun z hz => subset_closure (H.mul_mem hh hz)
    exact closure_minimal hsub (isClosed_closure.preimage (cont_mul_left h)) hy
  have hsub : (H : Set X) ⊆ (fun z => z * y) ⁻¹' closure (H : Set X) := fun z hz => h1 z hz
  exact closure_minimal hsub (isClosed_closure.preimage (cont_mul_right y)) hx

theorem inv_mem_closure {H : Subgroup X} {x : X} (hx : x ∈ closure (H : Set X)) :
    x⁻¹ ∈ closure (H : Set X) := by
  have hsub : (H : Set X) ⊆ (fun z => z⁻¹) ⁻¹' closure (H : Set X) :=
    fun z hz => subset_closure (H.inv_mem hz)
  exact closure_minimal hsub (isClosed_closure.preimage cont_inv) hx

/-- The closure of a subgroup, as a subgroup. -/
def closureSubgroup (H : Subgroup X) : Subgroup X where
  carrier := closure (H : Set X)
  mul_mem' := mul_mem_closure
  one_mem' := subset_closure H.one_mem
  inv_mem' := inv_mem_closure

theorem coe_closureSubgroup (H : Subgroup X) :
    ((closureSubgroup H : Subgroup X) : Set X) = closure (H : Set X) := rfl

/-! ### Products of irreducible sets -/

theorem isIrreducible_image2_mul {S T : Set X} (hS : IsIrreducible S) (hT : IsIrreducible T) :
    IsIrreducible (Set.image2 (· * ·) S T) := by
  refine ⟨hS.nonempty.image2 hT.nonempty, ?_⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed]
  intro A B hA hB hAB
  have key : ∀ t ∈ T, (fun s => s * t) '' S ⊆ A ∨ (fun s => s * t) '' S ⊆ B := by
    intro t ht
    have hirr := hS.image (fun s => s * t) (cont_mul_right t).continuousOn
    exact (isPreirreducible_iff_isClosed_union_isClosed.mp hirr.isPreirreducible) A B hA hB
      (by rintro _ ⟨s, hs, rfl⟩; exact hAB (Set.mem_image2_of_mem hs ht))
  have hTA : IsClosed (⋂ s ∈ S, (fun t => s * t) ⁻¹' A) :=
    isClosed_biInter fun s _ => hA.preimage (cont_mul_left s)
  have hTB : IsClosed (⋂ s ∈ S, (fun t => s * t) ⁻¹' B) :=
    isClosed_biInter fun s _ => hB.preimage (cont_mul_left s)
  have hcov : T ⊆ (⋂ s ∈ S, (fun t => s * t) ⁻¹' A) ∪ (⋂ s ∈ S, (fun t => s * t) ⁻¹' B) := by
    intro t ht
    rcases key t ht with h | h
    · left
      simp only [Set.mem_iInter, Set.mem_preimage]
      exact fun s hs => h ⟨s, hs, rfl⟩
    · right
      simp only [Set.mem_iInter, Set.mem_preimage]
      exact fun s hs => h ⟨s, hs, rfl⟩
  rcases (isPreirreducible_iff_isClosed_union_isClosed.mp hT.isPreirreducible) _ _ hTA hTB hcov
    with h | h
  · left
    rintro _ ⟨s, hs, t, ht, rfl⟩
    have := h ht
    simp only [Set.mem_iInter, Set.mem_preimage] at this
    exact this s hs
  · right
    rintro _ ⟨s, hs, t, ht, rfl⟩
    have := h ht
    simp only [Set.mem_iInter, Set.mem_preimage] at this
    exact this s hs

/-! ### The identity component -/

variable (X) in
/-- The irreducible component of `1`. -/
def G0 : Set X := irreducibleComponent (1 : X)

omit [SemiTopGroup X] in
theorem one_mem_G0 : (1 : X) ∈ G0 X := mem_irreducibleComponent

omit [SemiTopGroup X] in
theorem isIrreducible_G0 : IsIrreducible (G0 X) := isIrreducible_irreducibleComponent

omit [SemiTopGroup X] in
theorem isClosed_G0 : IsClosed (G0 X) := isClosed_irreducibleComponent

/-- Every irreducible set through `1` lies in `G0 X`. -/
theorem subset_G0 {S : Set X} (hS : IsIrreducible S) (h1 : (1 : X) ∈ S) : S ⊆ G0 X := by
  have hC : IsIrreducible (closure (Set.image2 (· * ·) S (G0 X))) :=
    (isIrreducible_image2_mul hS isIrreducible_G0).closure
  have hsub : G0 X ⊆ closure (Set.image2 (· * ·) S (G0 X)) := fun g hg =>
    subset_closure ⟨1, h1, g, hg, one_mul g⟩
  have heq : closure (Set.image2 (· * ·) S (G0 X)) = G0 X :=
    eq_irreducibleComponent hC.isPreirreducible hsub
  intro s hs
  rw [← heq]
  exact subset_closure ⟨s, hs, 1, one_mem_G0, mul_one s⟩

variable (X) in
/-- The identity component, as a subgroup. -/
def idComp : Subgroup X where
  carrier := G0 X
  one_mem' := one_mem_G0
  mul_mem' := fun {a b} ha hb =>
    subset_G0 (isIrreducible_image2_mul isIrreducible_G0 isIrreducible_G0)
      ⟨1, one_mem_G0, 1, one_mem_G0, one_mul 1⟩ ⟨a, ha, b, hb, rfl⟩
  inv_mem' := fun {a} ha =>
    subset_G0 (isIrreducible_G0.image _ (cont_inv (X := X)).continuousOn)
      ⟨1, one_mem_G0, inv_one⟩ ⟨a, ha, rfl⟩

theorem coe_idComp : ((idComp X : Subgroup X) : Set X) = G0 X := rfl

theorem mem_idComp {x : X} : x ∈ idComp X ↔ x ∈ G0 X := Iff.rfl

instance idComp_normal : (idComp X).Normal :=
  ⟨fun n hn g => subset_G0 (isIrreducible_G0.image (fun x => g * x * g⁻¹) (cont_conj g).continuousOn)
    ⟨1, one_mem_G0, by simp⟩ ⟨n, hn, rfl⟩⟩

theorem isClosed_idComp : IsClosed ((idComp X : Subgroup X) : Set X) := isClosed_G0

theorem isIrreducible_idComp : IsIrreducible ((idComp X : Subgroup X) : Set X) := isIrreducible_G0

/-- Left cosets of `G0 X` are irreducible components. -/
theorem image_G0_mem (g : X) : (fun x => g * x) '' G0 X ∈ irreducibleComponents X := by
  refine ⟨isIrreducible_G0.image _ (cont_mul_left g).continuousOn, fun T hT hsub => ?_⟩
  have h1 : IsIrreducible ((fun x => g⁻¹ * x) '' T) := hT.image _ (cont_mul_left _).continuousOn
  have h2 : G0 X ⊆ (fun x => g⁻¹ * x) '' T := fun x hx => ⟨g * x, hsub ⟨x, hx, rfl⟩, by simp⟩
  have h3 : (fun x => g⁻¹ * x) '' T = G0 X := eq_irreducibleComponent h1.isPreirreducible h2
  intro t ht
  have : g⁻¹ * t ∈ G0 X := by rw [← h3]; exact ⟨t, ht, rfl⟩
  exact ⟨g⁻¹ * t, this, by simp⟩

omit [TopologicalSpace X] [SemiTopGroup X] in
/-- The fibre of `X → X ⧸ H` over the class of `g` is the left coset `g H`. -/
theorem fiber_eq (H : Subgroup X) (g : X) :
    {x : X | (x : X ⧸ H) = (g : X ⧸ H)} = (fun x => g * x) '' (H : Set X) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe, QuotientGroup.eq]
  constructor
  · intro h
    refine ⟨g⁻¹ * x, ?_, by simp⟩
    have := H.inv_mem h
    simpa using this
  · rintro ⟨y, hy, rfl⟩
    have := H.inv_mem hy
    simpa using this

omit [TopologicalSpace X] [SemiTopGroup X] in
theorem fiber_eq_preimage (H : Subgroup X) (g : X) :
    {x : X | (x : X ⧸ H) = (g : X ⧸ H)} = (fun x => g⁻¹ * x) ⁻¹' (H : Set X) := by
  rw [fiber_eq]
  ext x
  simp only [Set.mem_image, Set.mem_preimage, SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨g⁻¹ * x, h, by simp⟩

instance idComp_finiteIndex [TopologicalSpace.NoetherianSpace X] : (idComp X).FiniteIndex := by
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)
  have : Finite (irreducibleComponents X) := hfin.to_subtype
  have hmem : ∀ q : X ⧸ idComp X, {x : X | (x : X ⧸ idComp X) = q} ∈ irreducibleComponents X := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [fiber_eq]
    exact image_G0_mem g
  let f : X ⧸ idComp X → irreducibleComponents X := fun q => ⟨_, hmem q⟩
  have hf : Function.Injective f := by
    intro q₁ q₂ h
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q₁
    have h' := congrArg Subtype.val h
    have hg : g ∈ {x : X | (x : X ⧸ idComp X) = (g : X ⧸ idComp X)} := rfl
    simp only [f] at h'
    rw [h'] at hg
    exact hg
  have : Finite (X ⧸ idComp X) := Finite.of_injective f hf
  exact Subgroup.finiteIndex_of_finite_quotient

/-- A closed subgroup of finite index is open. -/
theorem isOpen_of_isClosed_of_finiteIndex (H : Subgroup X) (hH : IsClosed (H : Set X))
    [H.FiniteIndex] : IsOpen (H : Set X) := by
  have hc : (H : Set X)ᶜ =
      ⋃ q : {q : X ⧸ H // q ≠ ((1 : X) : X ⧸ H)}, {x : X | (x : X ⧸ H) = q.1} := by
    ext x
    simp only [Set.mem_compl_iff, SetLike.mem_coe, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro hx
      refine ⟨⟨(x : X ⧸ H), ?_⟩, rfl⟩
      rw [Ne, QuotientGroup.eq]
      simpa using fun h => hx (by simpa using H.inv_mem h)
    · rintro ⟨⟨q, hq⟩, rfl⟩ hx
      apply hq
      rw [QuotientGroup.eq]
      simpa using H.inv_mem hx
  have hcl : IsClosed (H : Set X)ᶜ := by
    rw [hc]
    refine isClosed_iUnion_of_finite fun q => ?_
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective q.1
    rw [← hg, fiber_eq_preimage]
    exact hH.preimage (cont_mul_left g⁻¹)
  exact isClosed_compl_iff.mp hcl

theorem isOpen_idComp [TopologicalSpace.NoetherianSpace X] :
    IsOpen ((idComp X : Subgroup X) : Set X) :=
  isOpen_of_isClosed_of_finiteIndex _ isClosed_idComp

/-- The identity component lies in every closed subgroup of finite index. -/
theorem idComp_le_of_finiteIndex (H : Subgroup X) (hH : IsClosed (H : Set X)) [H.FiniteIndex] :
    idComp X ≤ H := by
  intro x hx
  have hsub := (isIrreducible_G0 (X := X)).isConnected.isPreconnected.subset_isClopen
    ⟨hH, isOpen_of_isClosed_of_finiteIndex H hH⟩ ⟨1, one_mem_G0, H.one_mem⟩
  exact hsub hx

theorem finite_iff_idComp_eq_bot [TopologicalSpace.NoetherianSpace X] [T1Space X] :
    Finite X ↔ idComp X = ⊥ := by
  constructor
  · intro hX
    have : DiscreteTopology X := Finite.instDiscreteTopology
    have hs : (G0 X).Subsingleton := (isIrreducible_G0 (X := X)).isPreirreducible.subsingleton
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.mpr (hs hx one_mem_G0)
  · intro h
    have h1 : (idComp X).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    rw [h, Subgroup.index_bot] at h1
    exact Nat.finite_of_card_ne_zero h1

end SemiTopGroup

end RamanujanPetersson.AlgGrpA


