-- Prove2me | Definitions.Def_GroupCohomology_ContinuousUnramified
-- name    : GroupCohomology_ContinuousUnramified
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/0e92d582-68cc-5a3b-b7fc-ea796b7ed58c
-- title:
--   Galois cochain cohomology with ramification restricted to S
-- statement:
--   Throughout, $\Gamma = \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ for $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, and $S$ is a finite set of rational primes. An intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ satisfies [`IntermediateField.IsUnramifiedOutside F S`](../def/GroupCohomology_ContinuousUnramified.html#L16) when $F/\mathbb{Q}$ is finite and, for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the inertia subgroup of $A$ over $\mathbb{Q}$ (the image in $\Gamma$ of the inertia subgroup inside the decomposition subgroup) is contained in the pointwise fixing subgroup of $F$. Such fields form a family containing $\bot$, stable under joins, under passing to subfields and under enlarging $S$.
--
--   For a set $X$, a function $f$ on $\Gamma$ (resp. on $\Gamma \times \Gamma$) is `IsLevelConstantS₁ S f` (resp. `IsLevelConstantS₂ S f`) when there is an $F$ unramified outside $S$ such that $f$ is invariant under right translation of its argument (resp. of each of its two arguments separately) by elements of the fixing subgroup of $F$. These conditions are stable under addition, post-composition with arbitrary maps, and enlarging $S$, hold for constants, and imply the corresponding conditions of the all-finite-levels theory `IsLevelConstant₁`/`IsLevelConstant₂` for the identity homomorphism on $\Gamma$.
--
--   For $M :$ `Rep k Γ` over a commutative ring $k$, `levelCochainsS₁`/`levelCochainsS₂` are the $k$-submodules of cochains satisfying these conditions; `levelCocyclesS₁` is their intersection with $Z^1$, and `continuousH1S S M` is the image of `levelCocyclesS₁` in $H^1(M)$. In degree two, `levelCocyclesS₂` $= Z^2 \cap C^2_S$ and `levelCoboundariesS₂` $= d_{12}(C^1_S)$, and `continuousH2S S M` is the quotient of `levelCocyclesS₂` by the coboundaries of $S$-level $1$-cochains lying in it — note the coboundaries are taken from $C^1_S$, not from all of $C^1$. Further declarations provide the quotient map and its vanishing criterion, the comparison map `continuousH2SToContinuousH2` into the all-levels `continuousH2` for the identity on $\Gamma$, the localisation `locRes₂S` along any group homomorphism $f : H \to \Gamma$ (restriction of coefficients by $f$, identity on the underlying module), the total localisation `locTotal₂S` over the index set `extArithIndex S` $= \{*\} \sqcup S$ with the maps `extArithLoc`, and the kernels `sha₂` of `locTotal₂S` and, for $A$ a representation over a field $K$, `sha₁` $=$ `continuousH1S S A` intersected with the kernel of the degree-one total localisation `locTotal`.
--
--   **Relation to Mathlib.** Mathlib supplies the inhomogeneous cochain objects `cocycles₁`, `cocycles₂`, `d₁₂`, `H1`, `H1π` for `Rep k G` and the abstract notions `IntermediateField.fixingSubgroup` and valuation-theoretic inertia; the restricted-ramification level conditions, the resulting cochain submodules and the degree-two quotient `continuousH2S` are the project's own, Mathlib having no notion of continuous or restricted-ramification group cohomology of a profinite Galois group.
--
--   **Where it is used.** These carriers are the cohomology groups in which the Selmer and Tate–Shafarevich modules of the endgame are formed: the localisation maps are indexed by the archimedean place together with the primes in $S$, and `sha₁`, `sha₂` are the kernels of total localisation used in the Poitou–Tate and Greenberg–Wiles bookkeeping for the auxiliary characters occurring there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_ContinuousUnramified.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_PoitouTate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory ExtCitation

noncomputable section

namespace IntermediateField

def IsUnramifiedOutside (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (S : Finset Nat.Primes) : Prop :=
  FiniteDimensional ℚ F ∧ ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
    A.LiesOverPrime (q : ℕ) → A.inertiaSubgroupIn ℚ ≤ F.fixingSubgroup

lemma isUnramifiedOutside_bot (S : Finset Nat.Primes) :
    (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)).IsUnramifiedOutside S := by
  refine ⟨inferInstance, fun q _ A _ σ _ => ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff]
  rintro x hx
  obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.1 hx
  exact σ.commutes r

lemma IsUnramifiedOutside.sup {S : Finset Nat.Primes} {F F' : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hF : F.IsUnramifiedOutside S) (hF' : F'.IsUnramifiedOutside S) : (F ⊔ F').IsUnramifiedOutside S := by
  haveI := hF.1; haveI := hF'.1
  refine ⟨IntermediateField.finiteDimensional_sup F F', fun q hq A hA σ hσ => ?_⟩
  rw [IntermediateField.fixingSubgroup_sup]
  exact ⟨hF.2 q hq A hA hσ, hF'.2 q hq A hA hσ⟩

lemma IsUnramifiedOutside.mono {S S' : Finset Nat.Primes} (h : S ⊆ S') {F : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hF : F.IsUnramifiedOutside S) : F.IsUnramifiedOutside S' :=
  ⟨hF.1, fun q hq A hA => hF.2 q (fun hqS => hq (h hqS)) A hA⟩

lemma IsUnramifiedOutside.of_le {S : Finset Nat.Primes} {F F' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hle : F' ≤ F)
    (hF : F.IsUnramifiedOutside S) : F'.IsUnramifiedOutside S := by
  haveI := hF.1
  exact ⟨FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle),
    fun q hq A hA => (hF.2 q hq A hA).trans (IntermediateField.fixingSubgroup_antitone hle)⟩

end IntermediateField

namespace groupCohomology

variable (S : Finset Nat.Primes)

def IsLevelConstantS₁ {X : Type*} (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X) : Prop :=
  ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
    ∀ g s, s ∈ F.fixingSubgroup → f (g * s) = f g

def IsLevelConstantS₂ {X : Type*}
    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X) : Prop :=
  ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
    ∀ g g' s s', s ∈ F.fixingSubgroup → s' ∈ F.fixingSubgroup → f (g * s, g' * s') = f (g, g')

variable {S} in
lemma IsLevelConstantS₁.isLevelConstant₁ {X : Type*} {f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X}
    (hf : IsLevelConstantS₁ S f) : IsLevelConstant₁ (MonoidHom.id _) f := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF.1, fun g s hs => h g s hs⟩

variable {S} in
lemma IsLevelConstantS₂.isLevelConstant₂ {X : Type*}
    {f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X}
    (hf : IsLevelConstantS₂ S f) : IsLevelConstant₂ (MonoidHom.id _) f := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF.1, fun g g' s s' hs hs' => h g g' s s' hs hs'⟩

variable {S} in
lemma IsLevelConstantS₁.add {X : Type*} [Add X] {f f' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X}
    (hf : IsLevelConstantS₁ S f) (hf' : IsLevelConstantS₁ S f') : IsLevelConstantS₁ S (f + f') := by
  obtain ⟨F, hF, h⟩ := hf
  obtain ⟨F', hF', h'⟩ := hf'
  refine ⟨F ⊔ F', hF.sup hF', fun g s hs => ?_⟩
  simp only [Pi.add_apply]
  rw [h g s (IntermediateField.fixingSubgroup_antitone le_sup_left hs),
    h' g s (IntermediateField.fixingSubgroup_antitone le_sup_right hs)]

variable {S} in
lemma IsLevelConstantS₂.add {X : Type*} [Add X]
    {f f' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X}
    (hf : IsLevelConstantS₂ S f) (hf' : IsLevelConstantS₂ S f') : IsLevelConstantS₂ S (f + f') := by
  obtain ⟨F, hF, h⟩ := hf
  obtain ⟨F', hF', h'⟩ := hf'
  refine ⟨F ⊔ F', hF.sup hF', fun g g' s s' hs hs' => ?_⟩
  simp only [Pi.add_apply]
  rw [h g g' s s' (IntermediateField.fixingSubgroup_antitone le_sup_left hs)
      (IntermediateField.fixingSubgroup_antitone le_sup_left hs'),
    h' g g' s s' (IntermediateField.fixingSubgroup_antitone le_sup_right hs)
      (IntermediateField.fixingSubgroup_antitone le_sup_right hs')]

lemma isLevelConstantS₁_const {X : Type*} (x : X) :
    IsLevelConstantS₁ S (fun _ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => x) :=
  ⟨⊥, IntermediateField.isUnramifiedOutside_bot S, fun _ _ _ => rfl⟩

lemma isLevelConstantS₂_const {X : Type*} (x : X) :
    IsLevelConstantS₂ S
      (fun _ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => x) :=
  ⟨⊥, IntermediateField.isUnramifiedOutside_bot S, fun _ _ _ _ _ _ => rfl⟩

variable {S} in
lemma IsLevelConstantS₁.comp {X Y : Type*} {f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X}
    (hf : IsLevelConstantS₁ S f) (φ : X → Y) : IsLevelConstantS₁ S (φ ∘ f) := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF, fun g s hs => by simp only [Function.comp_apply, h g s hs]⟩

variable {S} in
lemma IsLevelConstantS₂.comp {X Y : Type*}
    {f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X}
    (hf : IsLevelConstantS₂ S f) (φ : X → Y) : IsLevelConstantS₂ S (φ ∘ f) := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF, fun g g' s s' hs hs' => by simp only [Function.comp_apply, h g g' s s' hs hs']⟩

variable {S} in
lemma IsLevelConstantS₁.mono {S' : Finset Nat.Primes} (h : S ⊆ S') {X : Type*}
    {f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X} (hf : IsLevelConstantS₁ S f) : IsLevelConstantS₁ S' f := by
  obtain ⟨F, hF, hc⟩ := hf
  exact ⟨F, hF.mono h, hc⟩

variable {S} in
lemma IsLevelConstantS₂.mono {S' : Finset Nat.Primes} (h : S ⊆ S') {X : Type*}
    {f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → X}
    (hf : IsLevelConstantS₂ S f) : IsLevelConstantS₂ S' f := by
  obtain ⟨F, hF, hc⟩ := hf
  exact ⟨F, hF.mono h, hc⟩

variable {k : Type} [CommRing k] (M : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

def levelCochainsS₁ : Submodule k ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) where
  carrier := {f | IsLevelConstantS₁ S f}
  add_mem' hf hf' := hf.add hf'
  zero_mem' := isLevelConstantS₁_const S (0 : M)
  smul_mem' c _ hf := hf.comp (c • ·)

def levelCochainsS₂ :
    Submodule k ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) where
  carrier := {f | IsLevelConstantS₂ S f}
  add_mem' hf hf' := hf.add hf'
  zero_mem' := isLevelConstantS₂_const S (0 : M)
  smul_mem' c _ hf := hf.comp (c • ·)

lemma mem_levelCochainsS₁_iff (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) :
    f ∈ levelCochainsS₁ S M ↔ IsLevelConstantS₁ S f := Iff.rfl

lemma mem_levelCochainsS₂_iff
    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) :
    f ∈ levelCochainsS₂ S M ↔ IsLevelConstantS₂ S f := Iff.rfl

def levelCocyclesS₁ : Submodule k (cocycles₁ M) :=
  (levelCochainsS₁ S M).comap (cocycles₁ M).subtype

def continuousH1S : Submodule k (H1 M) :=
  (levelCocyclesS₁ S M).map (H1π M).hom

lemma mem_continuousH1S_iff (x : H1 M) :
    x ∈ continuousH1S S M ↔ ∃ c : cocycles₁ M, IsLevelConstantS₁ S c ∧ (H1π M).hom c = x := by
  simp only [continuousH1S, Submodule.mem_map, levelCocyclesS₁, Submodule.mem_comap]; rfl

lemma continuousH1S_le_continuousH1 : continuousH1S S M ≤ continuousH1 (MonoidHom.id _) M := by
  rintro x hx
  obtain ⟨c, hc, rfl⟩ := (mem_continuousH1S_iff S M x).1 hx
  exact H1π_mem_continuousH1 _ M hc.isLevelConstant₁

variable {S} in

lemma continuousH1S_mono {S' : Finset Nat.Primes} (h : S ⊆ S') : continuousH1S S M ≤ continuousH1S S' M := by
  rintro x hx
  obtain ⟨c, hc, rfl⟩ := (mem_continuousH1S_iff S M x).1 hx
  exact (mem_continuousH1S_iff S' M _).2 ⟨c, hc.mono h, rfl⟩

def levelCocyclesS₂ :
    Submodule k ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) :=
  cocycles₂ M ⊓ levelCochainsS₂ S M

def levelCoboundariesS₂ :
    Submodule k ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) :=
  (levelCochainsS₁ S M).map (d₁₂ M).hom

lemma mem_levelCocyclesS₂_iff
    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) :
    f ∈ levelCocyclesS₂ S M ↔ f ∈ cocycles₂ M ∧ IsLevelConstantS₂ S f := Iff.rfl

lemma mem_levelCoboundariesS₂_iff
    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) :
    f ∈ levelCoboundariesS₂ S M ↔
      ∃ x : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M, IsLevelConstantS₁ S x ∧ (d₁₂ M).hom x = f := by
  simp only [levelCoboundariesS₂, Submodule.mem_map, mem_levelCochainsS₁_iff]

lemma levelCocyclesS₂_le_levelCocycles₂ : levelCocyclesS₂ S M ≤ levelCocycles₂ (MonoidHom.id _) M :=
  fun _ h => ⟨h.1, h.2.isLevelConstant₂⟩

lemma levelCoboundariesS₂_le_levelCoboundaries₂ :
    levelCoboundariesS₂ S M ≤ levelCoboundaries₂ (MonoidHom.id _) M := by
  rintro f hf
  obtain ⟨x, hx, rfl⟩ := (mem_levelCoboundariesS₂_iff S M f).1 hf
  exact (mem_levelCoboundaries₂_iff _ M _).2 ⟨x, hx.isLevelConstant₁, rfl⟩

abbrev continuousH2S : Type :=
  ↥(levelCocyclesS₂ S M) ⧸ (levelCoboundariesS₂ S M).comap (levelCocyclesS₂ S M).subtype

abbrev continuousH2Sπ : ↥(levelCocyclesS₂ S M) →ₗ[k] continuousH2S S M :=
  Submodule.mkQ _

lemma continuousH2Sπ_eq_zero_iff (f : ↥(levelCocyclesS₂ S M)) :
    continuousH2Sπ S M f = 0 ↔
      (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M)
        ∈ levelCoboundariesS₂ S M := by
  simp [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]

def levelCocyclesS₂ToLevelCocycles₂ : ↥(levelCocyclesS₂ S M) →ₗ[k] ↥(levelCocycles₂ (MonoidHom.id _) M) :=
  Submodule.inclusion (levelCocyclesS₂_le_levelCocycles₂ S M)

noncomputable def continuousH2SToContinuousH2 : continuousH2S S M →ₗ[k] continuousH2 (MonoidHom.id _) M :=
  Submodule.mapQ _ _ (levelCocyclesS₂ToLevelCocycles₂ S M) (fun c hc => by
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hc ⊢
    exact levelCoboundariesS₂_le_levelCoboundaries₂ S M hc)

noncomputable def locRes₂S {H : Type} [Group H] (f : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    continuousH2S S M →ₗ[k] continuousH2 f (Rep.res f M) :=
  continuousH2Map (rH := MonoidHom.id _) (rG := f) f (fun _ => rfl)
      (LinearMap.id : M →ₗ[k] Rep.res f M) (fun _ _ => rfl)
    ∘ₗ continuousH2SToContinuousH2 S M

noncomputable def locTotal₂S :
    continuousH2S S M →ₗ[k] ∀ v : extArithIndex S, continuousH2 (extArithLoc S v) (Rep.res (extArithLoc S v) M) :=
  LinearMap.pi fun v => locRes₂S S M (extArithLoc S v)

@[simp]
lemma locTotal₂S_apply (x : continuousH2S S M) (v : extArithIndex S) :
    locTotal₂S S M x v = locRes₂S S M (extArithLoc S v) x := rfl

noncomputable def sha₂ : Submodule k (continuousH2S S M) :=
  LinearMap.ker (locTotal₂S S M)

section Sha
variable {K : Type} [Field K] (A : Rep K (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

def sha₁ : Submodule K (H1 A) :=
  continuousH1S S A ⊓ LinearMap.ker (locTotal (extArithLoc S) A)

end Sha

end groupCohomology

end


