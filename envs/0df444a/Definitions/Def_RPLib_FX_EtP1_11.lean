-- Prove2me | Definitions.Def_RPLib_FX_EtP1_11
-- name    : RPLib_FX_EtP1_11
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T03:19:49.917883+00:00
-- url     : https://prove2.me/theorems/e770a344-3420-4ac9-bb03-fe2616816ce7
-- title:
--   Étale cohomology of the projective line, library file 11 of 34
-- statement:
--   File 11 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtSheaves_Closed`: S4-EtSheaves, part 14: `i_*` vanishes off `Z`
--   * `S4.Def_RP_EtCompact_ExtAdj`: S4-EtCompact, part 1: `Ext` along an adjunction
--   * `S4.Def_RP_EtCompact_P1Exc`: S4-EtCompact, part 28: excision on `P^1_K` at `∞` (O8a, file 2)
--   * `S4.Def_RP_EtCompact_A1Hc`: S4-EtCompact, part 29: `H^*_c(A^1, Λ)` inside `P^1` (O8a, file 3)
--   * `S4.Def_RP_CdOne_Coh`: S4-PD (3a), part 1: elementary degree-2 group cohomology
--   * `S4.Def_RP_Tsen_Zero`: S4-PD (1), T1: common zeros over an algebraically closed field; the strong `C₁` property
--   * `S4.Def_RP_Tsen_RatFunc`: S4-PD (1), T2: Tsen's theorem for `k(t)`
--   * `S4.Def_RP_Tsen_Norm`: S4-PD (1), T3: finite extensions of `C₁` fields are `C₁` (the norm form)
--   * `S4.Def_RP_Tsen`: S4-PD (1): Tsen's theorem
--   * `S4.Def_RP_CdOne_Br`: S4-PD (3a), part 2: `Br(L/K) = 0` for a Galois `p`-extension of a C1 field
--   * `S4.Def_RP_CdOne_Lc`: S4-PD (3), group layer part 1: locally constant cochains and the index lemma
--   * `S4.Def_RP_EtCompact_GlobQ`: S4-EtCompact, part 54: the global Kummer section at a closed point (F7c of plan v5)
--   * `S4.Def_RP_EtCompact_PtCd`: S4-EtCompact, part 38: `H^(n+2)` of a point vanishes when `cd ≤ 1` (CC2c)
--   * `S4.Def_RP_EtCompact_GenPt`: S4-EtCompact, part 39: `H^(n+2)` of `C₁` points and of the generic point of `A¹` (CC2d)
--   * `S4.Def_RP_EtCompact_GmKc`: S4-EtCompact: `H^1(G_m, Λ) ≃ Λ` (O8c, files M4c + M4e)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_10

/-!
# Étale cohomology of the projective line, library file 11 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtSheaves_Closed`: S4-EtSheaves, part 14: `i_*` vanishes off `Z`
* `S4.Def_RP_EtCompact_ExtAdj`: S4-EtCompact, part 1: `Ext` along an adjunction
* `S4.Def_RP_EtCompact_P1Exc`: S4-EtCompact, part 28: excision on `P^1_K` at `∞` (O8a, file 2)
* `S4.Def_RP_EtCompact_A1Hc`: S4-EtCompact, part 29: `H^*_c(A^1, Λ)` inside `P^1` (O8a, file 3)
* `S4.Def_RP_CdOne_Coh`: S4-PD (3a), part 1: elementary degree-2 group cohomology
* `S4.Def_RP_Tsen_Zero`: S4-PD (1), T1: common zeros over an algebraically closed field; the strong `C₁` property
* `S4.Def_RP_Tsen_RatFunc`: S4-PD (1), T2: Tsen's theorem for `k(t)`
* `S4.Def_RP_Tsen_Norm`: S4-PD (1), T3: finite extensions of `C₁` fields are `C₁` (the norm form)
* `S4.Def_RP_Tsen`: S4-PD (1): Tsen's theorem
* `S4.Def_RP_CdOne_Br`: S4-PD (3a), part 2: `Br(L/K) = 0` for a Galois `p`-extension of a C1 field
* `S4.Def_RP_CdOne_Lc`: S4-PD (3), group layer part 1: locally constant cochains and the index lemma
* `S4.Def_RP_EtCompact_GlobQ`: S4-EtCompact, part 54: the global Kummer section at a closed point (F7c of plan v5)
* `S4.Def_RP_EtCompact_PtCd`: S4-EtCompact, part 38: `H^(n+2)` of a point vanishes when `cd ≤ 1` (CC2c)
* `S4.Def_RP_EtCompact_GenPt`: S4-EtCompact, part 39: `H^(n+2)` of `C₁` points and of the generic point of `A¹` (CC2d)
* `S4.Def_RP_EtCompact_GmKc`: S4-EtCompact: `H^1(G_m, Λ) ≃ Λ` (O8c, files M4c + M4e)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtSheaves_Closed =====
section

/-!
# S4-EtSheaves, part 14: `i_*` vanishes off `Z`

For `i : Z ⟶ X` and an etale `j : U ⟶ X` whose image misses the image of `i`, the restriction
`j^* i_* G` is the zero sheaf: its values are those of `G` on the empty schemes `W ×_X Z`.
Hence the stalks of `i_* G` vanish at geometric points outside the (closed) image of `i`, every
map `j_! G' ⟶ i_* G` is zero, and `j_! j^* F ⟶ F ⟶ i_* i^* F` is a complex.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ]

variable {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) [Etale j]

/-- The open complement of a closed immersion. -/
def complOpens [IsClosedImmersion i] : X.Opens :=
  ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtCompact_ExtAdj =====
section

/-!
# S4-EtCompact, part 1: `Ext` along an adjunction

For an adjunction `L ⊣ R` between abelian categories with `R` exact and `L` preserving
monomorphisms (so `R` preserves injective objects), the map
`e ↦ mk₀ (η_A) ∘ R(e) : Ext (L A) B n → Ext A (R B) n` is bijective.
Proof: induction on `n` with injective presentations of `B`, as in
`Functor.mapExt_bijective_of_preservesInjectiveObjects`.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact

universe w v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable [HasExt.{w} C] [HasExt.{w} D]
variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
variable [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- The adjunction map on `Ext`: `e ↦ mk₀ η_A ∘ R(e)`. -/
def extAdjMap (A : C) (B : D) (n : ℕ) : Ext (L.obj A) B n →+ Ext A (R.obj B) n where
  toFun e := (Ext.mk₀ (adj.unit.app A)).comp (e.mapExactFunctor R) (zero_add n)
  map_zero' := by simp [Ext.mapExactFunctor_zero]
  map_add' x y := by simp [Ext.mapExactFunctor_add]

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_P1Exc =====
section

/-!
# S4-EtCompact, part 28: excision on `P^1_K` at `∞` (O8a, file 2)

General facts:
* `Hmap_zero_injective`: `H^0(X, -)` sends monomorphisms to injections; so `extO` is injective in degree 0.
* `cutUnivIso : cut univ F ≅ F`; `cutRangeIso i F : cut (range i) F ≅ i_* i^* F` for a closed immersion `i`
  (from the EtSheaves cut sequence), hence `hcRangeEquiv : H^n_c(range i, F) ≃+ H^n(Z, i^* F)`.
* The point scheme `Spec κ(y)` of a point `y`: `Spec κ(y) ⟶ Spec κ(y)`'s residue map is an isomorphism and
  `κ(pt) ≅ κ(y)`; for `κ(y)` algebraically closed, `H^(n+1)(Spec κ(y), -) = 0` (`H_ptOf_eq_zero`), so
  `H^(n+1)_c({y}, F) = 0` for every closed point `y` with algebraically closed residue field (`hc_closedPt_eq_zero`).

On `P^1_K` (`K` algebraically closed), with `S = univ` and `O = A^1 = D₊(X₀)` (`S \ O = {∞}`), the excision sequence
gives: `extO : H^m_c(A^1 ⊆ P^1, F) → H^m(P^1, cut univ F)` is bijective for `m ≥ 2`, surjective for `m = 1` and
injective for `m = 0` (`P1.extO_bijective`, `P1.extO_one_surjective`, `extO_zero_injective`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section General

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

section Closed

variable {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

end Closed

end General

section Point

variable {Y : Scheme.{u}} (y : Y)

/-- The point of `Spec κ(y)`. -/
abbrev ptOf : Spec (Y.residueField y) := default

instance isClosedImmersion_ptOf :
    IsClosedImmersion ((Spec (Y.residueField y)).fromSpecResidueField (ptOf y)) := by
  rw [← isClosed_singleton_iff_isClosedImmersion]
  have h : ({ptOf y} : Set (Spec (Y.residueField y))) = Set.univ :=
    Set.eq_univ_of_forall fun z => Subsingleton.elim z _
  rw [h]
  exact isClosed_univ

instance surjective_ptOf : Surjective ((Spec (Y.residueField y)).fromSpecResidueField (ptOf y)) :=
  ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩

instance isIso_ptOf : IsIso ((Spec (Y.residueField y)).fromSpecResidueField (ptOf y)) :=
  isIso_of_isClosedImmersion_of_surjective _

/-- `κ(y) ≅ κ(pt)` for the point of `Spec κ(y)`. -/
def ptResidueIso : Y.residueField y ≅ (Spec (Y.residueField y)).residueField (ptOf y) :=
  (Spec.fullyFaithful.preimageIso (X := Opposite.op ((Spec (Y.residueField y)).residueField (ptOf y)))
    (Y := Opposite.op (Y.residueField y))
    (asIso ((Spec (Y.residueField y)).fromSpecResidueField (ptOf y)))).unop

instance isAlgClosed_ptOf [IsAlgClosed (Y.residueField y)] :
    IsAlgClosed ((Spec (Y.residueField y)).residueField (ptOf y)) :=
  IsAlgClosed.of_ringEquiv _ _ (ptResidueIso y).commRingCatIsoToRingEquiv

variable (Λ : Type u) [CommRing Λ]

end Point

section P1

variable (K : Type u) [Field K] [IsAlgClosed K] (Λ : Type u) [CommRing Λ]

end P1

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_A1Hc =====
section

/-!
# S4-EtCompact, part 29: `H^*_c(A^1, Λ)` inside `P^1` (O8a, file 3)

* `lshResIso j G : j_! j^* G ≅ openCut (range j) G` for any open immersion `j` (stalkwise, via `Abelian.monoLift`).
* `cutOpenIso O F : cut (univ ∩ O) F ≅ openCut O F`.
* `A1.hcEquiv : H^n_c(A^1, Λ) ≃+ H^n_c(univ ∩ A^1 ⊆ P^1, Λ_{P^1})` (the compactification `A1.cpt`).
* The comparison `A1.toP1 n : H^n_c(A^1, Λ) →+ H^n(P^1, Λ)` (extension by zero) is injective for `n = 0`, surjective
  for `n = 1` and bijective for `n ≥ 2` (`K` algebraically closed); `A1.hcEquivP1 : H^(n+2)_c(A^1, Λ) ≃+ H^(n+2)(P^1, Λ)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section OpenIm

variable {Λ : Type u} [CommRing Λ] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **`j_! j^* G ≅ openCut (range j) G`** for an open immersion `j`. -/
def lshResIso (G : EtSh Λ X) : (lsh j Λ).obj ((res j Λ).obj G) ≅ openCut Λ j.opensRange G :=
  asIso (lshToOpenCut j G)

end OpenIm

section OpenCut

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

end OpenCut

section A1

variable (K : Type u) [Field K] (Λ : Type u) [CommRing Λ]

variable [IsAlgClosed K]

end A1

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_CdOne_Coh =====
section

/-!
# S4-PD (3a), part 1: elementary degree-2 group cohomology

Explicit, additive computations behind `Br(L/K) = 0` over a C1 field (no `FiniteCyclic`, any universes):
* `d₁ b`, the coboundary of a 1-cochain; `isCoboundary₂_of_sub` transfers coboundary-ness along `f - d₁ b`.
* `isCoboundary₂_of_cyclic`: if `σ` generates the finite group `G` and every `σ`-fixed element of `A` is a norm
  `∑_{t < ord σ} σ ^ t • c`, every 2-cocycle is a coboundary.
* `exists_inflated` (degree-2 inflation-restriction): for `N ◁ G` with `H¹(N, A) = 0` and `f|N×N` a coboundary,
  `f - d₁ b` is invariant under right multiplication by `N` in both variables and takes `N`-fixed values.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CdOne

open groupCohomology

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- The coboundary of a 1-cochain. -/
def d₁ (b : G → A) : G × G → A := fun p => p.1 • b p.2 - b (p.1 * p.2) + b p.1

@[simp] theorem d₁_apply (b : G → A) (g h : G) : d₁ b (g, h) = g • b h - b (g * h) + b g := rfl

theorem d₁_add (b b' : G → A) : d₁ (b + b') = d₁ b + d₁ b' := by
  funext p; simp only [d₁, Pi.add_apply, smul_add]; abel

theorem eq_of_sub_eq {a b c d : A} (h : c = d) (he : a - b = c - d) : a = b := by
  rw [← sub_eq_zero, he, h, sub_self]

theorem isCocycle₂_d₁ (b : G → A) : IsCocycle₂ (d₁ b) := by
  intro g h j
  simp only [d₁_apply, smul_add, smul_sub, mul_smul, mul_assoc]
  abel

theorem isCocycle₂_sub_d₁ {f : G × G → A} (hf : IsCocycle₂ f) (b : G → A) : IsCocycle₂ (f - d₁ b) := by
  intro g h j
  have h1 := hf g h j
  have h2 := isCocycle₂_d₁ b g h j
  simp only [Pi.sub_apply, smul_sub]
  exact eq_of_sub_eq (congrArg₂ HSub.hSub h1 h2) (by abel)

theorem isCoboundary₂_of_sub {f : G × G → A} (b : G → A) (h : IsCoboundary₂ (f - d₁ b)) :
    IsCoboundary₂ f := by
  obtain ⟨x, hx⟩ := h
  refine ⟨b + x, fun g h => ?_⟩
  have := hx g h
  simp only [Pi.sub_apply, d₁_apply, Pi.add_apply, smul_add] at this ⊢
  rw [eq_sub_iff_add_eq] at this
  rw [← this]; abel

/-! ## The cyclic case -/

section Cyclic

variable [Finite G] {σ : G} (hσ : ∀ g : G, ∃ i : ℕ, σ ^ i = g)

/-- The exponent of `g` in `[0, ord σ)`. -/
noncomputable def idx (g : G) : ℕ := (hσ g).choose % orderOf σ

include hσ in
theorem pow_idx (g : G) : σ ^ idx hσ g = g := by
  rw [idx, pow_mod_orderOf, (hσ g).choose_spec]

theorem idx_lt (g : G) : idx hσ g < orderOf σ :=
  Nat.mod_lt _ (isOfFinOrder_of_finite σ).orderOf_pos

theorem idx_pow {i : ℕ} (hi : i < orderOf σ) : idx hσ (σ ^ i) = i := by
  have h := pow_idx hσ (σ ^ i)
  rw [(isOfFinOrder_of_finite σ).pow_inj_mod, Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt (idx_lt hσ _)] at h
  exact h

/-- A normalized cocycle on a cyclic group: `F (σ^i, σ^j) = [i + j ≥ m] a`. -/
theorem cyclic_normal_form {F : G × G → A} (hF : IsCocycle₂ F) (hF11 : F (1, 1) = 0)
    (hF0 : ∀ k, k + 1 < orderOf σ → F (σ ^ k, σ) = 0) (i j : ℕ) (hi : i < orderOf σ) (hj : j < orderOf σ) :
    F (σ ^ i, σ ^ j) = if orderOf σ ≤ i + j then F (σ ^ (orderOf σ - 1), σ) else 0 := by
  induction j with
  | zero =>
    rw [if_neg (show ¬ orderOf σ ≤ i + 0 by omega), pow_zero, map_one_snd_of_isCocycle₂ hF (σ ^ i), hF11,
      smul_zero]
  | succ j ih =>
    have hc := hF (σ ^ i) (σ ^ j) σ
    rw [← pow_add, ← pow_succ, hF0 j (by omega), smul_zero, zero_add, ih (by omega)] at hc
    rw [← hc]
    by_cases h1 : i + j + 1 < orderOf σ
    · rw [hF0 _ h1, if_neg (show ¬ orderOf σ ≤ i + j by omega),
        if_neg (show ¬ orderOf σ ≤ i + (j + 1) by omega), add_zero]
    · by_cases h2 : i + j + 1 = orderOf σ
      · rw [if_neg (show ¬ orderOf σ ≤ i + j by omega), if_pos (show orderOf σ ≤ i + (j + 1) by omega),
          add_zero, show i + j = orderOf σ - 1 by omega]
      · obtain ⟨r, hr⟩ : ∃ r, i + j = orderOf σ + r := ⟨i + j - orderOf σ, by omega⟩
        rw [if_pos (show orderOf σ ≤ i + j by omega), if_pos (show orderOf σ ≤ i + (j + 1) by omega), hr,
          pow_add, pow_orderOf_eq_one, one_mul, hF0 r (by omega), zero_add]

theorem sum_pow_smul_add (c : A) (i j : ℕ) :
    σ ^ i • ∑ t ∈ Finset.range j, σ ^ t • c + ∑ t ∈ Finset.range i, σ ^ t • c =
      ∑ t ∈ Finset.range (i + j), σ ^ t • c := by
  simp only [Finset.sum_range_add, Finset.smul_sum, ← mul_smul, ← pow_add]
  exact add_comm _ _

include hσ in
theorem isCoboundary₂_of_cyclic {f : G × G → A} (hf : IsCocycle₂ f)
    (hnorm : ∀ a : A, σ • a = a → ∃ c : A, ∑ t ∈ Finset.range (orderOf σ), σ ^ t • c = a) :
    IsCoboundary₂ f := by
  classical
  have hm0 : 0 < orderOf σ := (isOfFinOrder_of_finite σ).orderOf_pos
  obtain ⟨b, hb⟩ : ∃ b : G → A, ∀ g, b g = f (1, 1) - ∑ t ∈ Finset.range (idx hσ g), f (σ ^ t, σ) :=
    ⟨_, fun _ => rfl⟩
  have hFc : IsCocycle₂ (f - d₁ b) := isCocycle₂_sub_d₁ hf b
  have hb1 : b 1 = f (1, 1) := by
    have h0 : idx hσ 1 = 0 := by simpa using idx_pow hσ (i := 0) hm0
    rw [hb, h0, Finset.sum_range_zero, sub_zero]
  have hF11 : (f - d₁ b) (1, 1) = 0 := by
    simp only [Pi.sub_apply, d₁_apply, one_smul, mul_one, hb1]; abel
  have hF0 : ∀ k, k + 1 < orderOf σ → (f - d₁ b) (σ ^ k, σ) = 0 := by
    intro k hk
    have h1 : idx hσ σ = 1 := by simpa using idx_pow hσ (i := 1) (by omega)
    have hbσ : b σ = 0 := by
      rw [hb, h1, Finset.sum_range_one, pow_zero, map_one_fst_of_isCocycle₂ hf σ, sub_self]
    have hk1 : idx hσ (σ ^ k * σ) = k + 1 := by rw [← pow_succ]; exact idx_pow hσ hk
    have hk0 : idx hσ (σ ^ k) = k := idx_pow hσ (by omega)
    rw [Pi.sub_apply, d₁_apply, hbσ, smul_zero, hb (σ ^ k * σ), hb (σ ^ k), hk1, hk0, Finset.sum_range_succ]
    abel
  have hnf := cyclic_normal_form hFc hF11 hF0
  -- the invariant element `a = F (σ ^ (m - 1), σ)`
  have hσa : σ • (f - d₁ b) (σ ^ (orderOf σ - 1), σ) = (f - d₁ b) (σ ^ (orderOf σ - 1), σ) := by
    by_cases hm1 : orderOf σ = 1
    · rw [orderOf_eq_one_iff.mp hm1, one_smul]
    · have hc := hFc σ (σ ^ (orderOf σ - 1)) σ
      have e1 : σ * σ ^ (orderOf σ - 1) = 1 := by
        rw [← pow_succ', Nat.sub_add_cancel hm0, pow_orderOf_eq_one]
      have e2 : σ ^ (orderOf σ - 1) * σ = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel hm0, pow_orderOf_eq_one]
      have e3 := hnf 1 (orderOf σ - 1) (by omega) (by omega)
      rw [pow_one, if_pos (show orderOf σ ≤ 1 + (orderOf σ - 1) by omega)] at e3
      rw [e1, e2, map_one_fst_of_isCocycle₂ hFc σ, hF11, zero_add, e3,
        map_one_snd_of_isCocycle₂ hFc σ, hF11, smul_zero, add_zero] at hc
      exact hc.symm
  obtain ⟨c, hcn⟩ := hnorm _ hσa
  obtain ⟨b', hb'⟩ : ∃ b' : G → A, ∀ g, b' g = ∑ t ∈ Finset.range (idx hσ g), σ ^ t • c :=
    ⟨_, fun _ => rfl⟩
  apply isCoboundary₂_of_sub b
  refine ⟨b', fun g h => ?_⟩
  obtain ⟨i, hi, rfl⟩ : ∃ i, i < orderOf σ ∧ σ ^ i = g := ⟨_, idx_lt hσ g, pow_idx hσ g⟩
  obtain ⟨j, hj, rfl⟩ : ∃ j, j < orderOf σ ∧ σ ^ j = h := ⟨_, idx_lt hσ h, pow_idx hσ h⟩
  rw [hnf i j hi hj, ← pow_add, hb', hb', hb', idx_pow hσ hi, idx_pow hσ hj]
  by_cases hij : orderOf σ ≤ i + j
  · obtain ⟨r, hr⟩ : ∃ r, i + j = orderOf σ + r := ⟨i + j - orderOf σ, by omega⟩
    rw [if_pos hij, hr, pow_add, pow_orderOf_eq_one, one_mul, idx_pow hσ (by omega : r < orderOf σ),
      sub_add_eq_add_sub, sum_pow_smul_add, hr, Finset.sum_range_add, hcn]
    simp only [pow_add, pow_orderOf_eq_one, one_mul, add_sub_cancel_right]
  · rw [if_neg hij, idx_pow hσ (by omega : i + j < orderOf σ), sub_add_eq_add_sub, sum_pow_smul_add,
      sub_self]

end Cyclic

/-! ## Inflation-restriction in degree 2 -/

section InfRes

variable (N : Subgroup G) [hN : N.Normal]

/-- A representative of the coset `g N`. -/
noncomputable def rep (g : G) : G := (QuotientGroup.mk g : G ⧸ N).out

theorem rep_inv_mul_mem (g : G) : (rep N g)⁻¹ * g ∈ N :=
  QuotientGroup.eq.mp (QuotientGroup.out_eq' _)

theorem rep_eq_of_mem {g g' : G} (h : g⁻¹ * g' ∈ N) : rep N g = rep N g' := by
  unfold rep; rw [QuotientGroup.eq.mpr h]

theorem rep_mul_mem (g : G) {n : G} (hn : n ∈ N) : rep N (g * n) = rep N g :=
  rep_eq_of_mem N (by simpa [mul_assoc] using N.inv_mem hn)

theorem rep_mem_of_mem {n : G} (hn : n ∈ N) : rep N n ∈ N := by
  have h := N.mul_mem (rep_inv_mul_mem N n) (N.inv_mem hn)
  rw [mul_inv_cancel_right] at h
  simpa using N.inv_mem h

theorem rep_of_mem {n : G} (hn : n ∈ N) : rep N n = rep N 1 :=
  rep_eq_of_mem N (by simpa using N.inv_mem hn)

include hN in
theorem conj_mem' {n : G} (hn : n ∈ N) (h : G) : h⁻¹ * n * h ∈ N := by
  simpa using hN.conj_mem n hn h⁻¹

include hN in
theorem rep_mem_mul {n : G} (hn : n ∈ N) (h : G) : rep N (n * h) = rep N h := by
  refine rep_eq_of_mem N ?_
  have := conj_mem' N (N.inv_mem hn) h
  convert this using 1; group

theorem exists_zero_on_sub {f : G × G → A}
    (hNf : IsCoboundary₂ (fun p : N × N => f ((p.1 : G), (p.2 : G)))) :
    ∃ b : G → A, ∀ n ∈ N, ∀ n' ∈ N, (f - d₁ b) (n, n') = 0 := by
  classical
  obtain ⟨β, hβ⟩ := hNf
  refine ⟨fun g => if h : g ∈ N then β ⟨g, h⟩ else 0, fun n hn n' hn' => ?_⟩
  have e : n • β ⟨n', hn'⟩ - β ⟨n * n', N.mul_mem hn hn'⟩ + β ⟨n, hn⟩ = f (n, n') :=
    hβ ⟨n, hn⟩ ⟨n', hn'⟩
  simp only [Pi.sub_apply, d₁_apply, dif_pos hn, dif_pos hn', dif_pos (N.mul_mem hn hn')]
  rw [e, sub_self]

theorem exists_zero_right {f : G × G → A} (hf : IsCocycle₂ f)
    (h0 : ∀ n ∈ N, ∀ n' ∈ N, f (n, n') = 0) :
    ∃ b : G → A, ∀ g, ∀ n ∈ N, (f - d₁ b) (g, n) = 0 := by
  refine ⟨fun g => -f (rep N g, (rep N g)⁻¹ * g), fun g n hn => ?_⟩
  have hbn : f (rep N n, (rep N n)⁻¹ * n) = 0 :=
    h0 _ (rep_mem_of_mem N hn) _ (rep_inv_mul_mem N n)
  have hgn : rep N (g * n) = rep N g := rep_mul_mem N g hn
  have hc := hf (rep N g) ((rep N g)⁻¹ * g) n
  rw [mul_inv_cancel_left, h0 _ (rep_inv_mul_mem N g) _ hn, smul_zero, zero_add,
    mul_assoc ((rep N g)⁻¹) g n] at hc
  simp only [Pi.sub_apply, d₁_apply, hgn, hbn, neg_zero, smul_zero]
  rw [← hc]; abel

include hN in
theorem exists_zero_both {f : G × G → A} (hf : IsCocycle₂ f) (h1 : ∀ g, ∀ n ∈ N, f (g, n) = 0)
    (hH1 : ∀ φ : N → A, IsCocycle₁ φ → IsCoboundary₁ φ) :
    ∃ b : G → A, (∀ g, ∀ n ∈ N, (f - d₁ b) (g, n) = 0) ∧ ∀ n ∈ N, ∀ h, (f - d₁ b) (n, h) = 0 := by
  classical
  have hfR : ∀ g h, ∀ n ∈ N, f (g, h * n) = f (g, h) := by
    intro g h n hn
    have := hf g h n
    rw [h1 _ n hn, h1 h n hn, smul_zero, zero_add, zero_add] at this
    exact this.symm
  have hcoc : ∀ k : G, IsCocycle₁ (fun n : N => f ((n : G), k)) := by
    intro k n n'
    have hc := hf n n' k
    rw [h1 _ _ n'.2, add_zero] at hc
    have e : f ((n : G), (n' : G) * k) = f (n, k) := by
      rw [show (n' : G) * k = k * (k⁻¹ * n' * k) by group]
      exact hfR _ _ _ (conj_mem' N n'.2 k)
    rw [e] at hc
    exact hc
  choose c hc using fun k : G => hH1 _ (hcoc k)
  have hc' : ∀ k, ∀ n ∈ N, n • c k - c k = f (n, k) := fun k n hn => hc k ⟨n, hn⟩
  refine ⟨fun h => c (rep N h) - c (rep N 1), fun g n hn => ?_, fun n hn h => ?_⟩
  · simp only [Pi.sub_apply, d₁_apply, rep_of_mem N hn, rep_mul_mem N g hn, sub_self, smul_zero,
      h1 g n hn]
    abel
  · have hfn : f (n, h) = f (n, rep N h) := by
      conv_lhs => rw [← mul_inv_cancel_left (rep N h) h]
      exact hfR _ _ _ (rep_inv_mul_mem N h)
    have hf1 : f (n, rep N 1) = 0 := h1 n _ (rep_mem_of_mem N (one_mem N))
    simp only [Pi.sub_apply, d₁_apply, rep_of_mem N hn, rep_mem_mul N hn, sub_self, add_zero, smul_sub]
    have h0' : n • c (rep N 1) - c (rep N 1) = 0 := by rw [hc' _ n hn, hf1]
    rw [hfn, ← hc' _ n hn]
    exact eq_of_sub_eq h0' (by abel)

include hN in
theorem invariant_of_zero {F : G × G → A} (hF : IsCocycle₂ F) (hR : ∀ g, ∀ n ∈ N, F (g, n) = 0)
    (hL : ∀ n ∈ N, ∀ h, F (n, h) = 0) (g h : G) {n : G} (hn : n ∈ N) :
    F (g * n, h) = F (g, h) ∧ F (g, h * n) = F (g, h) ∧ n • F (g, h) = F (g, h) := by
  have hright : ∀ g h, ∀ n ∈ N, F (g, h * n) = F (g, h) := by
    intro g h n hn
    have := hF g h n
    rw [hR _ n hn, hR h n hn, smul_zero, zero_add, zero_add] at this
    exact this.symm
  have hleft : ∀ g h, ∀ n ∈ N, F (g * n, h) = F (g, h) := by
    intro g h n hn
    have := hF g n h
    rw [hR g n hn, hL n hn h, smul_zero, zero_add, add_zero,
      show n * h = h * (h⁻¹ * n * h) by group] at this
    rw [this]; exact hright _ _ _ (conj_mem' N hn h)
  refine ⟨hleft g h n hn, hright g h n hn, ?_⟩
  have := hF n g h
  rw [hL n hn g, hL n hn (g * h), add_zero, add_zero, show n * g = g * (g⁻¹ * n * g) by group,
    hleft _ _ _ (conj_mem' N hn g)] at this
  exact this.symm

include hN in
/-- Degree-2 inflation-restriction: `f` is cohomologous to a cocycle inflated from `G ⧸ N` with values in `A^N`. -/
theorem exists_inflated {f : G × G → A} (hf : IsCocycle₂ f)
    (hH1 : ∀ φ : N → A, IsCocycle₁ φ → IsCoboundary₁ φ)
    (hNf : IsCoboundary₂ (fun p : N × N => f ((p.1 : G), (p.2 : G)))) :
    ∃ b : G → A, IsCocycle₂ (f - d₁ b) ∧ ∀ g h : G, ∀ n ∈ N,
      (f - d₁ b) (g * n, h) = (f - d₁ b) (g, h) ∧ (f - d₁ b) (g, h * n) = (f - d₁ b) (g, h) ∧
        n • (f - d₁ b) (g, h) = (f - d₁ b) (g, h) := by
  obtain ⟨b0, hb0⟩ := exists_zero_on_sub N hNf
  have hf0 := isCocycle₂_sub_d₁ hf b0
  obtain ⟨b1, hb1⟩ := exists_zero_right N hf0 hb0
  have hf1 := isCocycle₂_sub_d₁ hf0 b1
  obtain ⟨b2, hb2R, hb2L⟩ := exists_zero_both N hf1 hb1 hH1
  have hf2 := isCocycle₂_sub_d₁ hf1 b2
  have e : f - d₁ (b0 + b1 + b2) = f - d₁ b0 - d₁ b1 - d₁ b2 := by
    rw [d₁_add, d₁_add]; abel
  refine ⟨b0 + b1 + b2, ?_, fun g h n hn => ?_⟩
  · rw [e]; exact hf2
  · rw [e]; exact invariant_of_zero N hf2 hb2R hb2L g h hn

end InfRes

end RamanujanPetersson.CdOne


end

-- ===== S4.Def_RP_Tsen_Zero =====
section

set_option autoImplicit false

/-!
# S4-PD (1), T1: common zeros over an algebraically closed field; the strong `C₁` property

* `exists_common_zero`: over an algebraically closed field `k`, `m` polynomials in `n > m` variables without constant
  term have a common nonzero zero (Krull's height theorem + the Nullstellensatz).
* `IsC1 K`: every polynomial in `n` variables over `K` with total degree `< n` and constant term `0` has a nonzero zero.
  (`IsC1.exists_zero_of_isHomogeneous`: the classical `C₁` property for forms.)
-/

namespace RamanujanPetersson.Tsen

open MvPolynomial

section Zero

variable {k : Type*} [Field k]

theorem ringKrullDim_mvPolynomial_fin (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) = n := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

theorem finiteRingKrullDim_mvPolynomial_fin (n : ℕ) :
    FiniteRingKrullDim (MvPolynomial (Fin n) k) := by
  rw [FiniteRingKrullDim, Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top]
  have h := ringKrullDim_mvPolynomial_fin (k := k) n
  rw [ringKrullDim] at h
  rw [h]
  exact ⟨WithBot.natCast_ne_bot n, by
    intro h'
    have : ((n : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) := by simpa using h'
    exact ENat.natCast_ne_top n (WithBot.coe_injective this)⟩

/-- Evaluation after the translation `X j ↦ X j - a j`. -/
theorem eval_translate {n : ℕ} (a x : Fin n → k) (p : MvPolynomial (Fin n) k) :
    eval x (aeval (fun j => X j - C (a j)) p) = eval (fun j => x j - a j) p := by
  have h := congrArg (fun φ : MvPolynomial (Fin n) k →ₐ[k] k => φ p)
    (MvPolynomial.comp_aeval (fun j => (X j - C (a j) : MvPolynomial (Fin n) k)) (aeval x))
  simp only [AlgHom.comp_apply, map_sub, aeval_X, aeval_C, Algebra.algebraMap_self,
    RingHom.id_apply] at h
  rw [← coe_aeval_eq_eval, ← coe_aeval_eq_eval]
  exact h

/-- **Common zeros.** Over an algebraically closed field, `m` polynomials without constant term in `n > m` variables
have a common nonzero zero. -/
theorem exists_common_zero [IsAlgClosed k] {n m : ℕ} (hmn : m < n) (f : Fin m → MvPolynomial (Fin n) k)
    (hf : ∀ i, constantCoeff (f i) = 0) : ∃ x : Fin n → k, x ≠ 0 ∧ ∀ i, eval x (f i) = 0 := by
  classical
  by_contra hne
  push Not at hne
  have := finiteRingKrullDim_mvPolynomial_fin (k := k) n
  obtain ⟨M, hM, hMh⟩ := Ideal.exists_isMaximal_height (R := MvPolynomial (Fin n) k)
  obtain ⟨a, rfl⟩ := eq_vanishingIdeal_singleton_of_isMaximal k hM
  set τ : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k := aeval (fun j => X j - C (a j))
  set s : Finset (MvPolynomial (Fin n) k) := Finset.univ.image (fun i => τ (f i))
  -- the zero locus of `span s` is `{a}`
  have hZ : zeroLocus k (Ideal.span (s : Set (MvPolynomial (Fin n) k))) = {a} := by
    ext x
    rw [zeroLocus_span, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hxa
      have hsub : (fun j => x j - a j) ≠ 0 := by
        intro h0
        apply hxa
        funext j
        have := congrFun h0 j
        simpa [sub_eq_zero] using this
      obtain ⟨i, hi⟩ := hne _ hsub
      apply hi
      have := hx (τ (f i)) (by simp [s])
      rw [aeval_eq_eval, eval_translate] at this
      exact this
    · rintro rfl p hp
      simp only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hp
      obtain ⟨i, rfl⟩ := hp
      rw [aeval_eq_eval, eval_translate]
      have : (fun j => x j - x j) = (0 : Fin n → k) := by funext j; simp
      rw [this, eval_zero]
      exact hf i
  have hrad : (Ideal.span (s : Set (MvPolynomial (Fin n) k))).radical = vanishingIdeal k {a} := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := k), hZ]
  have hmin : vanishingIdeal k {a} ∈ (Ideal.span (s : Set (MvPolynomial (Fin n) k))).minimalPrimes := by
    refine ⟨⟨hM.isPrime, hrad ▸ Ideal.le_radical⟩, ?_⟩
    rintro q ⟨hq, hsq⟩ _
    rw [← hrad]
    exact (Ideal.IsPrime.radical_le_iff hq).2 hsq
  have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
  have h2 : s.card ≤ m := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := fun i => τ (f i)))
  rw [ringKrullDim_mvPolynomial_fin] at hMh
  have h3 : (vanishingIdeal k {a}).height = (n : ℕ∞) := by exact_mod_cast hMh
  rw [h3] at h1
  have h4 : n ≤ s.card := by exact_mod_cast h1
  omega

end Zero

/-- The (strong) **`C₁` property**: every polynomial in `n` variables of total degree `< n` without constant term has a
nonzero zero. Over a field it implies the classical `C₁` property for forms (`IsC1.exists_zero_of_isHomogeneous`). -/
def IsC1 (K : Type*) [Field K] : Prop :=
  ∀ (n : ℕ) (f : MvPolynomial (Fin n) K), f.totalDegree < n → constantCoeff f = 0 →
    ∃ x : Fin n → K, x ≠ 0 ∧ eval x f = 0

end RamanujanPetersson.Tsen


end

-- ===== S4.Def_RP_Tsen_RatFunc =====
section

set_option autoImplicit false

/-!
# S4-PD (1), T2: Tsen's theorem for `k(t)`

* `exists_zero_polynomial`: `k` algebraically closed, `F ∈ k[t][x₀,…,x_{n-1}]` with total degree `< n` and no constant
  term has a nonzero zero in `k[t]ⁿ` (substitute `xᵢ = ∑_{j ≤ N} a_{ij} tʲ`, count unknowns against the coefficients of
  the powers of `t`, and apply `exists_common_zero`).
* `exists_clear_denom`: common denominators for a multivariate polynomial over a fraction field.
* `isC1_ratFunc`: `RatFunc k` is `C₁` (strong form `IsC1`).
-/

namespace RamanujanPetersson.Tsen

open Polynomial

section Core

variable {k : Type*} [Field k]

/-- The generic substitution `xᵢ = ∑_{j ≤ N} a_{(i,j)} tʲ`, with the `a`'s as variables. -/
noncomputable def subVar (n N : ℕ) (i : Fin n) : (MvPolynomial (Fin (n * (N + 1))) k)[X] :=
  ∑ j : Fin (N + 1), C (MvPolynomial.X (finProdFinEquiv (i, j))) * X ^ (j : ℕ)

/-- `F` after the generic substitution, a polynomial in `t` over the polynomial ring of the unknowns. -/
noncomputable def subPoly (n N : ℕ) (F : MvPolynomial (Fin n) k[X]) :
    (MvPolynomial (Fin (n * (N + 1))) k)[X] :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom MvPolynomial.C) (subVar n N) F

/-- The substitution at a point `a` of the unknowns. -/
noncomputable def specVar (n N : ℕ) (a : Fin (n * (N + 1)) → k) (i : Fin n) : k[X] :=
  ∑ j : Fin (N + 1), C (a (finProdFinEquiv (i, j))) * X ^ (j : ℕ)

theorem map_subPoly (n N : ℕ) (F : MvPolynomial (Fin n) k[X]) (a : Fin (n * (N + 1)) → k) :
    (subPoly n N F).map (MvPolynomial.eval a) = MvPolynomial.eval (specVar n N a) F := by
  unfold subPoly
  rw [← Polynomial.coe_mapRingHom, MvPolynomial.eval₂_comp_left]
  have h1 : (Polynomial.mapRingHom (MvPolynomial.eval a)).comp
      (Polynomial.mapRingHom (MvPolynomial.C (σ := Fin (n * (N + 1))) (R := k))) = RingHom.id k[X] := by
    rw [Polynomial.mapRingHom_comp]
    have : (MvPolynomial.eval a).comp (MvPolynomial.C (σ := Fin (n * (N + 1))) (R := k)) = RingHom.id k := by
      ext c; simp
    rw [this, Polynomial.mapRingHom_id]
  have h2 : (Polynomial.mapRingHom (MvPolynomial.eval a)) ∘ subVar n N = specVar n N a := by
    funext i
    simp [subVar, specVar, Polynomial.map_sum]
  rw [h1, h2]
  rfl

theorem coeff_specVar (n N : ℕ) (a : Fin (n * (N + 1)) → k) (i : Fin n) (j : Fin (N + 1)) :
    (specVar n N a i).coeff j = a (finProdFinEquiv (i, j)) := by
  simp only [specVar, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [if_neg]
    exact fun h => hb (Fin.ext h.symm)
  · simp

theorem natDegree_subVar_le (n N : ℕ) (i : Fin n) : (subVar (k := k) n N i).natDegree ≤ N := by
  unfold subVar
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp j.isLt)

theorem natDegree_subPoly_le (n N c : ℕ) (F : MvPolynomial (Fin n) k[X])
    (hc : ∀ m, (F.coeff m).natDegree ≤ c) :
    (subPoly n N F).natDegree ≤ N * F.totalDegree + c := by
  unfold subPoly
  rw [MvPolynomial.eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  refine Polynomial.natDegree_mul_le.trans ?_
  have h1 : (Polynomial.mapRingHom (MvPolynomial.C (σ := Fin (n * (N + 1))) (R := k))
      (F.coeff m)).natDegree ≤ c := Polynomial.natDegree_map_le.trans (hc m)
  have hsum : ∑ i, m i ≤ F.totalDegree := by
    have := MvPolynomial.le_totalDegree hm
    rwa [Finsupp.sum_fintype _ _ (by simp)] at this
  have h2 : (∏ i, subVar (k := k) n N i ^ m i).natDegree ≤ N * F.totalDegree := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc ∑ i, (subVar (k := k) n N i ^ m i).natDegree ≤ ∑ i, m i * N :=
          Finset.sum_le_sum fun i _ =>
            Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (natDegree_subVar_le n N i))
      _ = N * ∑ i, m i := by rw [Finset.mul_sum]; simp [mul_comm]
      _ ≤ N * F.totalDegree := Nat.mul_le_mul_left _ hsum
  omega

theorem constantCoeff_coeff_subPoly (n N : ℕ) (F : MvPolynomial (Fin n) k[X])
    (hF : MvPolynomial.constantCoeff F = 0) (m : ℕ) :
    MvPolynomial.constantCoeff ((subPoly n N F).coeff m) = 0 := by
  have h := congrArg (fun p => Polynomial.coeff p m) (map_subPoly n N F 0)
  simp only [Polynomial.coeff_map] at h
  have h0 : specVar n N (0 : Fin (n * (N + 1)) → k) = 0 := by
    funext i; simp [specVar]
  rw [h0, MvPolynomial.eval_zero, MvPolynomial.eval_zero] at h
  rw [h]
  simp [hF]

/-- **Core of Tsen's theorem.** Over `k[t]`, `k` algebraically closed: a polynomial in `n` variables of total degree
`< n` without constant term has a nonzero zero in `k[t]ⁿ`. -/
theorem exists_zero_polynomial [IsAlgClosed k] {n : ℕ} (F : MvPolynomial (Fin n) k[X])
    (hdeg : F.totalDegree < n) (hF : MvPolynomial.constantCoeff F = 0) :
    ∃ x : Fin n → k[X], x ≠ 0 ∧ MvPolynomial.eval x F = 0 := by
  classical
  obtain ⟨c, hc⟩ : ∃ c, ∀ m, (F.coeff m).natDegree ≤ c :=
    ⟨F.support.sup fun m => (F.coeff m).natDegree, fun m => by
      by_cases hm : m ∈ F.support
      · exact Finset.le_sup (f := fun m => (F.coeff m).natDegree) hm
      · rw [MvPolynomial.notMem_support_iff.mp hm]; simp⟩
  have hcount : (c + 1) * F.totalDegree + c + 1 < n * (c + 1 + 1) := by
    have h1 : (F.totalDegree + 1) * (c + 2) ≤ n * (c + 2) := Nat.mul_le_mul_right _ hdeg
    nlinarith [h1]
  let P : Fin ((c + 1) * F.totalDegree + c + 1) → MvPolynomial (Fin (n * (c + 1 + 1))) k :=
    fun m => (subPoly n (c + 1) F).coeff m
  obtain ⟨a, ha, haP⟩ := exists_common_zero hcount P
    (fun m => constantCoeff_coeff_subPoly n (c + 1) F hF m)
  refine ⟨specVar n (c + 1) a, ?_, ?_⟩
  · intro h0
    apply ha
    funext p
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
    have := congrArg (fun q => Polynomial.coeff q j) (congrFun h0 i)
    simpa [coeff_specVar] using this
  · ext m
    rw [← map_subPoly, Polynomial.coeff_map]
    by_cases hm : m < (c + 1) * F.totalDegree + c + 1
    · simpa [P] using haP ⟨m, hm⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        ((natDegree_subPoly_le n (c + 1) c F hc).trans_lt (by omega))]
      simp

end Core

/-- Common denominators: a multivariate polynomial over a fraction field becomes integral after multiplying by one
nonzero element. -/
theorem exists_clear_denom {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {σ : Type*} (f : MvPolynomial σ K) :
    ∃ (b : A) (F : MvPolynomial σ A), b ≠ 0 ∧
      ∀ m, algebraMap A K (F.coeff m) = algebraMap A K b * f.coeff m := by
  classical
  obtain ⟨⟨b, hb⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A) (f.support.image fun m => f.coeff m)
  have hall : ∀ m, ∃ r : A, algebraMap A K r = b • f.coeff m := by
    intro m
    by_cases hm : m ∈ f.support
    · exact RingHom.mem_rangeS.mp (hint _ (Finset.mem_image_of_mem _ hm))
    · exact ⟨0, by rw [MvPolynomial.notMem_support_iff.mp hm, smul_zero, map_zero]⟩
  choose r hr using hall
  refine ⟨b, ∑ m' ∈ f.support, MvPolynomial.monomial m' (r m'), nonZeroDivisors.ne_zero hb, ?_⟩
  intro m
  have hc : (∑ m' ∈ f.support, MvPolynomial.monomial m' (r m')).coeff m =
      if m ∈ f.support then r m else 0 := by
    rw [MvPolynomial.coeff_sum]
    simp [MvPolynomial.coeff_monomial]
  rw [hc]
  split_ifs with hm
  · exact (hr m).trans (Algebra.smul_def _ _)
  · rw [MvPolynomial.notMem_support_iff.mp hm, mul_zero, map_zero]

/-- **Tsen's theorem for `k(t)`** (strong `C₁` form). -/
theorem isC1_ratFunc (k : Type*) [Field k] [IsAlgClosed k] : IsC1 (RatFunc k) := by
  intro n f hdeg hconst
  obtain ⟨b, F, hb, hF⟩ := exists_clear_denom (A := k[X]) f
  have hinj := IsFractionRing.injective k[X] (RatFunc k)
  have hsupp : F.support ⊆ f.support := by
    intro m hm
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h0
    apply hm
    apply hinj
    rw [hF, h0, mul_zero, map_zero]
  have hdegF : F.totalDegree < n := by
    refine lt_of_le_of_lt ?_ hdeg
    unfold MvPolynomial.totalDegree
    exact Finset.sup_mono hsupp
  have hconstF : MvPolynomial.constantCoeff F = 0 := by
    apply hinj
    have e1 : MvPolynomial.constantCoeff F = F.coeff 0 := congrFun MvPolynomial.constantCoeff_eq F
    have e2 : MvPolynomial.constantCoeff f = f.coeff 0 := congrFun MvPolynomial.constantCoeff_eq f
    rw [e1, hF, ← e2, hconst, mul_zero, map_zero]
  obtain ⟨x, hx0, hx⟩ := exists_zero_polynomial F hdegF hconstF
  refine ⟨fun i => algebraMap k[X] (RatFunc k) (x i), ?_, ?_⟩
  · intro h
    apply hx0
    funext i
    apply hinj
    simpa using congrFun h i
  · have hmap : MvPolynomial.map (algebraMap k[X] (RatFunc k)) F =
        MvPolynomial.C (algebraMap k[X] (RatFunc k) b) * f := by
      ext m
      rw [MvPolynomial.coeff_map, hF, MvPolynomial.coeff_C_mul]
    have h1 : MvPolynomial.eval (fun i => algebraMap k[X] (RatFunc k) (x i))
        (MvPolynomial.map (algebraMap k[X] (RatFunc k)) F) =
        algebraMap k[X] (RatFunc k) (MvPolynomial.eval x F) := by
      rw [MvPolynomial.eval_map]
      have := MvPolynomial.eval₂_comp_left (algebraMap k[X] (RatFunc k)) (RingHom.id _) x F
      rw [RingHom.comp_id] at this
      exact this.symm
    rw [hmap, hx, map_zero, map_mul, MvPolynomial.eval_C] at h1
    exact (mul_eq_zero.mp h1).resolve_left (fun h => hb (hinj (h.trans (map_zero _).symm)))

end RamanujanPetersson.Tsen


end

-- ===== S4.Def_RP_Tsen_Norm =====
section

set_option autoImplicit false

/-!
# S4-PD (1), T3: finite extensions of `C₁` fields are `C₁` (the norm form)

* `coeffMap g z`: apply a `K`-linear functional `g : L → K` to every coefficient of `z`; it commutes with evaluation at
  `K`-points (`eval_coeffMap`) and does not raise the total degree.
* `totalDegree_bind₁_le`, `totalDegree_det_le`: degree bounds for linear substitution and determinants.
* `exists_normForm`: for `L/K` with basis `b` (`e` elements) and `f ∈ L[x₀,…,x_{n-1}]` there is
  `P ∈ K[y_{(i,j)}]` with `totalDegree P ≤ e * totalDegree f` and `P(y) = N_{L/K}(f(∑ⱼ y_{(i,j)} bⱼ))`.
* `IsC1.of_finite`: `L/K` finite and `K` is `C₁` imply `L` is `C₁`.
-/

namespace RamanujanPetersson.Tsen

open MvPolynomial

section CoeffMap

variable {σ K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Apply a `K`-linear functional to every coefficient. -/
noncomputable def coeffMap (g : L →ₗ[K] K) (z : MvPolynomial σ L) : MvPolynomial σ K :=
  ∑ d ∈ z.support, monomial d (g (z.coeff d))

theorem totalDegree_coeffMap_le (g : L →ₗ[K] K) (z : MvPolynomial σ L) :
    (coeffMap g z).totalDegree ≤ z.totalDegree :=
  totalDegree_finsetSum_le fun _ hd => (totalDegree_monomial_le _ _).trans (le_totalDegree hd)

theorem eval_coeffMap (g : L →ₗ[K] K) (z : MvPolynomial σ L) (y : σ → K) :
    eval y (coeffMap g z) = g (eval (fun i => algebraMap K L (y i)) z) := by
  have hp : ∀ d : σ →₀ ℕ, ∏ i ∈ d.support, (algebraMap K L (y i)) ^ d i =
      algebraMap K L (∏ i ∈ d.support, y i ^ d i) := by
    intro d; rw [map_prod]; simp [map_pow]
  rw [coeffMap, map_sum, MvPolynomial.eval_eq (fun i => algebraMap K L (y i)) z, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.eval_monomial, hp d, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul,
    mul_comm]
  rfl

end CoeffMap

theorem totalDegree_bind₁_le {σ τ R : Type*} [CommRing R] (g : σ → MvPolynomial τ R) (f : MvPolynomial σ R)
    (hg : ∀ i, (g i).totalDegree ≤ 1) : (bind₁ g f).totalDegree ≤ f.totalDegree := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hd)
  refine Finset.sum_le_sum fun i _ => ?_
  refine (totalDegree_pow _ _).trans ?_
  calc d i * (g i).totalDegree ≤ d i * 1 := Nat.mul_le_mul_left _ (hg i)
    _ = d i := mul_one _

theorem totalDegree_det_le {σ R : Type*} [CommRing R] {e : ℕ} (M : Matrix (Fin e) (Fin e) (MvPolynomial σ R))
    (D : ℕ) (hM : ∀ i j, (M i j).totalDegree ≤ D) : M.det.totalDegree ≤ e * D := by
  rw [Matrix.det_apply']
  apply totalDegree_finsetSum_le
  intro τ _
  refine (totalDegree_mul _ _).trans ?_
  have h1 : ((Equiv.Perm.sign τ : ℤ) : MvPolynomial σ R).totalDegree = 0 := by
    rw [← map_intCast (C : R →+* MvPolynomial σ R), totalDegree_C]
  rw [h1, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i, (M (τ i) i).totalDegree ≤ ∑ _i : Fin e, D := Finset.sum_le_sum fun i _ => hM _ _
    _ = e * D := by simp

section NormForm

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

omit [FiniteDimensional K L] in
/-- **The norm form.** `P(y) = N_{L/K}(f(∑ⱼ y_{(i,j)} bⱼ))` is a polynomial of degree `≤ e · deg f` over `K`. -/
theorem exists_normForm {e : ℕ} (b : Module.Basis (Fin e) K L) {n : ℕ} (f : MvPolynomial (Fin n) L) :
    ∃ P : MvPolynomial (Fin (n * e)) K, P.totalDegree ≤ e * f.totalDegree ∧
      ∀ y : Fin (n * e) → K,
        eval y P = Algebra.norm K (eval (fun i => ∑ j, y (finProdFinEquiv (i, j)) • b j) f) := by
  classical
  let g : Fin n → MvPolynomial (Fin (n * e)) L :=
    fun i => ∑ j : Fin e, C (b j) * X (finProdFinEquiv (i, j))
  have hg : ∀ i, (g i).totalDegree ≤ 1 := by
    intro i
    refine totalDegree_finsetSum_le fun j _ => (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]
  let z := bind₁ g f
  have hz : ∀ y : Fin (n * e) → K, eval (fun p => algebraMap K L (y p)) z =
      eval (fun i => ∑ j, y (finProdFinEquiv (i, j)) • b j) f := by
    intro y
    refine (eval₂Hom_bind₁ (RingHom.id L) (fun p => algebraMap K L (y p)) g f).trans ?_
    show eval _ f = eval _ f
    refine congrArg (fun x : Fin n → L => eval x f) (funext fun i => ?_)
    show eval _ (g i) = _
    simp only [g, map_sum, map_mul, eval_C, eval_X]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_comm]
  let M : Matrix (Fin e) (Fin e) (MvPolynomial (Fin (n * e)) K) :=
    fun i j => coeffMap ((b.coord i).comp (LinearMap.mulRight K (b j))) z
  refine ⟨M.det, ?_, ?_⟩
  · refine (totalDegree_det_le M z.totalDegree fun i j => totalDegree_coeffMap_le _ _).trans ?_
    exact Nat.mul_le_mul_left _ (totalDegree_bind₁_le g f hg)
  · intro y
    rw [RingHom.map_det, Algebra.norm_eq_matrix_det b]
    congr 1
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]
    show eval y (coeffMap _ z) = _
    rw [eval_coeffMap, hz]
    rfl

/-- **Lang.** A finite extension of a `C₁` field is `C₁`. -/
theorem IsC1.of_finite (hK : IsC1 K) : IsC1 L := by
  classical
  intro n f hdeg hconst
  obtain ⟨e, b, hepos⟩ : ∃ e, ∃ _ : Module.Basis (Fin e) K L, 0 < e :=
    ⟨_, Module.finBasis K L, Module.finrank_pos⟩
  obtain ⟨P, hPdeg, hP⟩ := exists_normForm b f
  have hdegP : P.totalDegree < n * e :=
    lt_of_le_of_lt hPdeg (by rw [mul_comm n e]; exact Nat.mul_lt_mul_of_pos_left hdeg hepos)
  have hconstP : constantCoeff P = 0 := by
    rw [← MvPolynomial.eval_zero, hP]
    simp [MvPolynomial.eval_zero', hconst]
  obtain ⟨y, hy0, hy⟩ := hK (n * e) P hdegP hconstP
  rw [hP, Algebra.norm_eq_zero_iff] at hy
  refine ⟨fun i => ∑ j, y (finProdFinEquiv (i, j)) • b j, ?_, hy⟩
  intro hx
  apply hy0
  funext p
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
  exact Fintype.linearIndependent_iff.mp b.linearIndependent _ (congrFun hx i) j

end NormForm

end RamanujanPetersson.Tsen


end

-- ===== S4.Def_RP_Tsen =====
section

set_option autoImplicit false

/-!
# S4-PD (1): Tsen's theorem

* `IsC1.of_algebraic`: an algebraic extension of a `C₁` field is `C₁` (adjoin the coefficients, `IsC1.of_finite`).
* `tsen`: **Tsen's theorem.** Every algebraic extension of `k(t)`, `k` algebraically closed, is `C₁`
  (strong form `IsC1`: polynomials in `n` variables of total degree `< n` without constant term have a nonzero zero).
* `IsC1.norm_surjective`: over a `C₁` field the norm of every finite extension is surjective.
* `tsen_norm_surjective`: the norm of a finite extension of an algebraic extension of `k(t)` is surjective.
-/

namespace RamanujanPetersson.Tsen

open MvPolynomial

/-- An algebraic extension of a `C₁` field is `C₁`. -/
theorem IsC1.of_algebraic {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (hK : IsC1 K) : IsC1 L := by
  classical
  intro n f hdeg hconst
  let F := IntermediateField.adjoin K (f.coeffs : Set L)
  have : Finite (f.coeffs : Set L) := (Finset.finite_toSet _).to_subtype
  have : FiniteDimensional K F := IntermediateField.finiteDimensional_adjoin
    fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hF : IsC1 F := IsC1.of_finite hK
  have hinj : Function.Injective (algebraMap F L) := (algebraMap F L).injective
  obtain ⟨f', hf'⟩ : f ∈ Set.range (MvPolynomial.map (algebraMap F L)) :=
    MvPolynomial.mem_range_map_iff_coeffs_subset.mpr fun c hc =>
      ⟨⟨c, IntermediateField.subset_adjoin K _ hc⟩, rfl⟩
  have hdeg' : f'.totalDegree < n := by
    have h1 : (MvPolynomial.map (algebraMap F L) f').totalDegree = f'.totalDegree := by
      unfold MvPolynomial.totalDegree
      rw [MvPolynomial.support_map_of_injective _ hinj]
    rw [← h1, hf']
    exact hdeg
  have hconst' : constantCoeff f' = 0 := by
    apply hinj
    rw [← MvPolynomial.constantCoeff_map, hf', hconst, map_zero]
  obtain ⟨x, hx0, hx⟩ := hF n f' hdeg' hconst'
  refine ⟨fun i => algebraMap F L (x i), ?_, ?_⟩
  · intro h
    apply hx0
    funext i
    exact hinj ((congrFun h i).trans (map_zero _).symm)
  · rw [← hf', MvPolynomial.eval_map]
    have h2 := MvPolynomial.eval₂_comp_left (algebraMap F L) (RingHom.id _) x f'
    rw [RingHom.comp_id] at h2
    refine h2.symm.trans ?_
    rw [show MvPolynomial.eval₂ (RingHom.id F) x f' = eval x f' from rfl, hx, map_zero]

/-- Over a `C₁` field, the norm of a finite extension is surjective. -/
theorem IsC1.norm_surjective {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hK : IsC1 K) : Function.Surjective (Algebra.norm K : L → K) := by
  classical
  intro a
  by_cases ha : a = 0
  · exact ⟨0, by rw [ha, Algebra.norm_zero]⟩
  obtain ⟨e, b, hepos⟩ : ∃ e, ∃ _ : Module.Basis (Fin e) K L, 0 < e :=
    ⟨_, Module.finBasis K L, Module.finrank_pos⟩
  obtain ⟨P, hPdeg, hP⟩ := exists_normForm b (X 0 : MvPolynomial (Fin 1) L)
  rw [totalDegree_X, mul_one] at hPdeg
  let Q : MvPolynomial (Fin (1 * e + 1)) K :=
    rename Fin.castSucc P - C a * X (Fin.last (1 * e)) ^ e
  have hQdeg : Q.totalDegree < 1 * e + 1 := by
    show (rename Fin.castSucc P - C a * X (Fin.last (1 * e)) ^ e).totalDegree < 1 * e + 1
    have h1 : (rename Fin.castSucc P).totalDegree ≤ e := (totalDegree_rename_le _ _).trans hPdeg
    have h2 : (C a * X (Fin.last (1 * e)) ^ e : MvPolynomial (Fin (1 * e + 1)) K).totalDegree ≤ e := by
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      refine (totalDegree_pow _ _).trans ?_
      rw [totalDegree_X, mul_one]
    have := (totalDegree_sub _ _).trans (max_le h1 h2)
    omega
  have hP0 : constantCoeff P = 0 := by
    rw [← MvPolynomial.eval_zero, hP]
    simp [Algebra.norm_zero]
  have hQconst : constantCoeff Q = 0 := by
    simp [Q, MvPolynomial.constantCoeff_rename, hP0, zero_pow hepos.ne']
  obtain ⟨w, hw0, hw⟩ := hK _ Q hQdeg hQconst
  set x : L := ∑ j, w (Fin.castSucc (finProdFinEquiv (0, j))) • b j with hx
  have hnorm : Algebra.norm K x = a * w (Fin.last _) ^ e := by
    have h3 : eval w Q = Algebra.norm K x - a * w (Fin.last _) ^ e := by
      simp only [Q, map_sub, map_mul, map_pow, eval_C, eval_X, MvPolynomial.eval_rename, hP]
      try rfl
    rw [h3] at hw
    exact sub_eq_zero.mp hw
  have ht : w (Fin.last _) ≠ 0 := by
    intro ht
    rw [ht, zero_pow hepos.ne', mul_zero, Algebra.norm_eq_zero_iff] at hnorm
    apply hw0
    funext p
    induction p using Fin.lastCases with
    | last => exact ht
    | cast q =>
      obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective q
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact Fintype.linearIndependent_iff.mp b.linearIndependent _ hnorm j
  refine ⟨x * algebraMap K L (w (Fin.last _))⁻¹, ?_⟩
  rw [map_mul, Algebra.norm_algebraMap, hnorm, Module.finrank_eq_card_basis b, Fintype.card_fin, inv_pow,
    mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht), mul_one]

end RamanujanPetersson.Tsen


end

-- ===== S4.Def_RP_CdOne_Br =====
section

/-!
# S4-PD (3a), part 2: `Br(L/K) = 0` for a Galois `p`-extension of a C1 field

`br_eq_zero`: if `K` is C1 and `L/K` is finite Galois with `Gal(L/K)` a `p`-group, every multiplicative 2-cocycle
`Gal(L/K)² → Lˣ` is a coboundary. Induction on `[L : K]`: a central subgroup `N` of order `p`, the cyclic case
for `L / L^N` (norm surjectivity from C1), Hilbert 90 on `N`, inflation-restriction, and descent to `Gal(L^N/K)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe v

namespace RamanujanPetersson.CdOne

open groupCohomology IntermediateField RamanujanPetersson.Tsen

section Mul

variable {G M : Type*} [Monoid G] [CommGroup M] [MulDistribMulAction G M]

/-- `Additive M` with the action induced by the multiplicative action of `G` on `M`. -/
abbrev addAct : DistribMulAction G (Additive M) where
  smul g a := Additive.ofMul (g • a.toMul)
  one_smul a := by show Additive.ofMul ((1 : G) • a.toMul) = a; rw [one_smul]; rfl
  mul_smul g h a := by
    show Additive.ofMul ((g * h) • a.toMul) = Additive.ofMul (g • (h • a.toMul)); rw [mul_smul]
  smul_zero g := by show Additive.ofMul (g • (1 : M)) = Additive.ofMul 1; rw [smul_one]
  smul_add g a b := by
    show Additive.ofMul (g • (a.toMul * b.toMul)) = Additive.ofMul (g • a.toMul * g • b.toMul)
    rw [smul_mul']

attribute [local instance] addAct

theorem isCocycle₂_ofMul {f : G × G → M} (hf : IsMulCocycle₂ f) :
    IsCocycle₂ (fun q => Additive.ofMul (f q)) := fun g h j => hf g h j

theorem isMulCoboundary₂_of_ofMul {f : G × G → M} (h : IsCoboundary₂ (fun q => Additive.ofMul (f q))) :
    IsMulCoboundary₂ f := by
  obtain ⟨x, hx⟩ := h
  exact ⟨fun g => (x g).toMul, fun g h => hx g h⟩

end Mul

attribute [local instance] addAct

section Galois

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- `Gal(L / L^N) ≃* N`. -/
noncomputable def galFixedEquiv (N : Subgroup Gal(L/K)) : Gal(L/fixedField N) ≃* N :=
  (fixingSubgroupEquiv (fixedField N)).symm.trans (MulEquiv.subgroupCongr (fixingSubgroup_fixedField N))

theorem galFixedEquiv_apply (N : Subgroup Gal(L/K)) (τ : Gal(L/fixedField N)) (y : L) :
    ((galFixedEquiv N τ : N) : Gal(L/K)) y = τ y := rfl

/-- Hilbert 90 for a subgroup `N` acting on `Lˣ` (through `Gal(L / L^N)`). -/
theorem h1_subgroup (N : Subgroup Gal(L/K)) (φ : N → Additive Lˣ) (hφ : IsCocycle₁ φ) : IsCoboundary₁ φ := by
  set e := galFixedEquiv N
  have hact : ∀ (τ : Gal(L/fixedField N)) (u : Lˣ), ((e τ : N) : Gal(L/K)) • u = τ • u :=
    fun τ u => Units.ext rfl
  have hφ' : IsMulCocycle₁ (fun τ : Gal(L/fixedField N) => (φ (e τ)).toMul) := by
    intro τ τ'
    show (φ (e (τ * τ'))).toMul = τ • (φ (e τ')).toMul * (φ (e τ)).toMul
    rw [map_mul, hφ (e τ) (e τ'), ← hact]
    rfl
  obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units _ hφ'
  refine ⟨Additive.ofMul β, fun n => ?_⟩
  obtain ⟨τ, rfl⟩ := e.surjective n
  have := hβ τ
  rw [← hact] at this
  exact congrArg Additive.ofMul this

/-- A `z`-fixed element is a "norm" `∏_{t < ord z} z^t(y)` when the norm to `L^⟨z⟩` is surjective. -/
theorem exists_prod_pow_eq [IsGalois K L] (z : Gal(L/K))
    (hsurj : Function.Surjective (Algebra.norm (fixedField (Subgroup.zpowers z)) : L → _)) (x : L)
    (hx : z x = x) : ∃ y : L, ∏ t ∈ Finset.range (orderOf z), (z ^ t) y = x := by
  classical
  set N := Subgroup.zpowers z
  have hxN : x ∈ fixedField N := by
    rw [mem_fixedField_iff]
    intro g hg
    have hst : N ≤ MulAction.stabilizer Gal(L/K) x :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hx)
    exact MulAction.mem_stabilizer_iff.mp (hst hg)
  obtain ⟨y, hy⟩ := hsurj ⟨x, hxN⟩
  refine ⟨y, ?_⟩
  have h1 := Algebra.norm_eq_prod_automorphisms (fixedField N) y
  rw [hy] at h1
  change x = ∏ σ : Gal(L/fixedField N), σ y at h1
  rw [h1]
  have hfin : IsOfFinOrder z := isOfFinOrder_of_finite z
  calc ∏ t ∈ Finset.range (orderOf z), (z ^ t) y = ∏ i : Fin (orderOf z), (z ^ (i : ℕ)) y :=
        (Fin.prod_univ_eq_prod_range (fun t => (z ^ t) y) _).symm
    _ = ∏ n : N, (n : Gal(L/K)) y :=
        Fintype.prod_equiv (finEquivZPowers hfin) _ _ (fun i => by rw [finEquivZPowers_apply])
    _ = ∏ σ : Gal(L/fixedField N), σ y := by
        convert (Fintype.prod_equiv (galFixedEquiv N) (fun τ : Gal(L/fixedField N) => τ y) (fun n : N => (n : Gal(L/K)) y)
          (fun τ => rfl)).symm

/-- The cyclic step: the restriction of a cocycle to `⟨z⟩` is a coboundary. -/
theorem isCoboundary₂_zpowers [IsGalois K L] (z : Gal(L/K))
    (hsurj : Function.Surjective (Algebra.norm (fixedField (Subgroup.zpowers z)) : L → _))
    {f : Gal(L/K) × Gal(L/K) → Lˣ} (hf : IsMulCocycle₂ f) :
    IsCoboundary₂ (fun q : Subgroup.zpowers z × Subgroup.zpowers z =>
      Additive.ofMul (f ((q.1 : Gal(L/K)), (q.2 : Gal(L/K))))) := by
  set N := Subgroup.zpowers z
  set σ : N := ⟨z, Subgroup.mem_zpowers z⟩
  have hfin : IsOfFinOrder z := isOfFinOrder_of_finite z
  have hord : orderOf σ = orderOf z := Subgroup.orderOf_mk z _
  have hσ : ∀ g : N, ∃ i : ℕ, σ ^ i = g := by
    rintro ⟨g, hg⟩
    obtain ⟨k, hk⟩ := Submonoid.mem_powers_iff _ _ |>.mp (hfin.mem_powers_iff_mem_zpowers.mpr hg)
    exact ⟨k, Subtype.ext (by simpa [σ] using hk)⟩
  have hfc : IsCocycle₂ (fun q : N × N => Additive.ofMul (f ((q.1 : Gal(L/K)), (q.2 : Gal(L/K))))) :=
    fun g h j => hf g h j
  refine isCoboundary₂_of_cyclic hσ hfc (fun a ha => ?_)
  have hza : z ((a.toMul : Lˣ) : L) = ((a.toMul : Lˣ) : L) :=
    congrArg (fun u : Additive Lˣ => ((u.toMul : Lˣ) : L)) ha
  obtain ⟨y, hy⟩ := exists_prod_pow_eq z hsurj _ hza
  have hy0 : y ≠ 0 := by
    rintro rfl
    refine (a.toMul).ne_zero ?_
    rw [← hy]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hfin.orderOf_pos) (map_zero _)
  refine ⟨Additive.ofMul (Units.mk0 y hy0), ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  rw [toMul_sum, Units.coe_prod, hord, ← hy]
  refine Finset.prod_congr rfl (fun t _ => ?_)
  rfl

set_option synthInstance.maxHeartbeats 400000 in
/-- Descent: a cocycle inflated from `Gal(L/K) ⧸ N` with values in `(Lˣ)^N` is a coboundary when
`Br(L^N / K) = 0`. -/
theorem isCoboundary₂_descend [IsGalois K L] (N : Subgroup Gal(L/K)) [N.Normal]
    {F : Gal(L/K) × Gal(L/K) → Additive Lˣ} (hF : IsCocycle₂ F)
    (hinv : ∀ g h : Gal(L/K), ∀ n ∈ N, F (g * n, h) = F (g, h) ∧ F (g, h * n) = F (g, h) ∧
      n • F (g, h) = F (g, h))
    (hE : ∀ fb : Gal(fixedField N/K) × Gal(fixedField N/K) → (fixedField N)ˣ, IsMulCocycle₂ fb →
      IsMulCoboundary₂ fb) :
    IsCoboundary₂ F := by
  set E := fixedField N
  set res := AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E
  have hres : Function.Surjective res := AlgEquiv.restrictNormalHom_surjective L
  set lift := Function.surjInv hres
  have hlift : ∀ σ, res (lift σ) = σ := Function.surjInv_eq hres
  have hker : ∀ g g', res g = res g' → g⁻¹ * g' ∈ N := by
    intro g g' h
    have : g⁻¹ * g' ∈ res.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    rw [IntermediateField.restrictNormalHom_ker, fixingSubgroup_fixedField] at this
    exact this
  have hFres : ∀ g g' h h', res g = res g' → res h = res h' → F (g, h) = F (g', h') := by
    intro g g' h h' hg hh
    rw [show g' = g * (g⁻¹ * g') by group, show h' = h * (h⁻¹ * h') by group,
      (hinv g _ _ (hker g g' hg)).1, (hinv g h _ (hker h h' hh)).2.1]
  have hval : ∀ g h, (((F (g, h)).toMul : Lˣ) : L) ∈ E := by
    intro g h
    rw [mem_fixedField_iff]
    intro n hn
    exact congrArg (fun u : Additive Lˣ => ((u.toMul : Lˣ) : L)) (hinv g h n hn).2.2
  let fb : Gal(E/K) × Gal(E/K) → Eˣ := fun q =>
    Units.mk0 ⟨(((F (lift q.1, lift q.2)).toMul : Lˣ) : L), hval _ _⟩
      (fun h0 => (F (lift q.1, lift q.2)).toMul.ne_zero (congrArg Subtype.val h0))
  have hact : ∀ (σ : Gal(E/K)) (e : E), ((σ e : E) : L) = (lift σ) (e : L) := by
    intro σ e
    conv_lhs => rw [← hlift σ]
    exact AlgEquiv.restrictNormalHom_apply E (lift σ) e
  have hfb : IsMulCocycle₂ fb := by
    intro σ τ ρ
    have e1 : F (lift (σ * τ), lift ρ) = F (lift σ * lift τ, lift ρ) :=
      hFres _ _ _ _ (by rw [map_mul, hlift, hlift, hlift]) rfl
    have e2 : F (lift σ, lift (τ * ρ)) = F (lift σ, lift τ * lift ρ) :=
      hFres _ _ _ _ rfl (by rw [map_mul, hlift, hlift, hlift])
    have key := congrArg (fun u : Additive Lˣ => ((u.toMul : Lˣ) : L)) (hF (lift σ) (lift τ) (lift ρ))
    apply Units.ext; apply Subtype.ext
    show (((F (lift (σ * τ), lift ρ)).toMul : Lˣ) : L) * (((F (lift σ, lift τ)).toMul : Lˣ) : L) =
      ((σ ((fb (τ, ρ) : Eˣ) : E) : E) : L) * (((F (lift σ, lift (τ * ρ))).toMul : Lˣ) : L)
    rw [hact, e1, e2]
    exact key
  obtain ⟨x, hx⟩ := hE fb hfb
  set ιu : Eˣ →* Lˣ := Units.map (algebraMap E L).toMonoidHom
  have hιu : ∀ (g : Gal(L/K)) (u : Eˣ), ιu ((res g : Gal(E/K)) • u : Eˣ) = g • ιu u := fun g u =>
    Units.ext (AlgEquiv.restrictNormalHom_apply E g (u : E))
  have hιf : ∀ σ τ, ιu (fb (σ, τ)) = (F (lift σ, lift τ)).toMul := fun _ _ => Units.ext rfl
  refine ⟨fun g => Additive.ofMul (ιu (x (res g))), fun g h => ?_⟩
  have := congrArg ιu (hx (res g) (res h))
  rw [map_mul, map_div, hιu, hιf, ← map_mul res g h,
    hFres (lift (res g)) g (lift (res h)) h (hlift _) (hlift _)] at this
  exact congrArg Additive.ofMul this

end Galois

/-- **`Br(L/K) = 0`** for a finite Galois `p`-extension `L` of a C1 field `K`: every multiplicative
2-cocycle `Gal(L/K)² → Lˣ` is a coboundary. -/
theorem br_eq_zero_aux {K : Type*} [Field K] (hK : IsC1 K) (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    ∀ (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
      Module.finrank K L ≤ n → IsPGroup p Gal(L/K) →
      ∀ f : Gal(L/K) × Gal(L/K) → Lˣ, IsMulCocycle₂ f → IsMulCoboundary₂ f := by
  induction n with
  | zero =>
    intro L _ _ _ _ hn
    have := Module.finrank_pos (R := K) (M := L)
    omega
  | succ n ih =>
    intro L _ _ _ _ hn hG f hf
    by_cases htriv : Subsingleton Gal(L/K)
    · refine ⟨fun _ => f (1, 1), fun g h => ?_⟩
      rw [Subsingleton.elim g 1, Subsingleton.elim h 1]
      simp
    rw [not_subsingleton_iff_nontrivial] at htriv
    -- a central element of order `p`
    have := hG.center_nontrivial
    have hc : p ∣ Nat.card (Subgroup.center Gal(L/K)) :=
      ((hG.to_subgroup _).card_eq_or_dvd).resolve_left Finite.one_lt_card.ne'
    obtain ⟨z0, hz0⟩ := exists_prime_orderOf_dvd_card' p hc
    set z : Gal(L/K) := (z0 : Gal(L/K))
    have hzc : z ∈ Subgroup.center Gal(L/K) := z0.2
    have hzp : orderOf z = p := by rw [Subgroup.orderOf_coe]; exact hz0
    set N := Subgroup.zpowers z
    have hNn : N.Normal := ⟨fun m hm g => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
      have hcomm : Commute g z := Subgroup.mem_center_iff.mp hzc g
      rw [(hcomm.zpow_right k).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers z k⟩
    set E := fixedField N
    have hE1 : IsC1 E := IsC1.of_finite hK
    have hsurj : Function.Surjective (Algebra.norm E : L → E) := IsC1.norm_surjective hE1
    -- degrees
    have hdeg : Module.finrank K E < Module.finrank K L := by
      have h1 := Module.finrank_mul_finrank K E L
      have h2 : Module.finrank E L = p := by
        rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, hzp]
      have h3 := Module.finrank_pos (R := K) (M := E)
      have h4 := hp.out.two_le
      rw [h2] at h1
      nlinarith
    have hGE : IsPGroup p Gal(E/K) :=
      hG.of_surjective (AlgEquiv.restrictNormalHom E) (AlgEquiv.restrictNormalHom_surjective L)
    -- the three steps
    have hNf := isCoboundary₂_zpowers z hsurj hf
    obtain ⟨b, hbc, hbinv⟩ := exists_inflated N (isCocycle₂_ofMul hf) (h1_subgroup N) hNf
    apply isMulCoboundary₂_of_ofMul
    apply isCoboundary₂_of_sub b
    exact isCoboundary₂_descend N hbc hbinv (fun fb hfb => ih E (by omega) hGE fb hfb)

theorem br_eq_zero {K : Type*} [Field K] (hK : IsC1 K) (p : ℕ) [Fact p.Prime] (L : Type v) [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (hG : IsPGroup p Gal(L/K))
    (f : Gal(L/K) × Gal(L/K) → Lˣ) (hf : IsMulCocycle₂ f) : IsMulCoboundary₂ f :=
  br_eq_zero_aux hK p _ L le_rfl hG f hf

end RamanujanPetersson.CdOne


end

-- ===== S4.Def_RP_CdOne_Lc =====
section

/-!
# S4-PD (3), group layer part 1: locally constant cochains and the index lemma

For a compact topological group `P` acting on `A` (locally constant action, `LcAct`):
* `lc_dite`, `lc_sum`, `lc_d₁`: closure properties of locally constant cochains;
* `exists_open_inv`: a locally constant function on `P × P` is invariant under right multiplication by an open
  subgroup in each variable (finite level); `exists_openNormal_le`, `actKer`, `isOpen_actKer`;
* `index_lemma`: for an open subgroup `H` whose index is invertible on `A`, a locally constant 2-cocycle whose
  restriction to `H × H` is the coboundary of a locally constant cochain is a locally constant coboundary on `P`
  (normalise to `f(g, n) = 0` for `n ∈ H`, then average over the left cosets `P ⧸ H`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CdOne

open groupCohomology Filter Topology

section LcBasic

variable {X : Type*} [TopologicalSpace X]

/-- Extension by zero from a clopen set is locally constant. -/
theorem lc_dite {S : Set X} [DecidablePred (· ∈ S)] (hS : IsClopen S) {Z : Type*} [Zero Z] (u : S → Z)
    (hu : IsLocallyConstant u) :
    IsLocallyConstant (fun x => if h : x ∈ S then u ⟨x, h⟩ else 0) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ S
  · have h1 : ∀ᶠ y in 𝓝 x, y ∈ S := hS.isOpen.mem_nhds hx
    have h2 : ∀ᶠ (y' : S) in 𝓝 ⟨x, hx⟩, ∀ h : y'.1 ∈ S, u ⟨y'.1, h⟩ = u ⟨x, hx⟩ := by
      filter_upwards [(IsLocallyConstant.iff_eventually_eq u).1 hu ⟨x, hx⟩] with y' hy' h
      exact hy'
    have h3 : ∀ᶠ y in 𝓝 x, ∀ h : y ∈ S, u ⟨y, h⟩ = u ⟨x, hx⟩ := by
      rw [← (hS.isOpen.isOpenEmbedding_subtypeVal).map_nhds_eq ⟨x, hx⟩]
      exact Filter.eventually_map.2 h2
    filter_upwards [h1, h3] with y hy hq
    rw [dif_pos hy, dif_pos hx]
    exact hq hy
  · have h1 : ∀ᶠ y in 𝓝 x, y ∉ S := hS.isClosed.isOpen_compl.mem_nhds hx
    filter_upwards [h1] with y hy
    rw [dif_neg hy, dif_neg hx]

/-- Finite sums of locally constant functions are locally constant. -/
theorem lc_sum {ι : Type*} [Fintype ι] {B : Type*} [AddCommMonoid B] (u : ι → X → B)
    (hu : ∀ i, IsLocallyConstant (u i)) : IsLocallyConstant (fun x => ∑ i, u i x) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have : ∀ᶠ y in 𝓝 x, ∀ i, u i y = u i x :=
    Filter.eventually_all.2 (fun i => (IsLocallyConstant.iff_eventually_eq _).1 (hu i) x)
  filter_upwards [this] with y hy
  exact Finset.sum_congr rfl (fun i _ => hy i)

end LcBasic

variable {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  {A : Type*} [AddCommGroup A] [DistribMulAction P A]

/-- `P` acts locally constantly on `A` (a continuous action on a discrete module). -/
def LcAct (P A : Type*) [Group P] [TopologicalSpace P] [AddCommGroup A] [DistribMulAction P A] : Prop :=
  ∀ a : A, IsLocallyConstant fun g : P => g • a

/-- `f` is the coboundary of a locally constant 1-cochain. -/
def IsLcCob (f : P × P → A) : Prop :=
  ∃ b : P → A, IsLocallyConstant b ∧ ∀ g h : P, f (g, h) = d₁ b (g, h)

theorem smul_zsmul' (g : P) (x : ℤ) (a : A) : g • (x • a) = x • (g • a) :=
  map_zsmul (DistribSMul.toAddMonoidHom A g) x a

/-! ## Coset representatives for a (not necessarily normal) subgroup -/

/-! ## The index lemma -/

end RamanujanPetersson.CdOne


end

-- ===== S4.Def_RP_EtCompact_GlobQ =====
section

/-!
# S4-EtCompact, part 54: the global Kummer section at a closed point (F7c of plan v5)

`A` a domain, `g = gen A`, `Ω = κ(η)^sep`, `ι : Ns ⟶ I`, `p : I ⟶ Q` on `Spec κ(η)` with `ι ≫ p = 0`, exact on
stalks, `I` injective, `Gal` trivial on `Ns_x̄`, `d • Ns_x̄ = 0`, `d` a unit of `A`, `ζ ∈ Ω` a primitive `d`-th root
fixed by `Gal`. For `π ≠ 0` in `A` and `r ∈ Ns_x̄`:

* `ϖ ^ d = π`, the character `σ ↦ (dlog(σϖ/ϖ)).val • r` (additive, open kernel), its twist lift `m ∈ I_x̄`;
* `alpha y₀ : Λ_Y ⟶ Q` (stalk `1 ↦ y₀` for a fixed `y₀`), `aMap y₀ := uC g ≫ g_* alpha : Λ_{Spec A} ⟶ g_* Q`;
* **`exists_globQ`**: a global `a : Λ ⟶ g_* Q` whose germs are all `p m`, and `a ≫ c` vanishes near every point of
  `D(π)` for every `c` killing `g_* p` (local triviality over `A[1/π]` with the unit `π`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.GlobQ

open RamanujanPetersson.EtSheaves RamanujanPetersson.Kummer

theorem val_add_nsmul {M : Type*} [AddCommGroup M] {d : ℕ} [NeZero d] {r : M} (hr : d • r = 0) (a b : ZMod d) :
    (a + b).val • r = a.val • r + b.val • r := by
  rw [ZMod.val_add, ← nsmul_eq_mod_nsmul _ hr, add_nsmul]

section Char

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {d : ℕ} [NeZero d] {ζ : Ω} (hζ : IsPrimitiveRoot ζ d)
  (hζG : ∀ σ : Ω ≃ₐ[K] Ω, σ ζ = ζ) {ϖ : Ω} (hϖ0 : ϖ ≠ 0) (hϖ : ∀ σ : Ω ≃ₐ[K] Ω, σ (ϖ ^ d) = ϖ ^ d)
include hζG hϖ0 hϖ

end Char

variable (A : Type) [CommRing A] [IsDomain A]

section Alpha

variable {Λ : Type} [CommRing Λ] {Q : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))}

end Alpha

section Main

variable {A} {Λ : Type} [CommRing Λ]
  {Ns I Q : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))} (ι : Ns ⟶ I) (p : I ⟶ Q)

end Main

end RamanujanPetersson.EtCompact.GlobQ

end

end

-- ===== S4.Def_RP_EtCompact_PtCd =====
section

/-!
# S4-EtCompact, part 38: `H^(n+2)` of a point vanishes when `cd ≤ 1` (CC2c)

`X ≅ Spec κ(x0)` (`IsIso (X.fromSpecResidueField x0)`), `G = Gal x0`.

* `PtH2 x0 F`: every locally constant 2-cocycle of `G` in `F_x̄` is the coboundary of a locally constant cochain;
* `coboundary_of_coker`: if `PtH2 x0 F`, every locally constant 1-cocycle in `(I/F)_x̄` (`F ↪ I` injective) is a
  coboundary (lift it to `I_x̄`, correct the lift by a cochain in `F_x̄`, use `coboundary_of_injective`);
* `h1_coker_eq_zero`: then `H¹(X, I/F) = 0` (an extension of `Λ_X` by `I/F` splits on stalks, hence as sheaves);
* **`pt_H_eq_zero`**: if `PtH2 x0 F` for all `F`, then `H^(n+2)(X, F) = 0` (dimension shifting);
* **`pt_H_eq_zero_of_hypL`**: the same when `Gal x0` satisfies `HypL ℓ` and `ℓ^k = 0` in `Λ` (`h2_lcCob`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Topology

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.CdOne

universe u

variable {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)] {Λ : Type u} [CommRing Λ]

/-- Cocycle-level `H²(Gal x0, F_x̄) = 0`. -/
def PtH2 (F : EtSh Λ X) : Prop :=
  ∀ f : Gal x0 × Gal x0 → stalk Λ F x0, IsLocallyConstant f →
    (∀ g h j : Gal x0, f (g * h, j) + f (g, h) = galRep Λ F x0 g (f (h, j)) + f (g, h * j)) →
    ∃ a : Gal x0 → stalk Λ F x0, IsLocallyConstant a ∧
      ∀ g h : Gal x0, f (g, h) = galRep Λ F x0 g (a h) - a (g * h) + a g

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_GenPt =====
section

/-!
# S4-EtCompact, part 39: `H^(n+2)` of `C₁` points and of the generic point of `A¹` (CC2d)

* `isC1_of_ringEquiv`: `C₁` transfers along ring isomorphisms;
* **`pt_H_eq_zero_of_C1`**: on `X ≅ Spec κ` with `κ` a `C₁` field containing a primitive `ℓ`-th root of unity
  (`ℓ ≠ char κ`) and `ℓ^m = 0` in `Λ`: `H^(n+2)(X, F) = 0` (`hypL_gal` + `pt_H_eq_zero_of_hypL`);
* `H_ptOf_eq_zero_of_C1`: the same on `Spec κ(y)` for a point `y` with `C₁` residue field;
* `isC1_genField_polynomial`: `κ(η)` of `A¹_k = Spec k[X]` is `C₁` (Tsen, `κ(η) ≅ k(X)`), and
  **`H_genPt_eq_zero`**: `H^(n+2)(Spec κ(η), F) = 0` for `k` algebraically closed, `ℓ ≠ char k`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Polynomial

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.CdOne RamanujanPetersson.Tsen

universe u

/-- `C₁` transfers along a ring isomorphism. -/
theorem isC1_of_ringEquiv {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (hK : IsC1 K) : IsC1 L := by
  let _ : Algebra K L := e.toRingHom.toAlgebra
  have : Algebra.IsAlgebraic K L := ⟨fun x => by
    have h : algebraMap K L (e.symm x) = x := e.apply_symm_apply x
    exact h ▸ isAlgebraic_algebraMap _⟩
  exact hK.of_algebraic

section Point

variable {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)] {Λ : Type u} [CommRing Λ]

end Point

section Generic

variable (k : Type) [Field k] [IsAlgClosed k]

/-- `κ(η)` of `A¹_k` is `C₁` (Tsen). -/
theorem isC1_genField_polynomial : IsC1 (GenBr.genField k[X]) :=
  isC1_of_ringEquiv (GenBr.fracIso k[X] (RatFunc k)) (isC1_ratFunc k)

/-- A primitive `ℓ`-th root of unity in an algebraically closed field with `ℓ ≠ 0`. -/
theorem exists_isPrimitiveRoot_of_ne {l : ℕ} [NeZero l] (hl : (l : k) ≠ 0) : ∃ ζ : k, IsPrimitiveRoot ζ l := by
  have : NeZero (l : k) := ⟨hl⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (cyclotomic l k) (degree_cyclotomic_pos l k (NeZero.pos l)).ne'
  exact ⟨ζ, (isRoot_cyclotomic_iff).1 hζ⟩

/-- The constants `k → κ(η)` of `A¹_k`. -/
def genConst : k →+* GenBr.genField k[X] :=
  (GenBr.fracIso k[X] (RatFunc k)).toRingHom.comp (algebraMap k (RatFunc k))

end Generic

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_GmKc =====
section

/-!
# S4-EtCompact: `H^1(G_m, Λ) ≃ Λ` (O8c, files M4c + M4e)

`R = k[X]_X`, `K = k(X)`, `E = K_U = maxUnram R K`, `Γ = π₁(G_m)`, `N = lⁿ` invertible in `k`, `k` algebraically
closed, `γ ^ N = X`.

* `LX.exists_kchar_eq_one`: some `σ₁` has `kchar γ σ₁ = 1` (else `γ ^ l^(n-1) ∈ K` and `X` is an `l`-th power).
* `LX.hom_eq_kchar_smul`: every locally constant homomorphism `c : Γ → V` (`N • V = 0`) is
  `c σ = (kchar γ σ).val • c σ₁`.
* `LX.h1LinEquiv`: `H¹_cont(Γ, M) ≃ M` (trivial action, `N • M = 0`), evaluation at `σ₁`.
* **`Gm.nonempty_h1Equiv`**: `H^1(G_m, Λ) ≃+ Λ` for `lⁿ • Λ = 0`.
-/

set_option autoImplicit false

open Polynomial AlgebraicGeometry

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtSheaves.GenBr Kummer EtPi1

section Gen

theorem mod_nsmul' {N : ℕ} {V : Type} [AddCommGroup V] {v : V} (hv : N • v = 0) (x : ℕ) :
    (x % N) • v = x • v := by
  conv_rhs => rw [← Nat.mod_add_div x N]
  rw [add_nsmul, mul_nsmul, hv, nsmul_zero, add_zero]

theorem val_add_nsmul {N : ℕ} [NeZero N] {V : Type} [AddCommGroup V] {v : V} (hv : N • v = 0) (a b : ZMod N) :
    (a + b).val • v = a.val • v + b.val • v := by
  rw [ZMod.val_add, mod_nsmul' hv, add_nsmul]

theorem val_one_nsmul {N : ℕ} {V : Type} [AddCommGroup V] {v : V} (hv : N • v = 0) :
    (1 : ZMod N).val • v = v := by
  rw [ZMod.val_one_eq_one_mod, mod_nsmul' hv, one_nsmul]

variable {K E : Type} [Field K] [Field E] [Algebra K E] {Γ : Subgroup (E ≃ₐ[K] E)}

end Gen

section Kc

variable {k : Type} [Field k] [IsAlgClosed k]

variable {N : ℕ} [NeZero N]

end Kc

section H1Gen

variable {k : Type} [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] {N : ℕ} [NeZero N] {M : Type} [AddCommGroup M] [Module Λ M]

end H1Gen

section GmH1

variable (k : Type) [Field k] [IsAlgClosed k]

end GmH1

end RamanujanPetersson.EtCompact

end

end


