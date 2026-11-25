-- Prove2me | Definitions.Def_RPLib_FX_EtHc_03
-- name    : RPLib_FX_EtHc_03
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:19:45.842952+00:00
-- url     : https://prove2.me/theorems/24ab194b-431a-5519-925a-0590a40e625f
-- title:
--   Compactly supported étale cohomology of the affine line, extension file 03 of 11
-- statement:
--   Extension file 03 of 11 for the compactly supported cohomology of the affine line, stacked on the projective-line library files it imports: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_Exc`: S4-EtCompact, part 5: the excision sequence (compact supports, subset model)
--   * `S4.Def_RP_EtCompact_Pres`: S4-EtCompact, part 8: presentations and the set-indexed `H^*_c`
--   * `S4.Def_RP_EtCompact_P1Pts`: S4-EtCompact, part 27: points of `P^1_K` (O8a, file 1)
--   * `S4.Def_RP_EtCompact_Pt`: S4-EtCompact, part 14: cohomology of a separably closed point (O6d / O7 in dimension 0)
--   * `S4.Def_RP_EtCompact_P1Exc`: S4-EtCompact, part 28: excision on `P^1_K` at `∞` (O8a, file 2)
--   * `S4.Def_RP_EtCompact_A1Hc`: S4-EtCompact, part 29: `H^*_c(A^1, Λ)` inside `P^1` (O8a, file 3)
--   * `S4.Def_RP_EtCompact_P1H0`: S4-EtCompact, part 30: `H^0_c(A^1, Λ) = 0` and `H^1_c(A^1, Λ) ≃ H^1(P^1, Λ)` (O8a, file 4)
--
--   **Formalization note.** Extension of the `RPLib_FX_EtP1` library (étale cohomology of the projective line) to the compactly supported cohomology of the affine line $\mathbf A^1_k = D_+(X_0) \subseteq \mathbf P^1_k$ over an algebraically closed field $k$, with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): the cut sheaves $F_S$ for locally closed $S$, the excision sequence $0 \to F_{S \cap O} \to F_S \to F_{S \setminus O} \to 0$ and its long exact sequence, the vanishing of the higher cohomology of a separably closed point, and the resulting comparison $H^n_c(\mathbf A^1, \Lambda) \to H^n(\mathbf P^1, \Lambda)$ (injective for $n = 1$, bijective for $n \ge 2$) with $H^0_c(\mathbf A^1, \Lambda) = 0$. The declarations of each library module are re-hosted verbatim, except that the three excision exactness proofs `exc_exact₁/₂/₃` are re-proved element-wise (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter II, §3 (extension by zero) and Chapter VI, §1-§3 (cohomology of curves, cohomology with compact support); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapters IV-V

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_14
import Definitions.Def_RPLib_FX_EtHc_01

/-!
# Compactly supported étale cohomology of the affine line, extension file 03 of 11

Declarations of the formalization of the compactly supported étale cohomology of the affine line
`A¹ = D₊(X₀) ⊆ P¹` over an algebraically closed field (the excision sequence for `j_! Λ ⊆ Λ ↠ i_* Λ`
and its consequences), stacked on the `RPLib_FX_EtP1` files it imports and re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim (except that the excision exactness proofs
`exc_exact₁/₂/₃` are re-proved element-wise, which the kernel checks faster) with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_Exc`: S4-EtCompact, part 5: the excision sequence (compact supports, subset model)
* `S4.Def_RP_EtCompact_Pres`: S4-EtCompact, part 8: presentations and the set-indexed `H^*_c`
* `S4.Def_RP_EtCompact_P1Pts`: S4-EtCompact, part 27: points of `P^1_K` (O8a, file 1)
* `S4.Def_RP_EtCompact_Pt`: S4-EtCompact, part 14: cohomology of a separably closed point (O6d / O7 in dimension 0)
* `S4.Def_RP_EtCompact_P1Exc`: S4-EtCompact, part 28: excision on `P^1_K` at `∞` (O8a, file 2)
* `S4.Def_RP_EtCompact_A1Hc`: S4-EtCompact, part 29: `H^*_c(A^1, Λ)` inside `P^1` (O8a, file 3)
* `S4.Def_RP_EtCompact_P1H0`: S4-EtCompact, part 30: `H^0_c(A^1, Λ) = 0` and `H^1_c(A^1, Λ) ≃ H^1(P^1, Λ)` (O8a, file 4)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_Exc =====
section

/-!
# S4-EtCompact, part 5: the excision sequence (compact supports, subset model)

On an ambient scheme `P` (the compactification), cohomology with compact supports of the
locally closed set `W ∩ Vᶜ` (`W, V` open) is `HcWV W V F n := H^n(P, cutWV W V F)`.
For opens `V ≤ V'` the set `S = W ∩ Vᶜ` splits into the relatively open `U = (W ⊓ V') ∩ Vᶜ`
and the relatively closed `Z = W ∩ V'ᶜ`, and
`0 ⟶ cutWV (W ⊓ V') V F ⟶ cutWV W V F ⟶ cutWV W V' F ⟶ 0`
is short exact (checked on stalks). Hence the **excision long exact sequence**
`… ⟶ H^n_c(U) ⟶ H^n_c(S) ⟶ H^n_c(Z) ⟶ H^(n+1)_c(U) ⟶ …` (E0Probe P2a).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}}

variable {Λ} (W : X.Opens) {V V' : X.Opens} (h : V ≤ V') (F : EtSh Λ X)

/-- **Excision, exactness at `H^n_c(S)`**: `H^n_c(U) → H^n_c(S) → H^n_c(Z)`. -/
theorem exc_exact₂ (n : ℕ) :
    Function.Exact (Hmap Λ (excComplex W h F).f n) (Hmap Λ (excComplex W h F).g n) := by
  -- element-wise (`Ext.covariant_sequence_exact₂`): the `AddCommGrpCat` form costs the kernel ~2x more
  intro y
  constructor
  · intro hy
    exact Ext.covariant_sequence_exact₂ (unitSh Λ X) (excComplex_shortExact W h F) y hy
  · rintro ⟨x, rfl⟩
    change (x.comp (Ext.mk₀ (excComplex W h F).f) (add_zero n)).comp (Ext.mk₀ (excComplex W h F).g)
      (add_zero n) = 0
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, (excComplex W h F).zero, Ext.mk₀_zero,
      Ext.comp_zero]

end RamanujanPetersson.EtCompact


end

-- ===== S4.Def_RP_EtCompact_Pres =====
section

/-!
# S4-EtCompact, part 8: presentations and the set-indexed `H^*_c`

`cutWV W V F` only depends on the locally closed set `W ∩ Vᶜ` (up to a canonical chain of stalkwise
isomorphisms). So `HcSet S F n := H^n(X, cut S F)` (`cut` from `Def_RP_EtSheaves_CutSet`, which is
`cutWV (cutOpen S) (cutCompl S)`) is computed by any presentation `S = W ∩ Vᶜ`, and the excision
long exact sequence holds for every locally closed `S` and open `O`:
`… → H^n_c(S ∩ O) → H^n_c(S) → H^n_c(S \ O) → H^(n+1)_c(S ∩ O) → …` (E0Probe P2 in subset form).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

section Pres

variable (F : EtSh Λ X)

variable {W₁ V₁ W₂ V₂ : X.Opens} (hS : wvSet W₁ V₁ = wvSet W₂ V₂)

end Pres

section HcSet

variable (F : EtSh Λ X)

/-- `H^n_c(S, F) ≃ H^n(X, cutWV W V F)` for any presentation `S = W ∩ Vᶜ`. -/
def hcSetEquiv {S : Set X} {W V : X.Opens} (h : wvSet W V = S) (n : ℕ) :
    HcSet Λ S F n ≃+ HcWV Λ W V F n :=
  Hiso Λ (cutIsoCutWV F h) n

end HcSet

section SetExc

variable (F : EtSh Λ X) {S : Set X} (hS : IsLocallyClosed S) (O : X.Opens)

end SetExc

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_P1Pts =====
section

/-!
# S4-EtCompact, part 27: points of `P^1_K` (O8a, file 1)

* `P1.genPt K`: the generic point `(0)`; `closure {genPt} = univ`, so `P^1_K` is irreducible (hence connected).
* `P1.infPt K`: the point `∞ = (X₀)`; every point whose ideal contains `X₀` is `∞` (`P1.eq_infPt_of_X0_mem`).
* The image of the chart `chartA1 : A^1_K ⟶ P^1_K` is `D₊(X₀)`, its complement is `{∞}`, so `{∞}` is closed and
  `Spec κ(∞) ⟶ P^1_K` is a closed immersion; for algebraically closed `K`, `κ(∞) ≅ K` is algebraically closed.
-/

set_option autoImplicit false

open AlgebraicGeometry MvPolynomial CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtCompact

universe u

variable (K : Type u) [Field K]

/-! ### The generic point -/

/-! ### The point at infinity -/

/-! ### The chart `A^1_K ⊆ P^1_K` and its complement `{∞}` -/

theorem P1.isClosed_infPt : IsClosed ({P1.infPt K} : Set (P1 K)) := by
  rw [← P1.compl_range_chartA1]
  exact (chartA1 K).opensRange.isOpen.isClosed_compl

/-- For algebraically closed `K`, `κ(∞) ≅ K`. -/
def P1.residueIsoInf [IsAlgClosed K] : (P1 K).residueField (P1.infPt K) ≅ CommRingCat.of K :=
  residueFieldIsoBase (P1.toSpecK K) (P1.infPt K) (P1.isClosed_infPt K)

instance P1.isAlgClosed_residue_infPt [IsAlgClosed K] :
    IsAlgClosed ((P1 K).residueField (P1.infPt K)) :=
  IsAlgClosed.of_ringEquiv K _ (P1.residueIsoInf K).symm.commRingCatIsoToRingEquiv

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_Pt =====
section

/-!
# S4-EtCompact, part 14: cohomology of a separably closed point (O6d / O7 in dimension 0)

For a scheme `X` with a point `x0` such that `Spec κ(x0) ⟶ X` is an isomorphism (`X` "is" `Spec κ(x0)`) and
`Gal(κ(x0)^sep/κ(x0))` trivial (e.g. `κ(x0)` separably closed: `gal_subsingleton`), the unit sheaf `Λ_X` is
projective (`unitSh_projective`, via the S4-EtSheaves Galois description `specField_homEquiv`), hence
**`H^n(X, F) = 0` for `n ≥ 1`** (`H_eq_zero_of_point`, `H_subsingleton_of_point`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

variable {X : Scheme.{u}} (x0 : X) [IsIso (X.fromSpecResidueField x0)] (Λ : Type u) [CommRing Λ]

/-- **`Λ_X` is projective** on a point with trivial Galois group. -/
theorem unitSh_projective [Subsingleton (Gal x0)] : Projective (unitSh Λ X) := by
  refine ⟨fun {F G} f e _ => ?_⟩
  let s := (geomPtAt x0).stalkF Λ
  let c := constStalkIso Λ (geomPtAt x0) (ModuleCat.of Λ Λ)
  let g0 : stalk Λ (unitSh Λ X) x0 := c.inv.hom (1 : Λ)
  have hepi : Epi (s.map e) := inferInstance
  obtain ⟨m', hm'⟩ := (ModuleCat.epi_iff_surjective (s.map e)).1 hepi ((s.map f).hom g0)
  let ℓ : stalk Λ (unitSh Λ X) x0 →ₗ[Λ] stalk Λ F x0 :=
    (LinearMap.toSpanSingleton Λ _ m').comp c.hom.hom
  have hℓ : ∀ σ : Gal x0, ℓ ∘ₗ galRep Λ (unitSh Λ X) x0 σ = galRep Λ F x0 σ ∘ₗ ℓ := by
    intro σ
    rw [Subsingleton.elim σ 1, map_one, map_one]
    exact LinearMap.ext fun v => by simp
  have key : ∀ r : Λ, c.hom.hom (c.inv.hom r) = r := fun r => by
    change (c.inv ≫ c.hom).hom r = r
    rw [Iso.inv_hom_id]
    rfl
  have key2 : ∀ v, c.inv.hom (c.hom.hom v) = v := fun v => by
    change (c.hom ≫ c.inv).hom v = v
    rw [Iso.hom_inv_id]
    rfl
  refine ⟨(specField_homEquiv x0 Λ (unitSh Λ X) F).symm ⟨ℓ, hℓ⟩, ?_⟩
  apply (specField_homEquiv x0 Λ (unitSh Λ X) G).injective
  apply Subtype.ext
  rw [specField_homEquiv_apply, specField_homEquiv_apply, Functor.map_comp, ModuleCat.hom_comp]
  have h1 : (s.map ((specField_homEquiv x0 Λ (unitSh Λ X) F).symm ⟨ℓ, hℓ⟩)).hom = ℓ := by
    rw [← specField_homEquiv_apply, Equiv.apply_symm_apply]
  rw [h1]
  apply LinearMap.ext
  intro v
  rw [← key2 v]
  have hv : c.inv.hom (c.hom.hom v) = c.hom.hom v • g0 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  have hg0 : ℓ g0 = m' := by
    change LinearMap.toSpanSingleton Λ _ m' (c.hom.hom (c.inv.hom 1)) = m'
    rw [key, LinearMap.toSpanSingleton_apply, one_smul]
  rw [LinearMap.comp_apply, hv, map_smul, map_smul, map_smul, hg0]
  exact congrArg _ hm'

/-- **Cohomology of a separably closed point vanishes in positive degrees.** -/
theorem H_eq_zero_of_point [Subsingleton (Gal x0)] (F : EtSh Λ X) (n : ℕ) (e : H Λ F (n + 1)) : e = 0 := by
  have := unitSh_projective x0 Λ
  exact Abelian.Ext.eq_zero_of_projective e

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

theorem isIso_openCutι_of_forall (W : X.Opens) (G : EtSh Λ X) (h : ∀ x : X, x ∈ W) :
    IsIso (openCutι Λ W G) := by
  rw [isIso_iff_stalk]
  intro x
  exact isIso_stalk_openCutι W G (geomPtAt x) (mem_center_geomPtAt (h x))

theorem isIso_quotCutπ_of_forall (V : X.Opens) (G : EtSh Λ X) (h : ∀ x : X, x ∉ V) :
    IsIso (quotCutπ Λ V G) := by
  rw [isIso_iff_stalk]
  intro x
  exact isIso_stalk_quotCutπ V G (geomPtAt x) (not_mem_center_geomPtAt (h x))

theorem mem_cutOpen_of_isClosed {S : Set X} (hS : IsClosed S) (x : X) : x ∈ cutOpen S := by
  show x ∈ interior (coborder S)
  rw [coborder_eq_univ_iff.mpr hS, interior_univ]
  exact Set.mem_univ x

/-- For closed `S`, `cut S F ≅ quotCut (cutCompl S) F`. -/
def cutClosedIso {S : Set X} (hS : IsClosed S) (F : EtSh Λ X) :
    cut Λ S F ≅ quotCut Λ (cutCompl S) F :=
  haveI := isIso_openCutι_of_forall (cutOpen S) (quotCut Λ (cutCompl S) F) (mem_cutOpen_of_isClosed hS)
  (asIso (openCutι Λ (cutOpen S) (quotCut Λ (cutCompl S) F)) :
    openCut Λ (cutOpen S) (quotCut Λ (cutCompl S) F) ≅ quotCut Λ (cutCompl S) F)

/-- **`cut univ F ≅ F`.** -/
def cutUnivIso (F : EtSh Λ X) : cut Λ Set.univ F ≅ F :=
  haveI := isIso_quotCutπ_of_forall (cutCompl (Set.univ : Set X)) F (fun x hx => by
    have h : x ∈ (closure (Set.univ : Set X))ᶜ := hx
    rw [closure_univ] at h
    exact h (Set.mem_univ x))
  cutClosedIso isClosed_univ F ≪≫ (asIso (quotCutπ Λ (cutCompl Set.univ) F)).symm

/-- `H^n_c(univ, F) ≃+ H^n(X, F)`. -/
def hcUnivEquiv (F : EtSh Λ X) (n : ℕ) : HcSet Λ Set.univ F n ≃+ H Λ F n :=
  Hiso Λ (cutUnivIso F) n

section Closed

variable {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

theorem cutCompl_range : cutCompl (Set.range i) = complOpens i := by
  apply TopologicalSpace.Opens.ext
  show (closure (Set.range i))ᶜ = (Set.range i)ᶜ
  rw [i.isClosedEmbedding.isClosed_range.closure_eq]

end Closed

end General

section Point

variable {Y : Scheme.{u}} (y : Y)

variable (Λ : Type u) [CommRing Λ]

end Point

section P1

variable (K : Type u) [Field K] [IsAlgClosed K] (Λ : Type u) [CommRing Λ]

omit [IsAlgClosed K] in
theorem P1.isLocallyClosed_univ : IsLocallyClosed (Set.univ : Set (P1 K)) :=
  isClosed_univ.isLocallyClosed

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

end OpenIm

section OpenCut

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

theorem wvSet_bot (O : X.Opens) : wvSet O ⊥ = Set.univ ∩ (O : Set X) := by
  ext x
  rw [mem_wvSet, Set.univ_inter, SetLike.mem_coe]
  simp

/-- `cut (univ ∩ O) F ≅ openCut O F` for an open `O`. -/
def cutOpenIso (O : X.Opens) (F : EtSh Λ X) : cut Λ (Set.univ ∩ (O : Set X)) F ≅ openCut Λ O F :=
  haveI := isIso_quotCutπ_of_forall (⊥ : X.Opens) F (fun x hx => by simp at hx)
  cutIsoCutWV F (wvSet_bot O) ≪≫ (lsh O.ι Λ).mapIso ((res O.ι Λ).mapIso (asIso (quotCutπ Λ ⊥ F)).symm)

end OpenCut

section A1

variable (K : Type u) [Field K] (Λ : Type u) [CommRing Λ]

variable [IsAlgClosed K]

end A1

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_P1H0 =====
section

/-!
# S4-EtCompact, part 30: `H^0_c(A^1, Λ) = 0` and `H^1_c(A^1, Λ) ≃ H^1(P^1, Λ)` (O8a, file 4)

* `smulEnd r F : F ⟶ F` (multiplication by `r : Λ`); its stalk maps are `r • 𝟙` (`stalk_smulEnd`).
* `exists_lift_unitSh`: if `ρ : A ⟶ B` is epi, `A ≅ Λ_X` and `B` has zero stalks off one point `x0`, every
  `ψ : Λ_X ⟶ B` lifts through `ρ` (stalk at `x0` is cyclic on `1`).
* `resC_zero_surjective`: `H^0_c(S) → H^0_c(S \ O)` is onto when `cut S F ≅ Λ_X` and `S \ O` is at most a point;
  hence `extO` is injective in degree `1` (`extO_one_injective_of`).
* `P1.hcA1_zero_eq_zero`, **`A1.hc_zero_eq_zero`**: `H^0_c(A^1, Λ) = 0` (any field).
* **`A1.hcEquivP1One`**: `H^1_c(A^1, Λ) ≃+ H^1(P^1, Λ)` (`K` algebraically closed).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section Smul

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

end Smul

section Lift

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}}

/-- **Lifting through an epi with point-supported target**: if `ρ : A ⟶ B` is epi, `Λ_X ≅ A`, and the stalks of
`B` vanish off `x0`, then every `ψ : Λ_X ⟶ B` factors through `ρ`. -/
theorem exists_lift_unitSh {A B : EtSh Λ X} (ρ : A ⟶ B) [Epi ρ] (e : unitSh Λ X ≅ A) (x0 : X)
    (hB : ∀ x : X, x ≠ x0 → IsZero (((geomPtAt x).stalkF Λ).obj B)) (ψ : unitSh Λ X ⟶ B) :
    ∃ f : unitSh Λ X ⟶ A, f ≫ ρ = ψ := by
  have hepi : Epi (((geomPtAt x0).stalkF Λ).map ρ) := inferInstance
  obtain ⟨a', ha'⟩ := (ModuleCat.epi_iff_surjective _).1 hepi ((((geomPtAt x0).stalkF Λ).map ψ).hom (oneAt Λ x0))
  have h2 : (((geomPtAt x0).stalkF Λ).map e.hom).hom ((((geomPtAt x0).stalkF Λ).map e.inv).hom a') = a' := by
    rw [← ModuleCat.comp_apply, ← CategoryTheory.Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id,
      ModuleCat.id_apply]
  refine ⟨smulEnd ((constStalkIso Λ (geomPtAt x0) (ModuleCat.of Λ Λ)).hom.hom
    ((((geomPtAt x0).stalkF Λ).map e.inv).hom a')) _ ≫ e.hom, hom_ext_stalk Λ (fun x => ?_)⟩
  by_cases hx : x = x0
  · rw [hx]
    refine unitSh_stalk_hom_ext Λ x0 ?_
    rw [Functor.map_comp, Functor.map_comp, ModuleCat.comp_apply, ModuleCat.comp_apply, smulEnd_stalk_apply,
      smul_oneAt, h2]
    exact ha'
  · exact (hB x hx).eq_of_tgt _ _

end Lift

section Res

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

end Res

section P1

variable (K : Type u) [Field K] (Λ : Type u) [CommRing Λ]

variable [IsAlgClosed K]

end P1

end RamanujanPetersson.EtCompact

end

end


