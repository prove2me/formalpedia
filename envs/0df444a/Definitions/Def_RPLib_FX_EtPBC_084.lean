-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_084
-- name    : RPLib_FX_EtPBC_084
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:17:00.284817+00:00
-- url     : https://prove2.me/theorems/9951835b-4b85-5011-80a2-b7b893c06065
-- title:
--   Proper base change for the projective line, library file 084
-- statement:
--   File 084 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2E3`: S4-EtPBC-A, O2 C-plan S4c1 (scheme level): affine Dedekind presentations of one-point classes
--   * `S4.Def_RP_EtPBC_A_O2L2x`: S4-EtPBC-A, L2x (PullH extras): `pullH` along composites and along etale maps
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_038
import Definitions.Def_RPLib_FX_EtPBC_040
import Definitions.Def_RPLib_FX_EtPBC_073

/-!
# Proper base change for the projective line, library file 084

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2E3`: S4-EtPBC-A, O2 C-plan S4c1 (scheme level): affine Dedekind presentations of one-point classes
* `S4.Def_RP_EtPBC_A_O2L2x`: S4-EtPBC-A, L2x (PullH extras): `pullH` along composites and along etale maps
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2E3 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4c1 (scheme level): affine Dedekind presentations of one-point classes

* `fib_injective_of_mono`: a mono of étale objects is injective on geometric fibres;
* `chartLift`, `chartRing`: an affine open `V` of `D` lying over an affine chart `c : Spec R ⟶ P` gives
  `φ_V : R ⟶ Γ(V)` with `Spec φ_V ≫ c = fromSpec ≫ D.hom`, and `φ_V` is étale;
* `A1pt k a`: the point `X = a` of `A¹`; `exists_A1pt_of_closed`: closed points of a chart are of this form;
* `phiG`, `D1`, `d1`: the basic open `Spec Γ(V)_g` as an étale object over `P` through the chart;
* **`isLoc_aff`**: a one-point class at `z ∈ range c` has a presentation `IsLocAff` through `Spec B`,
  `B` a Dedekind domain étale over `k[X]` in which `X - a` generates a prime (the `purity_xi` setting).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

universe u

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtDed

section Mono

end Mono

section Chart

end Chart

section A1

end A1

section D1

end D1

section Aff

variable {k : Type u} [Field k] {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

variable [IsAlgClosed k] (c : A1 k ⟶ P) [IsOpenImmersion c]

/-- **S4c1**: a one-point class at a point of the chart `c` has an affine Dedekind presentation. -/
theorem isLoc_aff {F : EtSh Λ P} {z : P} {β : Ext.{u} (freeSh Λ (etId P)) F 2} (hβ : IsLoc Λ F z β)
    (hzc : z ∈ Set.range c) : ∃ a : k, c (A1pt k a) = z ∧ IsLocAff Λ F c a β := by
  obtain ⟨Uo, Uz, h, hz, D, hD, hDn, hDr, κ, rfl⟩ := hβ
  have hzcl : IsClosed ({z} : Set P) := by
    have : ({z} : Set P) = (Uz : Set P)ᶜ := Set.ext fun x => by
      rw [Set.mem_singleton_iff, Set.mem_compl_iff, SetLike.mem_coe, hz x, not_not]
    rw [this]
    exact Uz.isOpen.isClosed_compl
  obtain ⟨a, ha⟩ := exists_A1pt_of_closed k c hzc hzcl
  refine ⟨a, ha, ?_⟩
  subst ha
  obtain ⟨n⟩ := id hDn
  have hw : D.hom (fpt _ n) = c (A1pt k a) := fib_over _ n
  have hwU : fpt _ n ∈ D.hom ⁻¹ᵁ c.opensRange := by
    show D.hom (fpt _ n) ∈ c.opensRange
    rw [hw]
    exact ⟨_, rfl⟩
  obtain ⟨V, hVa, hwV, hVle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens D.left)) hwU
  have hV : IsAffineOpen V := hVa
  have hVc : ∀ v ∈ V, D.hom v ∈ Set.range c := fun v hv => by
    have := hVle hv
    simpa [Scheme.Hom.coe_opensRange] using this
  letI := (chartRing c D hV hVc).hom.toAlgebra
  haveI : Algebra.Etale k[X] Γ(D.left, V) := chartRing_etale c D hV hVc
  let q := hV.primeIdealOf ⟨fpt _ n, hwV⟩
  have hqw : hV.fromSpec q = fpt _ n := hV.fromSpec_primeIdealOf _
  have hpt : Spec.map (chartRing c D hV hVc) q = A1pt k a := by
    rw [spec_chartRing]
    apply c.isOpenEmbedding.injective
    exact (chartLift_apply c D hV hVc q).trans ((congrArg (fun x => D.hom x) hqw).trans hw)
  have hqa : q.asIdeal.under k[X] = Ideal.span {X - C a} := congrArg PrimeSpectrum.asIdeal hpt
  obtain ⟨g, hgq, -, hded, hne, hspan, hprime⟩ := exists_good_away q.asIdeal a hqa
  -- the presentation through `D1`
  have hD₁ : Subsingleton ((geomPtAt (c (A1pt k a))).point.fiber.obj (D1 c hV hVc g)) :=
    ⟨fun b b' => fib_injective_of_mono (d1 c hV hVc g) _ (Subsingleton.elim _ _)⟩
  let v₁ : Spec (CommRingCat.of (Localization.Away g)) :=
    ⟨q.asIdeal.map (algebraMap Γ(D.left, V) (Localization.Away g)), hprime⟩
  have hv₁ : (d1 c hV hVc g).left v₁ = fpt _ n := by
    show hV.fromSpec (Spec.map (locG g) v₁) = fpt _ n
    have : Spec.map (locG g) v₁ = q := PrimeSpectrum.ext
      (IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) (Localization.Away g) q.isPrime
        ((Ideal.disjoint_powers_iff_notMem_of_isPrime g).2 hgq))
    rw [this, hqw]
  obtain ⟨b, -, -⟩ := exists_lift_fib (d1 c hV hVc g) _ n v₁ hv₁
  have hDn₁ : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj (D1 c hV hVc g)) := ⟨b⟩
  have hDr₁ : ∀ v : (D1 c hV hVc g).left, (D1 c hV hVc g).hom v ∈ Uo ∨ (D1 c hV hVc g).hom v = c (A1pt k a) :=
    fun v => by
      have e := d1_apply c hV hVc g v
      rcases hDr ((d1 c hV hVc g).left v) with h1 | h1
      · exact Or.inl ((congrArg (· ∈ Uo) e).mpr h1)
      · exact Or.inr (e.trans h1)
  have hS := locC_shortExact (Λ := Λ) D h _ hz hD hDn hDr
  have hS₁ := locC_shortExact (Λ := Λ) (D1 c hV hVc g) h _ hz hD₁ hDn₁ hDr₁
  have hφe : Etale (Spec.map (phiG c hV hVc g)) := Etale.of_comp _ c
  refine ⟨CommRingCat.of (Localization.Away g), phiG c hV hVc g, inferInstance,
    (HasRingHomProperty.Spec_iff (P := @Etale)).1 hφe, hded, ?_, ?_, Uo, Uz, h, hz, hD₁, hDn₁, hDr₁,
    (Ext.mk₀ (freeMap Λ (prdMap (d1 c hV hVc g) (opEt Uo)))).comp κ (zero_add 1), ?_⟩
  · rw [phiG_apply]; exact hne
  · rw [phiG_apply, hspan]; exact hprime
  · exact locCls_shrink h (d1 c hV hVc g) hS₁ hS κ

end Aff

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L2x =====
section

/-!
# S4-EtPBC-A, L2x (PullH extras): `pullH` along composites and along etale maps

* `mapExact_iso τ ξ`: isomorphic exact functors act alike on `Ext¹` (`τ : Φ ≅ Φ'`);
* `conjE x a b := mk₀ a ∘ x ∘ mk₀ b`, `conjE_conjE`, `mapExact_conjE`;
* `pullUnit_comp`: `Λ_X ≅ (f ≫ g)^*Λ_Z ≅ f^*g^*Λ_Z` is `Λ_X ≅ f^*Λ_Y ≅ f^*g^*Λ_Z`;
* **`pullH_comp`**: `pullH (f ≫ g) 1 κ = pullH f 1 (pullH g 1 κ)`;
* `pullUnit_res`: for etale `g`, `Λ_U ≅ g^*Λ_X ≅ res g Λ_X` is `unitRes g`;
* **`resLE_eq_pullH`**: for etale `g`, `resLE g 1 e = pullH g 1 e`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE

section IsoGen

universe w v₁ u₁ v₂ u₂

end IsoGen

universe u

section PullX

variable {Λ : Type u} [CommRing Λ]

/-- **`resLE` is `pullH`** for etale maps (degree one). -/
theorem resLE_eq_pullH {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] (e : H Λ (unitSh Λ X) 1) :
    resLE g 1 e = pullH Λ g 1 e := by
  have h1 : resLE g 1 e = conjE (e.mapExactFunctor (res g Λ)) (unitRes g Λ) (unitResIso g Λ).inv := by
    rw [resLE_apply, resHE_apply, conjE, Ext.comp_assoc_of_third_deg_zero]
  have hU : unitRes g Λ ≫ (pullIsoRes g Λ).inv.app (unitSh Λ X) = (pullUnit Λ g).hom := by
    rw [← pullUnit_res g, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hU' : (pullIsoRes g Λ).hom.app (unitSh Λ X) ≫ (unitResIso g Λ).inv = (pullUnit Λ g).inv := by
    rw [← cancel_epi (pullUnit Λ g).hom, ← Category.assoc, pullUnit_res g, Iso.hom_inv_id, ← unitResIso_hom,
      Iso.hom_inv_id]
  rw [h1, conjE_of_iso (pullIsoRes g Λ) e, conjE_conjE, hU, hU', pullH_eq_conjE]

end PullX

end RamanujanPetersson.EtPBC.EtMV

end

end


