-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_020
-- name    : RPLib_FX_EtPBC_020
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T18:52:46.022817+00:00
-- url     : https://prove2.me/theorems/7674230c-bfff-5ead-844e-42ff917fd9fc
-- title:
--   Proper base change for the projective line, library file 020
-- statement:
--   File 020 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_LshEt`: S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`
--   * `S4.Def_RP_EtPBC_A_O2KapP`: S4-EtPBC-A, O2 M6 (O2KapP): restriction of a piece Kummer class along an etale map
--   * `S4.Def_RP_EtPBC_A_O2PPTd`: S4-EtPBC-A, O2 GLOB (O2PPTd): the chart form of the piece transfer, and Zariski shrinks
--   * `S4.Def_RP_EtPBC_A_O2Mob`: S4-EtPBC-A, O2 Mob: charts of `P¹` missing one moved point at infinity
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_013
import Definitions.Def_RPLib_FX_EtPBC_014
import Definitions.Def_RPLib_FX_EtPBC_016

/-!
# Proper base change for the projective line, library file 020

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_LshEt`: S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`
* `S4.Def_RP_EtPBC_A_O2KapP`: S4-EtPBC-A, O2 M6 (O2KapP): restriction of a piece Kummer class along an etale map
* `S4.Def_RP_EtPBC_A_O2PPTd`: S4-EtPBC-A, O2 GLOB (O2PPTd): the chart form of the piece transfer, and Zariski shrinks
* `S4.Def_RP_EtPBC_A_O2Mob`: S4-EtPBC-A, O2 Mob: charts of `P¹` missing one moved point at infinity
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_LshEt =====
section

/-!
# S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`

For an etale `e : U ⟶ X`, a geometric point `x` of `X` and a module `J`, the restriction
`res e (x_* J)` of the skyscraper sheaf is assembled from the skyscraper sheaves `l_* J` at the
lifts `l` of `x` along `e` (`pr`, `assemble`, `assemble_pr`, `hom_ext_pr`). Hence:
* `injective_res_sky`: `res e (x_* J)` is injective for `J` injective;
* `res e` preserves injective objects (every injective is a retract of its god sheaf);
* **`lsh e Λ = e_!` preserves monomorphisms** (Mathlib's
  `preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite
open RamanujanPetersson.EtCompact

noncomputable section

namespace RamanujanPetersson.EtSheaves.LshEt

universe u

variable {U X : Scheme.{u}} (e : U ⟶ X) [Etale e] (x : GeomPt X)

variable {Λ : Type u} [CommRing Λ] (J : ModuleCat.{u} Λ)

theorem hom_ext_pr {G : EtSh Λ U} {f g : G ⟶ (res e Λ).obj (x.point.skyscraperSheaf J)}
    (H : ∀ l, f ≫ pr e x J l = g ≫ pr e x J l) : f = g := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W => r_hom_ext e x J fun b => ?_))
  have hb : fibInc e x (liftOf e x b) W.unop (dec e x b) = b := fl_ext x rfl
  have h1 := congrArg
    (fun φ => φ.hom.app W ≫ sπ J (liftPt e x (liftOf e x b)).point W (dec e x b)) (H (liftOf e x b))
  change (f.hom.app W ≫ (pr e x J _).hom.app W) ≫ _ =
    (g.hom.app W ≫ (pr e x J _).hom.app W) ≫ _ at h1
  rw [Category.assoc, Category.assoc, pr_app_π, hb] at h1
  exact h1

end RamanujanPetersson.EtSheaves.LshEt

end

end

-- ===== S4.Def_RP_EtPBC_A_O2KapP =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2KapP): restriction of a piece Kummer class along an etale map

For `f : X₁ ⟶ X` etale between affine schemes whose rings are finite products of Dedekind domains, and a Kummer
class `kapS p (kumD α)` on the piece `p` of `X` (`α^d = u`):
* `kerMap f p₁ : Γ(X) → Γ(X₁) ⧸ p₁`, `exists_minimalPrime_le_ker`, `kerLift`, **`piHom_comp_eq`**
  (the piece `p₁` of `X₁` maps into the piece `q` of `X` through `Spec (Γ(X₁) ⧸ p₁) ⟶ Spec (Γ(X) ⧸ q)`),
  `injective_of_etale` (an etale map of domains is injective), `resLE_congr`, `resLE_kapS_self`, `resLE_kapS_ne`;
* **`resLE_kapS_kumD_eq_zero`**: if `u` becomes a `d`-th power in the fraction field of every piece of `X₁` lying
  over `p`, then `resLE f 1 (kapS p (kumD α)) = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.Pur RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer
  RamanujanPetersson.EtCompact.GalTrE

universe u

section Fac

variable {X X₁ : Scheme.{0}} [IsAffine X] [IsAffine X₁] [IsNoetherianRing Γ(X, ⊤)] [IsNoetherianRing Γ(X₁, ⊤)]
  (h : ∀ (m : Ideal Γ(X, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  (h₁ : ∀ (m : Ideal Γ(X₁, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  (f : X₁ ⟶ X)

theorem kerLift_mk {p₁ : minimalPrimes Γ(X₁, ⊤)} {q : minimalPrimes Γ(X, ⊤)}
    (hq : (q : Ideal Γ(X, ⊤)) ≤ RingHom.ker (kerMap f p₁)) (a : Γ(X, ⊤)) :
    kerLift hq (Ideal.Quotient.mk (q : Ideal Γ(X, ⊤)) a) =
      Ideal.Quotient.mk (p₁ : Ideal Γ(X₁, ⊤)) (f.appTop a) :=
  rfl

end Fac

section KappaRes

end KappaRes

section Red

end Red

section KapP

end KapP

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PPTd =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2PPTd): the chart form of the piece transfer, and Zariski shrinks

For chart neighbourhoods `D = chEt c φ`, `D₁ = chEt c φ₁` and any `dm : D₁ ⟶ D` in `P.Etale`:
* `left_spec_map`: `dm.left ≫ Spec.map φ = Spec.map φ₁`; **`shG_wm`**: `wm (prdMap dm) ≫ shG c φ = shG c φ₁`;
* `sXW c φ R ζ0 ∈ Γ(W)` (the image of `ζ0 ∈ k`), `ζW_eq`, **`wm_appTop_sXW`**;
* **`locCls_kapS_chart`**: `locCls_kapS_shrink` (O2PPTc) with the roots of unity `ζW` of O2Km9a on both sides;
* **`piece_unique_away`**: if `Γ(X₁) = Γ(X)[1/s]` along `f`, at most one piece of `X₁` lies over a piece of `X`
  (applies to `toDF` by `isLocalization_away_toDF`, O2ZarCh).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Pur
  RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE

section Away

variable {X X₁ : Scheme.{0}} (f : X₁ ⟶ X)

/-- **At most one piece of `X₁` over a piece of `X`** when `Γ(X₁) = Γ(X)[1/s]` along `f`. -/
theorem piece_unique_away (s : Γ(X, ⊤))
    (hloc : letI := f.appTop.hom.toAlgebra; IsLocalization.Away s Γ(X₁, ⊤)) (p : minimalPrimes Γ(X, ⊤))
    {p₁ p₂ : minimalPrimes Γ(X₁, ⊤)} (h₁ : (p : Ideal Γ(X, ⊤)) ≤ RingHom.ker (kerMap f p₁))
    (h₂ : (p : Ideal Γ(X, ⊤)) ≤ RingHom.ker (kerMap f p₂)) : p₁ = p₂ := by
  let _ := f.appTop.hom.toAlgebra
  have _ := hloc
  have _ : (p : Ideal Γ(X, ⊤)).IsPrime := p.2.1.1
  rw [ker_kerMap] at h₁ h₂
  exact Subtype.ext (piece_eq_of_away s p₁.2 p₂.2 h₁ h₂)

end Away

section Chart

end Chart

section ChartPPT

end ChartPPT

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Mob =====
section

/-!
# S4-EtPBC-A, O2 Mob: charts of `P¹` missing one moved point at infinity

* `mobA c`: the shear `X₀ ↦ X₀ + c X₁`, `X₁ ↦ X₁`; `mobG c` the graded ring hom; `mobP c := Proj.map (mobG c)`,
  an isomorphism of `P¹` with inverse `mobP (-c)`.
* **`chartM c := chartA1 ≫ mobP c`**: an open immersion `A¹ ⟶ P¹` whose range is `P¹ ∖ {mobP c ∞}`
  (`mem_range_chartM`); `c ↦ mobP c ∞` is injective (`mobP_infPt_injective`).
-/

set_option autoImplicit false

open AlgebraicGeometry MvPolynomial CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtCompact

section Mob

variable {K : Type} [Field K]

theorem irr_le_map_mobG (c : K) :
    HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 2) K) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 2) K)).map (mobG c) := by
  calc HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 2) K)
      = (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 2) K)).map ((mobG c).comp (mobG (-c))) := by
        rw [mobG_comp, neg_add_cancel, mobG_zero, HomogeneousIdeal.map_id]
    _ = ((HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 2) K)).map (mobG (-c))).map (mobG c) :=
        HomogeneousIdeal.map_comp _ _
    _ ≤ (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 2) K)).map (mobG c) :=
        HomogeneousIdeal.map_mono _ ((HomogeneousIdeal.map_le_iff_le_comap _).2 (irr_le_comap_mobG (-c)))

variable (K) in
/-- The automorphism `mobP c` of `P¹`. -/
def mobP (c : K) : P1 K ⟶ P1 K := Proj.map (mobG c) (irr_le_map_mobG c)

theorem mobP_comp (c : K) : mobP K (-c) ≫ mobP K c = 𝟙 _ := by
  unfold mobP
  rw [← Proj.map_comp]
  refine (proj_map_congr ?_ _ _).trans Proj.map_id
  rw [mobG_comp, add_neg_cancel, mobG_zero]

instance (c : K) : IsIso (mobP K c) :=
  ⟨⟨mobP K (-c), by have h := mobP_comp (-c); rwa [neg_neg] at h, mobP_comp c⟩⟩

theorem mobP_ideal (c : K) (x : P1 K) :
    (mobP K c x).asHomogeneousIdeal = x.asHomogeneousIdeal.comap (mobG c) := rfl

theorem mobP_mobP (c c' : K) (x : P1 K) : mobP K c' (mobP K c x) = mobP K (c' + c) x :=
  ProjectiveSpectrum.ext (by rw [mobP_ideal, mobP_ideal, mobP_ideal, HomogeneousIdeal.comap_comap, mobG_comp])

theorem mobP_neg_apply (c : K) (x : P1 K) : mobP K c (mobP K (-c) x) = x :=
  ProjectiveSpectrum.ext (by rw [mobP_mobP, add_neg_cancel, mobP_ideal, mobG_zero, HomogeneousIdeal.comap_id])

theorem mobP_apply_neg (c : K) (x : P1 K) : mobP K (-c) (mobP K c x) = x := by
  have h := mobP_neg_apply (-c) x
  rwa [neg_neg] at h

variable (K) in
/-- **The moved chart** `chartM c := chartA1 ≫ mobP c`. -/
def chartM (c : K) : A1 K ⟶ P1 K := chartA1 K ≫ mobP K c

instance (c : K) : IsOpenImmersion (chartM K c) := by
  unfold chartM
  infer_instance

theorem mem_range_chartM (c : K) (x : P1 K) : x ∈ Set.range (chartM K c) ↔ x ≠ mobP K c (P1.infPt K) := by
  constructor
  · rintro ⟨y, rfl⟩ h
    rw [chartM, Scheme.Hom.comp_apply] at h
    have h' := congrArg (mobP K (-c)) h
    rw [mobP_apply_neg, mobP_apply_neg] at h'
    exact P1.infPt_not_mem_range K (h' ▸ ⟨y, rfl⟩)
  · intro h
    have hw : mobP K (-c) x ≠ P1.infPt K := fun hw => h (by rw [← hw, mobP_neg_apply])
    obtain ⟨y, hy⟩ := (P1.mem_range_chartA1_iff K _).2 hw
    exact ⟨y, by rw [chartM, Scheme.Hom.comp_apply, hy, mobP_neg_apply]⟩

theorem mobP_infPt_injective : Function.Injective (fun c : K => mobP K c (P1.infPt K)) := by
  intro c c' hcc
  have hcc' : mobP K c (P1.infPt K) = mobP K c' (P1.infPt K) := hcc
  by_contra hne
  have h0 : (X 0 - C c * X 1 : MvPolynomial (Fin 2) K) ∈ (mobP K c (P1.infPt K)).asHomogeneousIdeal := by
    rw [mobP_ideal]
    show mobG c (X 0 - C c * X 1) ∈ (P1.infPt K).asHomogeneousIdeal
    rw [mobG_apply, map_sub, map_mul, mobA_X0, mobA_X1, algHom_C, MvPolynomial.algebraMap_eq, add_sub_cancel_right]
    exact P1.X0_mem_infPt K
  rw [hcc', mobP_ideal] at h0
  change mobG c' (X 0 - C c * X 1) ∈ (P1.infPt K).asHomogeneousIdeal at h0
  rw [mobG_apply, map_sub, map_mul, mobA_X0, mobA_X1, algHom_C, MvPolynomial.algebraMap_eq] at h0
  have h1 : (C (c' - c) * X 1 : MvPolynomial (Fin 2) K) ∈ (P1.infPt K).asHomogeneousIdeal := by
    have h2 := Ideal.sub_mem _ h0 (P1.X0_mem_infPt K)
    have h3 : (X 0 + C c' * X 1 - C c * X 1 - X 0 : MvPolynomial (Fin 2) K) = C (c' - c) * X 1 := by
      rw [C_sub]
      ring
    rw [h3] at h2
    exact h2
  have hu : c' - c ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have h4 := Ideal.mul_mem_left _ (C (c' - c)⁻¹) h1
  rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hu, C_1, one_mul] at h4
  exact X1_not_mem_infPt h4

end Mob

end RamanujanPetersson.EtCompact

end

end


