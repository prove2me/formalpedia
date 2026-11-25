-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_029
-- name    : RPLib_FX_EtPBC_029
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:27:25.441782+00:00
-- url     : https://prove2.me/theorems/096d0d63-24ab-58e1-b018-b2fec2b75d77
-- title:
--   Proper base change for the projective line, library file 029
-- statement:
--   File 029 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovAs6b`: S4-EtPBC-A, R4-T2 (A3 assembly, As6b): the overlap maps of the approximated cover
--   * `S4.Def_RP_EtPBC_A_Z3P1b`: S4-EtPBC-A, (Z) geometric layer 4 (G-a): the transition `t s = 1` on the overlap of the two charts of `P¹_K`
--   * `S4.Def_RP_EtPBC_A_Z3Y`: S4-EtPBC-A, (Z) geometric layer 7 (G-b on `Y`): two-chart data of a finite `Y ⟶ P¹_V`
--   * `S4.Def_RP_EtPBC_A_LshEt`: S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`
--   * `S4.Def_RP_EtPBC_A_O2N1a`: S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_024
import Definitions.Def_RPLib_FX_EtPBC_025

/-!
# Proper base change for the projective line, library file 029

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovAs6b`: S4-EtPBC-A, R4-T2 (A3 assembly, As6b): the overlap maps of the approximated cover
* `S4.Def_RP_EtPBC_A_Z3P1b`: S4-EtPBC-A, (Z) geometric layer 4 (G-a): the transition `t s = 1` on the overlap of the two charts of `P¹_K`
* `S4.Def_RP_EtPBC_A_Z3Y`: S4-EtPBC-A, (Z) geometric layer 7 (G-b on `Y`): two-chart data of a finite `Y ⟶ P¹_V`
* `S4.Def_RP_EtPBC_A_LshEt`: S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`
* `S4.Def_RP_EtPBC_A_O2N1a`: S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_CovAs6b =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As6b): the overlap maps of the approximated cover

Over `R'` (via `σ : C →ₐ[A] R'`) the charts are `Pres (gmap (tsC σ Bᵢ) gCᵢ)` and the overlap is
`Pres (gmap (tsC σ N) (gmap (bcC φ₀ C) gC₀))`.
* `psi0`: `presMap (bcS R' φ₀)` followed by `presCongr`; `psi0_alg`, `psi0_tmul`, `psi0_X`, `psi0_away`.
* `isoN`, `psi1`: `presMap (bcS R' φ₁)`, `presCongr`, then `presIso` of the pushed substitution data;
  `psi1_alg`, `psi1_tmul`, `psi1_X`, `psi1_away`.
* `ctheta0`, `ctheta1`: compatibility of residue maps with `psi0`/`psi1` from values on constants and variables.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open TensorProduct

universe u

section Psi

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S] {R' : Type u} [CommRing R']
  [Algebra A R'] {B₀ B₁ N : Type u} [CommRing B₀] [Algebra A B₀] [CommRing B₁] [Algebra A B₁] [CommRing N]
  [Algebra A N] (φ₀ : B₀ →ₐ[A] N) (φ₁ : B₁ →ₐ[A] N) {C : Subalgebra A S} (σ : C →ₐ[A] R') {r₀ r₁ : ℕ}
  (gC₀ : Fin r₀ → MvPolynomial (Fin r₀) (C ⊗[A] B₀)) (gC₁ : Fin r₁ → MvPolynomial (Fin r₁) (C ⊗[A] B₁))

theorem psi0_tmul (r : R') (b : B₀) :
    psi0 φ₀ σ gC₀ (algebraMap (R' ⊗[A] B₀) (Pres (gmap (tsC σ B₀) gC₀)) (r ⊗ₜ b)) =
      algebraMap (R' ⊗[A] N) (Pres (gmap (tsC σ N) (gmap (bcC φ₀ C) gC₀))) (r ⊗ₜ φ₀ b) :=
  psi0_alg φ₀ σ gC₀ (r ⊗ₜ b)

variable (uC : Fin r₀ → MvPolynomial (Fin r₁) (C ⊗[A] N)) (vC : Fin r₁ → MvPolynomial (Fin r₀) (C ⊗[A] N))
  (H : (∀ j, MvPolynomial.bind₁ uC (gmap (bcC φ₀ C) gC₀ j) ∈ Ideal.span (Set.range (gmap (bcC φ₁ C) gC₁))) ∧
    (∀ i, MvPolynomial.bind₁ vC (gmap (bcC φ₁ C) gC₁ i) ∈ Ideal.span (Set.range (gmap (bcC φ₀ C) gC₀))) ∧
    (∀ i, MvPolynomial.bind₁ uC (vC i) - MvPolynomial.X i ∈ Ideal.span (Set.range (gmap (bcC φ₁ C) gC₁))) ∧
    (∀ j, MvPolynomial.bind₁ vC (uC j) - MvPolynomial.X j ∈ Ideal.span (Set.range (gmap (bcC φ₀ C) gC₀))))

/-- The overlap isomorphism between the two presentations over `R' ⊗ N`. -/
def isoN : Pres (gmap (bcS R' φ₁) (gmap (tsC σ B₁) gC₁)) ≃ₐ[R' ⊗[A] N]
    Pres (gmap (tsC σ N) (gmap (bcC φ₀ C) gC₀)) :=
  (presCongr (gmap_tsC_bcC φ₁ σ gC₁).symm).trans
    (presIso (gmap (tsC σ N) (gmap (bcC φ₁ C) gC₁)) (gmap (tsC σ N) (gmap (bcC φ₀ C) gC₀))
      (fun k => MvPolynomial.map (tsC σ N) (uC k)) (fun k => MvPolynomial.map (tsC σ N) (vC k))
      (subst_map (tsC σ N) (gmap (bcC φ₁ C) gC₁) (gmap (bcC φ₀ C) gC₀) uC vC H.1 H.2.1 H.2.2.1 H.2.2.2).1
      (subst_map (tsC σ N) (gmap (bcC φ₁ C) gC₁) (gmap (bcC φ₀ C) gC₀) uC vC H.1 H.2.1 H.2.2.1 H.2.2.2).2.1
      (subst_map (tsC σ N) (gmap (bcC φ₁ C) gC₁) (gmap (bcC φ₀ C) gC₀) uC vC H.1 H.2.1 H.2.2.1 H.2.2.2).2.2.1
      (subst_map (tsC σ N) (gmap (bcC φ₁ C) gC₁) (gmap (bcC φ₀ C) gC₀) uC vC H.1 H.2.1 H.2.2.1 H.2.2.2).2.2.2)

/-- The overlap map of chart 1 over `R'`. -/
def psi1 : Pres (gmap (tsC σ B₁) gC₁) →+* Pres (gmap (tsC σ N) (gmap (bcC φ₀ C) gC₀)) :=
  ((isoN φ₀ φ₁ σ gC₀ gC₁ uC vC H).toRingEquiv : _ →+* _).comp (presMap (bcS R' φ₁) (gmap (tsC σ B₁) gC₁))

variable {G Q : Type u} [CommRing G] [CommRing Q]

theorem ctheta0 (θ₀ : Pres (gmap (tsC σ B₀) gC₀) →+* G) (θN : Pres (gmap (tsC σ N) (gmap (bcC φ₀ C) gC₀)) →+* Q)
    (p : G →+* Q)
    (hc : ∀ x, p (θ₀ (algebraMap (R' ⊗[A] B₀) _ x)) = θN (algebraMap (R' ⊗[A] N) _ (bcS R' φ₀ x)))
    (hX : ∀ j, p (θ₀ (Ideal.Quotient.mk _ (MvPolynomial.X j))) = θN (Ideal.Quotient.mk _ (MvPolynomial.X j))) :
    p.comp θ₀ = θN.comp (psi0 φ₀ σ gC₀) :=
  pres_ringHom_ext _ _ (fun a => by rw [RingHom.comp_apply, RingHom.comp_apply, psi0_alg]; exact hc a)
    (fun j => by rw [RingHom.comp_apply, RingHom.comp_apply, psi0_X]; exact hX j)

end Psi

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Z3P1b =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 4 (G-a): the transition `t s = 1` on the overlap of the two charts of `P¹_K`

* `x01 = X₀ X₁`, `tr0`, `tr1`: the restrictions `K[X₀,X₁]_(Xᵢ) → K[X₀,X₁]_(X₀X₁)` (Mathlib `awayMap`);
  `tr_mul`: `tr0 (X₁/X₀) * tr1 (X₀/X₁) = 1`.
* `c0 = Spec tr0 ≫ ch 0`, `c1 = Spec tr1 ≫ ch 1`, `c0_eq_c1` (both are `Proj.awayι (X₀X₁)`), `top_le_c0`.
* `appLE_injective_of_eq`: for an open immersion `f` with image `W`, `f.appLE W ⊤` is injective.
* **`coord_mul_coord`**: `coord 0 1 |_W * coord 1 0 |_W = 1` on `W = chU 0 ⊓ chU 1`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K]

/-- **The transition**: `(X₁/X₀) · (X₀/X₁) = 1` on `D₊(X₀) ⊓ D₊(X₁)`. -/
theorem coord_mul_coord :
    (Proj (gr K)).presheaf.map (homOfLE inf_le_left : chU K 0 ⊓ chU K 1 ⟶ chU K 0).op (coord K 0 1) *
      (Proj (gr K)).presheaf.map (homOfLE inf_le_right : chU K 0 ⊓ chU K 1 ⟶ chU K 1).op (coord K 1 0) = 1 := by
  apply appLE_injective_of_eq (c0 K) (image_c0 K) (top_le_c0 K)
  have h0 := ConcreteCategory.congr_hom (res0 K) (Away.isLocalizationElem (x_mem K 0) (x_mem K 1))
  have h1 := ConcreteCategory.congr_hom (res1 K) (Away.isLocalizationElem (x_mem K 1) (x_mem K 0))
  simp only [CategoryTheory.comp_apply] at h0 h1
  rw [map_mul, map_one, coord, coord, h0, h1, ← map_mul]
  convert map_one (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of (Away (gr K) (x01 K)))).inv) using 2
  exact tr_mul K

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_Z3Y =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 7 (G-b on `Y`): two-chart data of a finite `Y ⟶ P¹_V`

For `π : Y ⟶ P¹_V` (`V` affine):
* `isAffineOpen_Qc`, `isAffineOpen_Yc`: the charts `Qᵢ` of `P¹_V` and `Yᵢ = π⁻¹ Qᵢ` are affine;
* `σY i j : Γ(V)[X] → Γ(Y, Yᵢ)` (`X ↦ π^*(Xⱼ/Xᵢ)`), **`finite_σY`** (`π` finite);
* `pull_res` (restriction commutes with pullback), **`basicOpen_tY`**, **`basicOpen_sY`**: `D(t) = D(s) = Y₀ ⊓ Y₁`;
* **`trans_Y`**: `t|_{Y₀₁} · s|_{Y₀₁} = 1`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace MvPolynomial HomogeneousLocalization
open RamanujanPetersson.EtCompact

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K))

variable {Y : Scheme.{u}} (π : Y ⟶ PV K gV)

/-- **The transition on `Y`**: `t|_{Y₀₁} · s|_{Y₀₁} = 1`. -/
theorem trans_Y :
    Y.presheaf.map (homOfLE inf_le_left : Yc K gV π 0 ⊓ Yc K gV π 1 ⟶ Yc K gV π 0).op
        (π.app (Qc K gV 0) (tc K gV 0 1)) *
      Y.presheaf.map (homOfLE inf_le_right : Yc K gV π 0 ⊓ Yc K gV π 1 ⟶ Yc K gV π 1).op
        (π.app (Qc K gV 1) (tc K gV 1 0)) = 1 := by
  have e0 := pull_res (π ≫ pr K gV) (inf_le_left : chU K 0 ⊓ chU K 1 ≤ chU K 0)
    ((Scheme.Hom.preimage_inf (π ≫ pr K gV)).le.trans inf_le_left) (coord K 0 1)
  have e1 := pull_res (π ≫ pr K gV) (inf_le_right : chU K 0 ⊓ chU K 1 ≤ chU K 1)
    ((Scheme.Hom.preimage_inf (π ≫ pr K gV)).le.trans inf_le_right) (coord K 1 0)
  have := congrArg₂ (· * ·) e0 e1
  simp only at this
  rw [← map_mul, coord_mul_coord, map_one] at this
  exact this

end RamanujanPetersson.EtPBC.Z3

end

end

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

/-- **Restriction along an etale map preserves injective objects.** -/
instance res_preservesInjectiveObjects : (res e Λ).PreservesInjectiveObjects where
  injective_obj {I} hI := by
    have hF : ∀ y : X, Injective ((res e Λ).obj
        ((geomPtAt y).point.skyscraperSheaf (Cech.godJ Λ I y))) := fun y =>
      injective_res_sky e (geomPtAt y) _
    have hP : Injective ((res e Λ).obj (Cech.god Λ I)) :=
      Injective.of_iso (PreservesProduct.iso (res e Λ)
        (fun y : X => (geomPtAt y).point.skyscraperSheaf (Cech.godJ Λ I y))).symm inferInstance
    let r : Cech.god Λ I ⟶ I := Injective.factorThru (𝟙 I) (Cech.godι Λ I)
    have hr : Cech.godι Λ I ≫ r = 𝟙 I := Injective.comp_factorThru _ _
    refine ⟨fun {A B} g f _ => ?_⟩
    obtain ⟨h, hh⟩ := Injective.factors (g ≫ (res e Λ).map (Cech.godι Λ I)) f
    refine ⟨h ≫ (res e Λ).map r, ?_⟩
    rw [← Category.assoc, hh, Category.assoc, ← CategoryTheory.Functor.map_comp, hr, CategoryTheory.Functor.map_id,
      Category.comp_id]

end RamanujanPetersson.EtSheaves.LshEt

end

end

-- ===== S4.Def_RP_EtPBC_A_O2N1a =====
section

/-!
# S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`

For an etale `g : U ⟶ X` and `y : U` (generalizing `GalTr`, which treats open immersions):
* `eE g y`: the geometric points `ȳ ≫ g` and `(g y)‾` are isomorphic (`κ(y)/κ(g y)` is finite separable, so
  `κ(y)^sep` is a separable closure of `κ(g y)`); `sepE g y : κ(g y)^sep ≃ κ(y)^sep`;
* `galTrE g y : Gal y →* Gal (g y)` (conjugation by `sepE`, `galTrE_left`);
* `resTrIsoE g y Λ F : (g^* F)_ȳ ≅ F_(g y)‾`, natural (`resTrIsoE_natural`) and **Galois equivariant**
  (`galRep_resTrE`: `galRep (g^* F) y σ` corresponds to `galRep F (g y) (galTrE σ)`);
* `unitRes g Λ : Λ_U ⟶ g^* Λ_X` (the section `1` goes to the restriction of `1`), `resTrIsoE_unitRes`
  (`1 ↦ 1` on stalks), **`isIso_unitRes`**.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.GalTr
  RamanujanPetersson.EtCompact.GGerm RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.GenAlg

universe u

variable {U X : Scheme.{u}} (g : U ⟶ X) (y : U)

variable [Etale g]

variable (Λ : Type u) [CommRing Λ]

/-! ### `Λ_U ⟶ g^* Λ_X` -/

/-- **`Λ_U ⟶ g^* Λ_X` is an isomorphism.** -/
theorem isIso_unitRes : IsIso (unitRes g Λ) := by
  rw [isIso_iff_stalk]
  intro x
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun v v' h => ?_, fun w => ?_⟩
  · change (((geomPtAt x).stalkF Λ).map (unitRes g Λ)).hom v =
      (((geomPtAt x).stalkF Λ).map (unitRes g Λ)).hom v' at h
    have hv := eq_smul_oneStalk x v
    have hv' := eq_smul_oneStalk x v'
    have h1 := unitRes_coord g Λ x ((constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).hom.hom v)
    have h2 := unitRes_coord g Λ x ((constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).hom.hom v')
    rw [← hv] at h1
    rw [← hv', ← h] at h2
    have hc := h1.symm.trans h2
    rw [hv, hv', hc]
  · refine ⟨(constStalkIso Λ (geomPtAt (g x)) (ModuleCat.of Λ Λ)).hom.hom
      ((resTrIsoE g x Λ (unitSh Λ X)).hom.hom w) • oneStalk Λ x, ?_⟩
    change (((geomPtAt x).stalkF Λ).map (unitRes g Λ)).hom _ = w
    rw [map_smul, unitRes_oneStalk, ← map_smul, ← eq_smul_oneStalk (g x)]
    exact congrArg (fun φ => ModuleCat.Hom.hom φ w) (resTrIsoE g x Λ (unitSh Λ X)).hom_inv_id

end RamanujanPetersson.EtCompact.GalTrE

end

end


