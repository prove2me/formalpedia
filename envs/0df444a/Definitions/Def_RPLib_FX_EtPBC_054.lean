-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_054
-- name    : RPLib_FX_EtPBC_054
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:27:02.261511+00:00
-- url     : https://prove2.me/theorems/ce8f658b-b446-597a-9261-4ffc07686518
-- title:
--   Proper base change for the projective line, library file 054
-- statement:
--   File 054 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovFil1`: S4-EtPBC-A, R4-T2 (A2c-1d): overlap relations with entries in `p^j` split into chart relations
--   * `S4.Def_RP_EtPBC_A_CovAs5c`: S4-EtPBC-A, R4-T2 (A3 assembly, As5c): one chart descends to a f.g. subalgebra
--   * `S4.Def_RP_EtPBC_A_DescG4`: S4-EtPBC-A, R4-T1d (part 1): the sheets `V ⟶ U₀`
--   * `S4.Def_RP_EtPBC_A_O2Sh2`: S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree
--   * `S4.Def_RP_EtPBC_A_O2Gl2g`: S4-EtPBC-A, O2 GLOB (O2Gl2g): stage S4, the data `e`, `g`, `hHp`, `hHq` of `uk_diff` (pure algebra)
--   * `S4.Def_RP_EtPBC_A_O2Gl2h`: S4-EtPBC-A, O2 GLOB (O2Gl2h): stage S4 on the charts, the data `e`, `g`, `hHp`, `hHq` of `uk_diff`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_036
import Definitions.Def_RPLib_FX_EtPBC_043

/-!
# Proper base change for the projective line, library file 054

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovFil1`: S4-EtPBC-A, R4-T2 (A2c-1d): overlap relations with entries in `p^j` split into chart relations
* `S4.Def_RP_EtPBC_A_CovAs5c`: S4-EtPBC-A, R4-T2 (A3 assembly, As5c): one chart descends to a f.g. subalgebra
* `S4.Def_RP_EtPBC_A_DescG4`: S4-EtPBC-A, R4-T1d (part 1): the sheets `V ⟶ U₀`
* `S4.Def_RP_EtPBC_A_O2Sh2`: S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree
* `S4.Def_RP_EtPBC_A_O2Gl2g`: S4-EtPBC-A, O2 GLOB (O2Gl2g): stage S4, the data `e`, `g`, `hHp`, `hHq` of `uk_diff` (pure algebra)
* `S4.Def_RP_EtPBC_A_O2Gl2h`: S4-EtPBC-A, O2 GLOB (O2Gl2h): stage S4 on the charts, the data `e`, `g`, `hHp`, `hHq` of `uk_diff`
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_CovFil1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-1d): overlap relations with entries in `p^j` split into chart relations

For a level-`k` cover `C` (charts `Bᵢ ⧸ Jᵢ^(k+1)`, `Jᵢ = p Bᵢ`):
* `decomp_succ`: an element of `p^(j+1) B` is `∑ αᵢ yᵢ` with `yᵢ ∈ p^j B`;
* `lψθ₀`, `lψθ₁`, `mem_lι₀`, `mem_lι₁`: bookkeeping for the level-`k` charts;
* `chart0_decomp`: a chart-0 relation with entries in `p^j` is `∑ cₗ ρ0ₗ + v` (base relations, flatness);
* `split_rel`: such a decomposition splits on the two charts (uniform `H¹` vanishing);
* **`lift_rel`**: an overlap relation `w` with entries in `p^j` is `ψ₀ a - u^d ψ₁ b` with `a`, `b` chart relations
  with entries in `p^j`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Lv

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁) (p : Ideal R)

/-- **Overlap relations with entries in `p^j` split into chart relations** (`j ≤ k`, `d ≥ d₀ + F`). -/
theorem lift_rel [IsNoetherianRing R] {g : ℕ} (α : Fin g → R) (hα : p = Ideal.span (Set.range α))
    (hts : φ₀ t₀ * φ₁ t₁ = 1) (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁)
    {k : ℕ} (C : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k) (d d₀ F : ℕ) (hd : d₀ + F ≤ d)
    (hspl : ∀ d', d₀ ≤ d' → ∀ n, ∀ z ∈ (p ^ n).map (C.ψ₀.comp (lι₀ ιB₀ C)),
      C.Spl (lι₀ ιB₀ C) (lι₁ ιB₁ C) (p ^ n) d' z)
    {j n' : ℕ} (hj : j ≤ k) (hn' : n' ≤ j) {L : ℕ} (ρ0 : Fin L → Fin g → B₀) (ρ1 : Fin L → Fin g → B₁)
    (f : Fin L → ℕ) (hf : ∀ l, f l ≤ F) (hρ0 : ∀ l, ρ0 l ∈ RelV p α ιB₀ n')
    (hρ1 : ∀ l, ρ1 l ∈ RelV p α ιB₁ n') (hρ : ∀ l i, φ₀ (ρ0 l i) = φ₀ t₀ ^ f l * φ₁ (ρ1 l i))
    (hgen : ∀ w ∈ RelV p α ιB₀ j, ∃ β : Fin L → B₀, (∀ l, β l ∈ (p ^ (j - n')).map ιB₀) ∧
      w = ∑ l, β l • ρ0 l)
    (w : Fin g → C.E) (hw : ∀ i, w i ∈ (p ^ j).map (C.ψ₀.comp (lι₀ ιB₀ C)))
    (hμ : ∑ i, C.ψ₀ (lι₀ ιB₀ C (α i)) * w i = 0) :
    ∃ (a : Fin g → C.E₀) (b : Fin g → C.E₁), (∀ i, a i ∈ (p ^ j).map (lι₀ ιB₀ C)) ∧
      (∀ i, b i ∈ (p ^ j).map (lι₁ ιB₁ C)) ∧ ∑ i, lι₀ ιB₀ C (α i) * a i = 0 ∧
      ∑ i, lι₁ ιB₁ C (α i) * b i = 0 ∧ ∀ i, w i = C.ψ₀ (a i) - C.u ^ d * C.ψ₁ (b i) := by
  have hαp : ∀ i, α i ∈ p := fun i => by
    rw [hα]
    exact Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨e, w', hw', hμ', hww'⟩ := TwoCov.to_chart0 (ι₀ := lι₀ ιB₀ C) (lhv hts C) (p ^ j) α w hw hμ
  obtain ⟨c, v, hc, hv, hwv⟩ := chart0_decomp ιB₀ p α hα hJ₀ C hj ρ0 hgen w' hw' hμ'
  exact split_rel ιB₀ ιB₁ p α hαp hts hJ₀ hJ₁ C d d₀ F hd hspl hj hn' ρ0 ρ1 f hf hρ0 hρ1 hρ e w c v hc hv
    (fun i => by rw [hww' i, hwv i])

end Lv

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs5c =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As5c): one chart descends to a f.g. subalgebra

**`desc_chart`**: if a square system `gC` over `C₀ ⊗ B` becomes etale-and-finite presented over `S ⊗ B` (witnesses
`hJ`, `hF` for `gmap (tvC B C₀) gC`), then the witnesses already exist over `C ⊗ B` for a f.g. `C ≥ C₀` (for the
system `gmap (tiC B h) gC`). Helpers `gmap_tvC_tiC`, `gmap_tiC_tiC`, `polymap_tvC_tiC`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open TensorProduct

universe u

section Chart

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S]
  {B : Type u} [CommRing B] [Algebra A B]

set_option maxHeartbeats 400000 in
/-- **The etale and finite witnesses of one chart descend to a f.g. subalgebra.** -/
theorem desc_chart [Module.Flat A S] {r : ℕ} (C₀ : Subalgebra A S) (hC₀ : C₀.FG)
    (gC : Fin r → MvPolynomial (Fin r) (C₀ ⊗[A] B))
    (hJ : ∃ w, jdet (gmap (tvC B C₀) gC) * w - 1 ∈ Ideal.span (Set.range (gmap (tvC B C₀) gC)))
    (hF : ∀ j, ∃ q : Polynomial (S ⊗[A] B), q.Monic ∧
      Polynomial.aeval (MvPolynomial.X j) q ∈ Ideal.span (Set.range (gmap (tvC B C₀) gC))) :
    ∃ (C : Subalgebra A S) (h : C₀ ≤ C), C.FG ∧
      (∃ w, jdet (gmap (tiC B h) gC) * w - 1 ∈ Ideal.span (Set.range (gmap (tiC B h) gC))) ∧
      (∀ j, ∃ q : Polynomial (C ⊗[A] B), q.Monic ∧
        Polynomial.aeval (MvPolynomial.X j) q ∈ Ideal.span (Set.range (gmap (tiC B h) gC))) := by
  classical
  obtain ⟨w, hw⟩ := hJ
  choose q hqm hq using hF
  obtain ⟨C₁, hC₁, hwl⟩ := exists_lift_polys (B := B) (fun _ : Unit => w)
  obtain ⟨wC, hwC⟩ := hwl ()
  obtain ⟨C₂, hC₂, hql⟩ := exists_lift_monics (B := B) q hqm
  choose qC hqCm hqC using hql
  have h₀ : C₀ ≤ C₀ ⊔ C₁ ⊔ C₂ := le_sup_left.trans le_sup_left
  have h₁ : C₁ ≤ C₀ ⊔ C₁ ⊔ C₂ := le_sup_right.trans le_sup_left
  have h₂ : C₂ ≤ C₀ ⊔ C₁ ⊔ C₂ := le_sup_right
  have hD : (C₀ ⊔ C₁ ⊔ C₂).FG := (hC₀.sup hC₁).sup hC₂
  have hg := gmap_tvC_tiC (B := B) h₀ gC
  have hjd : MvPolynomial.map (tvC B (C₀ ⊔ C₁ ⊔ C₂)) (jdet (gmap (tiC B h₀) gC)) =
      jdet (gmap (tvC B C₀) gC) := by
    rw [← jdet_map, hg]
  obtain ⟨C, h, hC, hz⟩ := desc_mem (B := B) (C₀ ⊔ C₁ ⊔ C₂) hD (gmap (tiC B h₀) gC)
    (Sum.elim (fun _ : Unit => jdet (gmap (tiC B h₀) gC) * MvPolynomial.map (tiC B h₁) wC - 1)
      (fun j : Fin r => Polynomial.aeval (MvPolynomial.X j) ((qC j).map (tiC B h₂))))
    (by
      rintro (⟨⟩ | j)
      · show MvPolynomial.map (tvC B (C₀ ⊔ C₁ ⊔ C₂))
            (jdet (gmap (tiC B h₀) gC) * MvPolynomial.map (tiC B h₁) wC - 1) ∈
          Ideal.span (Set.range (gmap (tvC B (C₀ ⊔ C₁ ⊔ C₂)) (gmap (tiC B h₀) gC)))
        rw [map_sub, map_mul, map_one, map_tvC_tiC, hwC, hjd, hg]
        exact hw
      · show MvPolynomial.map (tvC B (C₀ ⊔ C₁ ⊔ C₂))
            (Polynomial.aeval (MvPolynomial.X j) ((qC j).map (tiC B h₂))) ∈
          Ideal.span (Set.range (gmap (tvC B (C₀ ⊔ C₁ ⊔ C₂)) (gmap (tiC B h₀) gC)))
        rw [← aeval_X_map, polymap_tvC_tiC, hqC, hg]
        exact hq j)
  refine ⟨C, h₀.trans h, hC, ⟨MvPolynomial.map (tiC B h) (MvPolynomial.map (tiC B h₁) wC), ?_⟩, fun j =>
    ⟨((qC j).map (tiC B h₂)).map (tiC B h), ((hqCm j).map _).map _, ?_⟩⟩
  · have e' : MvPolynomial.map (tiC B h)
        (jdet (gmap (tiC B h₀) gC) * MvPolynomial.map (tiC B h₁) wC - 1) ∈
        Ideal.span (Set.range (gmap (tiC B h) (gmap (tiC B h₀) gC))) := hz (Sum.inl ())
    rw [← gmap_tiC_tiC h₀ h, jdet_map]
    rwa [map_sub, map_mul, map_one] at e'
  · have e' : MvPolynomial.map (tiC B h)
        (Polynomial.aeval (MvPolynomial.X j) ((qC j).map (tiC B h₂))) ∈
        Ideal.span (Set.range (gmap (tiC B h) (gmap (tiC B h₀) gC))) := hz (Sum.inr j)
    rw [← gmap_tiC_tiC h₀ h, aeval_X_map]
    exact e'

end Chart

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_DescG4 =====
section

/-!
# S4-EtPBC-A, R4-T1d (part 1): the sheets `V ⟶ U₀`

For `ν : M`, the evaluations `evR U ν : B(U) → CU V U`, `f ↦ f ν`, glue (along the affine opens of `X`, as in
Mathlib's `Scheme.Hom.toNormalization`) to the **sheet** `sheet ν : V ⟶ U₀` over `X`:
`ι_sheet` (its restriction to `V.hom⁻¹ U`), `sheet_toU0`, and `sheetE ν : V ⟶ U0E` in `X.Etale`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescG

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.DescA TensorProduct

universe u

section Sheet

variable {X : Scheme.{u}} (V : X.Etale) [IsAffineHom V.hom] [Surjective V.hom] {Λ : Type u} [CommRing Λ]
  {M : ModuleCat.{u} Λ} [Fintype M] [DecidableEq M] {E Q : EtSh Λ X} (a : constSh Λ X M ⟶ E) (b : E ⟶ Q)
  (hab : a ≫ b = 0) (hS : (ShortComplex.mk a b hab).ShortExact) (e : E.obj.obj (op V))
  (he : ∀ (W : X.Etale) (w₁ w₂ : W ⟶ V), (b.hom.app (op W)).hom ((E.obj.map w₁.op).hom e) =
    (b.hom.app (op W)).hom ((E.obj.map w₂.op).hom e))

/-- The chart maps of the `ν`-th sheet, on the pulled-back directed cover of `V`. -/
def sheetG (ν : M) (U : ((Scheme.AffineZariskiSite.directedCover X).pullback₁ (vh V)).I₀) :
    ((Scheme.AffineZariskiSite.directedCover X).pullback₁ (vh V)).X U ⟶ U0 V a b hab hS e he :=
  (pullbackRestrictIsoRestrict (vh V) _).hom ≫ (vh V ⁻¹ᵁ U.1).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (evR V a b hab hS e he U ν)) ≫
    (glD (coequifibered_alphaU V a b hab hS e he)).cover.f U

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem sheetG_compat (ν : M) {U U' : ((Scheme.AffineZariskiSite.directedCover X).pullback₁ (vh V)).I₀}
    (i : U ⟶ U') : Scheme.Cover.trans ((Scheme.AffineZariskiSite.directedCover X).pullback₁ (vh V)) i ≫
      sheetG V a b hab hS e he ν U' = sheetG V a b hab hS e he ν U := by
  unfold sheetG
  have : (pullbackRestrictIsoRestrict (vh V) U.1).inv ≫
      Scheme.Cover.trans ((Scheme.AffineZariskiSite.directedCover X).pullback₁ (vh V)) i ≫
      (pullbackRestrictIsoRestrict (vh V) U'.1).hom = V.left.homOfLE
        ((vh V).preimage_mono (Scheme.AffineZariskiSite.toOpens_mono i.1.1)) := by
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp +instances [Scheme.Cover.trans, Scheme.Cover.locallyDirectedPullbackCover]
  rw [← Iso.inv_comp_eq, reassoc_of% this, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc,
    ← Spec.map_comp_assoc]
  dsimp
  rw [← colimit.w (glD (coequifibered_alphaU V a b hab hS e he)).functor i]
  dsimp [glD, Scheme.AffineZariskiSite.relativeGluingData]
  rw [← Spec.map_comp_assoc]
  rfl

/-- **The `ν`-th sheet** `V ⟶ U₀`. -/
def sheet (ν : M) : V.left ⟶ U0 V a b hab hS e he :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((Scheme.AffineZariskiSite.directedCover X).pullback₁ (vh V)) (sheetG V a b hab hS e he ν)
    (sheetG_compat V a b hab hS e he ν)

theorem sheet_f (ν : M) (U : ((Scheme.AffineZariskiSite.directedCover X).pullback₁ (vh V)).I₀) :
    ((Scheme.AffineZariskiSite.directedCover X).pullback₁ (vh V)).f U ≫ sheet V a b hab hS e he ν =
      sheetG V a b hab hS e he ν U :=
  Scheme.OpenCover.map_glueMorphismsOfLocallyDirected _ _ _ U

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
theorem ι_sheet' (ν : M) (U : X.affineOpens) :
    (vh V ⁻¹ᵁ U.1).ι ≫ sheet V a b hab hS e he ν = (vh V ⁻¹ᵁ U.1).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (evR V a b hab hS e he U ν)) ≫
        (glD (coequifibered_alphaU V a b hab hS e he)).cover.f U := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict (vh V) U.1).hom, ← Category.assoc]
  trans ((Scheme.AffineZariskiSite.directedCover X).pullback₁ (vh V)).f U ≫ sheet V a b hab hS e he ν
  · congr 1
    simp
  exact sheet_f V a b hab hS e he ν U

@[reassoc]
theorem ι_sheet (ν : M) (U : X.affineOpens) :
    (V.hom ⁻¹ᵁ U.1).ι ≫ sheet V a b hab hS e he ν = (V.hom ⁻¹ᵁ U.1).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (evR V a b hab hS e he U ν)) ≫
        (glD (coequifibered_alphaU V a b hab hS e he)).cover.f U :=
  ι_sheet' V a b hab hS e he ν U

end Sheet

end RamanujanPetersson.EtPBC.DescG

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Sh2 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree

* `dg W`: the diagonal of `W ×_P W` (clopen: `isClopen_dg`); `dsec Λ W`: its indicator section of `Λ_W`;
* `shapφ Λ W : Λ[W] ⟶ π_* Λ_W` is the map given by `dsec` (`shapφ_taut`);
* `cval_S`: values of `Σ_a l_a · τ_a^* dsec` along a sheet;
* **`isIso_shapφ`**, **`shapIso`**: `shapφ` is an isomorphism (stalkwise: `stalk_inj`, `stalk_surj`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtShap

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtTr

universe u

variable {P : Scheme.{u}}

section Dg

end Dg

section Iso

variable (Λ : Type u) [CommRing Λ] (W : P.Etale) [IsSeparated W.hom]

variable [QuasiCompact W.hom]

/-- **`shapφ` is injective on stalks.** -/
theorem stalk_inj (x : P) : Function.Injective (((geomPtAt x).stalkF Λ).map (shapφ Λ W)).hom := by
  classical
  have : Finite ((geomPtAt x).point.fiber.obj W) := finite_fiber W x
  have := Fintype.ofFinite ((geomPtAt x).point.fiber.obj W)
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  obtain ⟨l, rfl⟩ := freeLin_surjective W x y
  obtain ⟨T, t, τ, -, hτ, -⟩ := exists_split_inj ⊤ W x (by simp)
  rw [stalk_shapφ_freeLin, ← germ_S Λ W x τ t hτ l] at hy
  obtain ⟨V, g, b, hb, hS⟩ := exists_nbhd_of_germ_eq_zero ((push W.hom Λ).obj (unitSh Λ W.left)) x t _ hy
  have hl : l = 0 := by
    ext q
    have h0 := cval_S Λ W τ l g (g ≫ τ q) (fpt x b) q (fun a => agr_iff W x τ t hτ g b hb a q)
    have hS' : ((unitSh Λ W.left).obj.map ((etPull W.hom).map g).op).hom
        (∑ a, l a • ((unitSh Λ W.left).obj.map ((etPull W.hom).map (τ a)).op).hom (dsec Λ W)) = 0 := hS
    rw [hS', map_zero] at h0
    exact h0.symm.trans (cval_zero _)
  rw [hl, map_zero]

end Iso

end RamanujanPetersson.EtPBC.EtShap

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2g =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2g): stage S4, the data `e`, `g`, `hHp`, `hHq` of `uk_diff` (pure algebra)

GLOB/REL PLAN v1, stage S4 (ring level, abstract rings). `G₂ = G₁[1/s]` (the Zariski shrink `W₂ → W₁`), `B₁ → G₁`,
`B₂ → G₂`, `ι : B₁ → B₂` compatible, `z ∈ Π_q Frac(G₁ ⧸ q)` integral over `B₁`, `μH T₂^N = x₁` with
`x₁ = T₁^N ũ (1 - T₁ z)` (`ũ = (u₁ on p₁, 1 elsewhere)`):
* `eq_comap_of_le_comap`: below a minimal prime of a localization lies exactly one minimal prime (its contraction);
* `exists_psi`, `psi_unique`, `psi_update`, `psi_update_ne`: the maps `Frac(G₁ ⧸ q₁) → Frac(G₂ ⧸ q)`;
* `exists_monic_he`: one monic `g ∈ B₂[X]` of positive degree killing every `-Ψ_q (z_{q₁})`;
* **`exists_S4_gen`**: `e q := -Ψ_q (z_{q₁ q})` and `g` with `he`, `hHp` (any compatible `Ψ`), `hHq`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

section Below

end Below

section Psi

end Psi

section Monic

end Monic

section S4Gen

variable {G₁ G₂ B₁ B₂ : Type} [CommRing G₁] [CommRing G₂] [CommRing B₁] [CommRing B₂] [Nontrivial B₂]
  [Algebra G₁ G₂] (s : G₁) [IsLocalization.Away s G₂] [DecidableEq (minimalPrimes G₁)]
  (bW₁ : B₁ →+* G₁) (bW₂ : B₂ →+* G₂) (ι : B₁ →+* B₂) (hι : ∀ b, algebraMap G₁ G₂ (bW₁ b) = bW₂ (ι b))
  [Algebra B₁ (PiQ G₁)] (halg : ∀ b, algebraMap B₁ (PiQ G₁) b = toPiQ (bW₁ b))

include s hι halg in
/-- **Stage S4 (ring level)**: `e`, `g`, `he`, `hHp`, `hHq` of `uk_diff` from `μH T₂^N = x₁ = T₁^N ũ (1 - T₁ z)`. -/
theorem exists_S4_gen (p₁ : minimalPrimes G₁) (u₁ : FractionRing (G₁ ⧸ (p₁ : Ideal G₁))) {T₁ x₁ : G₁} {T₂ μH : G₂}
    {z : PiQ G₁} {N : ℕ} (hT : algebraMap G₁ G₂ T₁ = T₂) (hT₂ : ∀ q : minimalPrimes G₂, toPiQ T₂ q ≠ 0)
    (hH : μH * T₂ ^ N = algebraMap G₁ G₂ x₁)
    (hy : toPiQ x₁ = toPiQ T₁ ^ N * Function.update (1 : PiQ G₁) p₁ u₁ * (1 - toPiQ T₁ * z))
    (hz : IsIntegral B₁ z) :
    ∃ e : ∀ q : minimalPrimes G₂, FractionRing (G₂ ⧸ (q : Ideal G₂)), ∃ g : B₂[X], g.Monic ∧ 0 < g.natDegree ∧
      (∀ q : minimalPrimes G₂, g.eval₂ ((algebraMap _ (FractionRing (G₂ ⧸ (q : Ideal G₂)))).comp
        ((Ideal.Quotient.mk (q : Ideal G₂)).comp bW₂)) (e q) = 0) ∧
      ∀ p₂ : minimalPrimes G₂, (p₁ : Ideal G₁) ≤ (p₂ : Ideal G₂).comap (algebraMap G₁ G₂) →
        (∀ Ψ : FractionRing (G₁ ⧸ (p₁ : Ideal G₁)) →+* FractionRing (G₂ ⧸ (p₂ : Ideal G₂)),
          (∀ a : G₁, Ψ (algebraMap _ _ (Ideal.Quotient.mk (p₁ : Ideal G₁) a)) =
            algebraMap _ _ (Ideal.Quotient.mk (p₂ : Ideal G₂) (algebraMap G₁ G₂ a))) →
          algebraMap _ (FractionRing (G₂ ⧸ (p₂ : Ideal G₂))) (Ideal.Quotient.mk (p₂ : Ideal G₂) μH) =
            Ψ u₁ * (1 + algebraMap _ _ (Ideal.Quotient.mk (p₂ : Ideal G₂) T₂) * e p₂)) ∧
        ∀ q : minimalPrimes G₂, q ≠ p₂ →
          algebraMap _ (FractionRing (G₂ ⧸ (q : Ideal G₂))) (Ideal.Quotient.mk (q : Ideal G₂) μH) =
            1 + algebraMap _ _ (Ideal.Quotient.mk (q : Ideal G₂) T₂) * e q := by
  have hbelow : ∀ q : minimalPrimes G₂, ∃ q₁ : minimalPrimes G₁,
      (q₁ : Ideal G₁) = (q : Ideal G₂).comap (algebraMap G₁ G₂) := by
    intro q
    have : (q : Ideal G₂).IsPrime := q.2.1.1
    obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le
      (bot_le : (⊥ : Ideal G₁) ≤ (q : Ideal G₂).comap (algebraMap G₁ G₂))
    have : P.IsPrime := hP.1.1
    exact ⟨⟨P, hP⟩, eq_comap_of_le_comap (Submonoid.powers s) q.2 hPle⟩
  choose q₁ hq₁ using hbelow
  have hΨex : ∀ q : minimalPrimes G₂,
      ∃ Ψ : FractionRing (G₁ ⧸ (q₁ q : Ideal G₁)) →+* FractionRing (G₂ ⧸ (q : Ideal G₂)),
      ∀ a : G₁, Ψ (algebraMap _ _ (Ideal.Quotient.mk (q₁ q : Ideal G₁) a)) =
        algebraMap _ _ (Ideal.Quotient.mk (q : Ideal G₂) (algebraMap G₁ G₂ a)) := by
    intro q
    have : (q₁ q : Ideal G₁).IsPrime := (q₁ q).2.1.1
    have : (q : Ideal G₂).IsPrime := q.2.1.1
    exact exists_psi (algebraMap G₁ G₂) _ _ (hq₁ q).symm
  choose Ψ hΨ using hΨex
  have hval : ∀ q : minimalPrimes G₂,
      algebraMap _ (FractionRing (G₂ ⧸ (q : Ideal G₂))) (Ideal.Quotient.mk (q : Ideal G₂) μH) =
        Ψ q (Function.update (1 : PiQ G₁) p₁ u₁ (q₁ q)) *
          (1 + algebraMap _ _ (Ideal.Quotient.mk (q : Ideal G₂) T₂) * -Ψ q (z (q₁ q))) := by
    intro q
    have hTq : Ψ q (toPiQ T₁ (q₁ q)) =
        algebraMap _ (FractionRing (G₂ ⧸ (q : Ideal G₂))) (Ideal.Quotient.mk (q : Ideal G₂) T₂) := by
      rw [toPiQ_apply, hΨ q T₁, hT]
    have hT₂q : algebraMap _ (FractionRing (G₂ ⧸ (q : Ideal G₂))) (Ideal.Quotient.mk (q : Ideal G₂) T₂) ≠ 0 :=
      hT₂ q
    have hX : algebraMap _ (FractionRing (G₂ ⧸ (q : Ideal G₂))) (Ideal.Quotient.mk (q : Ideal G₂) μH) *
        algebraMap _ (FractionRing (G₂ ⧸ (q : Ideal G₂))) (Ideal.Quotient.mk (q : Ideal G₂) T₂) ^ N =
        Ψ q (toPiQ x₁ (q₁ q)) := by
      rw [toPiQ_apply, hΨ q x₁, ← hH, map_mul, map_mul, map_pow, map_pow]
    have e1 := congrFun hy (q₁ q)
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, Pi.one_apply] at e1
    exact frac_value (Ψ q) hTq hT₂q (hX.trans (congrArg (Ψ q) e1))
  have hβ : ∀ (q : minimalPrimes G₂) (b : B₁), Ψ q (algebraMap B₁ (PiQ G₁) b (q₁ q)) =
      ((algebraMap _ (FractionRing (G₂ ⧸ (q : Ideal G₂)))).comp ((Ideal.Quotient.mk (q : Ideal G₂)).comp bW₂)) (ι b) := by
    intro q b
    rw [halg]
    exact (hΨ q (bW₁ b)).trans (congrArg (fun x => algebraMap _ (FractionRing (G₂ ⧸ (q : Ideal G₂)))
      (Ideal.Quotient.mk (q : Ideal G₂) x)) (hι b))
  obtain ⟨g, hgm, hgd, hge⟩ := exists_monic_he (K := fun q : minimalPrimes G₂ => FractionRing (G₂ ⧸ (q : Ideal G₂)))
    q₁ Ψ ι (fun q => (algebraMap _ (FractionRing (G₂ ⧸ (q : Ideal G₂)))).comp
      ((Ideal.Quotient.mk (q : Ideal G₂)).comp bW₂)) hβ hz
  refine ⟨fun q => -Ψ q (z (q₁ q)), g, hgm, hgd, hge, fun p₂ hp₂ => ⟨fun Ψ' hΨ' => ?_, fun q hq => ?_⟩⟩
  · have : (p₁ : Ideal G₁).IsPrime := p₁.2.1.1
    have h1 : q₁ p₂ = p₁ :=
      Subtype.ext ((hq₁ p₂).trans (eq_comap_of_le_comap (Submonoid.powers s) p₂.2 hp₂).symm)
    refine (hval p₂).trans ?_
    rw [psi_update h1 (Ψ p₂) Ψ' (fun a => (hΨ p₂ a).trans (hΨ' a).symm) u₁]
  · have h1 : q₁ q ≠ p₁ := by
      intro h1
      have hle := hq₁ q
      rw [h1] at hle
      have : (p₁ : Ideal G₁).IsPrime := p₁.2.1.1
      exact hq (Subtype.ext (piece_eq_of_away s q.2 p₂.2 hle.le hp₂))
    refine (hval q).trans ?_
    rw [psi_update_ne h1, one_mul]

end S4Gen

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2h =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2h): stage S4 on the charts, the data `e`, `g`, `hHp`, `hHq` of `uk_diff`

GLOB/REL PLAN v1, stage S4. `d = d₂₁ ≫ d₀ : D₂ ⟶ D₁ ⟶ D_{g₀}` with `Γ(W₂) = Γ(W₁)[1/s]` along `d₂₁` (Zariski) and
`d₂₁.left = Spec.map ι`; `H · ρ(r)^N = ρ y` on `Y₁`, `(prdMap d₀)^* y = r^N ũ (1 - r z)` in `Π_q Frac(Γ(W₁) ⧸ q)`
(`ũ = (u₁ on p₁, 1 elsewhere)`, `z` integral over `B₁`):
* **`exists_S4`**: `e`, a monic `g ∈ B₂[X]` of positive degree with `g(e q) = 0` (`he`), and for the piece `p₂` over `p₁`:
  `m^* H = Ψ u₁ (1 + bK(φ₂ r) e p₂)` (`hHp`, any compatible `Ψ`), `m^* H = 1 + bK(φ₂ r) e q` for `q ≠ p₂` (`hHq`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section S4GenB

variable {G₁ G₂ B₁ B₂ : Type} [CommRing G₁] [CommRing G₂] [CommRing B₁] [CommRing B₂] [Nontrivial B₂]
  [DecidableEq (minimalPrimes G₁)]

/-- `exists_S4_gen` with the ring map `σ`, the piece maps `β q` and the kernel maps `κ q` as parameters, so that a
chart instance is a plain application (no destructuring on chart rings). -/
theorem exists_S4_genB (σ : G₁ →+* G₂) (s : G₁) (hloc : letI := σ.toAlgebra; IsLocalization.Away s G₂)
    (bW₁ : B₁ →+* G₁) (bW₂ : B₂ →+* G₂) (ι : B₁ →+* B₂) (hι : ∀ b, σ (bW₁ b) = bW₂ (ι b))
    [Algebra B₁ (PiQ G₁)] (halg : ∀ b, algebraMap B₁ (PiQ G₁) b = toPiQ (bW₁ b))
    (β : ∀ q : minimalPrimes G₂, B₂ →+* FractionRing (G₂ ⧸ q.1))
    (hβ : ∀ q b, β q b = algebraMap _ _ (Ideal.Quotient.mk q.1 (bW₂ b)))
    (κ : ∀ q : minimalPrimes G₂, G₁ →+* G₂ ⧸ q.1) (hκ : ∀ q, RingHom.ker (κ q) = Ideal.comap σ q.1)
    (p₁ : minimalPrimes G₁) (u₁ : FractionRing (G₁ ⧸ p₁.1)) {T₁ x₁ : G₁} {t₂ : B₂} {μH : G₂}
    {z : PiQ G₁} {N : ℕ} (hT : σ T₁ = bW₂ t₂) (hT₂ : ∀ q : minimalPrimes G₂, toPiQ (bW₂ t₂) q ≠ 0)
    (hH : μH * bW₂ t₂ ^ N = σ x₁)
    (hy : toPiQ x₁ = toPiQ T₁ ^ N * Function.update (1 : PiQ G₁) p₁ u₁ * (1 - toPiQ T₁ * z))
    (hz : IsIntegral B₁ z) :
    ∃ e : ∀ q : minimalPrimes G₂, FractionRing (G₂ ⧸ q.1), ∃ g : B₂[X], g.Monic ∧ 0 < g.natDegree ∧
      (∀ q, g.eval₂ (β q) (e q) = 0) ∧
      ∀ p₂ : minimalPrimes G₂, (p₁ : Ideal G₁) ≤ RingHom.ker (κ p₂) →
        (∀ Ψ : FractionRing (G₁ ⧸ p₁.1) →+* FractionRing (G₂ ⧸ p₂.1),
          (∀ a, Ψ (algebraMap _ _ (Ideal.Quotient.mk p₁.1 a)) = algebraMap _ _ (Ideal.Quotient.mk p₂.1 (σ a))) →
          algebraMap _ (FractionRing (G₂ ⧸ p₂.1)) (Ideal.Quotient.mk p₂.1 μH) = Ψ u₁ * (1 + β p₂ t₂ * e p₂)) ∧
        ∀ q, q ≠ p₂ → algebraMap _ (FractionRing (G₂ ⧸ q.1)) (Ideal.Quotient.mk q.1 μH) = 1 + β q t₂ * e q := by
  let _ := σ.toAlgebra
  have := hloc
  obtain ⟨e, g, hgm, hgd, hge, hp⟩ := exists_S4_gen s bW₁ bW₂ ι hι halg p₁ u₁ hT hT₂ hH hy hz
  refine ⟨e, g, hgm, hgd, fun q => ?_, fun p₂ hp₂ => ?_⟩
  · have hβ' : β q = (algebraMap _ _).comp ((Ideal.Quotient.mk q.1).comp bW₂) := RingHom.ext (hβ q)
    rw [hβ']
    exact hge q
  · have h2 := hp p₂ (hp₂.trans (hκ p₂).le)
    refine ⟨fun Ψ hΨ => ?_, fun q hq => ?_⟩
    · rw [hβ]
      exact h2.1 Ψ hΨ
    · rw [hβ]
      exact h2.2 q hq

end S4GenB

section S4

end S4

end RamanujanPetersson.EtPBC.EtKum

end

end


