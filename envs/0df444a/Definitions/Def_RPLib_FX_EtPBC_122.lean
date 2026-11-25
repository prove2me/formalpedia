-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_122
-- name    : RPLib_FX_EtPBC_122
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:22:14.351904+00:00
-- url     : https://prove2.me/theorems/247ba0b6-6051-5d49-8b10-aaee0aa32ef6
-- title:
--   Proper base change for the projective line, library file 122
-- statement:
--   File 122 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovLim5`: S4-EtPBC-A, R4-T2 (A2c-2f): multiplication by `T₀`, `T₁` on compatible families; completed generation
--   * `S4.Def_RP_EtPBC_A_CovAs3a`: S4-EtPBC-A, R4-T2 (A3 assembly, As3a): one bound `D` for the tower
--   * `S4.Def_RP_EtPBC_A_DescG5`: S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`
--   * `S4.Def_RP_EtPBC_A_O2Gl2h`: S4-EtPBC-A, O2 GLOB (O2Gl2h): stage S4 on the charts, the data `e`, `g`, `hHp`, `hHq` of `uk_diff`
--   * `S4.Def_RP_EtPBC_A_O2Rel2`: S4-EtPBC-A, O2 REL (O2R3a): the target term of the relation lies in `G`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_111

/-!
# Proper base change for the projective line, library file 122

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovLim5`: S4-EtPBC-A, R4-T2 (A2c-2f): multiplication by `T₀`, `T₁` on compatible families; completed generation
* `S4.Def_RP_EtPBC_A_CovAs3a`: S4-EtPBC-A, R4-T2 (A3 assembly, As3a): one bound `D` for the tower
* `S4.Def_RP_EtPBC_A_DescG5`: S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`
* `S4.Def_RP_EtPBC_A_O2Gl2h`: S4-EtPBC-A, O2 GLOB (O2Gl2h): stage S4 on the charts, the data `e`, `g`, `hHp`, `hHq` of `uk_diff`
* `S4.Def_RP_EtPBC_A_O2Rel2`: S4-EtPBC-A, O2 REL (O2R3a): the target term of the relation lies in `G`
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_CovLim5 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-2f): multiplication by `T₀`, `T₁` on compatible families; completed generation

* `mT₀`, `mT₁`: multiplication of a family by `T₀ = (1, s)` and `T₁ = (t, 1)`; `ρ₀_t`, `ρ₁_s`; `mT₀_mem`, `mT₁_mem`;
* **`gam_struct`**: finitely many `τⱼ ∈ Gam (e+1)` such that every `x ∈ Gam (e+2)` is
  `T₀ (∑ aⱼ τⱼ) + T₁ (∑ a'ⱼ τⱼ)` (`R` noetherian and `p`-precomplete, `H¹(O(e)) = 0` at level `0`).
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section T

end T

section Struct

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (p : Ideal R) {g : ℕ} (α : Fin g → R)

/-- **Completed generation with multiplication structure**: `Gam (e+2) = T₀ (R-span of τ) + T₁ (R-span of τ)`. -/
theorem gam_struct [IsNoetherianRing R] [IsPrecomplete p R] (hα : ∀ i, α i ∈ p) (hts : φ₀ t₀ * φ₁ t₁ = 1)
    (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite)
    (hB₁ : (eval₂RingHom ιB₁ t₁).Finite) (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (e : ℕ)
    (hspl : ∀ z : (C 0).E, ∃ (x₀ : (C 0).E₀) (x₁ : (C 0).E₁), z = (C 0).ψ₀ x₀ - (C 0).u ^ e * (C 0).ψ₁ x₁)
    (hs : ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) (e + 1)))
    (hfil : ∀ k, FilProp ιB₀ ιB₁ p α (C k) (e + 2)) :
    ∃ (r : ℕ) (τ : Fin r → (∀ k, (C k).E₀) × (∀ k, (C k).E₁)), (∀ j, τ j ∈ Gam C H (e + 1)) ∧
      ∀ x ∈ Gam C H (e + 2), ∃ a a' : Fin r → R,
        x = mT₀ C (levF C ιB₀ ιB₁ τ a) + mT₁ C (levF C ιB₀ ιB₁ τ a') := by
  obtain ⟨r, τ₀, hτ₀, hgen⟩ := sec_gen_T ιB₀ ιB₁ hts hιB hB₀ hB₁ (C 0) e hspl
  choose τ hτ hτ1 hτ2 using fun j => exists_gam C H hs ⟨τ₀ j, hτ₀ j⟩
  let σ : Fin (r + r) → (∀ k, (C k).E₀) × (∀ k, (C k).E₁) :=
    Fin.append (fun j => mT₀ C (τ j)) (fun j => mT₁ C (τ j))
  have hσ : ∀ i, σ i ∈ Gam C H (e + 2) := by
    intro i
    induction i using Fin.addCases with
    | left j => simpa [σ] using mT₀_mem C H hts (hτ j)
    | right j =>
      show Fin.append (fun j => mT₀ C (τ j)) (fun j => mT₁ C (τ j)) (Fin.natAdd r j) ∈ Gam C H (e + 2)
      rw [Fin.append_right]
      exact mT₁_mem C H (hτ j)
  have hgen0 : ∀ y ∈ (C 0).sec (e + 2), ∃ c, y = lev C ιB₀ ιB₁ σ 0 c := by
    intro y hy
    obtain ⟨c, c', hcc⟩ := hgen y hy
    refine ⟨Fin.append c c', ?_⟩
    rw [hcc]
    simp only [σ, lev, Fin.sum_univ_add, Fin.append_left, Fin.append_right, mT₀, mT₁, hτ1, hτ2]
  refine ⟨r, τ, hτ, fun x hx => ?_⟩
  obtain ⟨a, ha⟩ := gam_gen C H ιB₀ ιB₁ p σ α hα hιB hJ₀ hJ₁ hσ hgen0 hfil hx
  refine ⟨fun j => a (Fin.castAdd r j), fun j => a (Fin.natAdd r j), Prod.ext (funext fun m => ?_)
    (funext fun m => ?_)⟩
  · rw [show x.1 m = (lev C ιB₀ ιB₁ σ m a).1 from congrArg Prod.fst (ha m)]
    simp only [σ, lev_fst, Fin.sum_univ_add, Fin.append_left, Fin.append_right, mT₀, mT₁, levF, Prod.fst_add,
      Pi.add_apply, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  · rw [show x.2 m = (lev C ιB₀ ιB₁ σ m a).2 from congrArg Prod.snd (ha m)]
    simp only [σ, lev_snd, Fin.sum_univ_add, Fin.append_left, Fin.append_right, mT₀, mT₁, levF, Prod.snd_add,
      Pi.add_apply, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring

end Struct

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs3a =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As3a): one bound `D` for the tower

**`hat_pack`**: for the tower over a level-`0` cover `C₀`, a single `D` serves the splitting hypothesis at level `0`
(`spl_tower` with `k = n = 0`), the surjectivity of the section maps (`secMap_surj_tower`) and the filtration property
(`fil_tower`), in the exact shapes `hspl`, `hs`, `hfil` used by `CovHat*`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section HatPack

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] (φ₀ : B₀ →+* N)
  (φ₁ : B₁ →+* N) (J₀ : Ideal B₀) (J₁ : Ideal B₁) (JN : Ideal N) (h₀ : J₀.map φ₀ = JN) (h₁ : J₁.map φ₁ = JN)
  (t₀ : B₀) (t₁ : B₁) (hφ₀ : IsAwayMap φ₀ t₀) (hφ₁ : IsAwayMap φ₁ t₁) (hu₀ : IsUnit (φ₀ t₀))
  (hu₁ : IsUnit (φ₁ t₁)) (C₀ : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ 0) (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁)
  (p : Ideal R)

include hφ₀ hφ₁ hu₀ hu₁

theorem hat_pack [IsNoetherianRing R] [IsNoetherianRing B₀] {g : ℕ} (α : Fin g → R)
    (hα : p = Ideal.span (Set.range α)) (hts : φ₀ t₀ * φ₁ t₁ = 1) (hB : (eval₂RingHom ιB₀ t₀).Finite)
    (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) :
    ∃ D : ℕ,
      (∀ e, D ≤ e → ∀ z : (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ 0).E,
        ∃ (x₀ : (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ 0).E₀)
          (x₁ : (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ 0).E₁),
          z = (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ 0).ψ₀ x₀ -
            (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ 0).u ^ e *
              (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ 0).ψ₁ x₁) ∧
      (∀ d, D ≤ d → ∀ k, Function.Surjective
        ((towerHom φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ k).secMap (Ideal.Quotient.factor_mk _ _) d)) ∧
      (∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ k) d) := by
  obtain ⟨d₀, hd₀⟩ := spl_tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ ιB₀ ιB₁ p hts hB hιB hJ₀
  obtain ⟨d₁, hd₁⟩ :=
    secMap_surj_tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ ιB₀ ιB₁ p hts hB hιB hJ₀ hJ₁
  obtain ⟨d₂, hd₂⟩ :=
    fil_tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ ιB₀ ιB₁ p α hα hts hB hιB hJ₀ hJ₁
  refine ⟨max d₀ (max d₁ d₂), fun e he z => ?_,
    fun d hd => hd₁ d (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hd)),
    fun d hd => hd₂ d (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hd))⟩
  have hz : z ∈ (p ^ 0).map ((tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ 0).ψ₀.comp
      (lι₀ ιB₀ (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ 0))) := by
    rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
    exact Submodule.mem_top
  obtain ⟨x₀, _, x₁, _, hz'⟩ := hd₀ e (le_trans (le_max_left _ _) he) 0 0 z hz
  exact ⟨x₀, x₁, hz'⟩

end HatPack

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_DescG5 =====
section

/-!
# S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`

* `sheet_cover`: the sheets `sheetE ν : V ⟶ U0E` cover `U0E` (every prime of `B(U)` comes from a sheet).
* `cU_kL`, `cval_dif_sheet`, `dif_sheet`: if `gi ≫ sheetE i = gj ≫ sheetE j` then `dif gi gj = j - i`
  (pointwise: the pair `(gi, gj)` lands in `Spec (C ⊗ C)` over an affine `U`, and `key_sheet`).
* `exists_sigma`: the sections `e + a(ν)` on the sheets glue to `σ ∈ E(U₀)`; `b_sigma`: `b σ` is the pull-back of `q`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescG

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.DescA TensorProduct

universe u

section Gen

end Gen

section Pt

end Pt

section Cover

variable {X : Scheme.{u}} (V : X.Etale) [IsAffineHom V.hom] [Surjective V.hom] {Λ : Type u} [CommRing Λ]
  {M : ModuleCat.{u} Λ} [Fintype M] [DecidableEq M] {E Q : EtSh Λ X} (a : constSh Λ X M ⟶ E) (b : E ⟶ Q)
  (hab : a ≫ b = 0) (hS : (ShortComplex.mk a b hab).ShortExact) (e : E.obj.obj (op V))
  (he : ∀ (W : X.Etale) (w₁ w₂ : W ⟶ V), (b.hom.app (op W)).hom ((E.obj.map w₁.op).hom e) =
    (b.hom.app (op W)).hom ((E.obj.map w₂.op).hom e))

/-- Pointwise, over an affine `U` containing the image of `w`. -/
theorem cval_dif_sheet_U {W : X.Etale} (i j : M) (gi gj : W ⟶ V)
    (hij : gi ≫ sheetE V a b hab hS e he i = gj ≫ sheetE V a b hab hS e he j) (U : X.AffineZariskiSite)
    (w : W.left) (hwU : vh W w ∈ U.1) :
    cval (dif a b hab hS e he W gi gj) w = j - i := by
  let T : W.left.Opens := vh W ⁻¹ᵁ U.1
  have hg : ∀ g : W ⟶ V, ∀ z : T, vh V ((T.ι ≫ g.left) z) ∈ U.1 := fun g z => by
    have h1 : vh V ((T.ι ≫ g.left) z) = vh W (T.ι z) := congrArg (fun f => f (T.ι z)) (MorphismProperty.Over.w g)
    exact (congrArg (· ∈ U.1) h1).mpr z.2
  have h : (T.ι ≫ gi.left) ≫ vh V = (T.ι ≫ gj.left) ≫ vh V :=
    (Category.assoc _ _ _).trans ((whisker_eq T.ι (MorphismProperty.Over.w gi)).trans
      ((whisker_eq T.ι (MorphismProperty.Over.w gj)).symm.trans (Category.assoc _ _ _).symm))
  have hsh : (T.ι ≫ gi.left) ≫ sheet V a b hab hS e he i = (T.ι ≫ gj.left) ≫ sheet V a b hab hS e he j :=
    (Category.assoc _ _ _).trans ((congrArg (fun g => T.ι ≫ g.left) hij).trans (Category.assoc _ _ _).symm)
  let kE : opn W T ⟶ etS U.2.fromSpec (CU V U ⊗[Γ(X, U.1)] CU V U) :=
    MorphismProperty.Over.homMk (kL V U (T.ι ≫ gi.left) (T.ι ≫ gj.left) h (hg gi) (hg gj))
      ((kL_w V U _ _ h (hg gi) (hg gj)).trans ((Category.assoc _ _ _).trans
        (whisker_eq T.ι (MorphismProperty.Over.w gi)))) trivial
  have hk1 : kE ≫ kmap U.2.fromSpec (tauU V U) (htauU V U) (j1 Γ(X, U.1) (CU V U)) = opnι W T ≫ gi := by
    apply MorphismProperty.Over.Hom.ext
    change kL V U (T.ι ≫ gi.left) (T.ι ≫ gj.left) h (hg gi) (hg gj) ≫
      Spec.map (CommRingCat.ofHom (j1 Γ(X, U.1) (CU V U)).toRingHom) ≫ tauU V U = T.ι ≫ gi.left
    exact (kL_j1_assoc V U _ _ h (hg gi) (hg gj) (tauU V U)).trans (liftU_fac V U _ _)
  have hk2 : kE ≫ kmap U.2.fromSpec (tauU V U) (htauU V U) (j2 Γ(X, U.1) (CU V U)) = opnι W T ≫ gj := by
    apply MorphismProperty.Over.Hom.ext
    change kL V U (T.ι ≫ gi.left) (T.ι ≫ gj.left) h (hg gi) (hg gj) ≫
      Spec.map (CommRingCat.ofHom (j2 Γ(X, U.1) (CU V U)).toRingHom) ≫ tauU V U = T.ι ≫ gj.left
    exact (kL_j2_assoc V U _ _ h (hg gi) (hg gj) (tauU V U)).trans (liftU_fac V U _ _)
  calc cval (dif a b hab hS e he W gi gj) w
      = cval (((constSh Λ X M).obj.map (opnι W T).op).hom (dif a b hab hS e he W gi gj))
          (⟨w, hwU⟩ : T) := (cval_map (opnι W T) (dif a b hab hS e he W gi gj) ⟨w, hwU⟩).symm
    _ = cval (dif a b hab hS e he (opn W T) (opnι W T ≫ gi) (opnι W T ≫ gj)) (⟨w, hwU⟩ : T) :=
          congrArg (fun c => cval c (⟨w, hwU⟩ : T)) (dif_map a b hab hS e he (opnι W T) gi gj)
    _ = cval (dif a b hab hS e he (opn W T)
          (kE ≫ kmap U.2.fromSpec (tauU V U) (htauU V U) (j1 Γ(X, U.1) (CU V U)))
          (kE ≫ kmap U.2.fromSpec (tauU V U) (htauU V U) (j2 Γ(X, U.1) (CU V U)))) (⟨w, hwU⟩ : T) := by
          rw [hk1, hk2]
    _ = cval (dif a b hab hS e he (etS U.2.fromSpec (CU V U ⊗[Γ(X, U.1)] CU V U))
          (kmap U.2.fromSpec (tauU V U) (htauU V U) (j1 Γ(X, U.1) (CU V U)))
          (kmap U.2.fromSpec (tauU V U) (htauU V U) (j2 Γ(X, U.1) (CU V U)))) (kE.left ⟨w, hwU⟩) :=
          (congrArg (fun c => cval c (⟨w, hwU⟩ : T)) (dif_map a b hab hS e he kE _ _)).symm.trans
            (cval_map kE _ _)
    _ = j - i := cU_kL V a b hab hS e he i j U _ _ h (hg gi) (hg gj) hsh _

/-- **Sheets identified on `W` differ by a constant**, pointwise. -/
theorem cval_dif_sheet {W : X.Etale} (i j : M) (gi gj : W ⟶ V)
    (hij : gi ≫ sheetE V a b hab hS e he i = gj ≫ sheetE V a b hab hS e he j) (w : W.left) :
    cval (dif a b hab hS e he W gi gj) w = j - i := by
  obtain ⟨Uo, hU, hwU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := vh W w) (U := ⊤) trivial
  exact cval_dif_sheet_U V a b hab hS e he i j gi gj hij ⟨Uo, hU⟩ w hwU

/-- **Sheets identified on `W` differ by a constant.** -/
theorem dif_sheet {W : X.Etale} (i j : M) (gi gj : W ⟶ V)
    (hij : gi ≫ sheetE V a b hab hS e he i = gj ≫ sheetE V a b hab hS e he j) :
    dif a b hab hS e he W gi gj = (constUnit M W).hom (j - i) :=
  T3d.sec_ext_cval _ _ fun w => by
    rw [cval_constUnit]
    exact cval_dif_sheet V a b hab hS e he i j gi gj hij w

end Cover

end RamanujanPetersson.EtPBC.DescG

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

end S4GenB

section S4

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left] {g₀ G : k[X]} (hG₀ : g₀ ∣ G) (hle : opnDg c G ≤ Uo)
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).left]
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).left]
  {B₁ : CommRingCat.{0}} (φ₁ : CommRingCat.of k[X] ⟶ B₁) [Etale (Spec.map φ₁ ≫ c)]
  [IsAffine (prd (chEt c φ₁) (opEt Uo)).left]
  {B₂ : CommRingCat.{0}} (φ₂ : CommRingCat.of k[X] ⟶ B₂) [Etale (Spec.map φ₂ ≫ c)]
  [IsAffine (prd (chEt c φ₂) (opEt Uo)).left]
  (hD₂ : ∀ v : (prd (chEt c φ₂) (opEt Uo)).left, (prd (chEt c φ₂) (opEt Uo)).hom v ∈ opnDg c G)
  (d₂₁ : chEt c φ₂ ⟶ chEt c φ₁) (d₀ : chEt c φ₁ ⟶ chEt c (locF (B := CommRingCat.of k[X]) g₀))

set_option maxHeartbeats 400000 in
/-- **Stage S4 on the charts**: `e`, `g`, `he`, `hHp`, `hHq` of `uk_diff` (`T' := Y₁`, `m := mG`, `t := φ₂ r`). -/
def exists_S4 (s : Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤))
    (hloc : letI := (wm (R := R) (prdMap d₂₁ (opEt Uo))).appTop.hom.toAlgebra
      IsLocalization.Away s Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤))
    (ι : B₁ ⟶ B₂) (hd : d₂₁.left = Spec.map ι) [Nontrivial B₂]
    [DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤))]
    [Algebra B₁ (PiQ Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤))]
    (halg : ∀ b, algebraMap B₁ (PiQ Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) b =
      toPiQ ((bW (Spec.map φ₁ ≫ c) (opEt Uo) R).hom b))
    (p₁ : minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤))
    (u₁ : FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1))
    {r : k[X]} (hr : r ≠ 0) {N : ℕ}
    {y : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)}
    {H : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤)}
    (hH : H * (wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop
      (gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) r) ^ N =
      (wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop y)
    {z : PiQ Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)}
    (hy : toPiQ ((wm (R := R) (prdMap d₀ (opEt Uo))).appTop y) =
      toPiQ (gamMap (shG c φ₁ (Uo := Uo) R) r) ^ N *
        Function.update (1 : PiQ Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) p₁ u₁ *
        (1 - toPiQ (gamMap (shG c φ₁ (Uo := Uo) R) r) * z))
    (hz : IsIntegral B₁ z) :
    ∃ e : ∀ q : minimalPrimes Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤),
        FractionRing (Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1),
      ∃ g : B₂[X], g.Monic ∧ 0 < g.natDegree ∧
      (∀ q, g.eval₂ (bK (Spec.map φ₂ ≫ c) (opEt Uo) R q) (e q) = 0) ∧
      ∀ p₂ : minimalPrimes Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤),
        (p₁ : Ideal Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) ≤
          RingHom.ker (kerMap (wm (R := R) (prdMap d₂₁ (opEt Uo))) p₂) →
        (∀ Ψ : FractionRing (Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₁.1) →+*
            FractionRing (Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₂.1),
          (∀ a, Ψ (algebraMap _ _ (Ideal.Quotient.mk p₁.1 a)) =
            algebraMap _ _ (Ideal.Quotient.mk p₂.1 ((wm (R := R) (prdMap d₂₁ (opEt Uo))).appTop a))) →
          algebraMap _ (FractionRing (Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p₂.1))
              (Ideal.Quotient.mk p₂.1 ((wm (R := R) (mG c hle (chEt c φ₂) hD₂)).appTop H)) =
            Ψ u₁ * (1 + bK (Spec.map φ₂ ≫ c) (opEt Uo) R p₂ (φ₂.hom r) * e p₂)) ∧
        ∀ q, q ≠ p₂ →
          algebraMap _ (FractionRing (Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1))
              (Ideal.Quotient.mk q.1 ((wm (R := R) (mG c hle (chEt c φ₂) hD₂)).appTop H)) =
            1 + bK (Spec.map φ₂ ≫ c) (opEt Uo) R q (φ₂.hom r) * e q :=
  exists_S4_genB (wm (R := R) (prdMap d₂₁ (opEt Uo))).appTop.hom s hloc (bW (Spec.map φ₁ ≫ c) (opEt Uo) R).hom
    (bW (Spec.map φ₂ ≫ c) (opEt Uo) R).hom ι.hom (wm_bW₂ c (Uo := Uo) R φ₁ φ₂ d₂₁ ι hd) halg
    (bK (Spec.map φ₂ ≫ c) (opEt Uo) R) (fun _ _ => rfl) (kerMap (wm (R := R) (prdMap d₂₁ (opEt Uo))))
    (fun q => ker_kerMap _ q) p₁ u₁ (wm_gamMap₂ c (Uo := Uo) R φ₁ φ₂ d₂₁ r) (toPiQ_bW_ne_zero c (Uo := Uo) R φ₂ hr)
    (wm_mG_H₂ c R hG₀ hle φ₁ φ₂ hD₂ d₂₁ d₀ r N hH) hy hz

end S4

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Rel2 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2R3a): the target term of the relation lies in `G`

REL PLAN v2 (s126), file R3, generic part. In the setting of `relation_sum` (O2R4):
* **`term_mem_of_rest`**: if every term `k ≠ k₀` lies in an additive subgroup `G`, so does the term `k₀`;
* **`term_mem_of_good`**: the same when every term `k ≠ k₀` is at a good point (one-point classes there lie in `G`) or
  is `0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} {ι : Type u} [Fintype ι] [DecidableEq ι]
  (S : ι → P.Etale) (U₀ : P.Opens)
  (z : ι → P) (hzi : Function.Injective z) (hU : ∀ x : P, x ∈ U₀ ↔ ∀ k, x ≠ z k)
  (hD : ∀ k, Subsingleton ((geomPtAt (z k)).point.fiber.obj (S k)))
  (hDn : ∀ k, Nonempty ((geomPtAt (z k)).point.fiber.obj (S k)))
  (hDr : ∀ k (v : (S k).left), (S k).hom v ∈ U₀ ∨ (S k).hom v = z k)
  (Uz : ι → P.Opens) (hz : ∀ k (x : P), x ∈ Uz k ↔ x ≠ z k)

include hzi hU hD hDn hDr hz in
/-- **The term `k₀` of the relation lies in `G` when all the others do.** -/
theorem term_mem_of_rest {F : EtSh Λ P} (G : AddSubgroup (Ext.{u} (freeSh Λ (etId P)) F 2))
    (κ : Ext.{u} (freeSh Λ (opEt U₀)) F 1) (k₀ : ι)
    (hk : ∀ k, k ≠ k₀ → (locC_shortExact (Λ := Λ) (S k) (locLe U₀ z hU Uz hz k) (z k) (hz k) (hD k) (hDn k)
      (hDr k)).extClass.comp ((Ext.mk₀ (freeMap Λ (prT (S k) (opEt U₀)))).comp κ (zero_add 1))
        (show 1 + 1 = 2 from rfl) ∈ G) :
    (locC_shortExact (Λ := Λ) (S k₀) (locLe U₀ z hU Uz hz k₀) (z k₀) (hz k₀) (hD k₀) (hDn k₀)
      (hDr k₀)).extClass.comp ((Ext.mk₀ (freeMap Λ (prT (S k₀) (opEt U₀)))).comp κ (zero_add 1))
        (show 1 + 1 = 2 from rfl) ∈ G := by
  have e := relation_sum S U₀ z hzi hU hD hDn hDr Uz hz κ
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k₀)] at e
  rw [eq_neg_of_add_eq_zero_left e]
  exact neg_mem (sum_mem fun k hk' => hk k (Finset.ne_of_mem_erase hk'))

end RamanujanPetersson.EtPBC.EtMV

end

end


