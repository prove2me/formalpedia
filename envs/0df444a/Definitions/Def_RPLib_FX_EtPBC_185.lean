-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_185
-- name    : RPLib_FX_EtPBC_185
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:28:09.317779+00:00
-- url     : https://prove2.me/theorems/493c0bbb-b4b3-51cb-9644-4d1d0f994138
-- title:
--   Proper base change for the projective line, library file 185
-- statement:
--   File 185 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovHat10`: S4-EtPBC-A, R4-T2 (A2c-4c): the completed chart `Ê₁` is finite over `B₁`
--   * `S4.Def_RP_EtPBC_A_CovAs3d`: S4-EtPBC-A, R4-T2 (A3 assembly, As3d): the completed cover as one existential package
--   * `S4.Def_RP_EtPBC_A_CovFib`: S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover
--   * `S4.Def_RP_EtPBC_A_CovSj`: S4-EtPBC-A, R4-T2 (G1e): making the lifted cover surjective
--   * `S4.Def_RP_EtPBC_A_SecExt`: S4-EtPBC-A, L1c (part 3): cohomology of sections of an injective resolution is `Ext` from a free sheaf
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_181

/-!
# Proper base change for the projective line, library file 185

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovHat10`: S4-EtPBC-A, R4-T2 (A2c-4c): the completed chart `Ê₁` is finite over `B₁`
* `S4.Def_RP_EtPBC_A_CovAs3d`: S4-EtPBC-A, R4-T2 (A3 assembly, As3d): the completed cover as one existential package
* `S4.Def_RP_EtPBC_A_CovFib`: S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover
* `S4.Def_RP_EtPBC_A_CovSj`: S4-EtPBC-A, R4-T2 (G1e): making the lifted cover surjective
* `S4.Def_RP_EtPBC_A_SecExt`: S4-EtPBC-A, L1c (part 3): cohomology of sections of an injective resolution is `Ext` from a free sheaf
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_CovHat10 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-4c): the completed chart `Ê₁` is finite over `B₁`

* `span_key₁`: every fraction is a `B₁`-combination of the fractions of finitely many generators of degree `D + 1`;
* **`hE₁_span`**: finitely many fractions span `Ê₁` over `B₁` (via `β₁`); **`β₁_finite`**.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Fin₁

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (p : Ideal R) (hts : φ₀ t₀ * φ₁ t₁ = 1) (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀))

include hts in
/-- **`Ê₁` is spanned over `B₁` by finitely many fractions.** -/
theorem hE₁_span [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R) (hα : ∀ i, α i ∈ p)
    (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite) (hB₁ : (eval₂RingHom ιB₁ t₁).Finite)
    (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hspl : ∀ e, D ≤ e → ∀ z : (C 0).E, ∃ (x₀ : (C 0).E₀) (x₁ : (C 0).E₁),
      z = (C 0).ψ₀ x₀ - (C 0).u ^ e * (C 0).ψ₁ x₁)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d) :
    ∃ (r : ℕ) (w : Fin r → hE₁ C H), ∀ z, ∃ b : Fin r → B₁, z = ∑ i, β₁ C H hφ₀ hu₀ (b i) * w i := by
  obtain ⟨r, σ, hσ, hgen0⟩ := gen_sys C H ιB₀ ιB₁ hts hιB hB₀ hB₁ (hs (D + 1) (by omega))
  refine ⟨r, fun i => frac₁ C H (D + 1) (σ i) (hσ i), fun z => ?_⟩
  obtain ⟨d, x, hx, h1, h2⟩ := (mem_hE₁ C H _).1 z.2
  rw [eq_frac₁ z hx h1 h2, ← frac₁_T₁ hx (D + 1)]
  exact span_key₁ C H ιB₀ ιB₁ p hts hφ₀ hu₀ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hspl hs hfil σ hσ hgen0 _ (by omega) _ _

end Fin₁

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs3d =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As3d): the completed cover as one existential package

**`hat_cov`**: for a level-0 cover `C₀` over a noetherian `p`-precomplete base `R` (`p ≤ jacobson ⊥`,
`p = span (range α)`), there are rings `Ê₀, Ê₁, Ê` with finite etale `B₀ → Ê₀`, `B₁ → Ê₁`, glued by away maps
`Êᵢ → Ê` over `N → Ê`, and surjections `θ̂ᵢ : Êᵢ ↠ C₀.Eᵢ` with kernel `p Êᵢ`, compatible with the gluing and with
the charts of `C₀` (the tower `tower .. C₀` stays hidden). `hat_cov_gen` is the same for any tower `C`, `H`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section HatCovGen

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (p : Ideal R) (hts : φ₀ t₀ * φ₁ t₁ = 1) (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀))
  (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁))

set_option maxHeartbeats 400000 in
/-- Surjectivity and kernels of `θ̂ᵢ` at level `0`. -/
def hat_sk [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R) (hα : ∀ i, α i ∈ p)
    (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite) (hB₁ : (eval₂RingHom ιB₁ t₁).Finite)
    (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d) :
    Function.Surjective (θ₀ C H hts 0) ∧ Function.Surjective (θ₁ C H 0) ∧
      RingHom.ker (θ₀ C H hts 0) = p.map ((β₀ C H hts hφ₁ hu₁).comp ιB₀) ∧
      RingHom.ker (θ₁ C H 0) = p.map ((β₁ C H hφ₀ hu₀).comp ιB₁) := by
  refine ⟨θ₀_surj C H ιB₀ ιB₁ p hts α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil 0,
    θ₁_surj C H ιB₀ ιB₁ p hts α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil 0, ?_, ?_⟩
  · rw [θ₀_ker C H ιB₀ ιB₁ p hts hφ₁ hu₁ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil 0, zero_add, pow_one]
    rfl
  · rw [θ₁_ker C H ιB₀ ιB₁ p hts hφ₀ hu₀ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil 0, zero_add, pow_one]
    rfl

end HatCovGen

section HatCov

end HatCov

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovFib =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover

For lift data `L : LiftD K gV π x q hx` of a fibre cover `q : T ⟶ Y_x`: the glued cover `dL L` of `Y_{V'}`
(`V' = Spec L.R'`), the lift `xL L` of `x`, and **`ψL L : U_x ⟶ T`** on `U_x = (dL L).glued ×_{Y_{V'}} Y_x`, glued
from the chart lifts `gW` (`g0`, `g1`; `overlap` on `Y₀₁`), with **`ψL_q`**: `ψL L ≫ q = pullback.snd`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN algKY algT CoverLift.cR CoverLift.aR CoverLift.c₀ CoverLift.c₁ CoverLift.c₀₁ CoverLift.a₀ CoverLift.a₁ CoverLift.a₀₁

universe u

variable {K : Type u} [Field K] {V : Scheme.{u}} {gV : V ⟶ Spec (CommRingCat.of K)} {Y : Scheme.{u}}
  {π : Y ⟶ PV K gV} {x : Spec (CommRingCat.of K) ⟶ V} [IsAffine V] [IsFinite π] {hx : x ≫ gV = 𝟙 _}
  {T : Scheme.{u}} {q : T ⟶ Yx K gV π x} [IsAffineHom q] (L : LiftD K gV π x q hx)

/-- **`ψL` is a map over `Y_x`.** -/
theorem ψL_q : ψL L ≫ q = pullback.snd (dL L).toBase (yxL L) := by
  letI := algKV K gV
  haveI := mono_yxMap K gV π x L.χ' (hxL L) hx
  rw [← cancel_mono (yxL L)]
  have e0 : (cvL L).f WalkingSpan.left ≫ ψL L = g0 L :=
    Scheme.OpenCover.map_glueMorphismsOfLocallyDirected (cvL L) (gL L) (gL_h L) WalkingSpan.left
  have e1 : (cvL L).f WalkingSpan.right ≫ ψL L = g1 L :=
    Scheme.OpenCover.map_glueMorphismsOfLocallyDirected (cvL L) (gL L) (gL_h L) WalkingSpan.right
  have hl : (cvL L).f WalkingSpan.left ≫ ψL L ≫ q ≫ yxL L =
      (cvL L).f WalkingSpan.left ≫ pullback.snd (dL L).toBase (yxL L) ≫ yxL L := by
    rw [reassoc_of% e0, g0, Category.assoc, fromSpec_yx K gV π x L.χ' (hxL L) q (isAffineOpen_Yc K gV π 0)
      (struct_res K gV π 0) hW0 hT0 L.θ₀ L.hθ₀, reassoc_of% (gW_θ L.θ₀ L.sθ₀ (w0 L) (hk0 L))]
    exact pb_key (covV K gV π L.R') (dL L) (yxL L) WalkingSpan.left
  have hr : (cvL L).f WalkingSpan.right ≫ ψL L ≫ q ≫ yxL L =
      (cvL L).f WalkingSpan.right ≫ pullback.snd (dL L).toBase (yxL L) ≫ yxL L := by
    rw [reassoc_of% e1, g1, Category.assoc, fromSpec_yx K gV π x L.χ' (hxL L) q (isAffineOpen_Yc K gV π 1)
      (struct_res K gV π 1) hW1 hT1 L.θ₁ L.hθ₁, reassoc_of% (gW_θ L.θ₁ L.sθ₁ (w1 L) (hk1 L))]
    exact pb_key (covV K gV π L.R') (dL L) (yxL L) WalkingSpan.right
  refine Scheme.Cover.hom_ext (cvL L) _ _ (fun j => ?_)
  simp only [Category.assoc]
  rcases j with _ | (_ | _)
  · have h := Scheme.Cover.trans_map (cvL L) WalkingSpan.Hom.fst
    refine (congrArg (· ≫ ψL L ≫ q ≫ yxL L) h.symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((cvL L).trans WalkingSpan.Hom.fst ≫ ·) hl).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact congrArg (· ≫ pullback.snd (dL L).toBase (yxL L) ≫ yxL L) h
  · exact hl
  · exact hr

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovSj =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1e): making the lifted cover surjective

For a finite etale `ρ : U ⟶ Y'` the range is clopen; `ρs ρ : U ⨿ Z ⟶ Y'` with `Z` the complement of the range is
finite and surjective. If `m : S ⟶ Y'` has range inside the range of `ρ`, every lift `pullback ρ m ⟶ T` over `S`
extends to `pullback (ρs ρ) m ⟶ T` (**`exists_surj_ext`**). For the lifted charts, `range_yxL`: the range of
`yxL L` lies in the range of `(dL L).toBase` when `q` is surjective; **`exists_surj_L`**.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

universe u

section Surj

end Surj

section Lifted

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN algKY algT CoverLift.cR CoverLift.aR CoverLift.eR CoverLift.c₀ CoverLift.c₁ CoverLift.c₀₁ CoverLift.a₀ CoverLift.a₁ CoverLift.a₀₁ CoverLift.f₀ CoverLift.f₁ CoverLift.et₀ CoverLift.et₁

variable {K : Type u} [Field K] {V : Scheme.{u}} {gV : V ⟶ Spec (CommRingCat.of K)} {Y : Scheme.{u}}
  {π : Y ⟶ PV K gV} {x : Spec (CommRingCat.of K) ⟶ V} [IsAffine V] [IsFinite π] {hx : x ≫ gV = 𝟙 _}
  {T : Scheme.{u}} {q : T ⟶ Yx K gV π x} [IsAffineHom q] (L : LiftD K gV π x q hx)

/-- **G1e: a finite surjective cover of `Y_{V'}` with a lift of `q`** (for surjective `q`). -/
theorem exists_surj_L [Surjective q] : letI := algKV K gV;
    ∃ (U' : Scheme.{u}) (ρ' : U' ⟶ YV K gV π L.R'), IsFinite ρ' ∧ Function.Surjective ρ' ∧
      ∃ ψ' : pullback ρ' (yxL L) ⟶ T, ψ' ≫ q = pullback.snd ρ' (yxL L) := by
  letI := algKV K gV
  haveI : IsFinite (dL L).toBase := isFinite_toBase K gV π L.R' L.ψ₀ L.ψ₁ L.hψ₀ L.hψ₁ L.aw₀ L.aw₁
  haveI : Etale (dL L).toBase := etale_toBase K gV π L.R' L.ψ₀ L.ψ₁ L.hψ₀ L.hψ₁ L.aw₀ L.aw₁
  exact exists_surj_ext (dL L).toBase (yxL L) (range_yxL L) q (ψL L) (ψL_q L)

end Lifted

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_SecExt =====
section

/-!
# S4-EtPBC-A, L1c (part 3): cohomology of sections of an injective resolution is `Ext` from a free sheaf

`secExt Λ I W p : H^(p+1)(I^•(W)) ≃+ Ext^(p+1)(Λ[W], F)` (`Λ[W] = freeSh Λ W`), from Mathlib's cocycle
description of `Ext` (`InjectiveResolution.extMk`) and `freeEquiv : Hom(Λ[W], G) ≃+ G(W)`. The homology is that of
the short complex `sc (p+1)`, which is `(secCx Λ I.cocomplex W).homology (p+1)` by definition.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}} {F : EtSh Λ X} (I : InjectiveResolution F)

theorem quotExt_bijective (W : X.Etale) (p : ℕ) : Function.Bijective (quotExt Λ I W p) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    exact (QuotientAddGroup.eq_zero_iff z).2 ((cocExt_eq_zero_iff Λ I W p z).1 hx)
  · intro α
    obtain ⟨z, rfl⟩ := cocExt_surjective Λ I W p α
    exact ⟨QuotientAddGroup.mk z, rfl⟩

end RamanujanPetersson.EtPBC

end

end


