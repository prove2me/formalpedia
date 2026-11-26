-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_153
-- name    : RPLib_FX_EtPBC_153
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:21:29.128796+00:00
-- url     : https://prove2.me/theorems/2f88d2e6-b98e-5aff-853e-a0ca7e6800d5
-- title:
--   Proper base change for the projective line, library file 153
-- statement:
--   File 153 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovHat4`: S4-EtPBC-A, R4-T2 (A2c-3d): fractions `x / T₀ᵈ`, `x / T₁ᵈ` in the completed charts
--   * `S4.Def_RP_EtPBC_A_CovHat6`: S4-EtPBC-A, R4-T2 (A2c-3f): the level reductions of the completed charts are surjective
--   * `S4.Def_RP_EtPBC_A_CovHat8`: S4-EtPBC-A, R4-T2 (A2c-4a): shifts of fractions by `T₀`, `T₁`
--   * `S4.Def_RP_EtPBC_A_CovGl2`: S4-EtPBC-A, R4-T2 (G1c, part 2b): gluing finite etale chart algebras over `Y_{V'}`
--   * `S4.Def_RP_EtPBC_A_CovFib`: S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover
--   * `S4.Def_RP_EtPBC_A_O2a`: S4-EtPBC-A, O2a: base change surjectivity passes to quotients in the top degree
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_139
import Definitions.Def_RPLib_FX_EtPBC_145

/-!
# Proper base change for the projective line, library file 153

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovHat4`: S4-EtPBC-A, R4-T2 (A2c-3d): fractions `x / T₀ᵈ`, `x / T₁ᵈ` in the completed charts
* `S4.Def_RP_EtPBC_A_CovHat6`: S4-EtPBC-A, R4-T2 (A2c-3f): the level reductions of the completed charts are surjective
* `S4.Def_RP_EtPBC_A_CovHat8`: S4-EtPBC-A, R4-T2 (A2c-4a): shifts of fractions by `T₀`, `T₁`
* `S4.Def_RP_EtPBC_A_CovGl2`: S4-EtPBC-A, R4-T2 (G1c, part 2b): gluing finite etale chart algebras over `Y_{V'}`
* `S4.Def_RP_EtPBC_A_CovFib`: S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover
* `S4.Def_RP_EtPBC_A_O2a`: S4-EtPBC-A, O2a: base change surjectivity passes to quotients in the top degree
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_CovHat4 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3d): fractions `x / T₀ᵈ`, `x / T₁ᵈ` in the completed charts

* **`frac₀ d x hx : hE₀`**, `frac₀_val`, `frac₀_spec`, `hE₀_ext`, **`eq_frac₀`**, `frac₀_congr`, **`frac₀_T₀`**,
  `frac₀_add`, `frac₀_mul`; chart 1: `frac₁`, `frac₁_spec`, `hE₁_ext`, `eq_frac₁`, `frac₁_congr`, `frac₁_T₁`, `frac₁_add`,
  `frac₁_mul`;
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Frac

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k))
  (hts : φ₀ t₀ * φ₁ t₁ = 1)

variable {C H}

/-- **`T₁ᵐ x / T₁^(d+m) = x / T₁ᵈ`.** -/
theorem frac₁_T₁ {d : ℕ} {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d) (m : ℕ) :
    frac₁ C H (d + m) (gT₁ C ^ m * x) (gT₁_pow_mem C H m hx) = frac₁ C H d x hx := by
  refine hE₁_ext (d + m) ?_ ?_
  · have e1 := frac₁_spec hx
    rw [frac₁_spec]
    show jL₀ C (tFm C ^ m * x.1) = jL₀ C (tFm C ^ (d + m)) * (frac₁ C H d x hx : L₀ C × ∀ k, (C k).E₁).1
    rw [map_mul, pow_add, map_mul]
    linear_combination (-(jL₀ C (tFm C ^ m))) * e1
  · show (gT₁ C ^ m * x).2 = x.2
    simp only [Prod.snd_mul, Prod.pow_snd, gT₁, one_pow, one_mul]

theorem frac₁_add {d : ℕ} {x y : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d) (hy : y ∈ Gam C H d) :
    frac₁ C H d x hx + frac₁ C H d y hy = frac₁ C H d (x + y) (add_mem hx hy) := by
  refine hE₁_ext d ?_ rfl
  rw [frac₁_spec (add_mem hx hy)]
  show jL₀ C (tFm C ^ d) * ((frac₁ C H d x hx : L₀ C × ∀ k, (C k).E₁).1 +
    (frac₁ C H d y hy : L₀ C × ∀ k, (C k).E₁).1) = jL₀ C (x.1 + y.1)
  rw [mul_add, frac₁_spec, frac₁_spec, map_add]

end Frac

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovHat6 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3f): the level reductions of the completed charts are surjective

* **`θ₀ k : hE₀ →+* E₀(k)`**, **`θ₁ k : hE₁ →+* E₁(k)`** (evaluation of the first, resp. second, coordinate);
  `θ₀_frac₀`, `θ₁_frac₁`, `ρ₀_θ₀`, `ρ₁_θ₁` (compatible with the transitions), `θ₀_β₀`, `θ₁_β₁`;
* **`gen_sys`**: lifts of level-`0` generators of `O(d)`; **`gam_lev_surj`**: every level-`m` section of `O(d)` is
  the level-`m` part of a compatible family;
* **`θ₀_surj`**, **`θ₁_surj`** (all `k`), when the transitions are surjective on sections and `FilProp` holds in all
  degrees `≥ D`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Theta

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (hts : φ₀ t₀ * φ₁ t₁ = 1)

theorem θ₁_apply (k : ℕ) (z : hE₁ C H) : θ₁ C H k z = (z : L₀ C × ∀ k, (C k).E₁).2 k := rfl

theorem θ₁_frac₁ (k : ℕ) {d : ℕ} {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d) :
    θ₁ C H k (frac₁ C H d x hx) = x.2 k := rfl

end Theta

section Surj

end Surj

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovHat8 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-4a): shifts of fractions by `T₀`, `T₁`

* `frac₀_mT₀` (`T₀ y / T₀^(d+1) = y / T₀ᵈ`), `frac₀_mT₁` (`T₁ y / T₀^(d+1) = t₀ · y / T₀ᵈ`), and the chart-1
  versions `frac₁_mT₁`, `frac₁_mT₀`;
* `frac₀_dec`, `frac₁_dec`: fractions of `T₀ y + T₁ y'`; `sum_comb₀`, `sum_comb₁` (coefficient bookkeeping).
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Comb

end Comb

section MT

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (hts : φ₀ t₀ * φ₁ t₁ = 1)
  (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀)) (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁))

theorem frac₁_mT₁ {d : ℕ} {y : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hy : y ∈ Gam C H d)
    (h : mT₁ C y ∈ Gam C H (d + 1)) : frac₁ C H (d + 1) (mT₁ C y) h = frac₁ C H d y hy := by
  refine hE₁_ext (d + 1) ?_ rfl
  have e1 := frac₁_spec hy
  rw [frac₁_spec]
  show jL₀ C (tFm C * y.1) = jL₀ C (tFm C ^ (d + 1)) * (frac₁ C H d y hy : L₀ C × ∀ k, (C k).E₁).1
  rw [map_mul, pow_succ (tFm C) d, map_mul]
  linear_combination (-(jL₀ C (tFm C))) * e1

/-- The fraction of `T₀ y + T₁ y'` in chart `0`. -/
theorem frac₀_dec {e : ℕ} {x y y' : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hy : y ∈ Gam C H (e + 1))
    (hy' : y' ∈ Gam C H (e + 1)) (hx : x ∈ Gam C H (e + 1 + 1)) (hx' : x = mT₀ C y + mT₁ C y') :
    frac₀ C H hts (e + 1 + 1) x hx =
      frac₀ C H hts (e + 1) y hy + β₀ C H hts hφ₁ hu₁ t₀ * frac₀ C H hts (e + 1) y' hy' := by
  have h0 := mT₀_mem C H hts hy
  have h1 := mT₁_mem C H hy'
  rw [frac₀_congr hts hx' hx (add_mem h0 h1), ← frac₀_add hts h0 h1, frac₀_mT₀ C H hts hy h0,
    frac₀_mT₁ C H hts hφ₁ hu₁ hy' h1]

end MT

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovGl2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1c, part 2b): gluing finite etale chart algebras over `Y_{V'}`

Chart algebras `E₀`, `E₁`, `E₀₁` over `R' ⊗ Γ(Y₀)`, `R' ⊗ Γ(Y₁)`, `R' ⊗ Γ(Y₀₁)`, glued by localizations `ψ₀`, `ψ₁` (the
data of `CoverLift`), give a relative gluing datum **`glD`** over the chart cover `covV`; its glued scheme maps to
`Y_{V'}` by **`toBase`**, which is finite and etale when `E₀`, `E₁` are.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV)

variable [IsAffine V] [IsFinite π] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R'] {E₀ E₁ E₀₁ : Type u}
  [CommRing E₀] [CommRing E₁] [CommRing E₀₁] [Algebra (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) E₀]
  [Algebra (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) E₁] [Algebra (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1)) E₀₁]
  (ψ₀ : E₀ →+* E₀₁) (ψ₁ : E₁ →+* E₀₁)
  (hψ₀ : ∀ (r : R') (b : Γ(Y, Yc K gV π 0)), ψ₀ (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) E₀ (r ⊗ₜ b)) =
    algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1)) E₀₁ (r ⊗ₜ φY0 K gV π b))
  (hψ₁ : ∀ (r : R') (b : Γ(Y, Yc K gV π 1)), ψ₁ (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) E₁ (r ⊗ₜ b)) =
    algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1)) E₀₁ (r ⊗ₜ φY1 K gV π b))
  (aw₀ : IsAwayMap ψ₀ (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) E₀
    ((1 : R') ⊗ₜ algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0) Polynomial.X)))
  (aw₁ : IsAwayMap ψ₁ (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) E₁
    ((1 : R') ⊗ₜ algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 1) Polynomial.X)))

/-- The natural transformation to the chart functor of `covV`. -/
def glNat : glF K gV π R' ψ₀ ψ₁ ⟶ (covV K gV π R').functorOfLocallyDirected where
  app := glα K gV π R' ψ₀ ψ₁
  naturality := by
    rintro X _ (_ | (_ | _))
    · change (glF K gV π R' ψ₀ ψ₁).map (𝟙 X) ≫ _ = _ ≫ (covV K gV π R').functorOfLocallyDirected.map (𝟙 X)
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact (pb0 K gV π R' ψ₀ hψ₀ aw₀).w
    · exact (pb1 K gV π R' ψ₁ hψ₁ aw₁).w

theorem glEq : (glNat K gV π R' ψ₀ ψ₁ hψ₀ hψ₁ aw₀ aw₁).Equifibered := by
  rintro X _ (_ | (_ | _))
  · change IsPullback ((glF K gV π R' ψ₀ ψ₁).map (𝟙 X)) _ _ ((covV K gV π R').functorOfLocallyDirected.map (𝟙 X))
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact IsPullback.of_id_fst
  · exact pb0 K gV π R' ψ₀ hψ₀ aw₀
  · exact pb1 K gV π R' ψ₁ hψ₁ aw₁

/-- **The relative gluing datum** of the chart algebras over `covV`. -/
def glD : (covV K gV π R').RelativeGluingData where
  functor := glF K gV π R' ψ₀ ψ₁
  natTrans := glNat K gV π R' ψ₀ ψ₁ hψ₀ hψ₁ aw₀ aw₁
  equifibered := glEq K gV π R' ψ₀ ψ₁ hψ₀ hψ₁ aw₀ aw₁

section FinEt

variable [Module.Finite (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) E₀] [Module.Finite (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) E₁]

theorem isFinite_app (j : (covV K gV π R').I₀) : IsFinite ((glD K gV π R' ψ₀ ψ₁ hψ₀ hψ₁ aw₀ aw₁).natTrans.app j) := by
  have h0 : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) E₀))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  rcases j with _ | (_ | _)
  · exact MorphismProperty.of_isPullback (P := @IsFinite) (pb0 K gV π R' ψ₀ hψ₀ aw₀) h0
  · exact h0
  · exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

end FinEt

section Et

variable [Algebra.Etale (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) E₀] [Algebra.Etale (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) E₁]

theorem etale_app (j : (covV K gV π R').I₀) : Etale ((glD K gV π R' ψ₀ ψ₁ hψ₀ hψ₁ aw₀ aw₁).natTrans.app j) := by
  have h0 : Etale (Spec.map (CommRingCat.ofHom (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) E₀))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  rcases j with _ | (_ | _)
  · exact MorphismProperty.of_isPullback (P := @Etale) (pb0 K gV π R' ψ₀ hψ₀ aw₀) h0
  · exact h0
  · exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)

end Et

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

/-- The gluing datum of the lifted charts. -/
abbrev dL : letI := algKV K gV; (covV K gV π L.R').RelativeGluingData :=
  letI := algKV K gV; glD K gV π L.R' L.ψ₀ L.ψ₁ L.hψ₀ L.hψ₁ L.aw₀ L.aw₁

/-- `U_x = U ×_{Y_{V'}} Y_x`. -/
abbrev UxL : Scheme.{u} := pullback (dL L).toBase (yxL L)

/-- The cover of `U_x` by the pulled back charts. -/
abbrev cvL : (UxL L).OpenCover := (dL L).cover.pullback₁ (pullback.fst (dL L).toBase (yxL L))

/-- The pulled back charts. -/
abbrev PL (j : WalkingSpan) : Scheme.{u} := (cvL L).X j

abbrev w0 : letI := algKV K gV; PL L WalkingSpan.left ⟶ Spec (CommRingCat.of L.E₀) := pullback.snd _ _
abbrev w1 : letI := algKV K gV; PL L WalkingSpan.right ⟶ Spec (CommRingCat.of L.E₁) := pullback.snd _ _

theorem ov_tr0 : letI := algKV K gV; (dL L).cover.trans WalkingSpan.Hom.fst = Spec.map (CommRingCat.ofHom L.ψ₀) := by
  letI := algKV K gV
  rfl

theorem ov_tr1 : letI := algKV K gV; (dL L).cover.trans WalkingSpan.Hom.snd = Spec.map (CommRingCat.ofHom L.ψ₁) := by
  letI := algKV K gV
  rfl

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_O2a =====
section

/-!
# S4-EtPBC-A, O2a: base change surjectivity passes to quotients in the top degree

* `Delta.surjAt_of_epi`: for `0 → X₁ → X₂ → X₃ → 0`, surjectivity in degree `q` for `X₂` gives surjectivity in
  degree `q` for `X₃` when `Ext^(q+1)(B, L X₁) = 0` (covariant exact sequence, no germ argument for `X₁`);
* `bcSurj_of_epi`: the same for base change germs along an epimorphism `G ⟶ H` of sheaves;
* **`bcSurj_two_of_epi`**: on `P¹_S` at a `K`-rational geometric point (`K = K̄`, `ℓ ≠ char K`, `ℓ^m Λ = 0`),
  `BCSurj 2` passes to quotients (`H³` of the fibre vanishes for every sheaf).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.Delta

universe w v₁ u₁ v₂ u₂ v₃ u₃

end RamanujanPetersson.EtPBC.Delta

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3

section Epi

universe u

end Epi

section P1Two

variable (K : Type) [Field K] [IsAlgClosed K] {Λ : Type} [CommRing Λ] (l : ℕ) [Fact l.Prime]
  (hl : (l : K) ≠ 0) (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0)
  {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K)) (s : GeomPt S) [IsIso (s.pt ≫ gS)]

include hl hΛ

/-- **`BCSurj 2` passes to quotients** on `P¹_S` (`H³` of the fibre vanishes for every sheaf). -/
theorem bcSurj_two_of_epi {G H : EtSh Λ (PV K gS)} (e : G ⟶ H) [Epi e] (hG : BCSurj Λ (qV K gS) s 2 G) :
    BCSurj Λ (qV K gS) s 2 H :=
  bcSurj_of_epi (qV K gS) s e 2 hG (fun x => fib_H_add_three_eq_zero K l hl m hΛ gS s _ 0 x)

end P1Two

end RamanujanPetersson.EtPBC

end

end


