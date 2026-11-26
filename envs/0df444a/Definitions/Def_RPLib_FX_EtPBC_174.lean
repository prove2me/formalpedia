-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_174
-- name    : RPLib_FX_EtPBC_174
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:14:52.07108+00:00
-- url     : https://prove2.me/theorems/a6f44af1-3ce5-5101-937c-be99000a86d1
-- title:
--   Proper base change for the projective line, library file 174
-- statement:
--   File 174 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovHat9`: S4-EtPBC-A, R4-T2 (A2c-4b): the completed chart `Ê₀` is finite over `B₀`
--   * `S4.Def_RP_EtPBC_A_CovEt`: S4-EtPBC-A, R4-T2 (A2c-5, E3c3): the completed chart `Ê₀` is etale near `p`
--   * `S4.Def_RP_EtPBC_A_CovHat10`: S4-EtPBC-A, R4-T2 (A2c-4c): the completed chart `Ê₁` is finite over `B₁`
--   * `S4.Def_RP_EtPBC_A_CovFib`: S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover
--   * `S4.Def_RP_EtPBC_A_SecCls`: S4-EtPBC-A, L1c (part 2): the cocycle map `ker g →+ Ext^(p+1)(Λ[W], F)`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_155
import Definitions.Def_RPLib_FX_EtPBC_167

/-!
# Proper base change for the projective line, library file 174

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovHat9`: S4-EtPBC-A, R4-T2 (A2c-4b): the completed chart `Ê₀` is finite over `B₀`
* `S4.Def_RP_EtPBC_A_CovEt`: S4-EtPBC-A, R4-T2 (A2c-5, E3c3): the completed chart `Ê₀` is etale near `p`
* `S4.Def_RP_EtPBC_A_CovHat10`: S4-EtPBC-A, R4-T2 (A2c-4c): the completed chart `Ê₁` is finite over `B₁`
* `S4.Def_RP_EtPBC_A_CovFib`: S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover
* `S4.Def_RP_EtPBC_A_SecCls`: S4-EtPBC-A, L1c (part 2): the cocycle map `ker g →+ Ext^(p+1)(Λ[W], F)`
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_CovHat9 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-4b): the completed chart `Ê₀` is finite over `B₀`

* `span_key₀`: every fraction is a `B₀`-combination of the fractions of finitely many generators of degree `D + 1`;
* **`hE₀_span`**: finitely many fractions span `Ê₀` over `B₀` (via `β₀`); **`β₀_finite`**.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Fin₀

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (p : Ideal R) (hts : φ₀ t₀ * φ₁ t₁ = 1) (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁))

/-- **`B₀ → Ê₀` is finite.** -/
theorem β₀_finite [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R) (hα : ∀ i, α i ∈ p)
    (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite) (hB₁ : (eval₂RingHom ιB₁ t₁).Finite)
    (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hspl : ∀ e, D ≤ e → ∀ z : (C 0).E, ∃ (x₀ : (C 0).E₀) (x₁ : (C 0).E₁),
      z = (C 0).ψ₀ x₀ - (C 0).u ^ e * (C 0).ψ₁ x₁)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d) : (β₀ C H hts hφ₁ hu₁).Finite := by
  classical
  obtain ⟨r, w, hw⟩ := hE₀_span C H ιB₀ ιB₁ p hts hφ₁ hu₁ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hspl hs hfil
  letI := (β₀ C H hts hφ₁ hu₁).toAlgebra
  show Module.Finite B₀ (hE₀ C H hts)
  refine ⟨⟨Finset.univ.image w, ?_⟩⟩
  rw [eq_top_iff]
  intro z _
  obtain ⟨b, hb⟩ := hw z
  rw [hb]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact Submodule.smul_mem _ (b i)
    (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem w (Finset.mem_univ i))))

end Fin₀

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovEt =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-5, E3c3): the completed chart `Ê₀` is etale near `p`

* **`et_near₀`**: there is `s ∈ Ê₀` with `s ≡ 1 mod J₀ Ê₀` and `Ê₀[1/s]` etale over `B₀` (via `β₀`).
  Flatness of `Ê₀ ⧸ J₀^(k+1)` over `B₀ ⧸ J₀^(k+1)` comes from `θ₀ k` (`fq_flat`), freeness near `V(J₀)` from the
  local criterion (`lf_mem_freeLocus`), the unit `r` killing `Ω` from `unr_elt`, and etaleness from `fq_etale` (`et_gen`).
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Et₀

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (p : Ideal R) (hts : φ₀ t₀ * φ₁ t₁ = 1) (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁))

/-- `ker (θ₀ k) = J₀^(k+1) Ê₀`. -/
def θ₀_ker' [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R)
    (hα : ∀ i, α i ∈ p) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite)
    (hB₁ : (eval₂RingHom ιB₁ t₁).Finite) (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d) (k : ℕ) :
    RingHom.ker (θ₀ C H hts k) = (J₀ ^ (k + 1)).map (β₀ C H hts hφ₁ hu₁) := by
  have e1 : J₀ ^ (k + 1) = (p ^ (k + 1)).map ιB₀ := by rw [Ideal.map_pow, hJ₀]
  rw [θ₀_ker C H ιB₀ ιB₁ p hts hφ₁ hu₁ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil k, e1, Ideal.map_map]
  all_goals rfl

end Et₀

end RamanujanPetersson.EtPBC.Cov

end

end

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
/-- Every fraction of degree `≥ D + 1` is a `B₁`-combination of the fractions of the generators `σ`. -/
theorem span_key₁ [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R) (hα : ∀ i, α i ∈ p)
    (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite) (hB₁ : (eval₂RingHom ιB₁ t₁).Finite)
    (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hspl : ∀ e, D ≤ e → ∀ z : (C 0).E, ∃ (x₀ : (C 0).E₀) (x₁ : (C 0).E₁),
      z = (C 0).ψ₀ x₀ - (C 0).u ^ e * (C 0).ψ₁ x₁)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d)
    {r : ℕ} (σ : Fin r → (∀ k, (C k).E₀) × (∀ k, (C k).E₁)) (hσ : ∀ i, σ i ∈ Gam C H (D + 1))
    (hgen0 : ∀ y ∈ (C 0).sec (D + 1), ∃ c, y = lev C ιB₀ ιB₁ σ 0 c) (d : ℕ) (hd : D + 1 ≤ d) :
    ∀ x (hx : x ∈ Gam C H d), ∃ b : Fin r → B₁,
      frac₁ C H d x hx = ∑ i, β₁ C H hφ₀ hu₀ (b i) * frac₁ C H (D + 1) (σ i) (hσ i) := by
  induction d, hd using Nat.le_induction with
  | base =>
    intro x hx
    obtain ⟨a, ha⟩ := gam_gen C H ιB₀ ιB₁ p σ α hα hιB hJ₀ hJ₁ hσ hgen0 (hfil (D + 1) (by omega)) hx
    have hxeq : x = ∑ i, ιP C ιB₀ ιB₁ (a i) * σ i := by
      rw [← levF_eq]
      exact Prod.ext (funext fun n => congrArg Prod.fst (ha n)) (funext fun n => congrArg Prod.snd (ha n))
    exact ⟨fun i => ιB₁ (a i), frac₁_lin C H ιB₀ ιB₁ hφ₀ hu₀ hιB hσ a hx hxeq⟩
  | succ d hd ih =>
    intro x hx
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    obtain ⟨r', τ, hτ, hdec⟩ := gam_struct C H ιB₀ ιB₁ p α hα hts hιB hB₀ hB₁ hJ₀ hJ₁ e
      (hspl e (by omega)) (hs (e + 1) (by omega)) (hfil (e + 2) (by omega))
    obtain ⟨a, a', hx'⟩ := hdec x (gam_cast C H (by omega) hx)
    have hy := levF_mem C H ιB₀ ιB₁ τ hιB hτ a
    have hy' := levF_mem C H ιB₀ ιB₁ τ hιB hτ a'
    obtain ⟨b, hb⟩ := ih _ hy
    obtain ⟨b', hb'⟩ := ih _ hy'
    refine ⟨fun i => t₁ * b i + b' i, ?_⟩
    exact (frac₁_dec C H hts hφ₀ hu₀ hy hy' hx hx').trans
      ((congrArg₂ (fun A B => β₁ C H hφ₀ hu₀ t₁ * A + B) hb hb').trans
        (sum_comb₁ (β₁ C H hφ₀ hu₀) t₁ b b' (fun i => frac₁ C H (D + 1) (σ i) (hσ i))))

end Fin₁

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

theorem ov_g1 : letI := algKV K gV;
    (cvL L).trans WalkingSpan.Hom.snd ≫ g1 L =
      gW L.θ₁ L.sθ₁ (wz L ≫ Spec.map (CommRingCat.ofHom L.ψ₁)) (ov_hk1 L) ≫ (hT1 (q := q)).fromSpec := by
  letI := algKV K gV
  rw [g1, ← Category.assoc, gW_comp]
  exact congrArg (· ≫ (hT1 (q := q)).fromSpec) (gW_congr L.θ₁ L.sθ₁ (ov_e1 L) _ _)

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_SecCls =====
section

/-!
# S4-EtPBC-A, L1c (part 2): the cocycle map `ker g →+ Ext^(p+1)(Λ[W], F)`

`cocExt` is surjective, and its kernel is the image of `I^p(W)` (`cocExt_eq_zero_iff`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}} {F : EtSh Λ X} (I : InjectiveResolution F)

theorem cocExt_surjective (W : X.Etale) (p : ℕ) : Function.Surjective (cocExt Λ I W p) := by
  intro α
  obtain ⟨f, hf, rfl⟩ := I.extMk_surjective α _ (up_next p)
  have hz : freeEquiv Λ W _ f ∈ LinearMap.ker (secSc Λ I W p).g.hom := by
    change (I.cocomplex.d (p + 1) ((ComplexShape.up ℕ).next (p + 1))).hom.app (op W) (freeEquiv Λ W _ f) = 0
    rw [← freeEquiv_comp, hf, map_zero]
  refine ⟨⟨_, hz⟩, ?_⟩
  rw [cocExt_apply]
  exact extMk_congr Λ I
    (by rw [show cocSec Λ I ⟨_, hz⟩ = freeEquiv Λ W _ f from rfl, AddEquiv.symm_apply_apply]) _ _ _

end RamanujanPetersson.EtPBC

end

end


