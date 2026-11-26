-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_167
-- name    : RPLib_FX_EtPBC_167
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:00:17.68378+00:00
-- url     : https://prove2.me/theorems/d64ecce0-ea0e-5913-9f29-0953d6018a4f
-- title:
--   Proper base change for the projective line, library file 167
-- statement:
--   File 167 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
--   * `S4.Def_RP_EtPBC_A_CovHat3`: S4-EtPBC-A, R4-T2 (A2c-3c): structure maps of the completed charts and the localization property
--   * `S4.Def_RP_EtPBC_A_CovHat8`: S4-EtPBC-A, R4-T2 (A2c-4a): shifts of fractions by `T₀`, `T₁`
--   * `S4.Def_RP_EtPBC_A_CovHat7`: S4-EtPBC-A, R4-T2 (A2c-3g): the kernels of the level reductions of the completed charts
--   * `S4.Def_RP_EtPBC_A_CovHat9`: S4-EtPBC-A, R4-T2 (A2c-4b): the completed chart `Ê₀` is finite over `B₀`
--   * `S4.Def_RP_EtPBC_A_CovSj`: S4-EtPBC-A, R4-T2 (G1e): making the lifted cover surjective
--   * `S4.Def_RP_EtPBC_A_SecCls`: S4-EtPBC-A, L1c (part 2): the cocycle map `ker g →+ Ext^(p+1)(Λ[W], F)`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_154
import Definitions.Def_RPLib_FX_EtPBC_160
import Definitions.Def_RPLib_FX_EtPBC_161

/-!
# Proper base change for the projective line, library file 167

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
* `S4.Def_RP_EtPBC_A_CovHat3`: S4-EtPBC-A, R4-T2 (A2c-3c): structure maps of the completed charts and the localization property
* `S4.Def_RP_EtPBC_A_CovHat8`: S4-EtPBC-A, R4-T2 (A2c-4a): shifts of fractions by `T₀`, `T₁`
* `S4.Def_RP_EtPBC_A_CovHat7`: S4-EtPBC-A, R4-T2 (A2c-3g): the kernels of the level reductions of the completed charts
* `S4.Def_RP_EtPBC_A_CovHat9`: S4-EtPBC-A, R4-T2 (A2c-4b): the completed chart `Ê₀` is finite over `B₀`
* `S4.Def_RP_EtPBC_A_CovSj`: S4-EtPBC-A, R4-T2 (G1e): making the lifted cover surjective
* `S4.Def_RP_EtPBC_A_SecCls`: S4-EtPBC-A, L1c (part 2): the cocycle map `ker g →+ Ext^(p+1)(Λ[W], F)`
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_CovHat2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts

* **`hE`** `⊆ L₀ × L₁` (fractions `x / T₁ᵃ T₀ᵇ`, `x ∈ Gam (a + b)`); **`hψ₀ : hE₀ →+* hE`**, **`hψ₁ : hE₁ →+* hE`**;
* `ρ₀_fB`, `ρ₁_fB`, **`famB_mem`**: `(fB₀ b₀, fB₁ b₁) ∈ Gam d` when `φ₀ b₀ = φ₀ t₀ ^ d * φ₁ b₁`;
* **`liftN₀ : N →+* L₀`**, **`liftN₁ : N →+* L₁`** (from `N = B₀[1/t₀] = B₁[1/t₁]`), `liftN₀_φ₀`, `liftN₁_φ₁`,
  `liftN₀_inv`, `liftN₁_inv`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Hat2

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k))

theorem hψ₁_val (hts : φ₀ t₀ * φ₁ t₁ = 1) (z : hE₁ C H) :
    (hψ₁ C H hts z : L₀ C × L₁ C) = ((z : L₀ C × ∀ k, (C k).E₁).1, jL₁ C (z : L₀ C × ∀ k, (C k).E₁).2) :=
  rfl

end Hat2

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovHat3 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3c): structure maps of the completed charts and the localization property

* **`β₀ : B₀ →+* hE₀`**, **`β₁ : B₁ →+* hE₁`**, **`β : N →+* hE`**, with `β₀_val`, `β₁_val`, `β_val`;
* **`hψ₀_β₀`**, **`hψ₁_β₁`**: `hψᵢ ∘ βᵢ = β ∘ φᵢ`;
* **`aw_hψ₀`**: `IsAwayMap hψ₀ (β₀ t₀)`, **`aw_hψ₁`**: `IsAwayMap hψ₁ (β₁ t₁)`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Hat3

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k))
  (hts : φ₀ t₀ * φ₁ t₁ = 1) (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀)) (hφ₁ : IsAwayMap φ₁ t₁)
  (hu₁ : IsUnit (φ₁ t₁))

/-- `hψ₁ ∘ β₁ = β ∘ φ₁`. -/
def hψ₁_β₁ : (hψ₁ C H hts).comp (β₁ C H hφ₀ hu₀) = (β C H hts hφ₀ hu₀ hφ₁ hu₁).comp φ₁ :=
  RingHom.ext fun b => Subtype.ext (Prod.ext rfl (liftN₁_φ₁ C hφ₁ hu₁ b).symm)

end Hat3

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

include hts in
/-- The fraction of `T₀ y + T₁ y'` in chart `1`. -/
theorem frac₁_dec {e : ℕ} {x y y' : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hy : y ∈ Gam C H (e + 1))
    (hy' : y' ∈ Gam C H (e + 1)) (hx : x ∈ Gam C H (e + 1 + 1)) (hx' : x = mT₀ C y + mT₁ C y') :
    frac₁ C H (e + 1 + 1) x hx =
      β₁ C H hφ₀ hu₀ t₁ * frac₁ C H (e + 1) y hy + frac₁ C H (e + 1) y' hy' := by
  have h0 := mT₀_mem C H hts hy
  have h1 := mT₁_mem C H hy'
  rw [frac₁_congr hx' hx (add_mem h0 h1), ← frac₁_add h0 h1, frac₁_mT₀ C H hts hφ₀ hu₀ hy h0,
    frac₁_mT₁ C H hy' h1]

end MT

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovHat7 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3g): the kernels of the level reductions of the completed charts

Over a noetherian `p`-precomplete `R`: **`θ₀_ker`**: `ker (θ₀ k) = p^(k+1) Ê₀`, **`θ₁_ker`**: `ker (θ₁ k) = p^(k+1) Ê₁`
(a fraction vanishing at level `k` becomes, after multiplying by a power of `T₀` resp. `T₁`, a family vanishing at
level `k` (`van₀`, `van₁`), hence a `p^(k+1)`-combination of generators by `gam_ker` (`frac₀_mem_of_van`,
`frac₁_mem_of_van`)).
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Van

end Van

section Ker

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (p : Ideal R) (hts : φ₀ t₀ * φ₁ t₁ = 1) (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀))
  (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁))

/-- **`ker (θ₀ k) = p^(k+1) Ê₀`.** -/
def θ₀_ker [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R) (hα : ∀ i, α i ∈ p)
    (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite) (hB₁ : (eval₂RingHom ιB₁ t₁).Finite)
    (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d) (k : ℕ) :
    RingHom.ker (θ₀ C H hts k) = (p ^ (k + 1)).map (ιh₀ C H ιB₀ hts hφ₁ hu₁) := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    obtain ⟨d, x, hx, h1, h2⟩ := (mem_hE₀ C H hts _).1 z.2
    have hx0 : x.1 k = 0 := (congrFun h1 k).symm.trans hz
    obtain ⟨m, hm⟩ := van₀ C H hts hx k hx0
    rw [eq_frac₀ hts z hx h1 h2, ← frac₀_T₀ hts hx (m + D)]
    exact frac₀_mem_of_van C H ιB₀ ιB₁ p hts hφ₁ hu₁ α hα hιB hB₀ hB₁ hJ₀ hJ₁ (hs _ (by omega))
      (hfil _ (by omega)) _ k (hm D).1 (hm D).2
  · rw [Ideal.map_le_iff_le_comap]
    intro c hc
    rw [Ideal.mem_comap, RingHom.mem_ker]
    show (C k).a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) (ιB₀ c)) = 0
    have hm : ιB₀ c ∈ J₀ ^ (k + 1) := by
      rw [hJ₀, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hc
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hm, map_zero]

end Ker

end RamanujanPetersson.EtPBC.Cov

end

end

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

/-- **`Ê₀` is spanned over `B₀` by finitely many fractions.** -/
theorem hE₀_span [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R) (hα : ∀ i, α i ∈ p)
    (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite) (hB₁ : (eval₂RingHom ιB₁ t₁).Finite)
    (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hspl : ∀ e, D ≤ e → ∀ z : (C 0).E, ∃ (x₀ : (C 0).E₀) (x₁ : (C 0).E₁),
      z = (C 0).ψ₀ x₀ - (C 0).u ^ e * (C 0).ψ₁ x₁)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d) :
    ∃ (r : ℕ) (w : Fin r → hE₀ C H hts), ∀ z, ∃ b : Fin r → B₀, z = ∑ i, β₀ C H hts hφ₁ hu₁ (b i) * w i := by
  obtain ⟨r, σ, hσ, hgen0⟩ := gen_sys C H ιB₀ ιB₁ hts hιB hB₀ hB₁ (hs (D + 1) (by omega))
  refine ⟨r, fun i => frac₀ C H hts (D + 1) (σ i) (hσ i), fun z => ?_⟩
  obtain ⟨d, x, hx, h1, h2⟩ := (mem_hE₀ C H hts _).1 z.2
  rw [eq_frac₀ hts z hx h1 h2, ← frac₀_T₀ hts hx (D + 1)]
  exact span_key₀ C H ιB₀ ιB₁ p hts hφ₁ hu₁ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hspl hs hfil σ hσ hgen0 _ (by omega) _ _

end Fin₀

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

/-- **The range of `Y_x ⟶ Y_{V'}` lies in the range of the glued cover** (for surjective `q`). -/
theorem range_yxL [Surjective q] : Set.range (yxL L) ⊆ Set.range (dL L).toBase := by
  letI := algKV K gV
  rintro _ ⟨y, rfl⟩
  obtain ⟨t, rfl⟩ := q.surjective y
  have hy : q t ∈ fx K gV π x ⁻¹ᵁ Yc K gV π 0 ⊔ fx K gV π x ⁻¹ᵁ Yc K gV π 1 := by
    rw [Yx_sup K gV π x]
    trivial
  rcases TopologicalSpace.Opens.mem_sup.mp hy with h | h
  · obtain ⟨s, rfl⟩ : t ∈ Set.range (hT0 (q := q)).fromSpec := by
      rw [IsAffineOpen.range_fromSpec]
      exact h
    refine ⟨(dL L).cover.f WalkingSpan.left (Spec.map (CommRingCat.ofHom L.θ₀) s), ?_⟩
    have e := congrArg (fun φ => φ s) (fromSpec_yx K gV π x L.χ' (hxL L) q (isAffineOpen_Yc K gV π 0)
      (struct_res K gV π 0) hW0 hT0 L.θ₀ L.hθ₀)
    have e2 := congrArg (fun φ => (Spec.map (CommRingCat.ofHom L.θ₀) ≫ φ) s) (eqY0 L)
    simp only [Scheme.Hom.comp_apply] at e e2
    exact e2.symm.trans e.symm
  · obtain ⟨s, rfl⟩ : t ∈ Set.range (hT1 (q := q)).fromSpec := by
      rw [IsAffineOpen.range_fromSpec]
      exact h
    refine ⟨(dL L).cover.f WalkingSpan.right (Spec.map (CommRingCat.ofHom L.θ₁) s), ?_⟩
    have e := congrArg (fun φ => φ s) (fromSpec_yx K gV π x L.χ' (hxL L) q (isAffineOpen_Yc K gV π 1)
      (struct_res K gV π 1) hW1 hT1 L.θ₁ L.hθ₁)
    have e2 := congrArg (fun φ => (Spec.map (CommRingCat.ofHom L.θ₁) ≫ φ) s) (eqY1 L)
    simp only [Scheme.Hom.comp_apply] at e e2
    exact e2.symm.trans e.symm

end Lifted

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

theorem cocExt_apply (W : X.Etale) (p : ℕ) (z : LinearMap.ker (secSc Λ I W p).g.hom) :
    cocExt Λ I W p z = I.extMk ((freeEquiv Λ W (I.cocomplex.X (p + 1))).symm (cocSec Λ I z))
      ((ComplexShape.up ℕ).next (p + 1)) (up_next p) (cocExt_aux Λ I W p z) := rfl

theorem cocExt_eq_zero_iff (W : X.Etale) (p : ℕ) (z : LinearMap.ker (secSc Λ I W p).g.hom) :
    cocExt Λ I W p z = 0 ↔ z ∈ LinearMap.range (secSc Λ I W p).moduleCatToCycles := by
  rw [cocExt_apply, I.extMk_eq_zero_iff _ _ _ _ _ (up_prev p)]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨freeEquiv Λ W _ g, Subtype.ext ?_⟩
    change (I.cocomplex.d ((ComplexShape.up ℕ).prev (p + 1)) (p + 1)).hom.app (op W) (freeEquiv Λ W _ g) =
      cocSec Λ I z
    rw [← freeEquiv_comp, hg, AddEquiv.apply_symm_apply]
  · rintro ⟨y, hy⟩
    let y' : (I.cocomplex.X ((ComplexShape.up ℕ).prev (p + 1))).val.obj (op W) := y
    refine ⟨(freeEquiv Λ W (I.cocomplex.X ((ComplexShape.up ℕ).prev (p + 1)))).symm y', ?_⟩
    apply (freeEquiv Λ W _).injective
    rw [freeEquiv_comp, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact congrArg Subtype.val hy

end RamanujanPetersson.EtPBC

end

end


