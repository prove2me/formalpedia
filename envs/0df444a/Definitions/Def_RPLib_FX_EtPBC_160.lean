-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_160
-- name    : RPLib_FX_EtPBC_160
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:57:46.419+00:00
-- url     : https://prove2.me/theorems/98e66a7a-db31-58e3-8569-85a50dc3ff61
-- title:
--   Proper base change for the projective line, library file 160
-- statement:
--   File 160 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
--   * `S4.Def_RP_EtPBC_A_CovHat3`: S4-EtPBC-A, R4-T2 (A2c-3c): structure maps of the completed charts and the localization property
--   * `S4.Def_RP_EtPBC_A_CovHat4`: S4-EtPBC-A, R4-T2 (A2c-3d): fractions `x / T₀ᵈ`, `x / T₁ᵈ` in the completed charts
--   * `S4.Def_RP_EtPBC_A_CovHat7`: S4-EtPBC-A, R4-T2 (A2c-3g): the kernels of the level reductions of the completed charts
--   * `S4.Def_RP_EtPBC_A_CovHat9`: S4-EtPBC-A, R4-T2 (A2c-4b): the completed chart `Ê₀` is finite over `B₀`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_152
import Definitions.Def_RPLib_FX_EtPBC_153

/-!
# Proper base change for the projective line, library file 160

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
* `S4.Def_RP_EtPBC_A_CovHat3`: S4-EtPBC-A, R4-T2 (A2c-3c): structure maps of the completed charts and the localization property
* `S4.Def_RP_EtPBC_A_CovHat4`: S4-EtPBC-A, R4-T2 (A2c-3d): fractions `x / T₀ᵈ`, `x / T₁ᵈ` in the completed charts
* `S4.Def_RP_EtPBC_A_CovHat7`: S4-EtPBC-A, R4-T2 (A2c-3g): the kernels of the level reductions of the completed charts
* `S4.Def_RP_EtPBC_A_CovHat9`: S4-EtPBC-A, R4-T2 (A2c-4b): the completed chart `Ê₀` is finite over `B₀`
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

/-- **`Ê₁ → Ê`** (`x / T₁ᵈ ↦ x / T₁ᵈ T₀⁰`). -/
def hψ₁ (hts : φ₀ t₀ * φ₁ t₁ = 1) : hE₁ C H →+* hE C H hts :=
  ((RingHom.prodMap (RingHom.id (L₀ C)) (jL₁ C)).comp (hE₁ C H).subtype).codRestrict (hE C H hts)
    fun z => by
      obtain ⟨d, x, hx, h1, h2⟩ := (mem_hE₁ C H z.1).1 z.2
      refine ⟨d, 0, x, gam_cast C H (Nat.add_zero d).symm hx, h1, ?_⟩
      show jL₁ C (sFm C ^ 0) * jL₁ C z.1.2 = jL₁ C x.2
      rw [pow_zero, map_one, one_mul, h2]

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

/-- **`Ê = Ê₀[1/t₀]`.** -/
theorem aw_hψ₀ : IsAwayMap (hψ₀ C H hts) (β₀ C H hts hφ₁ hu₁ t₀) := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨a, b, x, hx, h1, h2⟩ := (mem_hE C H hts y).1 hy
    have hinva : jL₁ C (sFm C) ^ a * liftN₁ C hφ₁ hu₁ (φ₀ t₀) ^ a = 1 := by
      rw [← mul_pow, liftN₁_inv C hts hφ₁ hu₁, one_pow]
    have hm : (x.1, liftN₁ C hφ₁ hu₁ (φ₀ t₀) ^ a * y.2) ∈ hE₀ C H hts := by
      refine (mem_hE₀ C H hts _).2 ⟨a + b, x, hx, rfl, ?_⟩
      show jL₁ C (sFm C ^ (a + b)) * (liftN₁ C hφ₁ hu₁ (φ₀ t₀) ^ a * y.2) = jL₁ C x.2
      simp only [pow_add, map_mul, map_pow] at h2 ⊢
      linear_combination (jL₁ C (sFm C) ^ b * y.2) * hinva + h2
    refine ⟨a, ⟨_, hm⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
    · show jL₀ C (fB₀ C t₀) ^ a * y.1 = jL₀ C x.1
      rw [← h1, map_pow]
    · rfl
  · rintro ⟨z, hz⟩ h0
    have h01 : jL₀ C z.1 = 0 := congrArg (fun w : hE C H hts => (w : L₀ C × L₁ C).1) h0
    have h02 : z.2 = 0 := congrArg (fun w : hE C H hts => (w : L₀ C × L₁ C).2) h0
    obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (tFm C)) (L₀ C) z.1).1 h01
    refine ⟨m, Subtype.ext (Prod.ext ?_ ?_)⟩
    · show fB₀ C t₀ ^ m * z.1 = 0
      exact hm
    · show liftN₁ C hφ₁ hu₁ (φ₀ t₀) ^ m * z.2 = 0
      rw [h02, mul_zero]

end Hat3

end RamanujanPetersson.EtPBC.Cov

end

end

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

theorem eq_frac₁ (z : hE₁ C H) {d : ℕ} {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d)
    (h1 : jL₀ C (tFm C ^ d) * (z : L₀ C × ∀ k, (C k).E₁).1 = jL₀ C x.1)
    (h2 : (z : L₀ C × ∀ k, (C k).E₁).2 = x.2) : z = frac₁ C H d x hx :=
  hE₁_ext d (h1.trans (frac₁_spec hx).symm) h2

theorem frac₁_congr {d : ℕ} {x y : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (h : x = y) (hx : x ∈ Gam C H d)
    (hy : y ∈ Gam C H d) : frac₁ C H d x hx = frac₁ C H d y hy := by
  subst h
  rfl

end Frac

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

/-- A fraction of a family vanishing at level `k` lies in `p^(k+1) Ê₀`. -/
def frac₀_mem_of_van [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R) (hα : ∀ i, α i ∈ p)
    (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite) (hB₁ : (eval₂RingHom ιB₁ t₁).Finite)
    (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) {e : ℕ}
    (hs : ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) e))
    (hfil : ∀ k, FilProp ιB₀ ιB₁ p α (C k) e) {y : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hy : y ∈ Gam C H e)
    (k : ℕ) (h0 : y.1 k = 0) (h1 : y.2 k = 0) :
    frac₀ C H hts e y hy ∈ (p ^ (k + 1)).map (ιh₀ C H ιB₀ hts hφ₁ hu₁) := by
  obtain ⟨r, σ, hσ, hgen0⟩ := gen_sys C H ιB₀ ιB₁ hts hιB hB₀ hB₁ hs
  obtain ⟨a, ha, hlev⟩ := gam_ker C H ιB₀ ιB₁ p σ α hα hιB hJ₀ hJ₁ hσ hgen0 hfil hy k h0 h1
  have hyeq : y = ∑ i, ιP C ιB₀ ιB₁ (a i) * σ i := by
    rw [← levF_eq]
    exact Prod.ext (funext fun n => congrArg Prod.fst (hlev n)) (funext fun n => congrArg Prod.snd (hlev n))
  rw [frac₀_lin C H ιB₀ ιB₁ hts hφ₁ hu₁ hιB hσ a hy hyeq]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (ha i))

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

/-- Every fraction of degree `≥ D + 1` is a `B₀`-combination of the fractions of the generators `σ`. -/
theorem span_key₀ [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R) (hα : ∀ i, α i ∈ p)
    (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite) (hB₁ : (eval₂RingHom ιB₁ t₁).Finite)
    (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hspl : ∀ e, D ≤ e → ∀ z : (C 0).E, ∃ (x₀ : (C 0).E₀) (x₁ : (C 0).E₁),
      z = (C 0).ψ₀ x₀ - (C 0).u ^ e * (C 0).ψ₁ x₁)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d)
    {r : ℕ} (σ : Fin r → (∀ k, (C k).E₀) × (∀ k, (C k).E₁)) (hσ : ∀ i, σ i ∈ Gam C H (D + 1))
    (hgen0 : ∀ y ∈ (C 0).sec (D + 1), ∃ c, y = lev C ιB₀ ιB₁ σ 0 c) (d : ℕ) (hd : D + 1 ≤ d) :
    ∀ x (hx : x ∈ Gam C H d), ∃ b : Fin r → B₀,
      frac₀ C H hts d x hx = ∑ i, β₀ C H hts hφ₁ hu₁ (b i) * frac₀ C H hts (D + 1) (σ i) (hσ i) := by
  induction d, hd using Nat.le_induction with
  | base =>
    intro x hx
    obtain ⟨a, ha⟩ := gam_gen C H ιB₀ ιB₁ p σ α hα hιB hJ₀ hJ₁ hσ hgen0 (hfil (D + 1) (by omega)) hx
    have hxeq : x = ∑ i, ιP C ιB₀ ιB₁ (a i) * σ i := by
      rw [← levF_eq]
      exact Prod.ext (funext fun n => congrArg Prod.fst (ha n)) (funext fun n => congrArg Prod.snd (ha n))
    exact ⟨fun i => ιB₀ (a i), frac₀_lin C H ιB₀ ιB₁ hts hφ₁ hu₁ hιB hσ a hx hxeq⟩
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
    refine ⟨fun i => b i + t₀ * b' i, ?_⟩
    exact (frac₀_dec C H hts hφ₁ hu₁ hy hy' hx hx').trans
      ((congrArg₂ (fun A B => A + β₀ C H hts hφ₁ hu₁ t₀ * B) hb hb').trans
        (sum_comb₀ (β₀ C H hts hφ₁ hu₁) t₀ b b' (fun i => frac₀ C H hts (D + 1) (σ i) (hσ i))))

end Fin₀

end RamanujanPetersson.EtPBC.Cov

end

end


