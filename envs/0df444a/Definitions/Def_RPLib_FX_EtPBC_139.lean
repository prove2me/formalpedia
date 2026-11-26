-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_139
-- name    : RPLib_FX_EtPBC_139
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:33:28.262255+00:00
-- url     : https://prove2.me/theorems/2248593e-def0-5b34-963c-e11be8d6e8e2
-- title:
--   Proper base change for the projective line, library file 139
-- statement:
--   File 139 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovHat1`: S4-EtPBC-A, R4-T2 (A2c-3a): the completed chart rings as subrings of products of localizations
--   * `S4.Def_RP_EtPBC_A_CovHat3`: S4-EtPBC-A, R4-T2 (A2c-3c): structure maps of the completed charts and the localization property
--   * `S4.Def_RP_EtPBC_A_CovHat4`: S4-EtPBC-A, R4-T2 (A2c-3d): fractions `x / T₀ᵈ`, `x / T₁ᵈ` in the completed charts
--   * `S4.Def_RP_EtPBC_A_CovHat6`: S4-EtPBC-A, R4-T2 (A2c-3f): the level reductions of the completed charts are surjective
--   * `S4.Def_RP_EtPBC_A_CovHat11`: S4-EtPBC-A, R4-T2 (A2c-3h): the level reductions of the completed overlap
--   * `S4.Def_RP_EtPBC_A_CovAs6b`: S4-EtPBC-A, R4-T2 (A3 assembly, As6b): the overlap maps of the approximated cover
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_083
import Definitions.Def_RPLib_FX_EtPBC_090
import Definitions.Def_RPLib_FX_EtPBC_092
import Definitions.Def_RPLib_FX_EtPBC_130

/-!
# Proper base change for the projective line, library file 139

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovHat1`: S4-EtPBC-A, R4-T2 (A2c-3a): the completed chart rings as subrings of products of localizations
* `S4.Def_RP_EtPBC_A_CovHat3`: S4-EtPBC-A, R4-T2 (A2c-3c): structure maps of the completed charts and the localization property
* `S4.Def_RP_EtPBC_A_CovHat4`: S4-EtPBC-A, R4-T2 (A2c-3d): fractions `x / T₀ᵈ`, `x / T₁ᵈ` in the completed charts
* `S4.Def_RP_EtPBC_A_CovHat6`: S4-EtPBC-A, R4-T2 (A2c-3f): the level reductions of the completed charts are surjective
* `S4.Def_RP_EtPBC_A_CovHat11`: S4-EtPBC-A, R4-T2 (A2c-3h): the level reductions of the completed overlap
* `S4.Def_RP_EtPBC_A_CovAs6b`: S4-EtPBC-A, R4-T2 (A3 assembly, As6b): the overlap maps of the approximated cover
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_CovHat1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3a): the completed chart rings as subrings of products of localizations

For a tower `C`, `H` of level covers:
* `fB₀`, `fB₁`: `Bᵢ → ∏ₖ Eᵢ(k)`; `tFm = fB₀ t₀`, `sFm = fB₁ t₁`; `L₀ = (∏ E₀(k))[1/t]`, `L₁ = (∏ E₁(k))[1/s]`;
* `gam_cast`, `gam_one`, `gam_mul`, `gam_pow`; `gT₀ = (1, s)`, `gT₁ = (t, 1)` with `gT₀_mem`, `gT₁_mem`;
* **`hE₀`** `⊆ ∏ E₀(k) × L₁` (fractions `x / T₀ᵈ`), **`hE₁`** `⊆ L₀ × ∏ E₁(k)` (fractions `x / T₁ᵈ`),
  **`hE`** `⊆ L₀ × L₁` (fractions `x / T₁ᵃ T₀ᵇ`); **`hψ₀ : hE₀ →+* hE`**, **`hψ₁ : hE₁ →+* hE`**.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Hat

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k))

theorem mem_hE₁ (z : L₀ C × ∀ k, (C k).E₁) : z ∈ hE₁ C H ↔
    ∃ d, ∃ x ∈ Gam C H d, jL₀ C (tFm C ^ d) * z.1 = jL₀ C x.1 ∧ z.2 = x.2 :=
  Iff.rfl

end Hat

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

/-- **`B₁ → Ê₁`**: `b ↦ (φ₁ b ∈ L₀, (a₁ b)ₖ)`. -/
def β₁ : B₁ →+* hE₁ C H :=
  (((liftN₀ C hφ₀ hu₀).comp φ₁).prod (fB₁ C)).codRestrict (hE₁ C H) fun b => by
    obtain ⟨d, b', hb'⟩ := hφ₀.1 (φ₁ b)
    refine (mem_hE₁ C H _).2 ⟨d, (fB₀ C b', fB₁ C b), famB_mem C H hb'.symm, ?_, rfl⟩
    show jL₀ C (tFm C ^ d) * liftN₀ C hφ₀ hu₀ (φ₁ b) = jL₀ C (fB₀ C b')
    rw [← liftN₀_φ₀ C hφ₀ hu₀ b', ← hb']
    simp only [map_mul, map_pow, liftN₀_φ₀]

/-- **`N → Ê`**. -/
def β : N →+* hE C H hts :=
  ((liftN₀ C hφ₀ hu₀).prod (liftN₁ C hφ₁ hu₁)).codRestrict (hE C H hts) fun n => by
    obtain ⟨a, b₀, ha⟩ := hφ₀.1 n
    obtain ⟨b, b₁, hb⟩ := hφ₁.1 n
    have hd : φ₀ t₀ ^ b * φ₁ t₁ ^ b = 1 := by rw [← mul_pow, hts, one_pow]
    refine (mem_hE C H hts _).2 ⟨a, b, (fB₀ C b₀, fB₁ C b₁), famB_mem C H ?_, ?_, ?_⟩
    · rw [← ha, ← hb, pow_add]
      linear_combination (-(φ₀ t₀ ^ a * n)) * hd
    · show jL₀ C (tFm C ^ a) * liftN₀ C hφ₀ hu₀ n = jL₀ C (fB₀ C b₀)
      rw [← liftN₀_φ₀ C hφ₀ hu₀ b₀, ← ha]
      simp only [map_mul, map_pow, liftN₀_φ₀]
    · show jL₁ C (sFm C ^ b) * liftN₁ C hφ₁ hu₁ n = jL₁ C (fB₁ C b₁)
      rw [← liftN₁_φ₁ C hφ₁ hu₁ b₁, ← hb]
      simp only [map_mul, map_pow, liftN₁_φ₁]

theorem β_val (n : N) : (β C H hts hφ₀ hu₀ hφ₁ hu₁ n : L₀ C × L₁ C) = (liftN₀ C hφ₀ hu₀ n, liftN₁ C hφ₁ hu₁ n) :=
  rfl

/-- **The chart squares commute**: `hψ₀ ∘ β₀ = β ∘ φ₀`. -/
def hψ₀_β₀ : (hψ₀ C H hts).comp (β₀ C H hts hφ₁ hu₁) = (β C H hts hφ₀ hu₀ hφ₁ hu₁).comp φ₀ :=
  RingHom.ext fun b => Subtype.ext (Prod.ext (liftN₀_φ₀ C hφ₀ hu₀ b).symm rfl)

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

/-- **`x / T₁ᵈ ∈ Ê₁`**. -/
def frac₁ (d : ℕ) (x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)) (hx : x ∈ Gam C H d) : hE₁ C H :=
  ⟨(IsLocalization.mk' (L₀ C) x.1 (⟨tFm C ^ d, d, rfl⟩ : Submonoid.powers (tFm C)), x.2),
    (mem_hE₁ C H _).2 ⟨d, x, hx, by rw [mul_comm]; exact IsLocalization.mk'_spec (L₀ C) x.1 _, rfl⟩⟩

variable {C H}

theorem frac₁_val {d : ℕ} {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d) :
    (frac₁ C H d x hx : L₀ C × ∀ k, (C k).E₁) =
      (IsLocalization.mk' (L₀ C) x.1 (⟨tFm C ^ d, d, rfl⟩ : Submonoid.powers (tFm C)), x.2) :=
  rfl

theorem frac₁_spec {d : ℕ} {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d) :
    jL₀ C (tFm C ^ d) * (frac₁ C H d x hx : L₀ C × ∀ k, (C k).E₁).1 = jL₀ C x.1 := by
  rw [mul_comm]
  exact IsLocalization.mk'_spec (L₀ C) x.1 _

theorem hE₁_ext {z z' : hE₁ C H} (d : ℕ)
    (h1 : jL₀ C (tFm C ^ d) * (z : L₀ C × ∀ k, (C k).E₁).1 = jL₀ C (tFm C ^ d) * (z' : L₀ C × ∀ k, (C k).E₁).1)
    (h2 : (z : L₀ C × ∀ k, (C k).E₁).2 = (z' : L₀ C × ∀ k, (C k).E₁).2) : z = z' :=
  Subtype.ext (Prod.ext ((isUnit_jL₀ C d).mul_left_cancel h1) h2)

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

/-- **The level-`k` reduction `Ê₁ → E₁(k)`.** -/
def θ₁ (k : ℕ) : hE₁ C H →+* (C k).E₁ :=
  ((Pi.evalRingHom (fun k => ((C k).E₁ : Type u)) k).comp (RingHom.snd (L₀ C) _)).comp (hE₁ C H).subtype

end Theta

section Surj

end Surj

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovHat11 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3h): the level reductions of the completed overlap

* `ev₀ k : L₀ → E(k)` (the lift of `ψ₀ ∘ eval k`, `t ↦ u` is a unit), `ev₀_jL₀`;
* **`θ k : Ê → E(k)`**, compatible with the chart reductions: **`θ_hψ₀`** (`θ ∘ ψ̂₀ = ψ₀ ∘ θ₀`), **`θ_hψ₁`**
  (`θ ∘ ψ̂₁ = ψ₁ ∘ θ₁`), and with the structure maps: **`θ_β`** (`θ ∘ β = a ∘ mk`).
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Ov

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (hts : φ₀ t₀ * φ₁ t₁ = 1)
  (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀)) (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁))

theorem θ_apply (k : ℕ) (z : hE C H hts) : θ C H hts k z = ev₀ C hts k (z : L₀ C × L₁ C).1 := rfl

/-- **`θ ∘ ψ̂₀ = ψ₀ ∘ θ₀`.** -/
def θ_hψ₀ (k : ℕ) (z : hE₀ C H hts) : θ C H hts k (hψ₀ C H hts z) = (C k).ψ₀ (θ₀ C H hts k z) :=
  ev₀_jL₀ C hts k _

/-- **`θ ∘ β = a ∘ mk`.** -/
def θ_β (k : ℕ) (n : N) :
    θ C H hts k (β C H hts hφ₀ hu₀ hφ₁ hu₁ n) = (C k).a (Ideal.Quotient.mk (JN ^ (k + 1)) n) := by
  obtain ⟨m, b, hb⟩ := hφ₀.1 n
  show ev₀ C hts k (liftN₀ C hφ₀ hu₀ n) = (C k).a (Ideal.Quotient.mk (JN ^ (k + 1)) n)
  have e1 := congrArg (fun w => ev₀ C hts k (liftN₀ C hφ₀ hu₀ w)) hb
  simp only [map_mul, map_pow, liftN₀_φ₀, ev₀_jL₀, fB₀_apply, lψθ₀] at e1
  have e2 := congrArg (fun w => (C k).a (Ideal.Quotient.mk (JN ^ (k + 1)) w)) hb
  simp only [map_mul, map_pow] at e2
  have hu' : (C k).a (Ideal.Quotient.mk (JN ^ (k + 1)) (φ₀ t₀)) *
      (C k).ψ₁ ((C k).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁)) = 1 := by
    rw [← lψθ₀]
    exact lhv hts (C k)
  have hud : (C k).a (Ideal.Quotient.mk (JN ^ (k + 1)) (φ₀ t₀)) ^ m *
      (C k).ψ₁ ((C k).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁)) ^ m = 1 := by
    rw [← mul_pow, hu', one_pow]
  linear_combination (C k).ψ₁ ((C k).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁)) ^ m * e1 -
    (C k).ψ₁ ((C k).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁)) ^ m * e2 -
    (ev₀ C hts k (liftN₀ C hφ₀ hu₀ n) - (C k).a (Ideal.Quotient.mk (JN ^ (k + 1)) n)) * hud

end Ov

end RamanujanPetersson.EtPBC.Cov

end

end

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

variable (uC : Fin r₀ → MvPolynomial (Fin r₁) (C ⊗[A] N)) (vC : Fin r₁ → MvPolynomial (Fin r₀) (C ⊗[A] N))
  (H : (∀ j, MvPolynomial.bind₁ uC (gmap (bcC φ₀ C) gC₀ j) ∈ Ideal.span (Set.range (gmap (bcC φ₁ C) gC₁))) ∧
    (∀ i, MvPolynomial.bind₁ vC (gmap (bcC φ₁ C) gC₁ i) ∈ Ideal.span (Set.range (gmap (bcC φ₀ C) gC₀))) ∧
    (∀ i, MvPolynomial.bind₁ uC (vC i) - MvPolynomial.X i ∈ Ideal.span (Set.range (gmap (bcC φ₁ C) gC₁))) ∧
    (∀ j, MvPolynomial.bind₁ vC (uC j) - MvPolynomial.X j ∈ Ideal.span (Set.range (gmap (bcC φ₀ C) gC₀))))

variable {G Q : Type u} [CommRing G] [CommRing Q]

theorem ctheta1 (θ₁ : Pres (gmap (tsC σ B₁) gC₁) →+* G) (θN : Pres (gmap (tsC σ N) (gmap (bcC φ₀ C) gC₀)) →+* Q)
    (p : G →+* Q)
    (hc : ∀ x, p (θ₁ (algebraMap (R' ⊗[A] B₁) _ x)) = θN (algebraMap (R' ⊗[A] N) _ (bcS R' φ₁ x)))
    (hX : ∀ j, p (θ₁ (Ideal.Quotient.mk _ (MvPolynomial.X j))) =
      θN (Ideal.Quotient.mk _ (MvPolynomial.map (tsC σ N) (vC j)))) :
    p.comp θ₁ = θN.comp (psi1 φ₀ φ₁ σ gC₀ gC₁ uC vC H) :=
  pres_ringHom_ext _ _ (fun a => by rw [RingHom.comp_apply, RingHom.comp_apply, psi1_alg]; exact hc a)
    (fun j => by rw [RingHom.comp_apply, RingHom.comp_apply, psi1_X]; exact hX j)

end Psi

end RamanujanPetersson.EtPBC.Cov

end

end


