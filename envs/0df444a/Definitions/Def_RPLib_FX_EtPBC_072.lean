-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_072
-- name    : RPLib_FX_EtPBC_072
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T21:23:09.139028+00:00
-- url     : https://prove2.me/theorems/e4a9743a-adc6-5334-a244-90e27a83f23c
-- title:
--   Proper base change for the projective line, library file 072
-- statement:
--   File 072 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovHat1`: S4-EtPBC-A, R4-T2 (A2c-3a): the completed chart rings as subrings of products of localizations
--   * `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
--   * `S4.Def_RP_EtPBC_A_CovHat4`: S4-EtPBC-A, R4-T2 (A2c-3d): fractions `x / T₀ᵈ`, `x / T₁ᵈ` in the completed charts
--   * `S4.Def_RP_EtPBC_A_CovHat6`: S4-EtPBC-A, R4-T2 (A2c-3f): the level reductions of the completed charts are surjective
--   * `S4.Def_RP_EtPBC_A_DescG3`: S4-EtPBC-A, R4-T1c (part 2): the glued cover `U₀ ⟶ X` is finite, etale and surjective
--   * `S4.Def_RP_EtPBC_A_O2Sh1`: S4-EtPBC-A, O2 M6 (O2Sh1): `π_*` is exact for a separated etale `π` of constant degree
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_062
import Definitions.Def_RPLib_FX_EtPBC_063

/-!
# Proper base change for the projective line, library file 072

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovHat1`: S4-EtPBC-A, R4-T2 (A2c-3a): the completed chart rings as subrings of products of localizations
* `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
* `S4.Def_RP_EtPBC_A_CovHat4`: S4-EtPBC-A, R4-T2 (A2c-3d): fractions `x / T₀ᵈ`, `x / T₁ᵈ` in the completed charts
* `S4.Def_RP_EtPBC_A_CovHat6`: S4-EtPBC-A, R4-T2 (A2c-3f): the level reductions of the completed charts are surjective
* `S4.Def_RP_EtPBC_A_DescG3`: S4-EtPBC-A, R4-T1c (part 2): the glued cover `U₀ ⟶ X` is finite, etale and surjective
* `S4.Def_RP_EtPBC_A_O2Sh1`: S4-EtPBC-A, O2 M6 (O2Sh1): `π_*` is exact for a separated etale `π` of constant degree
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

/-- **The completed chart ring `Ê₀`**: fractions `x / T₀ᵈ` (`x ∈ Gam d`), as `(x.1, x.2 / sᵈ)`. -/
def hE₀ (hts : φ₀ t₀ * φ₁ t₁ = 1) : Subring ((∀ k, (C k).E₀) × L₁ C) where
  carrier := {z | ∃ d, ∃ x ∈ Gam C H d, z.1 = x.1 ∧ jL₁ C (sFm C ^ d) * z.2 = jL₁ C x.2}
  add_mem' := by
    rintro z z' ⟨d, x, hx, h1, h2⟩ ⟨e, y, hy, h1', h2'⟩
    refine ⟨d + e, gT₀ C ^ e * x + gT₀ C ^ d * y,
      add_mem (gT₀_pow_mem C H hts e hx) (gam_cast C H (by ring) (gT₀_pow_mem C H hts d hy)), ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.fst_mul, Prod.pow_fst, gT₀, one_pow, one_mul, h1, h1']
    · simp only [Prod.snd_add, Prod.snd_mul, Prod.pow_snd, gT₀, map_add, map_mul, pow_add]
      linear_combination jL₁ C (sFm C ^ e) * h2 + jL₁ C (sFm C ^ d) * h2'
  zero_mem' := ⟨0, 0, zero_mem _, rfl, by simp only [Prod.snd_zero, mul_zero, map_zero]⟩
  one_mem' := ⟨0, 1, gam_one C H, rfl, by rw [pow_zero, map_one, one_mul, Prod.snd_one, Prod.snd_one, map_one]⟩
  mul_mem' := by
    rintro z z' ⟨d, x, hx, h1, h2⟩ ⟨e, y, hy, h1', h2'⟩
    refine ⟨d + e, x * y, gam_mul C H hx hy, ?_, ?_⟩
    · simp only [Prod.fst_mul, h1, h1']
    · simp only [Prod.snd_mul, map_mul, pow_add]
      linear_combination (jL₁ C (sFm C ^ e) * z'.2) * h2 + jL₁ C x.2 * h2'
  neg_mem' := by
    rintro z ⟨d, x, hx, h1, h2⟩
    refine ⟨d, -x, neg_mem hx, ?_, ?_⟩
    · simp only [Prod.fst_neg, h1]
    · simp only [Prod.snd_neg, map_neg]
      linear_combination -h2

theorem mem_hE₀ (hts : φ₀ t₀ * φ₁ t₁ = 1) (z : (∀ k, (C k).E₀) × L₁ C) : z ∈ hE₀ C H hts ↔
    ∃ d, ∃ x ∈ Gam C H d, z.1 = x.1 ∧ jL₁ C (sFm C ^ d) * z.2 = jL₁ C x.2 :=
  Iff.rfl

end Hat

end RamanujanPetersson.EtPBC.Cov

end

end

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

/-- **The completed overlap ring `Ê`**: fractions `x / T₁ᵃ T₀ᵇ` (`x ∈ Gam (a + b)`), as `(x.1 / tᵃ, x.2 / sᵇ)`. -/
def hE (hts : φ₀ t₀ * φ₁ t₁ = 1) : Subring (L₀ C × L₁ C) where
  carrier := {z | ∃ a b, ∃ x ∈ Gam C H (a + b), jL₀ C (tFm C ^ a) * z.1 = jL₀ C x.1 ∧
    jL₁ C (sFm C ^ b) * z.2 = jL₁ C x.2}
  add_mem' := by
    rintro z z' ⟨a, b, x, hx, h1, h2⟩ ⟨a', b', y, hy, h1', h2'⟩
    refine ⟨a + a', b + b', gT₁ C ^ a' * (gT₀ C ^ b' * x) + gT₁ C ^ a * (gT₀ C ^ b * y),
      add_mem (gam_cast C H (by ring) (gT₁_pow_mem C H a' (gT₀_pow_mem C H hts b' hx)))
        (gam_cast C H (by ring) (gT₁_pow_mem C H a (gT₀_pow_mem C H hts b hy))), ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.fst_mul, Prod.pow_fst, gT₀, gT₁, one_pow, one_mul, map_add, map_mul, pow_add]
      linear_combination jL₀ C (tFm C ^ a') * h1 + jL₀ C (tFm C ^ a) * h1'
    · simp only [Prod.snd_add, Prod.snd_mul, Prod.pow_snd, gT₀, gT₁, one_pow, one_mul, map_add, map_mul, pow_add]
      linear_combination jL₁ C (sFm C ^ b') * h2 + jL₁ C (sFm C ^ b) * h2'
  zero_mem' := ⟨0, 0, 0, zero_mem _, by simp only [Prod.fst_zero, mul_zero, map_zero],
    by simp only [Prod.snd_zero, mul_zero, map_zero]⟩
  one_mem' := ⟨0, 0, 1, gam_one C H, by rw [pow_zero, map_one, one_mul, Prod.fst_one, Prod.fst_one, map_one],
    by rw [pow_zero, map_one, one_mul, Prod.snd_one, Prod.snd_one, map_one]⟩
  mul_mem' := by
    rintro z z' ⟨a, b, x, hx, h1, h2⟩ ⟨a', b', y, hy, h1', h2'⟩
    refine ⟨a + a', b + b', x * y, gam_cast C H (by ring) (gam_mul C H hx hy), ?_, ?_⟩
    · simp only [Prod.fst_mul, map_mul, pow_add]
      linear_combination (jL₀ C (tFm C ^ a') * z'.1) * h1 + jL₀ C x.1 * h1'
    · simp only [Prod.snd_mul, map_mul, pow_add]
      linear_combination (jL₁ C (sFm C ^ b') * z'.2) * h2 + jL₁ C x.2 * h2'
  neg_mem' := by
    rintro z ⟨a, b, x, hx, h1, h2⟩
    refine ⟨a, b, -x, neg_mem hx, ?_, ?_⟩
    · simp only [Prod.fst_neg, map_neg]
      linear_combination -h1
    · simp only [Prod.snd_neg, map_neg]
      linear_combination -h2

end Hat2

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

theorem hE₀_ext {z z' : hE₀ C H hts} (d : ℕ)
    (h1 : (z : (∀ k, (C k).E₀) × L₁ C).1 = (z' : (∀ k, (C k).E₀) × L₁ C).1)
    (h2 : jL₁ C (sFm C ^ d) * (z : (∀ k, (C k).E₀) × L₁ C).2 =
      jL₁ C (sFm C ^ d) * (z' : (∀ k, (C k).E₀) × L₁ C).2) : z = z' :=
  Subtype.ext (Prod.ext h1 ((isUnit_jL₁ C d).mul_left_cancel h2))

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

/-- **The level-`k` reduction `Ê₀ → E₀(k)`.** -/
def θ₀ (k : ℕ) : hE₀ C H hts →+* (C k).E₀ :=
  ((Pi.evalRingHom (fun k => ((C k).E₀ : Type u)) k).comp (RingHom.fst _ (L₁ C))).comp (hE₀ C H hts).subtype

theorem θ₀_apply (k : ℕ) (z : hE₀ C H hts) : θ₀ C H hts k z = (z : (∀ k, (C k).E₀) × L₁ C).1 k := rfl

end Theta

section Surj

end Surj

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_DescG3 =====
section

/-!
# S4-EtPBC-A, R4-T1c (part 2): the glued cover `U₀ ⟶ X` is finite, etale and surjective

* Generic (any coequifibered `α : 𝒪_X ⟶ F` on affine opens): `glD H` (the relative gluing data),
  `cover_toBase` (`Spec F(U) ⟶ U₀ ⟶ X` is `Spec α_U ≫ U.fromSpec`), `prop_toBase` (a Zariski-local property holds
  for `toBase` once it holds for every `Spec α_U`), `isFinite_toBase`, `etale_toBase`, `surjective_toBase`.
* For `V` etale and surjective over `X` with `V.hom` affine: `surj_comap`, the instance
  `Module.FaithfullyFlat Γ(X, U) (CU V U)`, and for the descended presheaf `FU`:
  **`U0`**, **`toU0`** `: U0 ⟶ X` with `IsFinite`, `Etale`, `Surjective`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescG

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.DescA TensorProduct

universe u

section Base

end Base

section Cover

variable {X : Scheme.{u}} (V : X.Etale) [IsAffineHom V.hom]

variable [Surjective V.hom] {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ} [Fintype M] [DecidableEq M]
  {E Q : EtSh Λ X} (a : constSh Λ X M ⟶ E) (b : E ⟶ Q) (hab : a ≫ b = 0)
  (hS : (ShortComplex.mk a b hab).ShortExact) (e : E.obj.obj (op V))
  (he : ∀ (W : X.Etale) (w₁ w₂ : W ⟶ V), (b.hom.app (op W)).hom ((E.obj.map w₁.op).hom e) =
    (b.hom.app (op W)).hom ((E.obj.map w₂.op).hom e))

instance surjective_toU0 : Surjective (toU0 V a b hab hS e he) :=
  surjective_toBase _ fun U => surj_B V a b hab hS e he U

end Cover

end RamanujanPetersson.EtPBC.DescG

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Sh1 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Sh1): `π_*` is exact for a separated etale `π` of constant degree

* `shObj s`, `shι s`: a map `s : N ⟶ W` of etale `P`-schemes gives a sheet `N ⟶ N ×_P W` over `W`.
* `sheet_cover`: sheets that biject onto every geometric fibre cover `N ×_P W`; `sheet_sep`: distinct sheets
  do not meet; `shι_cancel`.
* **`push_epi`**: if `W` is quasi-compact separated etale over `P` with `n` points in every geometric fibre, then
  `push W.hom` preserves epimorphisms (stalk lifts on a splitting neighbourhood, glued over the sheets), and
  **`push_preservesFiniteColimits_of_deg`**.
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

section Sheet

end Sheet

section Lift

variable {W N : P.Etale}

variable (Λ : Type u) [CommRing Λ]

/-- **`push W.hom` is exact** for `W` separated, quasi-compact etale of constant degree. -/
theorem push_preservesFiniteColimits_of_deg (W : P.Etale) [QuasiCompact W.hom] [IsSeparated W.hom] (n : ℕ)
    (hn : ∀ y : P, Nat.card ((geomPtAt y).point.fiber.obj W) = n) :
    PreservesFiniteColimits (push W.hom Λ) :=
  (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).2 fun S hS => by
    have : Epi S.g := hS.epi_g
    have hg := push_epi Λ W n hn S.g
    exact ⟨(RamanujanPetersson.EtCompact.ParSuf.map_shortExact_of_epi (pullAdj W.hom Λ) hS hg).exact, hg⟩

end Lift

end RamanujanPetersson.EtPBC.EtShap

end

end


