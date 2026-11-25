-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_083
-- name    : RPLib_FX_EtPBC_083
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T21:49:51.882842+00:00
-- url     : https://prove2.me/theorems/0dcea403-e761-5208-9d90-81776777271d
-- title:
--   Proper base change for the projective line, library file 083
-- statement:
--   File 083 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovHat1`: S4-EtPBC-A, R4-T2 (A2c-3a): the completed chart rings as subrings of products of localizations
--   * `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
--   * `S4.Def_RP_EtPBC_A_O2PP5a`: S4-EtPBC-A, O2 PP' (O2PP5a): an `IsLoc` class at `c(a)` comes from a domain chart over a fixed cofinite `U₀`
--   * `S4.Def_RP_EtPBC_A_O2L6c1`: S4-EtPBC-A, L6c1: a point class on `P¹_K` through the family square
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_071
import Definitions.Def_RPLib_FX_EtPBC_072
import Definitions.Def_RPLib_FX_EtPBC_073

/-!
# Proper base change for the projective line, library file 083

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovHat1`: S4-EtPBC-A, R4-T2 (A2c-3a): the completed chart rings as subrings of products of localizations
* `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
* `S4.Def_RP_EtPBC_A_O2PP5a`: S4-EtPBC-A, O2 PP' (O2PP5a): an `IsLoc` class at `c(a)` comes from a domain chart over a fixed cofinite `U₀`
* `S4.Def_RP_EtPBC_A_O2L6c1`: S4-EtPBC-A, L6c1: a point class on `P¹_K` through the family square
-/

set_option autoImplicit false

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

/-- **The completed chart ring `Ê₁`**: fractions `x / T₁ᵈ`, as `(x.1 / tᵈ, x.2)`. -/
def hE₁ : Subring (L₀ C × ∀ k, (C k).E₁) where
  carrier := {z | ∃ d, ∃ x ∈ Gam C H d, jL₀ C (tFm C ^ d) * z.1 = jL₀ C x.1 ∧ z.2 = x.2}
  add_mem' := by
    rintro z z' ⟨d, x, hx, h1, h2⟩ ⟨e, y, hy, h1', h2'⟩
    refine ⟨d + e, gT₁ C ^ e * x + gT₁ C ^ d * y,
      add_mem (gT₁_pow_mem C H e hx) (gam_cast C H (by ring) (gT₁_pow_mem C H d hy)), ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.fst_mul, Prod.pow_fst, gT₁, map_add, map_mul, pow_add]
      linear_combination jL₀ C (tFm C ^ e) * h1 + jL₀ C (tFm C ^ d) * h1'
    · simp only [Prod.snd_add, Prod.snd_mul, Prod.pow_snd, gT₁, one_pow, one_mul, h2, h2']
  zero_mem' := ⟨0, 0, zero_mem _, by simp only [Prod.fst_zero, mul_zero, map_zero], rfl⟩
  one_mem' := ⟨0, 1, gam_one C H, by rw [pow_zero, map_one, one_mul, Prod.fst_one, Prod.fst_one, map_one], rfl⟩
  mul_mem' := by
    rintro z z' ⟨d, x, hx, h1, h2⟩ ⟨e, y, hy, h1', h2'⟩
    refine ⟨d + e, x * y, gam_mul C H hx hy, ?_, ?_⟩
    · simp only [Prod.fst_mul, map_mul, pow_add]
      linear_combination (jL₀ C (tFm C ^ e) * z'.1) * h1 + jL₀ C x.1 * h1'
    · simp only [Prod.snd_mul, h2, h2']
  neg_mem' := by
    rintro z ⟨d, x, hx, h1, h2⟩
    refine ⟨d, -x, neg_mem hx, ?_, ?_⟩
    · simp only [Prod.fst_neg, map_neg]
      linear_combination -h1
    · simp only [Prod.snd_neg, h2]

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

theorem mem_hE (hts : φ₀ t₀ * φ₁ t₁ = 1) (z : L₀ C × L₁ C) : z ∈ hE C H hts ↔
    ∃ a b, ∃ x ∈ Gam C H (a + b), jL₀ C (tFm C ^ a) * z.1 = jL₀ C x.1 ∧ jL₁ C (sFm C ^ b) * z.2 = jL₁ C x.2 :=
  Iff.rfl

end Hat2

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP5a =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP5a): an `IsLoc` class at `c(a)` comes from a domain chart over a fixed cofinite `U₀`

* `prdTo`, `prdMapR_prdTo`: for `D` over `U₁ ∪ {z}` and `z ∉ U₀ ⊇ U₁`, `D ×_P U₀ ⟶ D ×_P U₁` splits `prdMapR`;
* `locCls_up`: `ε(D, U₁)∘κ = ε(D, U₀)∘Λ[prdTo]∘κ`;
* **`isLoc_chart`**: an `IsLoc` class at `z = c(a)` is `ε(chEt c φ, U₀)∘κ` for a chart `φ` with `B` a domain,
  given `g₀(a) ≠ 0` and `D_{g₀} ⊆ U₀ ∪ {z}` (`isLoc_aff_map`, shrink to `D_{φ g₀}`, `locCls_opn`, `locCls_up`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtDeg

universe u

section Up

end Up

section Chart

variable {k : Type} [Field k] [IsAlgClosed k] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c]
  {Λ : Type} [CommRing Λ] {U₀ Uz : P.Opens} (h₀ : U₀ ≤ Uz) {a : k} (hz : ∀ x : P, x ∈ Uz ↔ x ≠ c (A1pt k a))
  {g₀ : k[X]} (hg₀ : ∀ v : (chEt c (locF (B := CommRingCat.of k[X]) g₀)).left,
    (chEt c (locF (B := CommRingCat.of k[X]) g₀)).hom v ∈ U₀ ∨
      (chEt c (locF (B := CommRingCat.of k[X]) g₀)).hom v = c (A1pt k a))
  (hga : g₀.eval a ≠ 0)

include hg₀ hga in
/-- **An `IsLoc` class at `c(a)` is a domain-chart class over `U₀`**. -/
theorem isLoc_chart {F : EtSh Λ P} (β : Ext.{0} (freeSh Λ (etId P)) F 2) (hβ : IsLoc Λ F (c (A1pt k a)) β) :
    ∃ (B : CommRingCat.{0}) (φ : CommRingCat.of k[X] ⟶ B) (_ : Etale (Spec.map φ ≫ c)) (_ : IsDomain B)
      (hD : Subsingleton ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ)))
      (hDn : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ)))
      (hDr : ∀ v : (chEt c φ).left, (chEt c φ).hom v ∈ U₀ ∨ (chEt c φ).hom v = c (A1pt k a))
      (κ : Ext.{0} (freeSh Λ (prd (chEt c φ) (opEt U₀))) F 1),
      β = (locC_shortExact (Λ := Λ) (chEt c φ) h₀ (c (A1pt k a)) hz hD hDn hDr).extClass.comp κ
        (show 1 + 1 = 2 from rfl) := by
  obtain ⟨Uo', Uz', h', hz', D, hD, hDn, hDr, κ, rfl⟩ := hβ
  have hUz : Uz' = Uz := TopologicalSpace.Opens.ext (Set.ext fun x => (hz' x).trans (hz x).symm)
  subst hUz
  obtain ⟨B, φ, _, _, _, _, _, hD', hDn', hDr', κ', _, he⟩ := isLoc_aff_map c a h' hz' hD hDn hDr κ
  have hzU : c (A1pt k a) ∉ U₀ := fun hm => (hz _).1 (h₀ hm) rfl
  obtain ⟨n₀⟩ := id hDn'
  have := hD'
  have hdom : IsDomain (CommRingCat.of (Localization.Away (φ.hom g₀))) :=
    isDomain_locF (ne_zero_of_eval_ne_zero c φ n₀ hga)
  have hD₂ : Subsingleton ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c (φ ≫ locF (φ.hom g₀)))) :=
    subsingleton_fib_toDF c φ (φ.hom g₀) (c (A1pt k a))
  have hDn₂ : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c (φ ≫ locF (φ.hom g₀)))) :=
    nonempty_fib_toDF c φ (φ.hom g₀) (c (A1pt k a)) n₀ (not_mem_fpt_of_eval_ne_zero c φ n₀ hga)
  have hDrO := range_toDF c φ (φ.hom g₀) hDr'
  have hDrU := hDr_of_hom (toDg c φ (φ.hom g₀) g₀ (isUnit_locF_comp_of_dvd φ (dvd_refl g₀))) hg₀
  have hDr₁ := hDr_inf hDrO hDrU
  have h₁₀ : Uo' ⊓ U₀ ≤ Uo' := inf_le_left
  have h₁₀' : Uo' ⊓ U₀ ≤ U₀ := inf_le_right
  have h₁ := h₁₀.trans h'
  refine ⟨_, φ ≫ locF (φ.hom g₀), inferInstance, hdom, hD₂, hDn₂, hDrU, _,
    he.trans ((locCls_shrink h' (toDF c φ (φ.hom g₀))
      (locC_shortExact (Λ := Λ) _ h' _ hz' hD₂ hDn₂ hDrO) (locC_shortExact (Λ := Λ) _ h' _ hz' hD' hDn' hDr') κ').trans
      ((locCls_opn h₁₀ h' h₁ _ (locC_shortExact (Λ := Λ) _ h₁ _ hz' hD₂ hDn₂ hDr₁)
        (locC_shortExact (Λ := Λ) _ h' _ hz' hD₂ hDn₂ hDrO) _).trans
        (locCls_up _ (prd_mem_of _ hDr₁ hzU) h₁₀' h₀ h₁ (locC_shortExact (Λ := Λ) _ h₁ _ hz' hD₂ hDn₂ hDr₁)
          (locC_shortExact (Λ := Λ) _ h₀ _ hz hD₂ hDn₂ hDrU) _)))⟩

end Chart

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L6c1 =====
section

/-!
# S4-EtPBC-A, L6c1: a point class on `P¹_K` through the family square

For the data of a point class `x = pcD c' ∘ Λ[s']` with coefficients `T = ιP^* W`:
* `pcD_s'`: `x = ε(locC D) ∘ θ(prW, κ_D) ∘ Λ[s']`, `κ_D = isoT⁻¹^* toWa^* ξ`;
* `shrink_Db`: the same class through `D♭ = opn D Vb`;
* `hrM : aM ≫ ιP^*(rW) = opnι ≫ s'`, `hmapA`, `hκ` (the Kummer classes agree on `D♭ ×_P Uz'`);
* **`ptCls_Db`**: `x = Λ[σP] ∘ (ιP^*MVZ-class of fW^* κZ and ιP^* rW)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Polynomial Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE

section Cls

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (c : A1 K ⟶ P1 K) [IsOpenImmersion c] (a : K) (W : (PV K gS).Etale)
  {B : CommRingCat.{0}} (φ : CommRingCat.of K[X] ⟶ B) [Etale (Spec.map φ ≫ c)] [IsDedekindDomain B]
  (ht : φ.hom (X - C a) ≠ 0) (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime)
  (s' : chEt c φ ⟶ (etPull (ιP gS s)).obj W)
  (Uz' : (P1 K).Opens) (hUz' : ∀ x : P1 K, x ∈ Uz' ↔ x ≠ zc c a)
  {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0) (Λ : Type) [CommRing Λ] (hΛ : ∀ x : Λ, N • x = 0)
  (hUz : ∀ u : Spec B, (chEt c φ).hom u ∈ Uz' ↔ φ.hom (X - C a) ∉ u.asIdeal)
  (hS : (locC Λ (chEt c φ) (le_refl Uz')).ShortExact) (c' : Λ)

/-- `κ_D = isoT⁻¹^* toWa^* ξ` on `D ×_P Uz'`. -/
abbrev κD : H Λ (unitSh Λ (prd (chEt c φ) (opEt Uz')).left) 1 :=
  resLE (isoT c φ hUz).inv.left 1 (resLE (toWa c a φ).left 1 (xiA a hN Λ hΛ c'))

end Cls

end RamanujanPetersson.EtPBC.EtMV

end

end


