-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_063
-- name    : RPLib_FX_EtPBC_063
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T21:19:57.38639+00:00
-- url     : https://prove2.me/theorems/338a6a5a-dfc4-5c19-97a6-ffc03ce5fb08
-- title:
--   Proper base change for the projective line, library file 063
-- statement:
--   File 063 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovLim0`: S4-EtPBC-A, R4-T2 (A2c-2e): sections of `O(d)` at one level: finiteness and multiplication surjectivity
--   * `S4.Def_RP_EtPBC_A_CovHat1`: S4-EtPBC-A, R4-T2 (A2c-3a): the completed chart rings as subrings of products of localizations
--   * `S4.Def_RP_EtPBC_A_CovHat6`: S4-EtPBC-A, R4-T2 (A2c-3f): the level reductions of the completed charts are surjective
--   * `S4.Def_RP_EtPBC_A_Inj0d1`: S4-EtPBC-A, G1d part 2: `goodPt_fac`, `goodPt_w` (the lifted point lies over `s`) and `res0_eq_zero`
--   * `S4.Def_RP_EtPBC_A_O2Sh1`: S4-EtPBC-A, O2 M6 (O2Sh1): `π_*` is exact for a separated etale `π` of constant degree
--   * `S4.Def_RP_EtPBC_A_O2T2`: S4-EtPBC-A, O2 S5b: free sheaves of a disjoint union
--   * `S4.Def_RP_EtPBC_A_O2T3`: S4-EtPBC-A, O2 S5c: sections after shrinking, and the graph splitting
--   * `S4.Def_RP_EtPBC_A_O2PPTb`: S4-EtPBC-A, O2 GLOB (O2PPTb): a piece Kummer class pulled back along an etale map
--   * `S4.Def_RP_EtPBC_A_O2Gl1a`: S4-EtPBC-A, O2 GLOB (O2Gl1a): residue density at the special point
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_034
import Definitions.Def_RPLib_FX_EtPBC_050
import Definitions.Def_RPLib_FX_EtPBC_051
import Definitions.Def_RPLib_FX_EtPBC_053

/-!
# Proper base change for the projective line, library file 063

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovLim0`: S4-EtPBC-A, R4-T2 (A2c-2e): sections of `O(d)` at one level: finiteness and multiplication surjectivity
* `S4.Def_RP_EtPBC_A_CovHat1`: S4-EtPBC-A, R4-T2 (A2c-3a): the completed chart rings as subrings of products of localizations
* `S4.Def_RP_EtPBC_A_CovHat6`: S4-EtPBC-A, R4-T2 (A2c-3f): the level reductions of the completed charts are surjective
* `S4.Def_RP_EtPBC_A_Inj0d1`: S4-EtPBC-A, G1d part 2: `goodPt_fac`, `goodPt_w` (the lifted point lies over `s`) and `res0_eq_zero`
* `S4.Def_RP_EtPBC_A_O2Sh1`: S4-EtPBC-A, O2 M6 (O2Sh1): `π_*` is exact for a separated etale `π` of constant degree
* `S4.Def_RP_EtPBC_A_O2T2`: S4-EtPBC-A, O2 S5b: free sheaves of a disjoint union
* `S4.Def_RP_EtPBC_A_O2T3`: S4-EtPBC-A, O2 S5c: sections after shrinking, and the graph splitting
* `S4.Def_RP_EtPBC_A_O2PPTb`: S4-EtPBC-A, O2 GLOB (O2PPTb): a piece Kummer class pulled back along an etale map
* `S4.Def_RP_EtPBC_A_O2Gl1a`: S4-EtPBC-A, O2 GLOB (O2Gl1a): residue density at the special point
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_CovLim0 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-2e): sections of `O(d)` at one level: finiteness and multiplication surjectivity

For a level cover `C` (charts finite over `R[t]`, `R[s]`, `R` noetherian):
* **`sec_fg`**: the sections of `O(d)` are finitely many `R`-combinations of fixed sections (via `Z1.twoChart_fg`);
* **`sec_mul_surj`**: `Γ(e+2) = T₀ Γ(e+1) + T₁ Γ(e+1)` when `H¹(O(e)) = 0` (`T₀ = (1, s)`, `T₁ = (t, 1)`);
* `sec_gen_T`: generators of `Γ(e+2)` of the form `T₀ τⱼ`, `T₁ τⱼ`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Lv

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁)

/-- **Sections of `O(d)` at one level are a finite `R`-module.** -/
theorem sec_fg [IsNoetherianRing R] (hts : φ₀ t₀ * φ₁ t₁ = 1) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁)
    (hB₀ : (eval₂RingHom ιB₀ t₀).Finite) (hB₁ : (eval₂RingHom ιB₁ t₁).Finite) {k : ℕ}
    (C : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k) (d : ℕ) :
    ∃ (r : ℕ) (g : Fin r → C.E₀ × C.E₁), (∀ j, g j ∈ C.sec d) ∧
      ∀ y ∈ C.sec d, ∃ c : Fin r → R, y = ∑ j, (lι₀ ιB₀ C (c j) * (g j).1, lι₁ ιB₁ C (c j) * (g j).2) := by
  classical
  let f₀ : R[X] →+* C.E₀ := (C.a₀.comp (Ideal.Quotient.mk (J₀ ^ (k + 1)))).comp (eval₂RingHom ιB₀ t₀)
  let f₁ : R[X] →+* C.E₁ := (C.a₁.comp (Ideal.Quotient.mk (J₁ ^ (k + 1)))).comp (eval₂RingHom ιB₁ t₁)
  let fN : R[X] →+* C.E := C.ψ₀.comp f₀
  have hC₀ : ∀ a : R, f₀ (Polynomial.C a) = lι₀ ιB₀ C a := fun a => by simp [f₀, lι₀]
  have hC₁ : ∀ a : R, f₁ (Polynomial.C a) = lι₁ ιB₁ C a := fun a => by simp [f₁, lι₁]
  have hX₀ : f₀ X = C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) t₀) := by simp [f₀]
  have hX₁ : f₁ X = C.a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁) := by simp [f₁]
  have hXN : fN X = C.u := by
    show C.ψ₀ (f₀ X) = C.u
    rw [hX₀]
  have hCN : ∀ a : R, fN (Polynomial.C a) = C.ψ₁ (lι₁ ιB₁ C a) := fun a => by
    show C.ψ₀ (f₀ (Polynomial.C a)) = _
    rw [hC₀]
    exact RingHom.congr_fun (lι_compat ιB₀ ιB₁ hιB C) a
  have hv := lhv hts C
  letI : Algebra R[X] C.E₀ := f₀.toAlgebra
  letI : Algebra R[X] C.E₁ := f₁.toAlgebra
  letI : Algebra R[X] C.E := fN.toAlgebra
  letI : Algebra R C.E₀ := (f₀.comp Polynomial.C).toAlgebra
  letI : Algebra R C.E₁ := (f₁.comp Polynomial.C).toAlgebra
  letI : Algebra R C.E := (fN.comp Polynomial.C).toAlgebra
  haveI : IsScalarTower R R[X] C.E₀ := IsScalarTower.of_algebraMap_eq fun a => by
    rw [Polynomial.algebraMap_eq]
    rfl
  haveI : IsScalarTower R R[X] C.E₁ := IsScalarTower.of_algebraMap_eq fun a => by
    rw [Polynomial.algebraMap_eq]
    rfl
  haveI : IsScalarTower R R[X] C.E := IsScalarTower.of_algebraMap_eq fun a => by
    rw [Polynomial.algebraMap_eq]
    rfl
  haveI : Module.Finite R[X] C.E₀ :=
    (C.fin₀.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)).comp hB₀
  haveI : Module.Finite R[X] C.E₁ :=
    (C.fin₁.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)).comp hB₁
  let Φ₀ : C.E₀ →ₗ[R[X]] C.E :=
    { toFun := C.ψ₀
      map_add' := map_add _
      map_smul' := fun c m => by
        show C.ψ₀ (f₀ c * m) = fN c * C.ψ₀ m
        rw [map_mul]
        rfl }
  let Φ₁ : C.E₁ →ₗ[R] C.E :=
    { toFun := fun b => C.u ^ d * C.ψ₁ b
      map_add' := fun b b' => by
        show C.u ^ d * C.ψ₁ (b + b') = C.u ^ d * C.ψ₁ b + C.u ^ d * C.ψ₁ b'
        rw [map_add, mul_add]
      map_smul' := fun a b => by
        show C.u ^ d * C.ψ₁ (f₁ (Polynomial.C a) * b) = fN (Polynomial.C a) * (C.u ^ d * C.ψ₁ b)
        rw [map_mul, hC₁, hCN]
        ring }
  have h₁ : ∀ m : C.E₁, (X : R[X]) • Φ₁ ((X : R[X]) • m) = Φ₁ m := by
    intro m
    show fN X * (C.u ^ d * C.ψ₁ (f₁ X * m)) = C.u ^ d * C.ψ₁ m
    rw [hXN, hX₁, map_mul]
    linear_combination (C.u ^ d * C.ψ₁ m) * hv
  have hgen : ∀ m : C.E₁, ∃ (e : ℕ) (a : C.E₀), Φ₀ a = (X ^ e : R[X]) • Φ₁ m := by
    intro m
    obtain ⟨e, a, ha⟩ := C.aw₀.1 (C.u ^ d * C.ψ₁ m)
    refine ⟨e, a, ?_⟩
    show C.ψ₀ a = fN (X ^ e) * (C.u ^ d * C.ψ₁ m)
    rw [map_pow, hXN, ← ha]
  have hk₀ : ∀ a, Φ₀ a = 0 → a ∈ Z1.xTors (A := R) C.E₀ := by
    intro a ha
    obtain ⟨e, he⟩ := C.aw₀.2 a ha
    refine Z1.mem_xTors.2 ⟨e, ?_⟩
    show f₀ (X ^ e) * a = 0
    rw [map_pow, hX₀]
    exact he
  have hk₁ : ∀ b, Φ₁ b = 0 → b ∈ Z1.xTors (A := R) C.E₁ := by
    intro b hb
    have h : C.u ^ d * C.ψ₁ b = 0 := hb
    have hb' : C.ψ₁ b = 0 := by
      have e : C.ψ₁ b = C.ψ₁ (C.a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁)) ^ d * (C.u ^ d * C.ψ₁ b) := by
        rw [← mul_assoc, ← mul_pow, mul_comm (C.ψ₁ _) C.u, hv, one_pow, one_mul]
      rw [e, h, mul_zero]
    obtain ⟨e, he⟩ := C.aw₁.2 b hb'
    refine Z1.mem_xTors.2 ⟨e, ?_⟩
    show f₁ (X ^ e) * b = 0
    rw [map_pow, hX₁]
    exact he
  have hfg := Z1.twoChart_fg Φ₀ Φ₁ h₁ hgen hk₀ hk₁
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hmem : ∀ y : C.E₀ × C.E₁, y ∈ Z1.twoChart Φ₀ Φ₁ ↔ y ∈ C.sec d := fun y =>
    (Z1.mem_twoChart Φ₀ Φ₁ y).trans (TwoCov.mem_sec C d y).symm
  refine ⟨r, g, fun j => (hmem _).1 ?_, fun y hy => ?_⟩
  · rw [← hg]
    exact Submodule.subset_span ⟨j, rfl⟩
  · have hy' : y ∈ Submodule.span R (Set.range g) := by
      rw [hg]
      exact (hmem y).2 hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hy'
    refine ⟨c, ?_⟩
    rw [← hc]
    refine Finset.sum_congr rfl fun j _ => Prod.ext ?_ ?_
    · show f₀ (Polynomial.C (c j)) * (g j).1 = _
      rw [hC₀]
    · show f₁ (Polynomial.C (c j)) * (g j).2 = _
      rw [hC₁]

/-- **Generators of `Γ(e+2)` of the form `T₀ τⱼ`, `T₁ τⱼ`** with `τⱼ ∈ Γ(e+1)`. -/
theorem sec_gen_T [IsNoetherianRing R] (hts : φ₀ t₀ * φ₁ t₁ = 1) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁)
    (hB₀ : (eval₂RingHom ιB₀ t₀).Finite) (hB₁ : (eval₂RingHom ιB₁ t₁).Finite) {k : ℕ}
    (C : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k) (e : ℕ)
    (hspl : ∀ z : C.E, ∃ (x₀ : C.E₀) (x₁ : C.E₁), z = C.ψ₀ x₀ - C.u ^ e * C.ψ₁ x₁) :
    ∃ (r : ℕ) (τ : Fin r → C.E₀ × C.E₁), (∀ j, τ j ∈ C.sec (e + 1)) ∧ ∀ y ∈ C.sec (e + 2),
      ∃ c c' : Fin r → R, y =
        ∑ j, (lι₀ ιB₀ C (c j) * (τ j).1, lι₁ ιB₁ C (c j) * (C.a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁) * (τ j).2)) +
        ∑ j, (lι₀ ιB₀ C (c' j) * (C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) t₀) * (τ j).1), lι₁ ιB₁ C (c' j) * (τ j).2) := by
  obtain ⟨r, τ, hτ, hgen⟩ := sec_fg ιB₀ ιB₁ hts hιB hB₀ hB₁ C (e + 1)
  refine ⟨r, τ, hτ, fun y hy => ?_⟩
  obtain ⟨x, z, hx, hz, hyxz⟩ := sec_mul_surj hts C e hspl y hy
  obtain ⟨c, hc⟩ := hgen x hx
  obtain ⟨c', hc'⟩ := hgen z hz
  refine ⟨c, c', ?_⟩
  rw [hyxz, hc, hc']
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.fst_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  · simp only [Prod.snd_add, Prod.snd_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring

end Lv

end RamanujanPetersson.EtPBC.Cov

end

end

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

theorem gam_pow {d : ℕ} {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d) (n : ℕ) :
    x ^ n ∈ Gam C H (d * n) := by
  induction n with
  | zero => rw [pow_zero]; exact gam_one C H
  | succ n ih => rw [pow_succ x n]; exact gam_cast C H (by ring) (gam_mul C H ih hx)

theorem gT₀_pow_mem (hts : φ₀ t₀ * φ₁ t₁ = 1) (n : ℕ) {d : ℕ} {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)}
    (hx : x ∈ Gam C H d) : gT₀ C ^ n * x ∈ Gam C H (d + n) :=
  gam_cast C H (by ring) (gam_mul C H (gam_pow C H (gT₀_mem C H hts) n) hx)

theorem gT₁_pow_mem (n : ℕ) {d : ℕ} {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)}
    (hx : x ∈ Gam C H d) : gT₁ C ^ n * x ∈ Gam C H (d + n) :=
  gam_cast C H (by ring) (gam_mul C H (gam_pow C H (gT₁_mem C H) n) hx)

end Hat

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

end Theta

section Surj

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (p : Ideal R) (hts : φ₀ t₀ * φ₁ t₁ = 1)

include hts in
/-- **A generating system of compatible families** of `O(d)` (lifts of level-`0` generators). -/
theorem gen_sys [IsNoetherianRing R] (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite)
    (hB₁ : (eval₂RingHom ιB₁ t₁).Finite) {d : ℕ}
    (hs : ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d)) :
    ∃ (r : ℕ) (σ : Fin r → (∀ k, (C k).E₀) × (∀ k, (C k).E₁)), (∀ i, σ i ∈ Gam C H d) ∧
      ∀ y ∈ (C 0).sec d, ∃ c, y = lev C ιB₀ ιB₁ σ 0 c := by
  obtain ⟨r, g', hg, hgen⟩ := sec_fg ιB₀ ιB₁ hts hιB hB₀ hB₁ (C 0) d
  choose σ hσ hσ1 hσ2 using fun j => exists_gam C H hs ⟨g' j, hg j⟩
  refine ⟨r, σ, hσ, fun y hy => ?_⟩
  obtain ⟨c, hc⟩ := hgen y hy
  refine ⟨c, ?_⟩
  rw [hc]
  simp only [lev, hσ1, hσ2]

end Surj

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Inj0d1 =====
section

/-!
# S4-EtPBC-A, G1d part 2: `goodPt_fac`, `goodPt_w` (the lifted point lies over `s`) and `res0_eq_zero`
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- A degree-`0` class dies along `a` once its section restricts to `0`. -/
theorem res0_eq_zero {j j' : Nbhd s} (a : j' ⟶ j) (G : EtSh Λ P) (α : Ext.{u} ((nbhdSys Λ g s).obj j) G 0)
    (hz : (G.obj.map ((etPull g).map a.1).op).hom (sec0 Λ g s j G α) = 0) :
    Delta.res (nbhdSys Λ g s) a G 0 α = 0 := by
  rw [Delta.res_apply, ← Ext.mk₀_addEquiv₀_apply α, Ext.mk₀_comp_mk₀, Ext.mk₀_eq_zero_iff]
  apply (freeEquiv Λ ((etPull g).obj j'.1) G).injective
  exact ((freeEquiv_freeMap Λ ((etPull g).map a.1) G _).trans hz).trans
    (map_zero (freeEquiv Λ ((etPull g).obj j'.1) G)).symm

end RamanujanPetersson.EtPBC

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

/-- **`push W.hom` preserves epimorphisms** for `W` separated, quasi-compact etale of constant degree. -/
theorem push_epi (W : P.Etale) [QuasiCompact W.hom] [IsSeparated W.hom] (n : ℕ)
    (hn : ∀ y : P, Nat.card ((geomPtAt y).point.fiber.obj W) = n)
    {A B : EtSh Λ W.left} (f : A ⟶ B) [Epi f] : Epi ((push W.hom Λ).map f) := by
  refine (epi_iff_stalk Λ _).2 fun x => (ModuleCat.epi_iff_surjective _).2 fun y => ?_
  obtain ⟨Z, z, b, rfl⟩ :=
    (geomPtAt x).point.toPresheafFiber_jointly_surjective (P := ((push W.hom Λ).obj B).obj) y
  obtain ⟨M, d, m, hm, a, ha⟩ := exists_push_lift Λ W n hn f x z b
  refine ⟨germ ((push W.hom Λ).obj A) x m a, (germ_natural ((push W.hom Λ).map f) x m a).trans ?_⟩
  refine (congrArg (germ ((push W.hom Λ).obj B) x m) ha).trans
    ((GenAlg.germ_map ((push W.hom Λ).obj B) x d m b).trans ?_)
  rw [hm]
  rfl

end Lift

end RamanujanPetersson.EtPBC.EtShap

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T2 =====
section

/-!
# S4-EtPBC-A, O2 S5b: free sheaves of a disjoint union

* `stalk_desc_free`: on stalks, `biprod.desc Λ[i₁] Λ[i₂]` is `mapDomain i₁ + mapDomain i₂`;
* **`isIso_desc_free`**: `Λ[N₁] ⊞ Λ[N₂] ⟶ Λ[N]` is an iso when on every geometric fibre `i₁`, `i₂` are injective
  with disjoint images covering the fibre of `N`;
* **`isIso_opnSplit`**, `opnSplitIso`: `Λ[N|V₁] ⊞ Λ[N|V₂] ≅ Λ[N]` for a disjoint open cover `V₁ ⊔ V₂` of `N`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo
  RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk

universe u

section Split

variable (Λ : Type u) [CommRing Λ] {P : Scheme.{u}}

/-- **Free sheaf of a disjoint union**: `Λ[N₁] ⊞ Λ[N₂] ⟶ Λ[N]` is an iso when `i₁`, `i₂` split every geometric
fibre of `N`. -/
theorem isIso_desc_free {N₁ N₂ N : P.Etale} (i₁ : N₁ ⟶ N) (i₂ : N₂ ⟶ N)
    (h₁ : ∀ x : P, Function.Injective ((geomPtAt x).point.fiber.map i₁))
    (h₂ : ∀ x : P, Function.Injective ((geomPtAt x).point.fiber.map i₂))
    (hd : ∀ (x : P) (a : (geomPtAt x).point.fiber.obj N₁) (b : (geomPtAt x).point.fiber.obj N₂),
      (geomPtAt x).point.fiber.map i₁ a ≠ (geomPtAt x).point.fiber.map i₂ b)
    (hc : ∀ (x : P) (c : (geomPtAt x).point.fiber.obj N),
      (∃ a, (geomPtAt x).point.fiber.map i₁ a = c) ∨ ∃ b, (geomPtAt x).point.fiber.map i₂ b = c) :
    IsIso (biprod.desc (freeMap Λ i₁) (freeMap Λ i₂)) := by
  have hmono : Mono (biprod.desc (freeMap Λ i₁) (freeMap Λ i₂)) := by
    rw [mono_iff_stalk]
    intro x
    rw [ModuleCat.mono_iff_injective]
    intro z z' h
    obtain ⟨l₁, l₂, e₁, e₂, e⟩ := stalk_desc_free Λ i₁ i₂ x z
    obtain ⟨l₁', l₂', e₁', e₂', e'⟩ := stalk_desc_free Λ i₁ i₂ x z'
    rw [e, e'] at h
    have h' := freeLin_injective N x h
    have k₁ : l₁ = l₁' := by
      ext a
      have hn : (geomPtAt x).point.fiber.map i₁ a ∉ Set.range ((geomPtAt x).point.fiber.map i₂) :=
        fun ⟨b, hb⟩ => hd x a b hb.symm
      have hh := congrArg (fun l => l ((geomPtAt x).point.fiber.map i₁ a)) h'
      simp only [Finsupp.coe_add, Pi.add_apply] at hh
      rwa [Finsupp.mapDomain_apply (h₁ x), Finsupp.mapDomain_apply (h₁ x),
        Finsupp.mapDomain_of_notMem_range _ _ hn, Finsupp.mapDomain_of_notMem_range _ _ hn, add_zero, add_zero] at hh
    have k₂ : l₂ = l₂' := by
      ext b
      have hn : (geomPtAt x).point.fiber.map i₂ b ∉ Set.range ((geomPtAt x).point.fiber.map i₁) :=
        fun ⟨a, ha⟩ => hd x a b ha
      have hh := congrArg (fun l => l ((geomPtAt x).point.fiber.map i₂ b)) h'
      simp only [Finsupp.coe_add, Pi.add_apply] at hh
      rwa [Finsupp.mapDomain_apply (h₂ x), Finsupp.mapDomain_apply (h₂ x),
        Finsupp.mapDomain_of_notMem_range _ _ hn, Finsupp.mapDomain_of_notMem_range _ _ hn, zero_add, zero_add] at hh
    exact stalk_biprod_ext x (by rw [e₁, e₁', k₁]) (by rw [e₂, e₂', k₂])
  have hepi : Epi (biprod.desc (freeMap Λ i₁) (freeMap Λ i₂)) := by
    rw [epi_iff_stalk]
    intro x
    rw [ModuleCat.epi_iff_surjective]
    have hr : ∀ l : (geomPtAt x).point.fiber.obj N →₀ Λ, freeLin Λ N x l ∈
        LinearMap.range (((geomPtAt x).stalkF Λ).map (biprod.desc (freeMap Λ i₁) (freeMap Λ i₂))).hom := by
      intro l
      induction l using Finsupp.induction_linear with
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add p q hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq
      | single c r =>
        rcases hc x c with ⟨a, rfl⟩ | ⟨b, rfl⟩
        · refine ⟨(((geomPtAt x).stalkF Λ).map biprod.inl).hom (freeLin Λ N₁ x (Finsupp.single a r)), ?_⟩
          rw [stalk_comp_apply, biprod.inl_desc, freeLin_natural, Finsupp.mapDomain_single]
        · refine ⟨(((geomPtAt x).stalkF Λ).map biprod.inr).hom (freeLin Λ N₂ x (Finsupp.single b r)), ?_⟩
          rw [stalk_comp_apply, biprod.inr_desc, freeLin_natural, Finsupp.mapDomain_single]
    intro v
    obtain ⟨l, rfl⟩ := freeLin_surjective (Λ := Λ) N x v
    exact hr l
  exact isIso_of_mono_of_epi _

end Split

section OpnSplit

end OpnSplit

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T3 =====
section

/-!
# S4-EtPBC-A, O2 S5c: sections after shrinking, and the graph splitting

* `exists_opn_pt`: an open of `N` whose only geometric point over a closed Galois-trivial `z` is a given one;
* **`isLoc_sec`**: a one-point class has a presentation `D` with a map `s : D ⟶ T` through a given point `t` of `T`;
* `isClosed_range_sec`, `secV σ`: a section `σ` of a separated etale `N` has closed range, with open complement;
* **`isIso_secSplit`**, `secSplitIso`: `Λ_X ⊞ Λ[N|secV σ] ≅ Λ[N]`, first summand `Λ[σ]`;
* `isSeparated_opn`; `isSeparated_etPull` (so the graph of `m : W ⟶ T` splits).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo
  RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk

universe u

section PtOpn

end PtOpn

section SecSplit

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}} {N : X.Etale} [IsSeparated N.hom] (σ : etId X ⟶ N)

/-- **A section splits `Λ[N]`**: `Λ_X ⊞ Λ[N|secV] ⟶ Λ[N]` is an iso. -/
theorem isIso_secSplit : IsIso (biprod.desc (freeMap Λ σ) (freeMap Λ (opnι N (secV σ)))) := by
  refine isIso_desc_free Λ _ _ (fun x a a' _ => Subsingleton.elim a a')
    (fun x => fib_opn_injective _ (secV σ) x) ?_ ?_
  · intro x a b hab
    have h2 := opnι_mem _ (secV σ) (fpt x b)
    have h3 : (opnι N (secV σ)).left (fpt x b) ∉ Set.range σ.left := h2
    have e : σ.left (fpt x a) = (opnι N (secV σ)).left (fpt x b) := congrArg (fpt x) hab
    exact h3 ⟨fpt x a, e⟩
  · intro x c
    by_cases hc : fpt x c ∈ Set.range σ.left
    · obtain ⟨u, hu⟩ := hc
      obtain ⟨b, hb, -⟩ := exists_lift_fib σ x c u hu
      exact Or.inl ⟨b, hb⟩
    · have hc' : fpt x c ∈ secV σ := hc
      obtain ⟨b, hb, -⟩ := exists_lift_fib (opnι _ (secV σ)) x c (⟨fpt x c, hc'⟩ : secV σ)
        (Scheme.Opens.ι_apply (secV σ) ⟨fpt x c, hc'⟩)
      exact Or.inr ⟨b, hb⟩

/-- `Λ_X ⊞ Λ[N|secV σ] ≅ Λ[N]`. -/
def secSplitIso : freeSh Λ (etId X) ⊞ freeSh Λ (opn N (secV σ)) ≅ freeSh Λ N :=
  @asIso _ _ _ _ (biprod.desc (freeMap Λ σ) (freeMap Λ (opnι N (secV σ)))) (isIso_secSplit Λ σ)

theorem secSplitIso_hom :
    (secSplitIso Λ σ).hom = biprod.desc (freeMap Λ σ) (freeMap Λ (opnι N (secV σ))) := rfl

end SecSplit

section Lift

end Lift

section GraphSplit

end GraphSplit

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PPTb =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2PPTb): a piece Kummer class pulled back along an etale map

GLOB/REL PLAN v1 (5), piece part. For etale `f : X₁ ⟶ X` of affine schemes whose rings are finite products of
Dedekind domains:
* **`exists_rad_hom`**: moving a radical `α` (`α ^ d = u`) along `ψ : K →+* K'` (`φ : A →+* A'` compatible);
* **`exists_gam`**: one radical `γ p₁` on every piece `p₁` of `X₁` over `p`, with `γ p₁ ^ d = Ψ u` for every
  compatible `Ψ`;
* **`resLE_kapS_off`**: a piece class of `X` vanishes on the pieces of `X₁` not over its piece;
* **`resLE_kapS_kumD_sum`**: `resLE f (kapS p (kumD α)) = Σ_{p₁} kapS p₁ (χ₁ p₁)` with `χ₁ p₁ = kumD (γ p₁)` for the
  pieces `p₁` over `p` and `χ₁ p₁ = 0` for the others.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.Pur RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer
  RamanujanPetersson.EtCompact.GalTrE

section RadHom

end RadHom

section PPTb

variable {X X₁ : Scheme.{0}} [IsAffine X] [IsAffine X₁] [IsNoetherianRing Γ(X, ⊤)] [IsNoetherianRing Γ(X₁, ⊤)]
  (h : ∀ (m : Ideal Γ(X, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  (h₁ : ∀ (m : Ideal Γ(X₁, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  [∀ p : minimalPrimes Γ(X, ⊤), IsDedekindDomain (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))]
  [∀ p : minimalPrimes Γ(X₁, ⊤), IsDedekindDomain (Γ(X₁, ⊤) ⧸ (p : Ideal Γ(X₁, ⊤)))]
  [Fintype (minimalPrimes Γ(X, ⊤))] [DecidableEq (minimalPrimes Γ(X, ⊤))]
  [Fintype (minimalPrimes Γ(X₁, ⊤))] [DecidableEq (minimalPrimes Γ(X₁, ⊤))] (Λ : Type) [CommRing Λ]
  (f : X₁ ⟶ X) [Etale f] (p : minimalPrimes Γ(X, ⊤)) {N : ℕ} [NeZero N]
  {ζ : maxUnram (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))))}
  (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))))),
    σ ζ = ζ)
  {ζ₁ : ∀ p₁ : minimalPrimes Γ(X₁, ⊤), maxUnram (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1))}
  (hζ₁ : ∀ p₁, IsPrimitiveRoot (ζ₁ p₁) N)
  (hζΓ₁ : ∀ p₁ : minimalPrimes Γ(X₁, ⊤),
    ∀ σ ∈ (⊤ : Subgroup (Pi1 (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1)))), σ (ζ₁ p₁) = ζ₁ p₁)
  {d : ℕ} [NeZero d] (hdN : d ∣ N)
  {α : (maxUnram (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))))ˣ}
  (hα : α ∈ rad (⊤ : Subgroup (Pi1 (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))
    (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))))) d)
  {γ : ∀ p₁ : minimalPrimes Γ(X₁, ⊤), (maxUnram (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1)))ˣ}
  (hγ : ∀ p₁, γ p₁ ∈ rad (⊤ : Subgroup (Pi1 (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1)))) d)
  {gΛ : Λ} (hgΛ : d • gΛ = 0)

set_option maxHeartbeats 1000000 in
include h h₁ in
/-- **One radical on every piece of `X₁` over `p`.** -/
def exists_gam {u : FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))}
    (hu : (α : maxUnram (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))))) ^ d =
      algebraMap _ (maxUnram (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))))) u) :
    ∃ γ : ∀ p₁ : minimalPrimes Γ(X₁, ⊤), (maxUnram (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1)))ˣ,
      (∀ p₁, γ p₁ ∈ rad (⊤ : Subgroup (Pi1 (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1)))) d) ∧
      ∀ p₁ : minimalPrimes Γ(X₁, ⊤), (p : Ideal Γ(X, ⊤)) ≤ RingHom.ker (kerMap f p₁) →
      ∀ Ψ : FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) →+* FractionRing (Γ(X₁, ⊤) ⧸ p₁.1),
      (∀ a : Γ(X, ⊤), Ψ (algebraMap _ _ (Ideal.Quotient.mk (p : Ideal Γ(X, ⊤)) a)) =
        algebraMap _ _ (Ideal.Quotient.mk p₁.1 (f.appTop a))) →
      (γ p₁ : maxUnram (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1))) ^ d =
        algebraMap _ (maxUnram (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1))) (Ψ u) := by
  have key : ∀ p₁ : minimalPrimes Γ(X₁, ⊤),
      ∃ γ₀ : (maxUnram (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1)))ˣ,
      γ₀ ∈ rad (⊤ : Subgroup (Pi1 (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1)))) d ∧
      ((p : Ideal Γ(X, ⊤)) ≤ RingHom.ker (kerMap f p₁) →
      ∀ Ψ : FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) →+* FractionRing (Γ(X₁, ⊤) ⧸ p₁.1),
      (∀ a : Γ(X, ⊤), Ψ (algebraMap _ _ (Ideal.Quotient.mk (p : Ideal Γ(X, ⊤)) a)) =
        algebraMap _ _ (Ideal.Quotient.mk p₁.1 (f.appTop a))) →
      (γ₀ : maxUnram (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1))) ^ d =
        algebraMap _ (maxUnram (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1))) (Ψ u)) := by
    intro p₁
    by_cases hp : (p : Ideal Γ(X, ⊤)) ≤ RingHom.ker (kerMap f p₁)
    · have := etale_kerLift h h₁ f hp
      have hinj : Function.Injective (kerLift hp) := injective_of_etale (kerLift hp)
      have hiK : Function.Injective
          ((algebraMap (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1))).comp (kerLift hp)) :=
        (IsFractionRing.injective _ _).comp hinj
      have hψ : ∀ a : Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)),
          IsFractionRing.lift (K := FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))) hiK (algebraMap _ _ a) =
            algebraMap (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1)) (kerLift hp a) :=
        fun a => IsFractionRing.lift_algebraMap hiK a
      obtain ⟨γ₀, hγ₀, hγ₀d⟩ := exists_rad_hom (A := Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (A' := Γ(X₁, ⊤) ⧸ p₁.1)
        (K := FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))))
        (K' := FractionRing (Γ(X₁, ⊤) ⧸ p₁.1)) (kerLift hp)
        (IsFractionRing.lift (K := FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))) hiK) hψ hu
      refine ⟨γ₀, hγ₀, fun _ Ψ hΨ => ?_⟩
      have hΨe : Ψ = IsFractionRing.lift (K := FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))) hiK := by
        refine IsLocalization.ringHom_ext (nonZeroDivisors (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))) (RingHom.ext fun a => ?_)
        obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
        exact (hΨ a').trans (hψ (Ideal.Quotient.mk (p : Ideal Γ(X, ⊤)) a')).symm
      rw [hΨe]
      exact hγ₀d
    · exact ⟨1, Subgroup.one_mem _, fun hp' => absurd hp' hp⟩
  choose γ hγ hγd using key
  exact ⟨γ, hγ, hγd⟩

end PPTb

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl1a =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl1a): residue density at the special point

GLOB/REL PLAN v1, stage S2 input (`h1` of `exists_approx_crt`, O2Ap1). Over an algebraically closed `k`:
* `exists_const_add_mul`: if `B` is unramified and essentially of finite type over `k[X]` and `q` is the only maximal
  ideal containing `t = X - a`, then every `x : B` is `c₀ + t·y` with `c₀ ∈ k[X]`;
* `chart_h1`: the same for a chart `Spec B ⟶ A¹ ⟶ P` with exactly one geometric point over `c(X = a)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtDeg

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.EtDed

universe u

section Alg

end Alg

section Chart

variable {k : Type u} [Field k] {P : Scheme.{u}} (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{u}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)]

theorem chart_h1 [IsAlgClosed k] (a : k)
    (hD : Subsingleton ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ)))
    (d : (geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ)) (x : B) :
    ∃ c₀ : k[X], ∃ y : B, x = φ.hom c₀ + φ.hom (X - C a) * y := by
  let _ : Algebra k[X] B := φ.hom.toAlgebra
  have hφe : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 (Etale.of_comp _ c)
  have : Algebra.Etale k[X] B := hφe
  let q : Ideal B := (fpt (c (A1pt k a)) d).asIdeal
  have hqt : φ.hom (X - C a) ∈ q := by
    have h1 : (chEt c φ).hom (fpt (c (A1pt k a)) d) = c (A1pt k a) := fib_over _ d
    have h2 : Spec.map φ (fpt (c (A1pt k a)) d) = A1pt k a := c.isOpenEmbedding.injective h1
    have h3 : X - C a ∈ (Spec.map φ (fpt (c (A1pt k a)) d)).asIdeal := by
      rw [h2]; exact Ideal.mem_span_singleton_self _
    exact h3
  have huniq : ∀ n : Ideal B, n.IsMaximal → φ.hom (X - C a) ∈ n → n = q := by
    intro n hn ht
    let w : (chEt c φ).left := (⟨n, hn.isPrime⟩ : PrimeSpectrum B)
    have := eq_fpt_of_over hD d w (chEt_hom_eq_of_mem c φ a w ht)
    exact congrArg PrimeSpectrum.asIdeal this
  have hqm : q.IsMaximal := by
    obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q (fpt (c (A1pt k a)) d).isPrime.ne_top
    rw [← huniq m hm (hqm hqt)]; exact hm
  exact exists_const_add_mul a q hqt huniq x

end Chart

end RamanujanPetersson.EtPBC.EtDeg

end

end


