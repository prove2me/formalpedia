-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_089
-- name    : RPLib_FX_EtPBC_089
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T21:54:48.87061+00:00
-- url     : https://prove2.me/theorems/38a304ac-9f54-5d20-9fad-e783ae32996d
-- title:
--   Proper base change for the projective line, library file 089
-- statement:
--   File 089 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovG3`: S4-EtPBC-A, R4-T2 (A2b): sections of `O(d)` lift along the whole tower, for one `d₀`
--   * `S4.Def_RP_EtPBC_A_CovH1`: S4-EtPBC-A, R4-T2 (A2c-1a): `H¹` of `p^n O(d)` vanishes, and overlap relations come from chart 0
--   * `S4.Def_RP_EtPBC_A_CovFil2`: S4-EtPBC-A, R4-T2 (A2c-1e): the `p`-adic filtration on sections of `O(d)` is the `p`-power filtration
--   * `S4.Def_RP_EtPBC_A_StkBC`: S4-EtPBC-A, L1f: the base change map on stalks
--   * `S4.Def_RP_EtPBC_A_DescG4`: S4-EtPBC-A, R4-T1d (part 1): the sheets `V ⟶ U₀`
--   * `S4.Def_RP_EtPBC_A_Emb`: S4-EtPBC-A, M4(B): closure properties of `BCSurj 0`
--   * `S4.Def_RP_EtPBC_A_DescG5`: S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`
--   * `S4.Def_RP_EtPBC_A_O2S1`: S4-EtPBC-A, O2 M5 C-split: every class of `H²(P¹, F)` is a sum of one-point MV classes
--   * `S4.Def_RP_EtPBC_A_PBCP1`: S4-EtPBC-A, G0': base change in degrees `≥ 3`, and proper base change for `P¹_S` modulo degrees `1, 2`
--   * `S4.Def_RP_EtPBC_A_O2L7b2`: S4-EtPBC-A, O2 L7b2: transport of family MV-theta classes
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_34
import Definitions.Def_RPLib_FX_EtPBC_077
import Definitions.Def_RPLib_FX_EtPBC_081

/-!
# Proper base change for the projective line, library file 089

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovG3`: S4-EtPBC-A, R4-T2 (A2b): sections of `O(d)` lift along the whole tower, for one `d₀`
* `S4.Def_RP_EtPBC_A_CovH1`: S4-EtPBC-A, R4-T2 (A2c-1a): `H¹` of `p^n O(d)` vanishes, and overlap relations come from chart 0
* `S4.Def_RP_EtPBC_A_CovFil2`: S4-EtPBC-A, R4-T2 (A2c-1e): the `p`-adic filtration on sections of `O(d)` is the `p`-power filtration
* `S4.Def_RP_EtPBC_A_StkBC`: S4-EtPBC-A, L1f: the base change map on stalks
* `S4.Def_RP_EtPBC_A_DescG4`: S4-EtPBC-A, R4-T1d (part 1): the sheets `V ⟶ U₀`
* `S4.Def_RP_EtPBC_A_Emb`: S4-EtPBC-A, M4(B): closure properties of `BCSurj 0`
* `S4.Def_RP_EtPBC_A_DescG5`: S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`
* `S4.Def_RP_EtPBC_A_O2S1`: S4-EtPBC-A, O2 M5 C-split: every class of `H²(P¹, F)` is a sum of one-point MV classes
* `S4.Def_RP_EtPBC_A_PBCP1`: S4-EtPBC-A, G0': base change in degrees `≥ 3`, and proper base change for `P¹_S` modulo degrees `1, 2`
* `S4.Def_RP_EtPBC_A_O2L7b2`: S4-EtPBC-A, O2 L7b2: transport of family MV-theta classes
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_CovG3 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2b): sections of `O(d)` lift along the whole tower, for one `d₀`

Charts `Bᵢ` with ring maps `ιBᵢ : R → Bᵢ` (agreeing in `N`) and `Jᵢ = p Bᵢ`, `JN = p N`:
* level maps **`lι₀`**, **`lι₁`** (`R → Eᵢ` at level `k`), **`lI`** (the ideal `p E`), `lι_compat`, `lhv`;
* along a transition: `lρι₀`, **`ker_ρ`** (`ker ρ = p^(k+1) E'`), `lq₀`, `lq₁`, `lqI` (`p^(k+1) · p E' = 0`), `lI_comap`;
* **`good_tower`**: generators with the same exponents at every level of `tower`;
* **`secMap_surj_tower`**: one `d₀` such that `secMap (towerHom k) d` is surjective for all `k` and `d ≥ d₀`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Lv

end Lv

section Tower

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] (φ₀ : B₀ →+* N)
  (φ₁ : B₁ →+* N) (J₀ : Ideal B₀) (J₁ : Ideal B₁) (JN : Ideal N) (h₀ : J₀.map φ₀ = JN) (h₁ : J₁.map φ₁ = JN)
  (t₀ : B₀) (t₁ : B₁) (hφ₀ : IsAwayMap φ₀ t₀) (hφ₁ : IsAwayMap φ₁ t₁) (hu₀ : IsUnit (φ₀ t₀))
  (hu₁ : IsUnit (φ₁ t₁)) (C₀ : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ 0) (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁)
  (p : Ideal R)

include hφ₀ hφ₁ hu₀ hu₁

/-- **Sections of `O(d)` lift along the whole tower** for every `d ≥ d₀` (one `d₀` for all levels). -/
theorem secMap_surj_tower (hts : φ₀ t₀ * φ₁ t₁ = 1) (hB : (eval₂RingHom ιB₀ t₀).Finite)
    (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) :
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ k, Function.Surjective
      ((towerHom φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ k).secMap (Ideal.Quotient.factor_mk _ _) d) := by
  obtain ⟨r, e, hG⟩ := good_tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ ιB₀ p hts hB hJ₀
  refine ⟨∑ i, e i, fun d hd k => ?_⟩
  obtain ⟨m, y, hk⟩ := hG (k + 1)
  let H := towerHom φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ k
  have hle : ∀ i, e i ≤ d := fun i =>
    le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le (e j)) (Finset.mem_univ i)) hd
  have h1 := TwoCov.h1_mod _ _ (lι_compat ιB₀ ιB₁ hιB _) (lhv hts _) hk hle
  exact H.secMap_surj_of_h1 _ _ (lι_compat ιB₀ ιB₁ hιB _) (p ^ (k + 1)) (lq₀ ιB₀ p H hJ₀) (lq₁ ιB₁ p H hJ₁)
    (ker_ρ ιB₀ p H hJ₀).le _ (lqI ιB₀ p hJ₀) d h1 _

end Tower

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovH1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-1a): `H¹` of `p^n O(d)` vanishes, and overlap relations come from chart 0

For a two-chart cover `C` with ring maps `ιᵢ : R → Eᵢ` agreeing on the overlap:
* **`TwoCov.Spl ι₀ ι₁ 𝔞 d z`**: `z = ψ₀ x₀ - u^d ψ₁ x₁` with `xᵢ ∈ 𝔞 Eᵢ`; `Spl.add`, `Spl.zero`, `Spl.mono`, `Spl.mul`;
* **`TwoCov.spl_pow`**: `H¹ = 0` modulo `p E` and `p^N E = 0` give `Spl (p^n)` on all of `p^n E`;
* **`TwoCov.to_chart0`**: a relation vector on the overlap with entries in `𝔞 E` is `u^{-e} ψ₀` of one on chart 0;
* **`spl_tower`**: one `d₀` with `Spl (p^n) d` on `p^n E` at every level of the tower, all `n`, all `d ≥ d₀`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Spl

end Spl

section Tower

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] (φ₀ : B₀ →+* N)
  (φ₁ : B₁ →+* N) (J₀ : Ideal B₀) (J₁ : Ideal B₁) (JN : Ideal N) (h₀ : J₀.map φ₀ = JN) (h₁ : J₁.map φ₁ = JN)
  (t₀ : B₀) (t₁ : B₁) (hφ₀ : IsAwayMap φ₀ t₀) (hφ₁ : IsAwayMap φ₁ t₁) (hu₀ : IsUnit (φ₀ t₀))
  (hu₁ : IsUnit (φ₁ t₁)) (C₀ : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ 0) (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁)
  (p : Ideal R)

include hφ₀ hφ₁ hu₀ hu₁

/-- **`H¹(p^n O(d)) = 0` at every level of the tower** for one `d₀`. -/
theorem spl_tower (hts : φ₀ t₀ * φ₁ t₁ = 1) (hB : (eval₂RingHom ιB₀ t₀).Finite)
    (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hJ₀ : J₀ = p.map ιB₀) :
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ k n, ∀ z ∈ (p ^ n).map
      ((tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ k).ψ₀.comp
        (lι₀ ιB₀ (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ k))),
      (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ k).Spl
        (lι₀ ιB₀ (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ k))
        (lι₁ ιB₁ (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ k)) (p ^ n) d z := by
  obtain ⟨r, e, hG⟩ := good_tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ ιB₀ p hts hB hJ₀
  refine ⟨∑ i, e i, fun d hd k => ?_⟩
  obtain ⟨m, y, hk⟩ := hG k
  have hle : ∀ i, e i ≤ d := fun i =>
    le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le (e j)) (Finset.mem_univ i)) hd
  have h1 := TwoCov.h1_mod _ _ (lι_compat ιB₀ ιB₁ hιB _) (lhv hts _) hk hle
  have hN : (p ^ (k + 1)).map ((tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ k).ψ₀.comp
      (lι₀ ιB₀ (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ k))) = ⊥ := by
    rw [← Ideal.map_map, lpow_bot₀ φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ ιB₀ p hJ₀ _ le_rfl, Ideal.map_bot]
  exact TwoCov.spl_pow (lι_compat ιB₀ ιB₁ hιB _) p d (fun z => h1 z) (k + 1) hN

end Tower

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovFil2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-1e): the `p`-adic filtration on sections of `O(d)` is the `p`-power filtration

* `FilProp`: every section of `O(d)` with entries in `p^(j+1)` is `∑ αᵢ yᵢ` with `yᵢ` sections with entries in `p^j`;
* `fil_step`: `FilProp` at one level `k` for `d ≥ d₀ + F` (from uniform `H¹` vanishing and uniform relations);
* **`fil_tower`**: one `d₂` with `FilProp` at every level of the tower and every `d ≥ d₂`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Lv

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁) (p : Ideal R)

/-- **`FilProp` at one level** for `d ≥ d₀ + F`. -/
theorem fil_step [IsNoetherianRing R] {g : ℕ} (α : Fin g → R) (hα : p = Ideal.span (Set.range α))
    (hts : φ₀ t₀ * φ₁ t₁ = 1) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hJ₀ : J₀ = p.map ιB₀)
    (hJ₁ : J₁ = p.map ιB₁) {k : ℕ} (C : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k) (d d₀ F : ℕ) (hd : d₀ + F ≤ d)
    (hspl : ∀ d', d₀ ≤ d' → ∀ n, ∀ z ∈ (p ^ n).map (C.ψ₀.comp (lι₀ ιB₀ C)),
      C.Spl (lι₀ ιB₀ C) (lι₁ ιB₁ C) (p ^ n) d' z)
    (hrel : ∀ n, ∃ n' ≤ n, ∃ (L : ℕ) (ρ0 : Fin L → Fin g → B₀) (ρ1 : Fin L → Fin g → B₁) (f : Fin L → ℕ),
      (∀ l, f l ≤ F) ∧ (∀ l, ρ0 l ∈ RelV p α ιB₀ n') ∧ (∀ l, ρ1 l ∈ RelV p α ιB₁ n') ∧
      (∀ l i, φ₀ (ρ0 l i) = φ₀ t₀ ^ f l * φ₁ (ρ1 l i)) ∧
      ∀ w ∈ RelV p α ιB₀ n, ∃ β : Fin L → B₀, (∀ l, β l ∈ (p ^ (n - n')).map ιB₀) ∧
        w = ∑ l, β l • ρ0 l) :
    FilProp ιB₀ ιB₁ p α C d := by
  intro j x hx hx₀ hx₁
  rcases lt_or_ge k j with hkj | hjk
  · have h0 : x.1 = 0 := by
      have h := hx₀
      rw [lpow_bot₀ _ _ _ _ _ _ _ _ _ ιB₀ p hJ₀ C (by omega)] at h
      exact (Submodule.mem_bot _).1 h
    have h1 : x.2 = 0 := by
      have h := hx₁
      rw [lpow_bot₁ _ _ _ _ _ _ _ _ _ ιB₁ p hJ₁ C (by omega)] at h
      exact (Submodule.mem_bot _).1 h
    refine ⟨fun _ => 0, fun _ => (C.sec d).zero_mem, fun _ => Ideal.zero_mem _, fun _ => Ideal.zero_mem _,
      Prod.ext ?_ ?_⟩
    · rw [h0, Prod.fst_sum]
      simp
    · rw [h1, Prod.snd_sum]
      simp
  · obtain ⟨n', hn', L, ρ0, ρ1, f, hf, hρ0, hρ1, hρ, hgen⟩ := hrel j
    obtain ⟨y0, hy0, hx0e⟩ := decomp_succ p α hα (lι₀ ιB₀ C) j hx₀
    obtain ⟨z, hz, hx1e⟩ := decomp_succ p α hα (lι₁ ιB₁ C) j hx₁
    have hcomp := lι_compat ιB₀ ιB₁ hιB C
    obtain ⟨w, hwdef⟩ : ∃ w : Fin g → C.E, ∀ i, w i = C.ψ₀ (y0 i) - C.u ^ d * C.ψ₁ (z i) :=
      ⟨_, fun _ => rfl⟩
    have hw : ∀ i, w i ∈ (p ^ j).map (C.ψ₀.comp (lι₀ ιB₀ C)) := by
      intro i
      rw [hwdef]
      refine Ideal.sub_mem _ ?_ (Ideal.mul_mem_left _ _ ?_)
      · rw [← Ideal.map_map]
        exact Ideal.mem_map_of_mem _ (hy0 i)
      · rw [hcomp, ← Ideal.map_map]
        exact Ideal.mem_map_of_mem _ (hz i)
    have hμ : ∑ i, C.ψ₀ (lι₀ ιB₀ C (α i)) * w i = 0 := by
      have e1 : ∀ i, C.ψ₀ (lι₀ ιB₀ C (α i)) = C.ψ₁ (lι₁ ιB₁ C (α i)) := fun i =>
        RingHom.congr_fun hcomp (α i)
      have hsec : C.ψ₀ x.1 = C.u ^ d * C.ψ₁ x.2 := hx
      rw [hx0e, hx1e] at hsec
      simp only [map_sum, map_mul] at hsec
      simp only [hwdef, mul_sub, Finset.sum_sub_distrib]
      rw [sub_eq_zero, hsec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [e1]
      ring
    obtain ⟨a, b, ha, hb, ha0, hb0, hab⟩ := lift_rel ιB₀ ιB₁ p α hα hts hJ₀ hJ₁ C d d₀ F hd hspl hjk hn'
      ρ0 ρ1 f hf hρ0 hρ1 hρ hgen w hw hμ
    refine ⟨fun i => (y0 i - a i, z i - b i), fun i => ?_, fun i => Ideal.sub_mem _ (hy0 i) (ha i),
      fun i => Ideal.sub_mem _ (hz i) (hb i), Prod.ext ?_ ?_⟩
    · show C.ψ₀ (y0 i - a i) = C.u ^ d * C.ψ₁ (z i - b i)
      have h := hab i
      rw [hwdef] at h
      rw [map_sub, map_sub]
      linear_combination h
    · simp only [Prod.fst_sum, hx0e, mul_sub, Finset.sum_sub_distrib, ha0, sub_zero]
    · simp only [Prod.snd_sum, hx1e, mul_sub, Finset.sum_sub_distrib, hb0, sub_zero]

end Lv

section Tower

end Tower

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_StkBC =====
section

/-!
# S4-EtPBC-A, L1f: the base change map on stalks

Generic form: for `g : P ⟶ S`, a geometric point `s` of `S`, a sheaf `F` on `P`, `n : ℕ`, a presheaf `Q` on `S` and
additive bijections `e V : Q(V) ≃+ Ext^n(Λ[g⁻¹ V], F)` natural in `V` (`GermNat`), the germ maps
`germBC j = Delta.bc j ∘ e` (base change along the units `bcUnit`) are compatible, so they define `stalkBC` on the fibre
`Q_s` of `Q`. It is surjective / injective when base change is surjective / injective on germs (`BCSurj` / `BCInj`):
`stalkEquiv : Q_s ≃+ Ext^n(Λ_{P_s}, ι^* F)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- Base change is surjective on germs (degree `q`, sheaf `G`). -/
abbrev BCSurj (q : ℕ) (G : EtSh Λ P) : Prop :=
  Delta.SurjAt (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s) q G

variable (F : EtSh Λ P) (n : ℕ) (Q : (S.Etale)ᵒᵖ ⥤ ModuleCat.{u} Λ)
  (e : ∀ V : S.Etale, Q.obj (op V) ≃+ Ext.{u} (freeSh Λ ((etPull g).obj V)) F n)

/-- Naturality of the identifications `e`. -/
abbrev GermNat : Prop :=
  ∀ {V' V : S.Etale} (a : V' ⟶ V) (z : Q.obj (op V)),
    e V' (Q.map a.op z) = (Ext.mk₀ (freeMap Λ ((etPull g).map a))).comp (e V z) (zero_add n)

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_DescG4 =====
section

/-!
# S4-EtPBC-A, R4-T1d (part 1): the sheets `V ⟶ U₀`

For `ν : M`, the evaluations `evR U ν : B(U) → CU V U`, `f ↦ f ν`, glue (along the affine opens of `X`, as in
Mathlib's `Scheme.Hom.toNormalization`) to the **sheet** `sheet ν : V ⟶ U₀` over `X`:
`ι_sheet` (its restriction to `V.hom⁻¹ U`), `sheet_toU0`, and `sheetE ν : V ⟶ U0E` in `X.Etale`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescG

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.DescA TensorProduct

universe u

section Sheet

variable {X : Scheme.{u}} (V : X.Etale) [IsAffineHom V.hom] [Surjective V.hom] {Λ : Type u} [CommRing Λ]
  {M : ModuleCat.{u} Λ} [Fintype M] [DecidableEq M] {E Q : EtSh Λ X} (a : constSh Λ X M ⟶ E) (b : E ⟶ Q)
  (hab : a ≫ b = 0) (hS : (ShortComplex.mk a b hab).ShortExact) (e : E.obj.obj (op V))
  (he : ∀ (W : X.Etale) (w₁ w₂ : W ⟶ V), (b.hom.app (op W)).hom ((E.obj.map w₁.op).hom e) =
    (b.hom.app (op W)).hom ((E.obj.map w₂.op).hom e))

/-- `U₀` as an etale `X`-object. -/
abbrev U0E : X.Etale := Scheme.Etale.mk (toU0 V a b hab hS e he)

/-- The sheet as a map of etale `X`-objects. -/
def sheetE (ν : M) : V ⟶ U0E V a b hab hS e he :=
  MorphismProperty.Over.homMk (sheet V a b hab hS e he ν) (sheet_toU0 V a b hab hS e he ν) trivial

theorem sheetE_left (ν : M) : (sheetE V a b hab hS e he ν).left = sheet V a b hab hS e he ν := rfl

end Sheet

end RamanujanPetersson.EtPBC.DescG

end

end

-- ===== S4.Def_RP_EtPBC_A_Emb =====
section

/-!
# S4-EtPBC-A, M4(B): closure properties of `BCSurj 0`

* `bcSurj_zero_of_hom`, `hom_of_bcSurj_zero`: `BCSurj 0` as a statement about morphisms `Λ_{P_s} ⟶ ι^* H`;
* **`bcSurj_of_mono`**: `BCSurj 0` passes to subobjects (`g` universally closed: `bcInj_zero` on the cokernel);
* **`bcSurj_biprod`**: `BCSurj 0` for `H₁` and `H₂` gives it for `H₁ ⊞ H₂`;
* `EmbC F`: `F` embeds into a sheaf with `BCSurj 0`; **`bcSurj_of_embC`**, **`embC_of_mono`**.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- `F` embeds into a sheaf with `BCSurj 0`. -/
def EmbC (F : EtSh Λ P) : Prop :=
  ∃ (H : EtSh Λ P) (m : F ⟶ H), Mono m ∧ BCSurj Λ g s 0 H

theorem embC_of_bcSurj {F : EtSh Λ P} (h : BCSurj Λ g s 0 F) : EmbC g s F :=
  ⟨F, 𝟙 F, inferInstance, h⟩

end RamanujanPetersson.EtPBC

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

/-- One point of the cover. -/
theorem sheet_cover_pt (U : X.AffineZariskiSite) (Qp : PrimeSpectrum (datA V a b hab hS e he U).B) :
    (glD (coequifibered_alphaU V a b hab hS e he)).cover.f U Qp ∈
      ⋃ ν, Set.range (sheetE V a b hab hS e he ν).left := by
  obtain ⟨ν, P, hP⟩ := (datA V a b hab hS e he U).exists_sheet_prime Qp
  refine Set.mem_iUnion.2 ⟨ν, tauU V U P, ?_⟩
  have h1 := congrArg (fun f => f P) (tauU_sheet V a b hab hS e he ν U)
  have hev : (CommRingCat.ofHom (evR V a b hab hS e he U ν)).hom = (datA V a b hab hS e he U).evB ν :=
    RingHom.ext fun _ => rfl
  refine h1.trans (congrArg ((glD (coequifibered_alphaU V a b hab hS e he)).cover.f U) ?_)
  change PrimeSpectrum.comap (CommRingCat.ofHom (evR V a b hab hS e he U ν)).hom P = Qp
  rw [hev]
  exact hP

/-- **The sheets cover `U₀`.** -/
theorem sheet_cover : Sieve.ofArrows (fun _ : M => V) (sheetE V a b hab hS e he) ∈
    X.smallEtaleTopology (U0E V a b hab hS e he) := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨U, Qp, rfl⟩ := Scheme.Cover.exists_eq (glD (coequifibered_alphaU V a b hab hS e he)).cover y
  exact sheet_cover_pt V a b hab hS e he U Qp

end Cover

end RamanujanPetersson.EtPBC.DescG

end

end

-- ===== S4.Def_RP_EtPBC_A_O2S1 =====
section

/-!
# S4-EtPBC-A, O2 M5 C-split: every class of `H²(P¹, F)` is a sum of one-point MV classes

* `opEt_ext` (maps into `opEt U` are unique), `toOpEt`, `opEtMap`, `freeMap_id`;
* `mvC_shortExact'`: the MV criterion with "surjective onto the fibre of `Z`" instead of "nonempty";
* `locC`, **`locC_shortExact`**: the one-point MV complex `Λ[D ×_P Uo] ⟶ Λ[D] ⊞ Λ[P ∖ z] ⟶ Λ[P]` for an etale `D`
  with one geometric point over `z` and all other points over `Uo` (`Uo ⊆ P ∖ z`);
* `IsLoc Λ F z β` (one-point MV class `ε_loc ∘ κ`), `locSpan Λ F` (the subgroup they generate);
* `exists_good_one`, **`split_step`** (a class dying on `U` differs from a one-point class at `z ∉ U` by a class
  dying on `U ∪ {z}`), **`mem_locSpan_of_dies`** (induction on `#(P ∖ U)`), **`mem_locSpan_P1`**:
  `H²(P¹, F) = locSpan` (with `claimD`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtCompact.CurveHn RamanujanPetersson.EtPBC.GenGeo

universe u

section Gen

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

variable (Λ) in
/-- The subgroup generated by one-point MV classes. -/
def locSpan (F : EtSh Λ P) : AddSubgroup (Ext.{u} (freeSh Λ (etId P)) F 2) :=
  AddSubgroup.closure {β | ∃ z, IsLoc Λ F z β}

end Gen

section P1

end P1

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_PBCP1 =====
section

/-!
# S4-EtPBC-A, G0': base change in degrees `≥ 3`, and proper base change for `P¹_S` modulo degrees `1, 2`

For `g = pullback.snd : P¹_K ×_K S ⟶ S` (`K = K̄`, `ℓ ≠ char K`, `ℓ^m Λ = 0`) and a `K`-rational geometric point `s`:
* **`p1Bundle_bcSurj_add_three`**: base change is surjective on germs in degrees `q + 3` for every sheaf
  (`H^(q+3)(P¹_K, -) = 0`);
* **`pbc_p1_of_surj`**: if base change is surjective on germs in degrees `1` and `2` for every sheaf, then
  `(R^q g_* F)_s ≃ H^q(P_s, F|P_s)` for every sheaf `F` and every `q` (`S` noetherian of finite type over `K`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3

section P1Vanish3

variable (K : Type) [Field K] [IsAlgClosed K] {Λ : Type} [CommRing Λ] (l : ℕ) [Fact l.Prime]
  (hl : (l : K) ≠ 0) (m : ℕ) (hΛ : ((l ^ m : ℕ) : Λ) = 0)
  {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K)) (s : GeomPt S) [IsIso (s.pt ≫ gS)]

include hl hΛ

/-- `H^(q+3)` of the fibre vanishes for every sheaf. -/
theorem fib_H_add_three_eq_zero (G : EtSh Λ (fib (pullback.snd (P1.toSpecK K) gS) s)) (q : ℕ)
    (e : H Λ G (q + 3)) : e = 0 := by
  have h := CurveHn.P1.H_add_three_eq_zero_all K l hl m hΛ _ q ((fibH K gS s G (q + 3)).symm e)
  exact (fibH K gS s G (q + 3)).symm.injective (h.trans (map_zero _).symm)

end P1Vanish3

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L7b2 =====
section

/-!
# S4-EtPBC-A, O2 L7b2: transport of family MV-theta classes
**`TrE_mvTheta`**: for an MV square over `qV^*V` on `P = P¹_K ×_K S` and a `K`-point `v'` of `V` over `s`, the
transport `TrE` of the `P¹_K`-class `Λ[σG] ∘ ιP^*(ε ∘ θ(p₁, κ) ∘ Λ[r])` is the base change at `jG = (V, v')` of the
family class `ε ∘ θ(p₁, κ) ∘ Λ[r]`. Proof: `mvThetaR_pull` along `e`, `bc_mvThetaR` at `jG`, and `mvTheta_map` along
the base change identifications `isoE` (`nbhdSec_eq`, `isoE_natural`, `isoE_left_fW`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE

universe w v₀ u₀

section GenTr

universe w' v₁ u₁ v₂ u₂

end GenTr

section TrMV

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (Λ : Type) [CommRing Λ]
  (V : S.Etale) (v' : Spec (CommRingCat.of K) ⟶ V.left) (hv' : v' ≫ V.hom = sK gS s)

theorem hN_R : (unitIso Λ (fib (qV K gS) s)).inv ≫ freeMap Λ (nbhdSec (qV K gS) s (jR gS s V v' hv')) =
    ((unitIso Λ (fib (qV K gS) s)).inv ≫ freeMap Λ ((etIdPull (fibToP1 K gS s)).hom ≫
      (etPull (fibToP1 K gS s)).map (σG gS s V v' hv'))) ≫ freeMap Λ (isoE gS s ((etPull (qV K gS)).obj V)) := by
  have h1 : freeMap Λ (nbhdSec (qV K gS) s (jR gS s V v' hv')) = freeMap Λ ((etIdPull (fibToP1 K gS s)).hom ≫
      (etPull (fibToP1 K gS s)).map (σG gS s V v' hv') ≫ isoE gS s ((etPull (qV K gS)).obj V)) :=
    congrArg (freeMap Λ) (nbhdSec_eq gS s V v' hv')
  have h3 : freeMap Λ ((etIdPull (fibToP1 K gS s)).hom ≫ (etPull (fibToP1 K gS s)).map (σG gS s V v' hv') ≫
      isoE gS s ((etPull (qV K gS)).obj V)) = freeMap Λ (((etIdPull (fibToP1 K gS s)).hom ≫
        (etPull (fibToP1 K gS s)).map (σG gS s V v' hv')) ≫ isoE gS s ((etPull (qV K gS)).obj V)) :=
    congrArg (freeMap Λ) (Category.assoc _ _ _).symm
  rw [h1, h3, freeMap_comp, Category.assoc]

end TrMV

end RamanujanPetersson.EtPBC.EtMV

end

end


