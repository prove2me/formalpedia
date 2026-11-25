-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_053
-- name    : RPLib_FX_EtPBC_053
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:36:22.678828+00:00
-- url     : https://prove2.me/theorems/be2398cf-7c23-5015-869b-f2735a84d56e
-- title:
--   Proper base change for the projective line, library file 053
-- statement:
--   File 053 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovLim1`: S4-EtPBC-A, R4-T2 (A2c-2a): compatible families of sections along a tower of level covers
--   * `S4.Def_RP_EtPBC_A_CovLim2`: S4-EtPBC-A, R4-T2 (A2c-2b): `R`-combinations of compatible families at each level
--   * `S4.Def_RP_EtPBC_A_CovLim4`: S4-EtPBC-A, R4-T2 (A2c-2d): compatible families are combinations with coefficients in a `p`-precomplete ring
--   * `S4.Def_RP_EtPBC_A_CovLim5`: S4-EtPBC-A, R4-T2 (A2c-2f): multiplication by `T₀`, `T₁` on compatible families; completed generation
--   * `S4.Def_RP_EtPBC_A_CovHat1`: S4-EtPBC-A, R4-T2 (A2c-3a): the completed chart rings as subrings of products of localizations
--   * `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
--   * `S4.Def_RP_EtPBC_A_CovEtL`: S4-EtPBC-A, R4-T2 (A2c-5, E4b1): etale on `P¹` from etale near the closed fibre (generic)
--   * `S4.Def_RP_EtPBC_A_CovHat7`: S4-EtPBC-A, R4-T2 (A2c-3g): the kernels of the level reductions of the completed charts
--   * `S4.Def_RP_EtPBC_A_T3dC`: S4-EtPBC-A, R4-T3d (part C): compatibility of the base change maps, and the degree-one assembly
--   * `S4.Def_RP_EtPBC_A_EAlg`: S4-EtPBC-A, M4(E), ALG: maps out of a finitely generated sheaf via relations between germs
--   * `S4.Def_RP_EtPBC_A_H1FG`: S4-EtPBC-A, R2(c-e): degree-1 base change reduces to finitely generated subsheaves
--   * `S4.Def_RP_EtPBC_A_NagC`: S4-EtPBC-A, M4(N3): the relative normalization of a finite field point is finite
--   * `S4.Def_RP_EtPBC_A_O2L1`: S4-EtPBC-A, O2 (MV route), L1: base change of Mayer-Vietoris classes
--   * `S4.Def_RP_EtPBC_A_O2R3`: S4-EtPBC-A, O2 (MV route), M6a (3): the multi-point MV complex maps to each one-point complex
--   * `S4.Def_RP_EtPBC_A_O2R4`: S4-EtPBC-A, O2 (MV route), M6a (4): the relation between one-point classes
--   * `S4.Def_RP_EtPBC_A_O2Sh2`: S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree
--   * `S4.Def_RP_EtPBC_A_O2E7`: S4-EtPBC-A, O2 C-plan S4d2: purity on `W₁ = Spec B_t` with the chart Kummer class
--   * `S4.Def_RP_EtPBC_A_O2PPTb`: S4-EtPBC-A, O2 GLOB (O2PPTb): a piece Kummer class pulled back along an etale map
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_042
import Definitions.Def_RPLib_FX_EtPBC_043

/-!
# Proper base change for the projective line, library file 053

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovLim1`: S4-EtPBC-A, R4-T2 (A2c-2a): compatible families of sections along a tower of level covers
* `S4.Def_RP_EtPBC_A_CovLim2`: S4-EtPBC-A, R4-T2 (A2c-2b): `R`-combinations of compatible families at each level
* `S4.Def_RP_EtPBC_A_CovLim4`: S4-EtPBC-A, R4-T2 (A2c-2d): compatible families are combinations with coefficients in a `p`-precomplete ring
* `S4.Def_RP_EtPBC_A_CovLim5`: S4-EtPBC-A, R4-T2 (A2c-2f): multiplication by `T₀`, `T₁` on compatible families; completed generation
* `S4.Def_RP_EtPBC_A_CovHat1`: S4-EtPBC-A, R4-T2 (A2c-3a): the completed chart rings as subrings of products of localizations
* `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
* `S4.Def_RP_EtPBC_A_CovEtL`: S4-EtPBC-A, R4-T2 (A2c-5, E4b1): etale on `P¹` from etale near the closed fibre (generic)
* `S4.Def_RP_EtPBC_A_CovHat7`: S4-EtPBC-A, R4-T2 (A2c-3g): the kernels of the level reductions of the completed charts
* `S4.Def_RP_EtPBC_A_T3dC`: S4-EtPBC-A, R4-T3d (part C): compatibility of the base change maps, and the degree-one assembly
* `S4.Def_RP_EtPBC_A_EAlg`: S4-EtPBC-A, M4(E), ALG: maps out of a finitely generated sheaf via relations between germs
* `S4.Def_RP_EtPBC_A_H1FG`: S4-EtPBC-A, R2(c-e): degree-1 base change reduces to finitely generated subsheaves
* `S4.Def_RP_EtPBC_A_NagC`: S4-EtPBC-A, M4(N3): the relative normalization of a finite field point is finite
* `S4.Def_RP_EtPBC_A_O2L1`: S4-EtPBC-A, O2 (MV route), L1: base change of Mayer-Vietoris classes
* `S4.Def_RP_EtPBC_A_O2R3`: S4-EtPBC-A, O2 (MV route), M6a (3): the multi-point MV complex maps to each one-point complex
* `S4.Def_RP_EtPBC_A_O2R4`: S4-EtPBC-A, O2 (MV route), M6a (4): the relation between one-point classes
* `S4.Def_RP_EtPBC_A_O2Sh2`: S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree
* `S4.Def_RP_EtPBC_A_O2E7`: S4-EtPBC-A, O2 C-plan S4d2: purity on `W₁ = Spec B_t` with the chart Kummer class
* `S4.Def_RP_EtPBC_A_O2PPTb`: S4-EtPBC-A, O2 GLOB (O2PPTb): a piece Kummer class pulled back along an etale map
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_CovLim1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-2a): compatible families of sections along a tower of level covers

* `dep_choice`, `seq_choice`: sequences by choice along `ℕ`;
* `ker_ρ₀`, `ker_ρ₁`: the kernels of a transition are `p^(k+1)` on the charts; `mem_of_ρ₀`, `mem_of_ρ₁`: an element whose
  image has entries in `p^n` (`n ≤ k+1`) has entries in `p^n`;
* **`Gam C H d`**: compatible families of sections of `O(d)` along a tower `C`, `H`; **`exists_gam`**: every level-`0`
  section lifts when all transitions are surjective on sections.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Ker

end Ker

section Fam

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k))

/-- **Level-`0` sections lift to compatible families** when the transitions are surjective on sections. -/
theorem exists_gam {d : ℕ} (hs : ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (y : (C 0).sec d) : ∃ x ∈ Gam C H d, x.1 0 = y.1.1 ∧ x.2 0 = y.1.2 := by
  obtain ⟨f, hf0, hf⟩ := dep_choice (X := fun k => (C k).sec d)
    (fun k x' x => (H k).secMap (Ideal.Quotient.factor_mk _ _) d x' = x) y (fun k x => hs k x)
  refine ⟨(fun k => (f k).1.1, fun k => (f k).1.2), fun k => ⟨?_, ?_, (f k).2⟩,
    congrArg (fun z : (C 0).sec d => z.1.1) hf0, congrArg (fun z : (C 0).sec d => z.1.2) hf0⟩
  · exact congrArg (fun z : (C k).sec d => z.1.1) (hf k)
  · exact congrArg (fun z : (C k).sec d => z.1.2) (hf k)

end Fam

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovLim2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-2b): `R`-combinations of compatible families at each level

For families `σ : Fin r → (∀ k, E₀ k) × (∀ k, E₁ k)`:
* **`lev C ιB₀ ιB₁ σ m c`** `= ∑ cᵢ σᵢ` at level `m`; `lev_fst`, `lev_snd`, `lev_add`, `lev_sub`, `lev_zero`, `lev_comb`;
* `lev_mem`: it is a section of `O(d)` when the `σᵢ` are in `Gam`; `lev_ρ₀`, `lev_ρ₁`: compatibility;
* `lev_congr`: coefficients congruent modulo `p^(m+1)` give the same level-`m` combination;
* **`levF`**, `levF_mem`: the family of all levels lies in `Gam`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Lev

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (p : Ideal R) {r : ℕ} (σ : Fin r → (∀ k, (C k).E₀) × (∀ k, (C k).E₁))

theorem lev_mem (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) {d : ℕ} (hσ : ∀ i, σ i ∈ Gam C H d) (m : ℕ)
    (c : Fin r → R) : lev C ιB₀ ιB₁ σ m c ∈ (C m).sec d := by
  unfold lev
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  rw [TwoCov.mem_sec]
  have e := RingHom.congr_fun (lι_compat ιB₀ ιB₁ hιB (C m)) (c i)
  simp only [RingHom.comp_apply] at e
  have hs := ((mem_gam C H _).1 (hσ i) m).2.2
  simp only [map_mul, e, hs]
  ring

theorem lev_ρ₀ {d : ℕ} (hσ : ∀ i, σ i ∈ Gam C H d) (m : ℕ) (c : Fin r → R) :
    (H m).ρ₀ (lev C ιB₀ ιB₁ σ (m + 1) c).1 = (lev C ιB₀ ιB₁ σ m c).1 := by
  simp only [lev_fst, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e := RingHom.congr_fun (lρι₀ ιB₀ (H m)) (c i)
  simp only [RingHom.comp_apply] at e
  rw [e, ((mem_gam C H _).1 (hσ i) m).1]

theorem lev_ρ₁ {d : ℕ} (hσ : ∀ i, σ i ∈ Gam C H d) (m : ℕ) (c : Fin r → R) :
    (H m).ρ₁ (lev C ιB₀ ιB₁ σ (m + 1) c).2 = (lev C ιB₀ ιB₁ σ m c).2 := by
  simp only [lev_snd, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e := RingHom.congr_fun (lρι₁ ιB₁ (H m)) (c i)
  simp only [RingHom.comp_apply] at e
  rw [e, ((mem_gam C H _).1 (hσ i) m).2.1]

theorem levF_mem (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) {d : ℕ} (hσ : ∀ i, σ i ∈ Gam C H d) (c : Fin r → R) :
    levF C ιB₀ ιB₁ σ c ∈ Gam C H d :=
  (mem_gam C H _).2 fun k => ⟨lev_ρ₀ C H ιB₀ ιB₁ σ hσ k c, lev_ρ₁ C H ιB₀ ιB₁ σ hσ k c,
    lev_mem C H ιB₀ ιB₁ σ hιB hσ k c⟩

end Lev

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovLim4 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-2d): compatible families are combinations with coefficients in a `p`-precomplete ring

For compatible families `σ : Fin r → Gam C H d` generating level `0`, over `R` with `IsPrecomplete p R`:
* `gam_agree`: two compatible families that agree at level `k` agree at every level `m ≤ k`;
* `gam_seq`: a level-`k₀` combination extends to a combination at all levels with congruent coefficients;
* **`gam_gen`**: every compatible family is `∑ aᵢ σᵢ` at all levels;
* **`gam_ker`**: a compatible family vanishing at level `k` is `∑ aᵢ σᵢ` with all `aᵢ ∈ p^(k+1)`;
* `gen_all`: every level-`m` section is a combination of the `σᵢ`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Agree

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k))

/-- Compatible families that agree at level `k` agree at every level `m ≤ k`. -/
theorem gam_agree {d : ℕ} {x y : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d)
    (hy : y ∈ Gam C H d) : ∀ k m, m ≤ k → x.1 k = y.1 k → x.2 k = y.2 k → x.1 m = y.1 m ∧ x.2 m = y.2 m := by
  intro k
  induction k with
  | zero =>
    intro m hm h₀ h₁
    obtain rfl : m = 0 := by omega
    exact ⟨h₀, h₁⟩
  | succ k ih =>
    intro m hm h₀ h₁
    rcases Nat.lt_or_ge k m with hkm | hkm
    · obtain rfl : m = k + 1 := by omega
      exact ⟨h₀, h₁⟩
    · refine ih m hkm ?_ ?_
      · rw [← ((mem_gam C H x).1 hx k).1, ← ((mem_gam C H y).1 hy k).1, h₀]
      · rw [← ((mem_gam C H x).1 hx k).2.1, ← ((mem_gam C H y).1 hy k).2.1, h₁]

end Agree

section Lim

end Lim

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovLim5 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-2f): multiplication by `T₀`, `T₁` on compatible families; completed generation

* `mT₀`, `mT₁`: multiplication of a family by `T₀ = (1, s)` and `T₁ = (t, 1)`; `ρ₀_t`, `ρ₁_s`; `mT₀_mem`, `mT₁_mem`;
* **`gam_struct`**: finitely many `τⱼ ∈ Gam (e+1)` such that every `x ∈ Gam (e+2)` is
  `T₀ (∑ aⱼ τⱼ) + T₁ (∑ a'ⱼ τⱼ)` (`R` noetherian and `p`-precomplete, `H¹(O(e)) = 0` at level `0`).
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section T

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k))

theorem mT₀_mem (hts : φ₀ t₀ * φ₁ t₁ = 1) {d : ℕ} {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)}
    (hx : x ∈ Gam C H d) : mT₀ C x ∈ Gam C H (d + 1) := by
  refine (mem_gam C H _).2 fun k => ⟨((mem_gam C H x).1 hx k).1, ?_, ?_⟩
  · show (H k).ρ₁ ((C (k + 1)).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1 + 1)) t₁) * x.2 (k + 1)) =
      (C k).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁) * x.2 k
    rw [map_mul, ρ₁_s C H k, ((mem_gam C H x).1 hx k).2.1]
  · show (C k).ψ₀ (x.1 k) =
      (C k).u ^ (d + 1) * (C k).ψ₁ ((C k).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁) * x.2 k)
    rw [((mem_gam C H x).1 hx k).2.2, map_mul, pow_succ (C k).u d]
    linear_combination (-(C k).u ^ d * (C k).ψ₁ (x.2 k)) * lhv hts (C k)

theorem mT₁_mem {d : ℕ} {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)}
    (hx : x ∈ Gam C H d) : mT₁ C x ∈ Gam C H (d + 1) := by
  refine (mem_gam C H _).2 fun k => ⟨?_, ((mem_gam C H x).1 hx k).2.1, ?_⟩
  · show (H k).ρ₀ ((C (k + 1)).a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1 + 1)) t₀) * x.1 (k + 1)) =
      (C k).a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) t₀) * x.1 k
    rw [map_mul, ρ₀_t C H k, ((mem_gam C H x).1 hx k).1]
  · show (C k).ψ₀ ((C k).a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) t₀) * x.1 k) =
      (C k).u ^ (d + 1) * (C k).ψ₁ (x.2 k)
    have hu : (C k).ψ₀ ((C k).a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) t₀)) = (C k).u := rfl
    rw [map_mul, hu, ((mem_gam C H x).1 hx k).2.2, pow_succ (C k).u d]
    ring

end T

section Struct

end Struct

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

theorem gam_one : (1 : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)) ∈ Gam C H 0 := by
  refine (mem_gam C H _).2 fun k => ⟨?_, ?_, ?_⟩
  · exact map_one (H k).ρ₀
  · exact map_one (H k).ρ₁
  · show (C k).ψ₀ 1 = (C k).u ^ 0 * (C k).ψ₁ 1
    rw [map_one, map_one, pow_zero, one_mul]

theorem gam_mul {d e : ℕ} {x y : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d)
    (hy : y ∈ Gam C H e) : x * y ∈ Gam C H (d + e) := by
  refine (mem_gam C H _).2 fun k => ⟨?_, ?_, ?_⟩
  · show (H k).ρ₀ (x.1 (k + 1) * y.1 (k + 1)) = x.1 k * y.1 k
    rw [map_mul, ((mem_gam C H x).1 hx k).1, ((mem_gam C H y).1 hy k).1]
  · show (H k).ρ₁ (x.2 (k + 1) * y.2 (k + 1)) = x.2 k * y.2 k
    rw [map_mul, ((mem_gam C H x).1 hx k).2.1, ((mem_gam C H y).1 hy k).2.1]
  · show (C k).ψ₀ (x.1 k * y.1 k) = (C k).u ^ (d + e) * (C k).ψ₁ (x.2 k * y.2 k)
    rw [map_mul, map_mul, ((mem_gam C H x).1 hx k).2.2, ((mem_gam C H y).1 hy k).2.2, pow_add (C k).u d e]
    ring

theorem gT₀_mem (hts : φ₀ t₀ * φ₁ t₁ = 1) : gT₀ C ∈ Gam C H 1 := by
  refine (mem_gam C H _).2 fun k => ⟨?_, ?_, ?_⟩
  · exact map_one (H k).ρ₀
  · exact ρ₁_s C H k
  · show (C k).ψ₀ 1 = (C k).u ^ 1 * (C k).ψ₁ ((C k).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁))
    rw [map_one, pow_one, lhv hts (C k)]

theorem gT₁_mem : gT₁ C ∈ Gam C H 1 := by
  refine (mem_gam C H _).2 fun k => ⟨?_, ?_, ?_⟩
  · exact ρ₀_t C H k
  · exact map_one (H k).ρ₁
  · show (C k).ψ₀ ((C k).a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) t₀)) = (C k).u ^ 1 * (C k).ψ₁ 1
    rw [map_one, pow_one, mul_one]

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

/-- **Families from the base charts are compatible sections.** -/
theorem famB_mem {b₀ : B₀} {b₁ : B₁} {d : ℕ} (hrel : φ₀ b₀ = φ₀ t₀ ^ d * φ₁ b₁) :
    (fB₀ C b₀, fB₁ C b₁) ∈ Gam C H d := by
  refine (mem_gam C H _).2 fun k => ⟨ρ₀_fB C H b₀ k, ρ₁_fB C H b₁ k, ?_⟩
  have hu : (C k).u = (C k).a (Ideal.Quotient.mk (JN ^ (k + 1)) (φ₀ t₀)) := lψθ₀ (C k) t₀
  show (C k).ψ₀ (fB₀ C b₀ k) = (C k).u ^ d * (C k).ψ₁ (fB₁ C b₁ k)
  rw [fB₀_apply, fB₁_apply, lψθ₀, lψθ₁, hu, hrel, map_mul, map_mul, map_pow, map_pow]

end Hat2

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovEtL =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-5, E4b1): etale on `P¹` from etale near the closed fibre (generic)

* `etK B M`: the ideal of the (closed) non-etale locus of a finitely presented `B`-algebra `M`;
  `etK_of_away` (`M[1/s]` etale gives `s ∈ etK`), `etK_le_iff` (`etK ≤ q` iff `M` is not etale at `q`),
  `etale_of_etK` (`etK = ⊤` gives `M` etale).
* `loc_compat`: along `ψ ∘ β₀ = β ∘ φ` with `φ`, `ψ` away maps at `t`, `β₀ t`, etale-at transports (`loc_etaleAt`).
* **`glob_etale`**: finite covers `βᵢ : Bᵢ → Eᵢ` of the two charts of `P¹_R`, glued over `N`, that are etale on a basic
  open `D(sᵢ)` with `sᵢ ≡ 1 mod m Eᵢ` (`m ≤ jac R`) are etale (`glob` on the non-etale ideals).
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section EtK

end EtK

/-- **Finite covers of the two charts of `P¹_R`, etale near the closed fibre, are etale.** -/
theorem glob_etale {R B₀ B₁ N E₀ E₁ E : Type u} [CommRing R] [CommRing B₀] [CommRing B₁] [CommRing N]
    [CommRing E₀] [CommRing E₁] [CommRing E] [IsNoetherianRing B₀] [IsNoetherianRing B₁]
    (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁) (φ₀ : B₀ →+* N) (φ₁ : B₁ →+* N) (t₀ : B₀) (t₁ : B₁)
    (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀)) (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁))
    (hts : φ₀ t₀ * φ₁ t₁ = 1) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁)
    (hB₀ : (eval₂RingHom ιB₀ t₀).Finite) (hB₁ : (eval₂RingHom ιB₁ t₁).Finite) (m : Ideal R)
    (hm : m ≤ Ideal.jacobson ⊥) (β₀ : B₀ →+* E₀) (β₁ : B₁ →+* E₁) (β : N →+* E) (ψ₀ : E₀ →+* E)
    (ψ₁ : E₁ →+* E) (hc₀ : ψ₀.comp β₀ = β.comp φ₀) (hc₁ : ψ₁.comp β₁ = β.comp φ₁)
    (ha₀ : IsAwayMap ψ₀ (β₀ t₀)) (ha₁ : IsAwayMap ψ₁ (β₁ t₁)) (hf₀ : β₀.Finite) (hf₁ : β₁.Finite)
    (hn₀ : letI := β₀.toAlgebra
      ∃ s : E₀, s - 1 ∈ (m.map ιB₀).map β₀ ∧ Algebra.Etale B₀ (Localization.Away s))
    (hn₁ : letI := β₁.toAlgebra
      ∃ s : E₁, s - 1 ∈ (m.map ιB₁).map β₁ ∧ Algebra.Etale B₁ (Localization.Away s)) :
    β₀.Etale ∧ β₁.Etale := by
  have e₀ : ψ₀ (β₀ t₀) = β (φ₀ t₀) := RingHom.congr_fun hc₀ t₀
  have e₁ : ψ₁ (β₁ t₁) = β (φ₁ t₁) := RingHom.congr_fun hc₁ t₁
  have hu₀' : IsUnit (ψ₀ (β₀ t₀)) := by rw [e₀]; exact hu₀.map β
  have hu₁' : IsUnit (ψ₁ (β₁ t₁)) := by rw [e₁]; exact hu₁.map β
  have hts' : ψ₀ (β₀ t₀) * ψ₁ (β₁ t₁) = 1 := by rw [e₀, e₁, ← map_mul, hts, map_one]
  have hιB' : ψ₀.comp (β₀.comp ιB₀) = ψ₁.comp (β₁.comp ιB₁) := RingHom.ext fun r => by
    have h1 := RingHom.congr_fun hc₀ (ιB₀ r)
    have h2 := RingHom.congr_fun hc₁ (ιB₁ r)
    have h3 := RingHom.congr_fun hιB r
    simp only [RingHom.comp_apply] at h1 h2 h3 ⊢
    rw [h1, h2, h3]
  have hB₀' : (eval₂RingHom (β₀.comp ιB₀) (β₀ t₀)).Finite := by
    have h : eval₂RingHom (β₀.comp ιB₀) (β₀ t₀) = β₀.comp (eval₂RingHom ιB₀ t₀) := by
      ext <;> simp
    rw [h]
    exact hf₀.comp hB₀
  have hB₁' : (eval₂RingHom (β₁.comp ιB₁) (β₁ t₁)).Finite := by
    have h : eval₂RingHom (β₁.comp ιB₁) (β₁ t₁) = β₁.comp (eval₂RingHom ιB₁ t₁) := by
      ext <;> simp
    rw [h]
    exact hf₁.comp hB₁
  letI := β₀.toAlgebra
  letI := β₁.toAlgebra
  haveI : Module.Finite B₀ E₀ := hf₀
  haveI : Module.Finite B₁ E₁ := hf₁
  haveI : Algebra.FinitePresentation B₀ E₀ := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  haveI : Algebra.FinitePresentation B₁ E₁ := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have hK₀ : etK B₀ E₀ ⊔ m.map (β₀.comp ιB₀) = ⊤ := by
    obtain ⟨s, hs1, hs⟩ := hn₀
    rw [← Ideal.map_map, Ideal.eq_top_iff_one]
    have h := Ideal.sub_mem _ (Ideal.mem_sup_left (etK_of_away s hs)) (Ideal.mem_sup_right hs1)
    rwa [sub_sub_cancel] at h
  have hK₁ : etK B₁ E₁ ⊔ m.map (β₁.comp ιB₁) = ⊤ := by
    obtain ⟨s, hs1, hs⟩ := hn₁
    rw [← Ideal.map_map, Ideal.eq_top_iff_one]
    have h := Ideal.sub_mem _ (Ideal.mem_sup_left (etK_of_away s hs)) (Ideal.mem_sup_right hs1)
    rwa [sub_sub_cancel] at h
  have hcomp : ∀ Q : Ideal E, Q.IsPrime → (etK B₀ E₀ ≤ Q.comap ψ₀ ↔ etK B₁ E₁ ≤ Q.comap ψ₁) := by
    intro Q hQ
    have i₀ := (etK_le_iff (B := B₀) (M := E₀) ⟨Q.comap ψ₀, inferInstance⟩).trans
      (not_congr (loc_compat β₀ φ₀ β ψ₀ hc₀ t₀ hφ₀ hu₀ ha₀ hu₀' Q))
    have i₁ := (etK_le_iff (B := B₁) (M := E₁) ⟨Q.comap ψ₁, inferInstance⟩).trans
      (not_congr (loc_compat β₁ φ₁ β ψ₁ hc₁ t₁ hφ₁ hu₁ ha₁ hu₁' Q))
    exact i₀.trans i₁.symm
  have hK₀t : etK B₀ E₀ = ⊤ := glob (β₀.comp ιB₀) (β₁.comp ιB₁) ψ₀ ψ₁ (β₀ t₀) (β₁ t₁) ha₀ hu₀' hts' hιB'
    hB₀' hB₁' m hm (etK B₀ E₀) (etK B₁ E₁) hK₀ hK₁ (fun Q hQ h => (hcomp Q hQ).1 h)
  have hK₁t : etK B₁ E₁ = ⊤ := glob (β₁.comp ιB₁) (β₀.comp ιB₀) ψ₁ ψ₀ (β₁ t₁) (β₀ t₀) ha₁ hu₁'
    (by rw [mul_comm]; exact hts') hιB'.symm hB₁' hB₀' m hm (etK B₁ E₁) (etK B₀ E₀) hK₁ hK₀
    (fun Q hQ h => (hcomp Q hQ).2 h)
  exact ⟨etale_of_etK hK₀t, etale_of_etK hK₁t⟩

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

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k))

/-- A family with vanishing first coordinate at level `k` vanishes at level `k` after a power of `T₀`. -/
theorem van₀ (hts : φ₀ t₀ * φ₁ t₁ = 1) {d : ℕ} {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d)
    (k : ℕ) (hx0 : x.1 k = 0) :
    ∃ m, ∀ n, (gT₀ C ^ (m + n) * x).1 k = 0 ∧ (gT₀ C ^ (m + n) * x).2 k = 0 := by
  have hψx : (C k).ψ₁ (x.2 k) = 0 := by
    have e := ((mem_gam C H x).1 hx k).2.2
    rw [hx0, map_zero] at e
    have hud : (C k).u ^ d * (C k).ψ₁ ((C k).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁)) ^ d = 1 := by
      rw [← mul_pow, lhv hts (C k), one_pow]
    linear_combination (-(C k).ψ₁ (x.2 k)) * hud -
      (C k).ψ₁ ((C k).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁)) ^ d * e
  obtain ⟨m, hm⟩ := (C k).aw₁.2 (x.2 k) hψx
  refine ⟨m, fun n => ⟨?_, ?_⟩⟩
  · rw [Prod.fst_mul, Pi.mul_apply, hx0, mul_zero]
  · rw [Prod.snd_mul, Pi.mul_apply, Prod.pow_snd, Pi.pow_apply]
    show (C k).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁) ^ (m + n) * x.2 k = 0
    rw [pow_add _ m n, mul_right_comm, hm, zero_mul]

/-- A family with vanishing second coordinate at level `k` vanishes at level `k` after a power of `T₁`. -/
theorem van₁ {d : ℕ} {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d)
    (k : ℕ) (hx0 : x.2 k = 0) :
    ∃ m, ∀ n, (gT₁ C ^ (m + n) * x).1 k = 0 ∧ (gT₁ C ^ (m + n) * x).2 k = 0 := by
  have hψx : (C k).ψ₀ (x.1 k) = 0 := by
    rw [((mem_gam C H x).1 hx k).2.2, hx0, map_zero, mul_zero]
  obtain ⟨m, hm⟩ := (C k).aw₀.2 (x.1 k) hψx
  refine ⟨m, fun n => ⟨?_, ?_⟩⟩
  · rw [Prod.fst_mul, Pi.mul_apply, Prod.pow_fst, Pi.pow_apply]
    show (C k).a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) t₀) ^ (m + n) * x.1 k = 0
    rw [pow_add _ m n, mul_right_comm, hm, zero_mul]
  · rw [Prod.snd_mul, Pi.mul_apply, hx0, mul_zero]

end Van

section Ker

end Ker

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_T3dC =====
section

/-!
# S4-EtPBC-A, R4-T3d (part C): compatibility of the base change maps, and the degree-one assembly

`π : Y ⟶ P`, `f : P' ⟶ P`, `Φ : U ⟶ P'`, `h : U ⟶ Y` with `h ≫ π = Φ ≫ f`, `ι' : Ps ⟶ P'`, `ι = ι' ≫ f`:
* `hsU : U_s ⟶ Y_s` and `rUs : π_{s*} M_{Y_s} ⟶ φs_* M_{U_s}` (restriction on the fibre);
* **`C1`**: `eC M π ι ≫ rUs = ι^*(restriction) ≫ eC M Φ ι'` (both base change maps are restriction of sections);
* `HypT`: the input that T1 + T2 supply (every extension of `Λ` by `π_{s*} M_{Y_s}` is split by such data);
* **`bcSurj_one_push_of_hypT`**: base change is surjective in degree one for `π_* M_Y`, given `HypT`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.T3d

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.FBC RamanujanPetersson.EtPBC.PushKill

universe u

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ}

section C1

variable {P P' Y U Ps : Scheme.{u}} (π : Y ⟶ P) (f : P' ⟶ P) (Φ : U ⟶ P') (h : U ⟶ Y)
  (hh : h ≫ π = Φ ≫ f) (ι' : Ps ⟶ P')

theorem C1s_key_pt (V : P.Etale)
    (w : ((etPull (pullback.snd Φ ι')).obj ((etPull ι').obj ((etPull f).obj V))).left) :
    muq (pullback.fst π (ι' ≫ f)) π (pullback.snd π (ι' ≫ f) ≫ (ι' ≫ f)) pullback.condition V
      (((etPullCompIso (pullback.snd π (ι' ≫ f)) (ι' ≫ f)).inv.app V).left
        (muq (hsU π f Φ h hh ι' (ι' ≫ f) rfl) (pullback.snd π (ι' ≫ f)) (pullback.snd Φ ι')
          (hsU_snd π f Φ h hh ι' (ι' ≫ f) rfl) ((etPull (ι' ≫ f)).obj V)
          (((etPull (pullback.snd Φ ι')).map ((etPullCompIso ι' f).inv.app V)).left w))) =
    muq h π (Φ ≫ f) hh V (((etPullCompIso Φ f).inv.app V).left
      (muq (pullback.fst Φ ι') Φ (pullback.snd Φ ι' ≫ ι') pullback.condition ((etPull f).obj V)
        (((etPullCompIso (pullback.snd Φ ι') ι').inv.app ((etPull f).obj V)).left w))) :=
  (comp_apply4 _ _ _ _ w).symm.trans
    ((congrArg (fun m : ((etPull (pullback.snd Φ ι')).obj ((etPull ι').obj ((etPull f).obj V))).left ⟶
      pullback V.hom π => m w) (C1s_key π f Φ h hh ι' V)).trans (comp_apply4 _ _ _ _ w))

end C1

section B3

end B3

end RamanujanPetersson.EtPBC.T3d

end

end

-- ===== S4.Def_RP_EtPBC_A_EAlg =====
section

/-!
# S4-EtPBC-A, M4(E), ALG: maps out of a finitely generated sheaf via relations between germs

Fix `e : ∐ Λ[W j] ↠ F` (`J` finite). The generators `gen W e j ∈ F(W j)` are the images of the tautological
sections `taut Λ (W j) ∈ Λ[W j](W j)`. For sections `f j ∈ H(W j)` and `x : P`, `rel W H f x` is the linear map
`(Σ j, fibre of W j at x̄) →₀ Λ → H_x̄`, `l ↦ Σ l(j, a) · germ_a (f j)`.

* `free_stalk_span`, `coprod_span`, **`free_range`**: the stalk of `∐ Λ[W j]` at `x̄` is spanned by the germs of the
  tautological sections (the range of `rel` for `tg W` is everything);
* **`exists_desc`**: if at every `x` the relations of the generators `gen W e` are relations of `f`, there is
  `φ : F ⟶ H` with `φ (gen W e j) = f j`;
* **`mono_stalk`**: if at `x` the relations of `φ (gen W e j)` are relations of `gen W e`, then `φ` is injective on
  the stalk at `x̄`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.GenAlg

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

variable {J : Type u} [Finite J] (W : J → P.Etale)

variable {W}

/-- **Factorization through the quotient.** -/
theorem exists_desc {F : EtSh Λ P} (e : (∐ fun j => freeSh Λ (W j)) ⟶ F) (he : Epi e) (H : EtSh Λ P)
    (f : ∀ j, H.obj.obj (op (W j)))
    (h : ∀ x : P, LinearMap.ker (rel W F (gen e) x) ≤ LinearMap.ker (rel W H f x)) :
    ∃ φ : F ⟶ H, ∀ j, (φ.hom.app (op (W j))).hom (gen e j) = f j := by
  let φ' : (∐ fun j => freeSh Λ (W j)) ⟶ H := Sigma.desc fun j => (freeEquiv Λ (W j) H).symm (f j)
  have hφ' : ∀ j, (φ'.hom.app (op (W j))).hom (tg W j) = f j := by
    intro j
    rw [← gen_eq φ' j, gen, Sigma.ι_desc, AddEquiv.apply_symm_apply]
  have hφ'' : (fun j => (φ'.hom.app (op (W j))).hom (tg W j)) = f := funext hφ'
  have hk : kernel.ι e ≫ φ' = 0 := by
    refine hom_ext_stalk Λ fun x => ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun v => ?_)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero]
    change (((geomPtAt x).stalkF Λ).map φ').hom ((((geomPtAt x).stalkF Λ).map (kernel.ι e)).hom v) = 0
    obtain ⟨l, hl⟩ : (((geomPtAt x).stalkF Λ).map (kernel.ι e)).hom v ∈ LinearMap.range (rel W _ (tg W) x) := by
      rw [free_range]; trivial
    have hrelF : rel W F (gen e) x l = 0 := by
      rw [← rel_gen e x l, hl]
      change (((geomPtAt x).stalkF Λ).map (kernel.ι e) ≫ ((geomPtAt x).stalkF Λ).map e).hom v = 0
      rw [← CategoryTheory.Functor.map_comp, kernel.condition, CategoryTheory.Functor.map_zero]
      rfl
    have h2 := h x hrelF
    rw [LinearMap.mem_ker] at h2
    rw [← hl, rel_map, hφ'']
    exact h2
  refine ⟨Abelian.epiDesc e φ' hk, fun j => ?_⟩
  rw [gen_eq]
  change ((e ≫ Abelian.epiDesc e φ' hk).hom.app (op (W j))).hom (tg W j) = f j
  rw [Abelian.comp_epiDesc]
  exact hφ' j

/-- **Injectivity on a stalk.** -/
theorem mono_stalk {F H : EtSh Λ P} (e : (∐ fun j => freeSh Λ (W j)) ⟶ F) (he : Epi e) (φ : F ⟶ H) (x : P)
    (h : LinearMap.ker (rel W H (fun j => (φ.hom.app (op (W j))).hom (gen e j)) x) ≤
      LinearMap.ker (rel W F (gen e) x)) :
    Mono (((geomPtAt x).stalkF Λ).map φ) := by
  have hs : Function.Surjective (((geomPtAt x).stalkF Λ).map e).hom :=
    (ModuleCat.epi_iff_surjective _).1 ((epi_iff_stalk Λ e).1 he x)
  refine (ModuleCat.mono_iff_ker_eq_bot _).2 ((LinearMap.ker_eq_bot').2 fun w hw => ?_)
  obtain ⟨u, rfl⟩ := hs w
  obtain ⟨l, rfl⟩ : u ∈ LinearMap.range (rel W _ (tg W) x) := by
    rw [free_range]; trivial
  rw [rel_gen] at hw ⊢
  rw [rel_map] at hw
  exact h hw

end RamanujanPetersson.EtPBC.GenAlg

end

end

-- ===== S4.Def_RP_EtPBC_A_H1FG =====
section

/-!
# S4-EtPBC-A, R2(c-e): degree-1 base change reduces to finitely generated subsheaves

* `ofSec_sc`: `ofSec (c(1)) = c` for `c : Λ_Y ⟶ F`;
* `presHom c`: the map of injective presentations `injPres A ⟶ injPres B` over `c : A ⟶ B`;
* **`exists_kill`**: for `X` compact with affine maps from affines, every `β ∈ Ext¹(Λ_X, ι^* G)` is killed by
  `ι^* (coker φ)` for some `φ : ∐ Λ[W x] ⟶ G` from finitely many affines (local lift of the class on one affine
  etale surjection `V ⟶ X`, its Cech coboundary on `V ×_X V`, `exists_fg_sec`, gluing in the presentation of
  `ι^* (coker φ)`);
* **`bcSurj_one_of_fgt`**: `BCSurj 1` for every sheaf on `P` from `BCSurj 1` for `FGT` sheaves.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.Supp RamanujanPetersson.EtCompact.PtSec

universe u

section Kill

variable {Λ : Type u} [CommRing Λ] {X P : Scheme.{u}} (ι : X ⟶ P)

/-- **A degree-1 class is killed by the quotient by finitely many sections.** -/
theorem exists_kill [CompactSpace X] (hA : ∀ {Z : Scheme.{u}} (h : Z ⟶ X), IsAffine Z → IsAffineHom h)
    (G : EtSh Λ P) (β : Ext.{u} (unitSh Λ X) ((pull ι Λ).obj G) 1) :
    ∃ (t : Type u) (_ : Finite t) (W : t → P.Etale) (_ : ∀ x, IsAffine (W x).left)
      (φ : (∐ fun x => freeSh Λ (W x)) ⟶ G), β.comp (Ext.mk₀ ((pull ι Λ).map (cokernel.π φ))) (add_zero 1) = 0 := by
  have hP := injPres_shortExact ((pull ι Λ).obj G)
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ (unitSh Λ X) hP β (Ext.eq_zero_of_injective _) (zero_add 1)
  obtain ⟨σ, rfl⟩ := (Ext.mk₀_bijective _ _).2 x₃
  obtain ⟨V, fV, hV, hfV, p', hp'⟩ := exists_cover_lift hP (sc σ (etId X))
  let S := injPres ((pull ι Λ).obj G)
  let p0 : S.X₂.obj.obj (op (nv fV 0)) := (S.X₂.obj.map (pi0 fV).op).hom p'
  have hgp0 : (S.g.hom.app (op (nv fV 0))).hom p0 = (S.X₃.obj.map (base0 fV).op).hom (sc σ (etId X)) := by
    calc _ = (S.X₃.obj.map (pi0 fV).op).hom ((S.g.hom.app (op V)).hom p') := by
          rw [← ModuleCat.comp_apply, NatTrans.naturality, ModuleCat.comp_apply]
      _ = _ := by
          rw [hp', ← ModuleCat.comp_apply, ← Functor.map_comp, ← op_comp, pi0_arrow]
  have hd3 : (cd S.X₃ fV 0 1).hom ((S.X₃.obj.map (base0 fV).op).hom (sc σ (etId X))) = 0 := by
    rw [cech_d0_apply, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp,
      ← op_comp, ← op_comp, δ_base0, δ_base0, sub_self]
  have hc : (S.g.hom.app (op (nv fV 1))).hom ((cd S.X₂ fV 0 1).hom p0) = 0 := by
    rw [← cech_d_nat S.g fV 0 1 p0, hgp0, hd3]
  obtain ⟨a, ha⟩ := sec_exact hP (nv fV 1) _ hc
  have : IsAffineHom fV.left := hA fV.left hV
  have : IsAffine (nv fV 1).left := isAffine_nv1 fV
  obtain ⟨tt, W, z, hW, hz⟩ := exists_fg_sec ι G (nv fV 1) a
  let φ : (∐ fun x : tt => freeSh Λ (W x.1)) ⟶ G := Sigma.desc fun x => (freeEquiv Λ (W x.1) G).symm (z x.1)
  have hpa : (((pull ι Λ).map (cokernel.π φ)).hom.app (op (nv fV 1))).hom a = 0 := hz (cokernel.π φ) fun x hx => by
    have e0 : (freeEquiv Λ (W x) G).symm (z x) ≫ cokernel.π φ = 0 :=
      (congrArg (· ≫ cokernel.π φ)
        (Sigma.ι_desc (fun x : tt => (freeEquiv Λ (W x.1) G).symm (z x.1)) ⟨x, hx⟩).symm).trans
        ((Category.assoc _ _ _).trans ((congrArg (Sigma.ι (fun x : tt => freeSh Λ (W x.1)) ⟨x, hx⟩ ≫ ·)
          (cokernel.condition φ)).trans comp_zero))
    have e := freeEquiv_comp Λ (W x) ((freeEquiv Λ (W x) G).symm (z x)) (cokernel.π φ)
    rw [e0, map_zero, AddEquiv.apply_symm_apply] at e
    exact e.symm
  refine ⟨tt, inferInstance, fun x => W x.1, fun x => hW x.1, φ, ?_⟩
  have hP'' := injPres_shortExact ((pull ι Λ).obj (cokernel φ))
  let S'' := injPres ((pull ι Λ).obj (cokernel φ))
  let μ : S ⟶ S'' := presHom ((pull ι Λ).map (cokernel.π φ))
  have hnat := hP.extClass_naturality hP'' (presHom ((pull ι Λ).map (cokernel.π φ)))
  rw [presHom_τ₁] at hnat
  have e12 : (μ.τ₂.hom.app (op (nv fV 1))).hom ((S.f.hom.app (op (nv fV 1))).hom a) =
      (S''.f.hom.app (op (nv fV 1))).hom ((μ.τ₁.hom.app (op (nv fV 1))).hom a) :=
    (congrArg (fun φ => (φ.hom.app (op (nv fV 1))).hom a) μ.comm₁₂).symm
  have hx : (cd S''.X₂ fV 0 1).hom ((μ.τ₂.hom.app (op (nv fV 0))).hom p0) = 0 := by
    rw [cech_d_nat μ.τ₂ fV 0 1 p0, ← ha, e12]
    exact (congrArg (S''.f.hom.app (op (nv fV 1))).hom hpa).trans (map_zero _)
  obtain ⟨yy, hyy⟩ := descend fV S''.X₂ hfV _ hx
  have e23 : (S''.g.hom.app (op (nv fV 0))).hom ((μ.τ₂.hom.app (op (nv fV 0))).hom p0) =
      (μ.τ₃.hom.app (op (nv fV 0))).hom ((S.g.hom.app (op (nv fV 0))).hom p0) :=
    congrArg (fun φ => (φ.hom.app (op (nv fV 0))).hom p0) μ.comm₂₃
  have hπ : (S''.g.hom.app (op (etId X))).hom yy = (μ.τ₃.hom.app (op (etId X))).hom (sc σ (etId X)) :=
    sep_of_cover S''.X₃ (fun _ : Unit => base0 fV) (cover_of_surjective _ (base0_surj fV hfV)) _ _ fun _ =>
      (app_map S''.g (base0 fV) yy).symm.trans ((congrArg _ hyy).trans (e23.trans
        ((congrArg _ hgp0).trans (app_map μ.τ₃ (base0 fV) _))))
  have hy : ofSec yy ≫ S''.g = σ ≫ μ.τ₃ := by
    rw [ofSec_comp, hπ, ← ofSec_comp, ofSec_sc]
  rw [← hx₃]
  calc ((Ext.mk₀ σ).comp (hP.extClass : Ext.{u} _ _ 1) (zero_add 1)).comp
        (Ext.mk₀ ((pull ι Λ).map (cokernel.π φ))) (add_zero 1)
      = (Ext.mk₀ σ).comp ((hP.extClass : Ext.{u} _ _ 1).comp
          (Ext.mk₀ ((pull ι Λ).map (cokernel.π φ))) (add_zero 1)) (zero_add 1) :=
        Ext.comp_assoc_of_third_deg_zero _ _ _ _
    _ = (Ext.mk₀ σ).comp ((Ext.mk₀ μ.τ₃).comp (hP''.extClass : Ext.{u} _ _ 1) (zero_add 1)) (zero_add 1) :=
        congrArg (fun e => (Ext.mk₀ σ).comp e (zero_add 1)) hnat
    _ = (Ext.mk₀ (σ ≫ μ.τ₃)).comp (hP''.extClass : Ext.{u} _ _ 1) (zero_add 1) := Ext.mk₀_comp_mk₀_assoc _ _ _
    _ = (Ext.mk₀ (ofSec yy)).comp ((Ext.mk₀ S''.g).comp (hP''.extClass : Ext.{u} _ _ 1) (zero_add 1))
          (zero_add 1) := by
        rw [← hy, Ext.mk₀_comp_mk₀_assoc]
    _ = 0 := by
        rw [hP''.comp_extClass, Ext.comp_zero]

end Kill

section Red

end Red

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_NagC =====
section

/-!
# S4-EtPBC-A, M4(N3): the relative normalization of a finite field point is finite

* `finite_integralClosure_of_gen`: `A` of finite type over a perfect field `K`, `F` a field generated (as a field)
  by the image of `A`, `L` finite over `F` ⇒ the integral closure of `A` in `L` is a finite `A`-module (via `NagB`
  for the domain `A ⧸ ker`);
* **`isFinite_fromNormalization`**: `X` locally of finite type over a perfect field, `y : X`, `φ : κ(y) ⟶ κ(ξ)` a
  finite extension ⇒ the relative normalization of `Spec κ(ξ) ⟶ Spec κ(y) ⟶ X` is finite over `X`.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace RamanujanPetersson.EtPBC.Nagata

universe u

end RamanujanPetersson.EtPBC.Nagata

namespace RamanujanPetersson.EtPBC.Nagata

universe v

variable {X : Scheme.{v}} (y : X) {T : Scheme.{v}} (ξ : T) (φ : X.residueField y ⟶ T.residueField ξ)

/-- **N3: the relative normalization of `Spec κ(ξ) ⟶ Spec κ(y) ⟶ X` is finite** (`X` locally of finite type over a
perfect field, `κ(ξ)` finite over `κ(y)`). -/
theorem isFinite_fromNormalization (K : Type v) [Field K] (p : ℕ) [ExpChar K p] [PerfectRing K p]
    (h : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType h] (hφ : φ.hom.Finite) :
    IsFinite (Spec.map φ ≫ X.fromSpecResidueField y).fromNormalization := by
  set f := Spec.map φ ≫ X.fromSpecResidueField y with hfdef
  refine (isFinite_iff _).2 ⟨inferInstance, fun U hU => ?_⟩
  rw [f.fromNormalization_app hU, CommRingCat.hom_comp]
  refine RingHom.Finite.comp ?_ ?_
  · exact RingHom.Finite.of_surjective _ (f.normalizationObjIso hU).commRingCatIsoToRingEquiv.symm.surjective
  let := (f.app U).hom.toAlgebra
  rw [CommRingCat.hom_ofHom, RingHom.finite_algebraMap]
  by_cases hy : y ∈ U
  swap
  · haveI := subsingleton_sec y ξ φ hy
    have : Subsingleton (integralClosure Γ(X, U) Γ(Spec (T.residueField ξ), f ⁻¹ᵁ U)) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    infer_instance
  -- the K-algebra structure
  let : Algebra K Γ(X, U) := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ h.appLE ⊤ U le_top).hom.toAlgebra
  have : Algebra.FiniteType K Γ(X, U) := by
    have h1 := HasRingHomProperty.appLE @LocallyOfFiniteType h ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.FiniteType := RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.surjective
    exact h1.comp h2
  let : Algebra Γ(X, U) (X.residueField y) := (X.presheaf.germ U y hy ≫ X.residue y).hom.toAlgebra
  let : Algebra (X.residueField y) (T.residueField ξ) := φ.hom.toAlgebra
  let : Algebra Γ(X, U) (T.residueField ξ) := (X.presheaf.germ U y hy ≫ X.residue y ≫ φ).hom.toAlgebra
  have : IsScalarTower Γ(X, U) (X.residueField y) (T.residueField ξ) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional (X.residueField y) (T.residueField ξ) := hφ
  have hfin : Module.Finite Γ(X, U) (integralClosure Γ(X, U) (T.residueField ξ)) :=
    finite_integralClosure_of_gen K Γ(X, U) (X.residueField y) (T.residueField ξ) (residue_gen hU y hy) p
  -- identify the sections over `f ⁻¹ U = ⊤` with `κ(ξ)`
  have hle := top_le_preimage y ξ φ hy
  have heqU : (⊤ : (Spec (T.residueField ξ)).Opens) = f ⁻¹ᵁ U := le_antisymm hle le_top
  let rI : Γ(Spec (T.residueField ξ), f ⁻¹ᵁ U) ≅ T.residueField ξ :=
    (Spec (T.residueField ξ)).presheaf.mapIso (eqToIso heqU).op ≪≫ Scheme.ΓSpecIso _
  have hr : f.app U ≫ rI.hom = X.presheaf.germ U y hy ≫ X.residue y ≫ φ := by
    have e1 : f.app U ≫ (Spec (T.residueField ξ)).presheaf.map (eqToHom heqU).op = f.appLE U ⊤ hle := rfl
    simp only [rI, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]
    rw [← Category.assoc, e1, appLE_eq y ξ φ hy hle]
    simp
  let eA : Γ(Spec (T.residueField ξ), f ⁻¹ᵁ U) ≃ₐ[Γ(X, U)] T.residueField ξ :=
    { rI.commRingCatIsoToRingEquiv with
      commutes' := fun a => congrArg (fun g => g.hom a) hr }
  have hmap := integralClosure_map_algEquiv eA
  have : Module.Finite Γ(X, U) ((integralClosure Γ(X, U) Γ(Spec (T.residueField ξ), f ⁻¹ᵁ U)).map
      (eA : Γ(Spec (T.residueField ξ), f ⁻¹ᵁ U) →ₐ[Γ(X, U)] T.residueField ξ)) := by
    rw [hmap]; exact hfin
  exact Module.Finite.equiv (eA.subalgebraMap _).symm.toLinearEquiv

end RamanujanPetersson.EtPBC.Nagata

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L1 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), L1: base change of Mayer-Vietoris classes

* `mvMapHom`, **`mv_naturality`**: a morphism of MV data gives a morphism of MV complexes, so
  `ε₁ ∘ Λ[a'] = Λ[c] ∘ ε₂` in `Ext¹`.
* `mvPullHom`: `mvC(f⁻¹ data) ⟶ f^* mvC(data)` (an isomorphism), `mvPull_shortExact`;
  **`mapExact_mv`**: `f^*` of `ε.comp κ` is `ε(f⁻¹ data).comp (f^* κ)`.
* `freeToUnit_bcUnit`, **`bc_mv`**: the base change of `ε.comp κ` at a neighbourhood `j` of `s` is
  `σ_j^*(ε(ι⁻¹ data).comp (ι^* κ))`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk

universe u

section Nat

end Nat

section Pull

variable {Λ : Type u} [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

variable {W' W U Z : Y.Etale} (p₁ : W' ⟶ W) (p₂ : W' ⟶ U) (w : W ⟶ Z) (v : U ⟶ Z) (hsq : p₁ ≫ w = p₂ ≫ v)

variable {p₁ p₂ w v hsq}

/-- **`f^*` of an MV class**: `Λ[f⁻¹Z] → f^*Λ[Z]` followed by `f^*(ε ∘ κ)` is `ε(f⁻¹ data) ∘ f^*κ`. -/
theorem mapExact_mv (hS : (mvC Λ p₁ p₂ w v hsq).ShortExact)
    (hS' : (mvC Λ ((etPull f).map p₁) ((etPull f).map p₂) ((etPull f).map w) ((etPull f).map v)
      (pull_sq f p₁ p₂ w v hsq)).ShortExact) (F : EtSh Λ Y) {n m : ℕ} (κ : Ext (freeSh Λ W') F n)
    (h : 1 + n = m) :
    (Ext.mk₀ (pullFreeHom Λ f Z)).comp ((hS.extClass.comp κ h).mapExactFunctor (pull f Λ)) (zero_add m) =
      hS'.extClass.comp ((Ext.mk₀ (pullFreeHom Λ f W')).comp (κ.mapExactFunctor (pull f Λ)) (zero_add n)) h := by
  have hnat : hS'.extClass.comp (Ext.mk₀ (pullFreeHom Λ f W')) (add_zero 1) =
      (Ext.mk₀ (pullFreeHom Λ f Z)).comp (hS.map_of_exact (pull f Λ)).extClass (zero_add 1) :=
    hS'.extClass_naturality (hS.map_of_exact (pull f Λ)) (mvPullHom Λ f p₁ p₂ w v hsq)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass, ← Ext.comp_assoc_of_second_deg_zero, hnat]
  exact (Ext.comp_assoc _ _ _ (zero_add 1) h (by omega)).symm

end Pull

section BC

end BC

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2R3 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M6a (3): the multi-point MV complex maps to each one-point complex

For `k : ι`, an open `Uz ⊇ U₀` containing every point of every `S j` (`j ≠ k`):
* `copDescF` (maps out of `Λ[cop S]` from maps on the summands), `copι_copDescF`;
* `restSec`, `locτ₂`: the middle map `Λ[cop S] ⊞ Λ[U₀] ⟶ Λ[S k] ⊞ Λ[Uz]`;
* `loc_comm₁₂`, `loc_comm₂₃`, **`mvLocHom`**: a morphism of short complexes `mvCop ⟶ locC (S k)` with
  `τ₁ = copPr k` and `τ₃ = 𝟙`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} {ι : Type u} [Fintype ι] [DecidableEq ι]
  (S : ι → P.Etale)

variable (U₀ : P.Opens) (k : ι) {Uz : P.Opens} (h : U₀ ≤ Uz)
  (hrng : ∀ j, j ≠ k → ∀ v : (S j).left, (S j).hom v ∈ Uz)

theorem loc_comm₁₂_snd :
    copPr Λ (fun j => prd (S j) (opEt U₀)) k ≫ (-freeMap Λ (prT (S k) (opEt U₀) ≫ opEtMap h)) =
      freeMap Λ (copP₁ S U₀) ≫ copDescF Λ S (restSec Λ S k hrng) +
        (-freeMap Λ (copP₂ S U₀)) ≫ freeMap Λ (opEtMap h) := by
  refine freeCop_hom_ext _ (fun j => ?_)
  have hP₁ : ∀ {G : EtSh Λ P} (q : freeSh Λ (cop S) ⟶ G),
      freeMap Λ (copι (fun j => prd (S j) (opEt U₀)) j) ≫ freeMap Λ (copP₁ S U₀) ≫ q =
        freeMap Λ (prW (S j) (opEt U₀)) ≫ freeMap Λ (copι S j) ≫ q := by
    intro G q
    rw [← Category.assoc, ← Category.assoc, ← freeMap_comp, ← freeMap_comp, copι_copP₁]
  have hP₂ : ∀ {G : EtSh Λ P} (q : freeSh Λ (opEt U₀) ⟶ G),
      freeMap Λ (copι (fun j => prd (S j) (opEt U₀)) j) ≫ freeMap Λ (copP₂ S U₀) ≫ q =
        freeMap Λ (prT (S j) (opEt U₀)) ≫ q := by
    intro G q
    rw [← Category.assoc, ← freeMap_comp, copι_copP₂]
  rw [← Category.assoc, copι_copPr]
  simp only [Preadditive.comp_add, Preadditive.comp_neg, Preadditive.neg_comp]
  rw [hP₁, copι_copDescF, hP₂]
  by_cases hj : j = k
  · subst hj
    rw [copPrSec_self, restSec_self, Category.id_comp, Limits.comp_zero, zero_add, freeMap_comp]
  · rw [copPrSec_ne _ hj, restSec_ne S k hrng hj, Limits.zero_comp, neg_zero, ← freeMap_comp, ← freeMap_comp,
      opEt_ext (prW (S j) (opEt U₀) ≫ toOpEt (S j) Uz (hrng j hj)) (prT (S j) (opEt U₀) ≫ opEtMap h),
      add_neg_cancel]

theorem loc_comm₁₂ :
    copPr Λ (fun j => prd (S j) (opEt U₀)) k ≫
        biprod.lift (freeMap Λ (prW (S k) (opEt U₀))) (-freeMap Λ (prT (S k) (opEt U₀) ≫ opEtMap h)) =
      biprod.lift (freeMap Λ (copP₁ S U₀)) (-freeMap Λ (copP₂ S U₀)) ≫ locτ₂ Λ S U₀ k h hrng := by
  rw [locτ₂_eq]
  apply biprod.hom_ext
  · simp only [Category.assoc, Preadditive.add_comp, biprod.lift_fst, biprod.lift_desc,
      Limits.comp_zero, add_zero]
    exact loc_comm₁₂_fst (Λ := Λ) S U₀ k
  · simp only [Category.assoc, Preadditive.add_comp, biprod.lift_snd, biprod.lift_desc]
    exact loc_comm₁₂_snd (Λ := Λ) S U₀ k h hrng

variable (Λ) in
/-- **The morphism of short complexes** `mvCop ⟶ locC (S k)` (`τ₁ = copPr k`, `τ₃ = 𝟙`). -/
def mvLocHom : mvCop Λ S U₀ ⟶ locC Λ (S k) h where
  τ₁ := copPr Λ (fun j => prd (S j) (opEt U₀)) k
  τ₂ := locτ₂ Λ S U₀ k h hrng
  τ₃ := 𝟙 _
  comm₁₂ := loc_comm₁₂ S U₀ k h hrng
  comm₂₃ := loc_comm₂₃ S U₀ k h hrng

theorem mvLocHom_τ₁ : (mvLocHom Λ S U₀ k h hrng).τ₁ = copPr Λ (fun j => prd (S j) (opEt U₀)) k := rfl

theorem mvLocHom_τ₃ : (mvLocHom Λ S U₀ k h hrng).τ₃ = 𝟙 _ := rfl

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2R4 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M6a (4): the relation between one-point classes

* `ext_comp_sum`, `ext_sum_comp`, `ext_mk₀_sum` (finite sums and `Ext`);
* `locLe`, `locRng`; `extClass_loc_eq`: the one-point class at `z k` is the multi-point MV class followed by
  `copPr k` (naturality along `mvLocHom`);
* **`relation_sum`**: `Σ_k ε_loc(S k) ∘ (Λ[S k ×_P U₀ ⟶ U₀]^* κ) = 0` for every `κ ∈ Ext¹(Λ[U₀], F)`;
* `isLoc_relation_term`: each summand is a one-point class (`IsLoc`) at `z k`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

universe w u

section ExtSum

end ExtSum

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} {ι : Type u} [Fintype ι] [DecidableEq ι]
  (S : ι → P.Etale) (U₀ : P.Opens)
  (z : ι → P) (hzi : Function.Injective z) (hU : ∀ x : P, x ∈ U₀ ↔ ∀ k, x ≠ z k)
  (hD : ∀ k, Subsingleton ((geomPtAt (z k)).point.fiber.obj (S k)))
  (hDn : ∀ k, Nonempty ((geomPtAt (z k)).point.fiber.obj (S k)))
  (hDr : ∀ k (v : (S k).left), (S k).hom v ∈ U₀ ∨ (S k).hom v = z k)
  (Uz : ι → P.Opens) (hz : ∀ k (x : P), x ∈ Uz k ↔ x ≠ z k)

theorem sum_copPr_prT :
    ∑ k, copPr Λ (fun j => prd (S j) (opEt U₀)) k ≫ freeMap Λ (prT (S k) (opEt U₀)) =
      freeMap Λ (copP₂ S U₀) := by
  calc ∑ k, copPr Λ (fun j => prd (S j) (opEt U₀)) k ≫ freeMap Λ (prT (S k) (opEt U₀))
      = ∑ k, copPr Λ (fun j => prd (S j) (opEt U₀)) k ≫
          freeMap Λ (copι (fun j => prd (S j) (opEt U₀)) k) ≫ freeMap Λ (copP₂ S U₀) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [← freeMap_comp, copι_copP₂]
    _ = (∑ k, copPr Λ (fun j => prd (S j) (opEt U₀)) k ≫ freeMap Λ (copι (fun j => prd (S j) (opEt U₀)) k)) ≫
          freeMap Λ (copP₂ S U₀) := by
        rw [Preadditive.sum_comp]
        simp only [Category.assoc]
    _ = freeMap Λ (copP₂ S U₀) := by rw [sum_copPr, Category.id_comp]

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Sh2 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree

* `dg W`: the diagonal of `W ×_P W` (clopen: `isClopen_dg`); `dsec Λ W`: its indicator section of `Λ_W`;
* `shapφ Λ W : Λ[W] ⟶ π_* Λ_W` is the map given by `dsec` (`shapφ_taut`);
* `cval_S`: values of `Σ_a l_a · τ_a^* dsec` along a sheet;
* **`isIso_shapφ`**, **`shapIso`**: `shapφ` is an isomorphism (stalkwise: `stalk_inj`, `stalk_surj`).
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

section Dg

end Dg

section Iso

variable (Λ : Type u) [CommRing Λ] (W : P.Etale) [IsSeparated W.hom]

variable [QuasiCompact W.hom]

/-- **`shapφ` is surjective on stalks** (`W` of constant degree). -/
theorem stalk_surj (n : ℕ) (hn : ∀ y : P, Nat.card ((geomPtAt y).point.fiber.obj W) = n) (x : P) :
    Function.Surjective (((geomPtAt x).stalkF Λ).map (shapφ Λ W)).hom := by
  classical
  have : Finite ((geomPtAt x).point.fiber.obj W) := finite_fiber W x
  have := Fintype.ofFinite ((geomPtAt x).point.fiber.obj W)
  intro y
  obtain ⟨Z, z, s, rfl⟩ := (geomPtAt x).point.toPresheafFiber_jointly_surjective
    (P := ((push W.hom Λ).obj (unitSh Λ W.left)).obj) y
  obtain ⟨T, t, τ, -, hτ, hinj⟩ := exists_split_inj ⊤ W x (by simp)
  obtain ⟨M₀, m₀, d₀, e₀, hd₀, he₀⟩ := exists_common x z t
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : (unitSh Λ W.left).obj.obj (op ((etPull W.hom).obj M₀)),
      s₀ = ((unitSh Λ W.left).obj.map ((etPull W.hom).map d₀).op).hom s := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : (geomPtAt x).point.fiber.obj W → Λ, ∀ q,
      c q = cval (((unitSh Λ W.left).obj.map (shι (e₀ ≫ τ q)).op).hom s₀) (fpt x m₀ : M₀.left) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : (unitSh Λ W.left).obj.obj (op ((etPull W.hom).obj M₀)),
      D = s₀ - ((unitSh Λ W.left).obj.map ((etPull W.hom).map e₀).op).hom
        (∑ a, c a • ((unitSh Λ W.left).obj.map ((etPull W.hom).map (τ a)).op).hom (dsec Λ W)) := ⟨_, rfl⟩
  obtain ⟨O, hO⟩ : ∃ O : Set M₀.left, O = ⋂ q, {v : M₀.left |
      cval (((unitSh Λ W.left).obj.map (shι (e₀ ≫ τ q)).op).hom D) v = 0} := ⟨_, rfl⟩
  have hOo : IsOpen O := by
    rw [hO]
    exact isOpen_iInter_of_finite fun q =>
      (isLocallyConstant_cval (((unitSh Λ W.left).obj.map (shι (e₀ ≫ τ q)).op).hom D)).isOpen_fiber 0
  have hv₀ : fpt x m₀ ∈ O := by
    rw [hO]
    refine Set.mem_iInter.2 fun q => ?_
    show cval (((unitSh Λ W.left).obj.map (shι (e₀ ≫ τ q)).op).hom D) (fpt x m₀) = 0
    rw [hD, map_sub]
    exact (cval_sub _ _ _).trans ((congrArg₂ (· - ·) (hc q).symm
      (cval_S Λ W τ c e₀ (e₀ ≫ τ q) (fpt x m₀) q fun a => agr_iff W x τ t hτ e₀ m₀ he₀ a q)).trans (sub_self _))
  obtain ⟨V, hV⟩ : ∃ V : M₀.left.Opens, (V : Set M₀.left) = O := ⟨⟨O, hOo⟩, rfl⟩
  have hv₀V : fpt x m₀ ∈ V := by
    rw [← SetLike.mem_coe, hV]
    exact hv₀
  obtain ⟨m, hm, -⟩ := exists_lift_fib (opnι M₀ V) x m₀ (⟨fpt x m₀, hv₀V⟩ : V)
    (Scheme.Opens.ι_apply V ⟨fpt x m₀, hv₀V⟩)
  have hD0 : ((unitSh Λ W.left).obj.map ((etPull W.hom).map (opnι M₀ V)).op).hom D = 0 := by
    refine T3d.sec_ext_cval _ _ fun u => ?_
    rw [cval_zero]
    obtain ⟨q, v, rfl⟩ := sheet_pt (fun p => opnι M₀ V ≫ e₀ ≫ τ p) (bij_of n hn x τ hinj (opnι M₀ V) e₀) u
    refine (cval_map ((etPull W.hom).map (opnι M₀ V)) D _).trans ?_
    refine (congrArg (cval D) (pt_eq2 W (opnι M₀ V) (e₀ ≫ τ q) v)).trans ?_
    refine (cval_map (shι (e₀ ≫ τ q)) D ((opnι M₀ V).left v)).symm.trans ?_
    have hvO : (opnι M₀ V).left v ∈ O := by
      rw [← hV]
      exact (Scheme.Opens.range_ι V).subset (Set.mem_range_self v)
    rw [hO] at hvO
    exact Set.mem_iInter.1 hvO q
  have hgD : germ ((push W.hom Λ).obj (unitSh Λ W.left)) x m₀ D = 0 := by
    have h1 := GenAlg.germ_map ((push W.hom Λ).obj (unitSh Λ W.left)) x (opnι M₀ V) m D
    rw [hm] at h1
    rw [← h1]
    exact (congrArg (germ ((push W.hom Λ).obj (unitSh Λ W.left)) x m) hD0).trans
      (map_zero ((geomPtAt x).point.toPresheafFiber _ m ((push W.hom Λ).obj (unitSh Λ W.left)).obj).hom)
  have hgs : germ ((push W.hom Λ).obj (unitSh Λ W.left)) x z s =
      germ ((push W.hom Λ).obj (unitSh Λ W.left)) x m₀ s₀ := by
    rw [hs₀, ← hd₀]
    exact (GenAlg.germ_map ((push W.hom Λ).obj (unitSh Λ W.left)) x d₀ m₀ s).symm
  have hgR : germ ((push W.hom Λ).obj (unitSh Λ W.left)) x m₀
      (((unitSh Λ W.left).obj.map ((etPull W.hom).map e₀).op).hom
        (∑ a, c a • ((unitSh Λ W.left).obj.map ((etPull W.hom).map (τ a)).op).hom (dsec Λ W))) =
      germ ((push W.hom Λ).obj (unitSh Λ W.left)) x t
        ((∑ a, c a • ((unitSh Λ W.left).obj.map ((etPull W.hom).map (τ a)).op).hom (dsec Λ W) :
          (unitSh Λ W.left).obj.obj (op ((etPull W.hom).obj T)))) := by
    rw [← he₀]
    exact GenAlg.germ_map ((push W.hom Λ).obj (unitSh Λ W.left)) x e₀ m₀ _
  have hadd : germ ((push W.hom Λ).obj (unitSh Λ W.left)) x m₀ s₀ =
      germ ((push W.hom Λ).obj (unitSh Λ W.left)) x m₀ D +
        germ ((push W.hom Λ).obj (unitSh Λ W.left)) x m₀
          (((unitSh Λ W.left).obj.map ((etPull W.hom).map e₀).op).hom
            (∑ a, c a • ((unitSh Λ W.left).obj.map ((etPull W.hom).map (τ a)).op).hom (dsec Λ W))) := by
    rw [sub_eq_iff_eq_add.1 hD.symm]
    exact map_add ((geomPtAt x).point.toPresheafFiber M₀ m₀ ((push W.hom Λ).obj (unitSh Λ W.left)).obj).hom _ _
  refine ⟨freeLin Λ W x (Finsupp.equivFunOnFinite.symm c), Eq.trans ?_ hgs.symm⟩
  rw [hadd, hgD, zero_add, hgR, stalk_shapφ_freeLin, Finsupp.coe_equivFunOnFinite_symm, germ_S Λ W x τ t hτ c]

end Iso

end RamanujanPetersson.EtPBC.EtShap

end

end

-- ===== S4.Def_RP_EtPBC_A_O2E7 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4d2: purity on `W₁ = Spec B_t` with the chart Kummer class

* `LA k a = k[X]_{X-a}` (Dedekind, fraction field `RatFunc k`); `zetaA`, `gamA` (`gamA ^ N = X - a`);
* `xiA a hN Λ hΛ c : H¹(Spec k[X]_{X-a}, Λ)`: the Kummer class of `(X - a)^{1/N}` with coefficient `c`;
* `Wa c a = Spec k[X]_{X-a}` over `P` (the punctured chart neighbourhood), `phiA`, `toWa c a φ : W1 c φ a ⟶ Wa c a`;
* **`purity_W1`**: every `κ ∈ H¹(Spec B_t, Λ)` is `res_{toD1} κ₀ + res_{toWa} (xiA c')`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.Kummer
  RamanujanPetersson.EtPi1 RamanujanPetersson.EtCompact.Pur RamanujanPetersson.EtPBC.EtDed

section LA

variable (k : Type) [Field k] (a : k)

variable {k} [IsAlgClosed k] {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0)

variable (Λ : Type) [CommRing Λ] (hΛ : ∀ x : Λ, N • x = 0)

/-- **The chart Kummer class** `ξ_a(c) ∈ H¹(Spec k[X]_{X-a}, Λ)` of `(X - a)^{1/N}`. -/
def xiA (c : Λ) : H Λ (unitSh Λ (Spec (CommRingCat.of (LA k a)))) 1 :=
  kappaL (LA k a) (RatFunc k) Λ
    (kumChi_mul (zetaE_prim (LA k a) (zetaA_prim hN)) (zetaE_fix (LA k a) (zetaA hN))
      (mem_rad_of_pow_eq (gamA_pow a hN)) (hΛ c))
    (kumChi_isLocallyConstant (zetaE_prim (LA k a) (zetaA_prim hN)) (gamA a hN) c)

end LA

section Obj

end Obj

section Pur

end Pur

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

variable {A K A' K' : Type} [CommRing A] [Field K] [Algebra A K] [CommRing A'] [Field K'] [Algebra A' K']

/-- **Moving a radical along a ring map of fraction fields** (no instances needed). -/
theorem exists_rad_hom (φ : A →+* A') (ψ : K →+* K') (hψ : ∀ a : A, ψ (algebraMap A K a) = algebraMap A' K' (φ a))
    {d : ℕ} {α : (maxUnram A K)ˣ} {u : K} (hu : (α : maxUnram A K) ^ d = algebraMap K (maxUnram A K) u) :
    ∃ γ : (maxUnram A' K')ˣ, γ ∈ rad (⊤ : Subgroup (Pi1 A' K')) d ∧
      (γ : maxUnram A' K') ^ d = algebraMap K' (maxUnram A' K') (ψ u) := by
  let _ : Algebra K K' := ψ.toAlgebra
  let _ : Algebra A A' := φ.toAlgebra
  let _ : Algebra A K' := ((algebraMap A' K').comp φ).toAlgebra
  have _ : IsScalarTower A K K' := IsScalarTower.of_algebraMap_eq fun a => (hψ a).symm
  have _ : IsScalarTower A A' K' := IsScalarTower.of_algebraMap_eq fun a => rfl
  exact exists_rad_map (A := A) (K := K) (A' := A') (K' := K') hu

end RadHom

section PPTb

end PPTb

end RamanujanPetersson.EtPBC.EtKum

end

end


