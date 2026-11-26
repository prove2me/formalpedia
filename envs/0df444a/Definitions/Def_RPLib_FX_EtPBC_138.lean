-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_138
-- name    : RPLib_FX_EtPBC_138
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:33:07.202387+00:00
-- url     : https://prove2.me/theorems/e174047e-0cc9-51ea-af3f-42d6f0461d71
-- title:
--   Proper base change for the projective line, library file 138
-- statement:
--   File 138 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovHat4`: S4-EtPBC-A, R4-T2 (A2c-3d): fractions `x / T₀ᵈ`, `x / T₁ᵈ` in the completed charts
--   * `S4.Def_RP_EtPBC_A_CovHat5`: S4-EtPBC-A, R4-T2 (A2c-3e): fractions of `R`-combinations
--   * `S4.Def_RP_EtPBC_A_CovHat6`: S4-EtPBC-A, R4-T2 (A2c-3f): the level reductions of the completed charts are surjective
--   * `S4.Def_RP_EtPBC_A_CovHat8`: S4-EtPBC-A, R4-T2 (A2c-4a): shifts of fractions by `T₀`, `T₁`
--   * `S4.Def_RP_EtPBC_A_SecCls`: S4-EtPBC-A, L1c (part 2): the cocycle map `ker g →+ Ext^(p+1)(Λ[W], F)`
--   * `S4.Def_RP_EtPBC_A_O2Rel3`: S4-EtPBC-A, O2 REL (O2Rel3): the relation with a distinguished point
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_130

/-!
# Proper base change for the projective line, library file 138

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovHat4`: S4-EtPBC-A, R4-T2 (A2c-3d): fractions `x / T₀ᵈ`, `x / T₁ᵈ` in the completed charts
* `S4.Def_RP_EtPBC_A_CovHat5`: S4-EtPBC-A, R4-T2 (A2c-3e): fractions of `R`-combinations
* `S4.Def_RP_EtPBC_A_CovHat6`: S4-EtPBC-A, R4-T2 (A2c-3f): the level reductions of the completed charts are surjective
* `S4.Def_RP_EtPBC_A_CovHat8`: S4-EtPBC-A, R4-T2 (A2c-4a): shifts of fractions by `T₀`, `T₁`
* `S4.Def_RP_EtPBC_A_SecCls`: S4-EtPBC-A, L1c (part 2): the cocycle map `ker g →+ Ext^(p+1)(Λ[W], F)`
* `S4.Def_RP_EtPBC_A_O2Rel3`: S4-EtPBC-A, O2 REL (O2Rel3): the relation with a distinguished point
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

/-- **`T₀ᵐ x / T₀^(d+m) = x / T₀ᵈ`.** -/
theorem frac₀_T₀ {d : ℕ} {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d) (m : ℕ) :
    frac₀ C H hts (d + m) (gT₀ C ^ m * x) (gT₀_pow_mem C H hts m hx) = frac₀ C H hts d x hx := by
  refine hE₀_ext hts (d + m) ?_ ?_
  · show (gT₀ C ^ m * x).1 = x.1
    simp only [Prod.fst_mul, Prod.pow_fst, gT₀, one_pow, one_mul]
  · have e1 := frac₀_spec hts hx
    rw [frac₀_spec]
    show jL₁ C (sFm C ^ m * x.2) = jL₁ C (sFm C ^ (d + m)) * (frac₀ C H hts d x hx : (∀ k, (C k).E₀) × L₁ C).2
    rw [map_mul, pow_add, map_mul]
    linear_combination (-(jL₁ C (sFm C ^ m))) * e1

theorem frac₀_add {d : ℕ} {x y : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d) (hy : y ∈ Gam C H d) :
    frac₀ C H hts d x hx + frac₀ C H hts d y hy = frac₀ C H hts d (x + y) (add_mem hx hy) := by
  refine hE₀_ext hts d rfl ?_
  rw [frac₀_spec hts (add_mem hx hy)]
  show jL₁ C (sFm C ^ d) * ((frac₀ C H hts d x hx : (∀ k, (C k).E₀) × L₁ C).2 +
    (frac₀ C H hts d y hy : (∀ k, (C k).E₀) × L₁ C).2) = jL₁ C (x.2 + y.2)
  rw [mul_add, frac₀_spec, frac₀_spec, map_add]

end Frac

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovHat5 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3e): fractions of `R`-combinations

* `ιP : R →+* ∏E₀ × ∏E₁`, `ιh₀ = β₀ ∘ ιB₀`, `ιh₁ = β₁ ∘ ιB₁`, **`levF_eq`** (`levF σ a = ∑ ιP (aᵢ) σᵢ`),
  **`frac₀_lin`**, **`frac₁_lin`**: fractions of `R`-combinations are combinations of fractions.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Lin

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (hts : φ₀ t₀ * φ₁ t₁ = 1) (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀))
  (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁))

/-- `R → Ê₀`. -/
def ιh₀ : R →+* hE₀ C H hts := (β₀ C H hts hφ₁ hu₁).comp ιB₀

end Lin

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

theorem θ₀_frac₀ (k : ℕ) {d : ℕ} {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d) :
    θ₀ C H hts k (frac₀ C H hts d x hx) = x.1 k := rfl

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

theorem frac₀_mT₀ {d : ℕ} {y : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hy : y ∈ Gam C H d)
    (h : mT₀ C y ∈ Gam C H (d + 1)) : frac₀ C H hts (d + 1) (mT₀ C y) h = frac₀ C H hts d y hy := by
  refine hE₀_ext hts (d + 1) rfl ?_
  have e1 := frac₀_spec hts hy
  rw [frac₀_spec]
  show jL₁ C (sFm C * y.2) = jL₁ C (sFm C ^ (d + 1)) * (frac₀ C H hts d y hy : (∀ k, (C k).E₀) × L₁ C).2
  rw [map_mul, pow_succ (sFm C) d, map_mul]
  linear_combination (-(jL₁ C (sFm C))) * e1

end MT

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

/-- The cocycle map as an additive map. -/
def cocExt (W : X.Etale) (p : ℕ) : LinearMap.ker (secSc Λ I W p).g.hom →+ Ext.{u} (freeSh Λ W) F (p + 1) :=
  AddMonoidHom.mk' (cocExtFun Λ I W p) (cocExtFun_add Λ I W p)

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Rel3 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Rel3): the relation with a distinguished point

REL PLAN v2 (s126), file R3, generic part. `relation_sum` (O2R4) over `Option ι`: the point `z₀` (nbhd `S₀`) and the
other points `z j` outside `U₀` (nbhds `S j`):
* **`term_mem_option`**: the term at `z₀` lies in an additive subgroup `G` when every term at a `z j` is at a good point
  (one-point classes there lie in `G`) or is `0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} {ι : Type u} [Fintype ι] [DecidableEq ι] (U₀ : P.Opens)

/-- **The term at `z₀` lies in `G` when every other term is at a good point or is `0`.** -/
theorem term_mem_option {F : EtSh Λ P} (G : AddSubgroup (Ext.{u} (freeSh Λ (etId P)) F 2)) (good : P → Prop)
    (hG : ∀ x, good x → ∀ β, IsLoc Λ F x β → β ∈ G) (κ : Ext.{u} (freeSh Λ (opEt U₀)) F 1)
    {S₀ : P.Etale} {z₀ : P} {Uz₀ : P.Opens} (h₀ : U₀ ≤ Uz₀) (hz₀ : ∀ x : P, x ∈ Uz₀ ↔ x ≠ z₀)
    (hS₀ : Subsingleton ((geomPtAt z₀).point.fiber.obj S₀)) (hN₀ : Nonempty ((geomPtAt z₀).point.fiber.obj S₀))
    (hR₀ : ∀ v : S₀.left, S₀.hom v ∈ U₀ ∨ S₀.hom v = z₀)
    (S : ι → P.Etale) (z : ι → P) (hzi : Function.Injective z) (hz0 : ∀ j, z j ≠ z₀)
    (hU : ∀ x : P, x ∈ U₀ ↔ x ≠ z₀ ∧ ∀ j, x ≠ z j)
    (hD : ∀ j, Subsingleton ((geomPtAt (z j)).point.fiber.obj (S j)))
    (hDn : ∀ j, Nonempty ((geomPtAt (z j)).point.fiber.obj (S j)))
    (hDr : ∀ j (v : (S j).left), (S j).hom v ∈ U₀ ∨ (S j).hom v = z j)
    (Uz : ι → P.Opens) (h : ∀ j, U₀ ≤ Uz j) (hz : ∀ j (x : P), x ∈ Uz j ↔ x ≠ z j)
    (hk : ∀ j, good (z j) ∨ (locC_shortExact (Λ := Λ) (S j) (h j) (z j) (hz j) (hD j) (hDn j) (hDr j)).extClass.comp
      ((Ext.mk₀ (freeMap Λ (prT (S j) (opEt U₀)))).comp κ (zero_add 1)) (show 1 + 1 = 2 from rfl) = 0) :
    (locC_shortExact (Λ := Λ) S₀ h₀ z₀ hz₀ hS₀ hN₀ hR₀).extClass.comp
      ((Ext.mk₀ (freeMap Λ (prT S₀ (opEt U₀)))).comp κ (zero_add 1)) (show 1 + 1 = 2 from rfl) ∈ G := by
  have hzi' : Function.Injective (fun o : Option ι => o.elim z₀ z) := by
    rintro (_ | i) (_ | j) hij
    · rfl
    · exact absurd hij.symm (hz0 j)
    · exact absurd hij (hz0 i)
    · exact congrArg some (hzi hij)
  have hU' : ∀ x : P, x ∈ U₀ ↔ ∀ o : Option ι, x ≠ o.elim z₀ z := by
    intro x
    rw [hU x]
    constructor
    · rintro ⟨h1, h2⟩ (_ | j)
      · exact h1
      · exact h2 j
    · intro h3
      exact ⟨h3 none, fun j => h3 (some j)⟩
  have hD' : ∀ o : Option ι, Subsingleton ((geomPtAt (o.elim z₀ z)).point.fiber.obj (o.elim S₀ S)) := by
    rintro (_ | j)
    · exact hS₀
    · exact hD j
  have hDn' : ∀ o : Option ι, Nonempty ((geomPtAt (o.elim z₀ z)).point.fiber.obj (o.elim S₀ S)) := by
    rintro (_ | j)
    · exact hN₀
    · exact hDn j
  have hDr' : ∀ (o : Option ι) (v : (o.elim S₀ S).left), (o.elim S₀ S).hom v ∈ U₀ ∨ (o.elim S₀ S).hom v = o.elim z₀ z := by
    rintro (_ | j)
    · exact hR₀
    · exact hDr j
  have hz' : ∀ (o : Option ι) (x : P), x ∈ o.elim Uz₀ Uz ↔ x ≠ o.elim z₀ z := by
    rintro (_ | j)
    · exact hz₀
    · exact hz j
  exact term_mem_of_good (fun o : Option ι => o.elim S₀ S) U₀ (fun o : Option ι => o.elim z₀ z) hzi' hU' hD' hDn'
    hDr' (fun o : Option ι => o.elim Uz₀ Uz) hz' G good hG κ none (by
      rintro (_ | j) hj
      · exact absurd rfl hj
      · exact hk j)

end RamanujanPetersson.EtPBC.EtMV

end

end


