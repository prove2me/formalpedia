-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_146
-- name    : RPLib_FX_EtPBC_146
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:16:43.25419+00:00
-- url     : https://prove2.me/theorems/c21558a8-3de3-5e2a-81d5-57a989cef6f8
-- title:
--   Proper base change for the projective line, library file 146
-- statement:
--   File 146 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovHat3`: S4-EtPBC-A, R4-T2 (A2c-3c): structure maps of the completed charts and the localization property
--   * `S4.Def_RP_EtPBC_A_CovHat5`: S4-EtPBC-A, R4-T2 (A2c-3e): fractions of `R`-combinations
--   * `S4.Def_RP_EtPBC_A_CovHat6`: S4-EtPBC-A, R4-T2 (A2c-3f): the level reductions of the completed charts are surjective
--   * `S4.Def_RP_EtPBC_A_O2L7b1`: S4-EtPBC-A, O2 L7b1: the transport `Tr` from `P¹_K` to the fibre `P_s`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_138
import Definitions.Def_RPLib_FX_EtPBC_139

/-!
# Proper base change for the projective line, library file 146

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovHat3`: S4-EtPBC-A, R4-T2 (A2c-3c): structure maps of the completed charts and the localization property
* `S4.Def_RP_EtPBC_A_CovHat5`: S4-EtPBC-A, R4-T2 (A2c-3e): fractions of `R`-combinations
* `S4.Def_RP_EtPBC_A_CovHat6`: S4-EtPBC-A, R4-T2 (A2c-3f): the level reductions of the completed charts are surjective
* `S4.Def_RP_EtPBC_A_O2L7b1`: S4-EtPBC-A, O2 L7b1: the transport `Tr` from `P¹_K` to the fibre `P_s`
-/

set_option autoImplicit false

set_option linter.defProp false

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

theorem β₁_val (b : B₁) : (β₁ C H hφ₀ hu₀ b : L₀ C × ∀ k, (C k).E₁) = (liftN₀ C hφ₀ hu₀ (φ₁ b), fB₁ C b) :=
  rfl

end Hat3

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

/-- `R → Ê₁`. -/
def ιh₁ : R →+* hE₁ C H := (β₁ C H hφ₀ hu₀).comp ιB₁

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

theorem θ₁_β₁ (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀)) (k : ℕ) (b : B₁) :
    θ₁ C H k (β₁ C H hφ₀ hu₀ b) = (C k).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) b) := rfl

end Theta

section Surj

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (p : Ideal R) (hts : φ₀ t₀ * φ₁ t₁ = 1)

include hts in
/-- **`θ₁ k` is surjective.** -/
theorem θ₁_surj [IsNoetherianRing R] {g : ℕ} (α : Fin g → R) (hα : ∀ i, α i ∈ p)
    (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite) (hB₁ : (eval₂RingHom ιB₁ t₁).Finite)
    (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d) (k : ℕ) :
    Function.Surjective (θ₁ C H k) := by
  intro e
  obtain ⟨n, y₀, hy₀⟩ := (C k).aw₀.1 ((C k).ψ₁ e)
  obtain ⟨d, hnd, hDd⟩ : ∃ d, n ≤ d ∧ D ≤ d := ⟨max n D, le_max_left _ _, le_max_right _ _⟩
  have hmem : ((C k).a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) t₀) ^ (d - n) * y₀, e) ∈ (C k).sec d := by
    rw [TwoCov.mem_sec]
    show (C k).ψ₀ ((C k).a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) t₀) ^ (d - n) * y₀) = (C k).u ^ d * (C k).ψ₁ e
    have hud : (C k).ψ₀ ((C k).a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) t₀)) ^ (d - n) *
        (C k).ψ₀ ((C k).a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) t₀)) ^ n = (C k).u ^ d := by
      rw [← pow_add, Nat.sub_add_cancel hnd]
    rw [map_mul, map_pow, ← hy₀]
    linear_combination (C k).ψ₁ e * hud
  obtain ⟨x, hx, -, hx2⟩ :=
    gam_lev_surj C H ιB₀ ιB₁ p hts α hα hιB hB₀ hB₁ hJ₀ hJ₁ (hs d hDd) (hfil d hDd) k _ hmem
  exact ⟨frac₁ C H d x hx, hx2⟩

end Surj

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L7b1 =====
section

/-!
# S4-EtPBC-A, O2 L7b1: the transport `Tr` from `P¹_K` to the fibre `P_s`
For a `K`-rational geometric point `s` (`[IsIso (s.pt ≫ gS)]`), `e := fibToP1 : P_s ⟶ P¹_K` is an isomorphism with
`e ≫ ιP = ι` (`fibToP1_ιP`). Base change identifications `isoE X : e^*ιP^*X ⟶ ι^*X` (natural, invertible),
the section `σG` of `ιP^*(qV^*V)` through a `K`-point `v'` of `V`, the neighbourhood `jG = (V, v')` of `s`, and
**`nbhdSec_eq`**: `nbhdSec jG = c₀ ≫ e^*σG ≫ isoE`. **`TrE`**: `Ext²(Λ[P¹], Λ[ιP^*R]) → Ext²(Λ_{P_s}, ι^*Λ[R])`,
`x ↦ u ∘ e^*x ∘ v`; **`TrE_surjective`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE

universe u

section Gen

end Gen

section GenSurj

universe w v₁ u₁ v₂ u₂

end GenSurj

section Fib

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)]

variable (Λ : Type) [CommRing Λ]

theorem TrE_surjective (R : (PV K gS).Etale) : Function.Surjective (TrE gS s Λ R) :=
  surj_conj_gen (pull (fibToP1 K gS s) Λ) 2
    (pull_ext_bijective (Λ := Λ) (fibToP1 K gS s) (freeSh Λ (etId (P1 K)))
      (freeSh Λ ((etPull (ιP gS s)).obj R)) 2).2 (uE gS s Λ) (vE gS s Λ R)

end Fib

end RamanujanPetersson.EtPBC.EtMV

end

end


