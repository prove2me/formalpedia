-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_090
-- name    : RPLib_FX_EtPBC_090
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:17:18.442789+00:00
-- url     : https://prove2.me/theorems/44d6d4a9-2019-5ed0-86c8-9aef70502b49
-- title:
--   Proper base change for the projective line, library file 090
-- statement:
--   File 090 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovHat11`: S4-EtPBC-A, R4-T2 (A2c-3h): the level reductions of the completed overlap
--   * `S4.Def_RP_EtPBC_A_O2Sh3`: S4-EtPBC-A, O2 M6 (O2Sh3, part a): Shapiro's lemma for a separated etale `π = W.hom` of constant degree
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_081

/-!
# Proper base change for the projective line, library file 090

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovHat11`: S4-EtPBC-A, R4-T2 (A2c-3h): the level reductions of the completed overlap
* `S4.Def_RP_EtPBC_A_O2Sh3`: S4-EtPBC-A, O2 M6 (O2Sh3, part a): Shapiro's lemma for a separated etale `π = W.hom` of constant degree
-/

set_option autoImplicit false

set_option linter.defProp false

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

/-- **The level-`k` reduction `Ê → E(k)`.** -/
def θ (k : ℕ) : hE C H hts →+* (C k).E :=
  (ev₀ C hts k).comp ((RingHom.fst (L₀ C) (L₁ C)).comp (hE C H hts).subtype)

end Ov

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Sh3 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Sh3, part a): Shapiro's lemma for a separated etale `π = W.hom` of constant degree

* **`shapExt Λ W n hn A k : Ext_W(π^* A, Λ_W) ≃+ Ext_P(A, Λ[W])`** (adjunction `π^* ⊣ π_*`, `π_*` exact, and
  `Λ[W] ≅ π_* Λ_W`); `shapExt_apply`; **`shapExt_natural`** (naturality in `A`);
* `shapH`, `shapFree` (cohomology forms): file O2Sh3b (split for kernel time).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtShap

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV

universe u

variable (Λ : Type u) [CommRing Λ] {P : Scheme.{u}}

section Shap

variable (W : P.Etale) [QuasiCompact W.hom] [IsSeparated W.hom] (n : ℕ)
  (hn : ∀ y : P, Nat.card ((geomPtAt y).point.fiber.obj W) = n)

theorem shapExt_apply (A : EtSh Λ P) (k : ℕ) (x : Ext.{u} ((pull W.hom Λ).obj A) (unitSh Λ W.left) k) :
    shapExt Λ W n hn A k x =
      (haveI := push_preservesFiniteColimits_of_deg Λ W n hn;
        extAdjMap (pullAdj W.hom Λ) A (unitSh Λ W.left) k x).comp
        (Ext.mk₀ (shapIso Λ W n hn).inv) (add_zero k) :=
  rfl

end Shap

end RamanujanPetersson.EtPBC.EtShap

end

end


