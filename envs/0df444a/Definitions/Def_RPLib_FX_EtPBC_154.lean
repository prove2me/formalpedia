-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_154
-- name    : RPLib_FX_EtPBC_154
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:29:59.342893+00:00
-- url     : https://prove2.me/theorems/6330e187-b774-574f-a973-27580f86a850
-- title:
--   Proper base change for the projective line, library file 154
-- statement:
--   File 154 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovHat8`: S4-EtPBC-A, R4-T2 (A2c-4a): shifts of fractions by `T₀`, `T₁`
--   * `S4.Def_RP_EtPBC_A_StkBCb`: S4-EtPBC-A, L1f part 2: the stalk base change map `stalkBC` (colimit of the germ maps), `stalkBC_germ`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_139
import Definitions.Def_RPLib_FX_EtPBC_145

/-!
# Proper base change for the projective line, library file 154

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovHat8`: S4-EtPBC-A, R4-T2 (A2c-4a): shifts of fractions by `T₀`, `T₁`
* `S4.Def_RP_EtPBC_A_StkBCb`: S4-EtPBC-A, L1f part 2: the stalk base change map `stalkBC` (colimit of the germ maps), `stalkBC_germ`
-/

set_option autoImplicit false

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

include hts in
theorem frac₁_mT₀ {d : ℕ} {y : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hy : y ∈ Gam C H d)
    (h : mT₀ C y ∈ Gam C H (d + 1)) :
    frac₁ C H (d + 1) (mT₀ C y) h = β₁ C H hφ₀ hu₀ t₁ * frac₁ C H d y hy := by
  refine hE₁_ext (d + 1) ?_ rfl
  have e1 := frac₁_spec hy
  have hinv := liftN₀_inv C hts hφ₀ hu₀
  rw [frac₁_spec]
  show jL₀ C y.1 = jL₀ C (tFm C ^ (d + 1)) *
    (liftN₀ C hφ₀ hu₀ (φ₁ t₁) * (frac₁ C H d y hy : L₀ C × ∀ k, (C k).E₁).1)
  rw [pow_succ (tFm C) d, map_mul]
  linear_combination (-(jL₀ C (tFm C ^ d) * (frac₁ C H d y hy : L₀ C × ∀ k, (C k).E₁).1)) * hinv - e1

end MT

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_StkBCb =====
section

/-!
# S4-EtPBC-A, L1f part 2: the stalk base change map `stalkBC` (colimit of the germ maps), `stalkBC_germ`
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

variable (F : EtSh Λ P) (n : ℕ) (Q : (S.Etale)ᵒᵖ ⥤ ModuleCat.{u} Λ)
  (e : ∀ V : S.Etale, Q.obj (op V) ≃+ Ext.{u} (freeSh Λ ((etPull g).obj V)) F n)

variable {Λ g s F n Q e}

variable (s)

/-- The germ maps as a cocone of types. -/
def stalkCocone (he : GermNat Λ g F n Q e) :
    Cocone (((CategoryOfElements.π s.point.fiber).op ⋙ Q) ⋙ forget (ModuleCat.{u} Λ)) where
  pt := Ext.{u} (unitSh Λ (fib g s)) ((pull (fibι g s) Λ).obj F) n
  ι :=
    { app := fun j => TypeCat.ofHom (fun z => germBC Λ g s F n Q e j.unop z)
      naturality := fun _ _ f => ConcreteCategory.hom_ext _ _ (fun z => germBC_map he f.unop z) }

end RamanujanPetersson.EtPBC

end

end


