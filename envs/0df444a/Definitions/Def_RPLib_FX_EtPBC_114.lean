-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_114
-- name    : RPLib_FX_EtPBC_114
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:48:29.127155+00:00
-- url     : https://prove2.me/theorems/33534e37-fe8f-5d5d-8db7-5b403f49c824
-- title:
--   Proper base change for the projective line, library file 114
-- statement:
--   File 114 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2PPTb`: S4-EtPBC-A, O2 GLOB (O2PPTb): a piece Kummer class pulled back along an etale map
--   * `S4.Def_RP_EtPBC_A_O2T9a`: S4-EtPBC-A, O2 S6a (O2T9a): naturality of `resFreeIso` and `clsD` in the coefficients; `clsD` is one-point
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_055
import Definitions.Def_RPLib_FX_EtPBC_082
import Definitions.Def_RPLib_FX_EtPBC_104
import Definitions.Def_RPLib_FX_EtPBC_109

/-!
# Proper base change for the projective line, library file 114

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2PPTb`: S4-EtPBC-A, O2 GLOB (O2PPTb): a piece Kummer class pulled back along an etale map
* `S4.Def_RP_EtPBC_A_O2T9a`: S4-EtPBC-A, O2 S6a (O2T9a): naturality of `resFreeIso` and `clsD` in the coefficients; `clsD` is one-point
-/

set_option autoImplicit false

set_option linter.defProp false

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
/-- **A piece class of `X` vanishes on the pieces of `X₁` not over its piece.** -/
def resLE_kapS_off (p₁ : minimalPrimes Γ(X₁, ⊤)) (hp : ¬ (p : Ideal Γ(X, ⊤)) ≤ RingHom.ker (kerMap f p₁))
    (χ : ChL (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))) Λ) :
    resLE (piHom (piEquiv h₁) p₁) 1 (resLE f 1 (kapS h Λ p χ)) = 0 := by
  obtain ⟨q, hq⟩ := exists_minimalPrime_le_ker f p₁
  have hne : q ≠ p := fun e => hp (e ▸ hq)
  have := etale_kerLift h h₁ f hq
  refine (resLE_piece h h₁ f p₁ q hq _).trans ?_
  refine (congrArg (resLE (Spec.map (CommRingCat.ofHom (kerLift hq))) 1) (resLE_kapS_ne h Λ hne _)).trans ?_
  exact map_zero (resLEHom (Spec.map (CommRingCat.ofHom (kerLift hq))) (Λ := Λ) 1)

end PPTb

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T9a =====
section

/-!
# S4-EtPBC-A, O2 S6a (O2T9a): naturality of `resFreeIso` and `clsD` in the coefficients; `clsD` is one-point

* `resFreeIso_natural r`: `resFreeIso_{T'} ≫ res Λ[r] = Λ[e⁻¹ r] ≫ resFreeIso_T`;
* `clsD_natF f h Y`: `clsD (f ≫ res h) Y = clsD f Y ∘ h` for `h : F' ⟶ F` on `P`;
* **`clsD_isLoc`**: every `clsD f Y` is a one-point class `IsLoc` at `c (X = a)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option profiler true
set_option profiler.threshold 3000

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk

universe u

section ResNat

end ResNat

section ClsNat

variable {k : Type} [Field k] {Λ : Type} [CommRing Λ] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (a : k)
  {Uz : P.Opens} (hUz : ∀ u : Spec B, (chEt c φ).hom u ∈ Uz ↔ φ.hom (X - C a) ∉ u.asIdeal)
  (hS : (locC Λ (chEt c φ) (le_refl Uz)).ShortExact)

set_option backward.isDefEq.respectTransparency false in
/-- **`clsD` is natural in the coefficients** `F' ⟶ F` on `P`. -/
theorem clsD_natF {F F' : EtSh Λ P} {G : EtSh Λ (chEt c φ).left} (f : G ⟶ (res (chEt c φ).hom Λ).obj F')
    (h : F' ⟶ F) (Y : H Λ ((res (toD1 c φ a).left Λ).obj G) 1) :
    clsD c φ a hUz hS (f ≫ (res (chEt c φ).hom Λ).map h) Y =
      (clsD c φ a hUz hS f Y).comp (Ext.mk₀ h) (add_zero 2) := by
  have key : (extFree Λ (W1 c φ a) F 1).symm (Y.comp (Ext.mk₀ ((res (toD1 c φ a).left Λ).map
      (f ≫ (res (chEt c φ).hom Λ).map h) ≫ (resCompIso Λ (toD1 c φ a)).hom.app F)) (add_zero 1)) =
      ((extFree Λ (W1 c φ a) F' 1).symm (Y.comp (Ext.mk₀ ((res (toD1 c φ a).left Λ).map f ≫
        (resCompIso Λ (toD1 c φ a)).hom.app F')) (add_zero 1))).comp (Ext.mk₀ h) (add_zero 1) := by
    have hm : (res (toD1 c φ a).left Λ).map (f ≫ (res (chEt c φ).hom Λ).map h) ≫
          (resCompIso Λ (toD1 c φ a)).hom.app F =
        ((res (toD1 c φ a).left Λ).map f ≫ (resCompIso Λ (toD1 c φ a)).hom.app F') ≫
          (res (W1 c φ a).hom Λ).map h := by
      rw [Functor.map_comp]
      simp only [Category.assoc]
      congr 1
      exact (resCompIso Λ (toD1 c φ a)).hom.naturality h
    apply (extFree Λ (W1 c φ a) F 1).injective
    rw [extFree_comp_mk₀, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, hm]
  rw [clsD_eq, clsD_eq, key, Ext.comp_assoc_of_third_deg_zero]

end ClsNat

end RamanujanPetersson.EtPBC.EtMV

end

end


