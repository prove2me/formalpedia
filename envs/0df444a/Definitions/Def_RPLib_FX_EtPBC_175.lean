-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_175
-- name    : RPLib_FX_EtPBC_175
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:02:09.22026+00:00
-- url     : https://prove2.me/theorems/d9c5d094-cf1f-54f9-833b-9f682612b0f9
-- title:
--   Proper base change for the projective line, library file 175
-- statement:
--   File 175 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovHat7`: S4-EtPBC-A, R4-T2 (A2c-3g): the kernels of the level reductions of the completed charts
--   * `S4.Def_RP_EtPBC_A_SecExt`: S4-EtPBC-A, L1c (part 3): cohomology of sections of an injective resolution is `Ext` from a free sheaf
--   * `S4.Def_RP_EtPBC_A_O2T4d`: S4-EtPBC-A, O2 S5d (O2T4d): point class `pcD`, `clsD_sec`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_155
import Definitions.Def_RPLib_FX_EtPBC_167

/-!
# Proper base change for the projective line, library file 175

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovHat7`: S4-EtPBC-A, R4-T2 (A2c-3g): the kernels of the level reductions of the completed charts
* `S4.Def_RP_EtPBC_A_SecExt`: S4-EtPBC-A, L1c (part 3): cohomology of sections of an injective resolution is `Ext` from a free sheaf
* `S4.Def_RP_EtPBC_A_O2T4d`: S4-EtPBC-A, O2 S5d (O2T4d): point class `pcD`, `clsD_sec`
-/

set_option autoImplicit false

set_option linter.defProp false

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

end Van

section Ker

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (p : Ideal R) (hts : φ₀ t₀ * φ₁ t₁ = 1) (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀))
  (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁))

include hts in
/-- **`ker (θ₁ k) = p^(k+1) Ê₁`.** -/
def θ₁_ker [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R) (hα : ∀ i, α i ∈ p)
    (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite) (hB₁ : (eval₂RingHom ιB₁ t₁).Finite)
    (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d) (k : ℕ) :
    RingHom.ker (θ₁ C H k) = (p ^ (k + 1)).map (ιh₁ C H ιB₁ hφ₀ hu₀) := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    obtain ⟨d, x, hx, h1, h2⟩ := (mem_hE₁ C H _).1 z.2
    have hx0 : x.2 k = 0 := (congrFun h2 k).symm.trans hz
    obtain ⟨m, hm⟩ := van₁ C H hx k hx0
    rw [eq_frac₁ z hx h1 h2, ← frac₁_T₁ hx (m + D)]
    exact frac₁_mem_of_van C H ιB₀ ιB₁ p hts hφ₀ hu₀ α hα hιB hB₀ hB₁ hJ₀ hJ₁ (hs _ (by omega))
      (hfil _ (by omega)) _ k (hm D).1 (hm D).2
  · rw [Ideal.map_le_iff_le_comap]
    intro c hc
    rw [Ideal.mem_comap, RingHom.mem_ker]
    show (C k).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) (ιB₁ c)) = 0
    have hm : ιB₁ c ∈ J₁ ^ (k + 1) := by
      rw [hJ₁, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hc
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hm, map_zero]

end Ker

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_SecExt =====
section

/-!
# S4-EtPBC-A, L1c (part 3): cohomology of sections of an injective resolution is `Ext` from a free sheaf

`secExt Λ I W p : H^(p+1)(I^•(W)) ≃+ Ext^(p+1)(Λ[W], F)` (`Λ[W] = freeSh Λ W`), from Mathlib's cocycle
description of `Ext` (`InjectiveResolution.extMk`) and `freeEquiv : Hom(Λ[W], G) ≃+ G(W)`. The homology is that of
the short complex `sc (p+1)`, which is `(secCx Λ I.cocomplex W).homology (p+1)` by definition.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}} {F : EtSh Λ X} (I : InjectiveResolution F)

/-- The class map on the explicit homology `ker / im`. -/
def quotExt (W : X.Etale) (p : ℕ) :
    (LinearMap.ker (secSc Λ I W p).g.hom ⧸ LinearMap.range (secSc Λ I W p).moduleCatToCycles) →+
      Ext.{u} (freeSh Λ W) F (p + 1) :=
  QuotientAddGroup.lift _ (cocExt Λ I W p) (fun z hz => (cocExt_eq_zero_iff Λ I W p z).2 hz)

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T4d =====
section

/-!
# S4-EtPBC-A, O2 S5d (O2T4d): point class `pcD`, `clsD_sec`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk

universe u

section Pc

variable {k : Type} [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] {P : Scheme.{0}} (c : A1 k ⟶ P)
  [IsOpenImmersion c] {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (a : k)
  {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0) (hΛ : ∀ x : Λ, N • x = 0)
  {Uz : P.Opens} (hUz : ∀ u : Spec B, (chEt c φ).hom u ∈ Uz ↔ φ.hom (X - C a) ∉ u.asIdeal)
  (hS : (locC Λ (chEt c φ) (le_refl Uz)).ShortExact)

/-- Unfolding equation for `pcD` (rewrite with it, never with `pcD`: see `thetaM_eq`). -/
theorem pcD_eq (c' : Λ) : pcD c φ a hN hΛ hUz hS c' =
    (hS.extClass.comp (Ext.mk₀ (freeMap Λ (isoT c φ hUz).inv)) (add_zero 1)).comp
      (thetaM Λ (toD1 c φ a) 1 (resLE (toWa c a φ).left 1 (xiA a hN Λ hΛ c'))) (show 1 + 1 = 2 from rfl) :=
  rfl

end Pc

end RamanujanPetersson.EtPBC.EtMV

end

end


