-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_145
-- name    : RPLib_FX_EtPBC_145
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:00:09.746505+00:00
-- url     : https://prove2.me/theorems/5a2318cc-ea97-5986-b0df-4ccccdd9169b
-- title:
--   Proper base change for the projective line, library file 145
-- statement:
--   File 145 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovHat6`: S4-EtPBC-A, R4-T2 (A2c-3f): the level reductions of the completed charts are surjective
--   * `S4.Def_RP_EtPBC_A_CovHat8`: S4-EtPBC-A, R4-T2 (A2c-4a): shifts of fractions by `T₀`, `T₁`
--   * `S4.Def_RP_EtPBC_A_CovGl2`: S4-EtPBC-A, R4-T2 (G1c, part 2b): gluing finite etale chart algebras over `Y_{V'}`
--   * `S4.Def_RP_EtPBC_A_StkBC`: S4-EtPBC-A, L1f: the base change map on stalks
--   * `S4.Def_RP_EtPBC_A_NbExt2`: S4-EtPBC-A, M2 F8a: extending a clopen of `Y_s` to an etale neighbourhood
--   * `S4.Def_RP_EtPBC_A_NbExt3`: S4-EtPBC-A, M2 F8b + F9: surjectivity of base change in degree 0 for `π_* M_Y`
--   * `S4.Def_RP_EtPBC_A_NInd`: S4-EtPBC-A, M4(C,D,F): noetherian induction on supports
--   * `S4.Def_RP_EtPBC_A_O2Rel5`: S4-EtPBC-A, O2 REL (O2Rel5): the relation over all points outside a cofinite open
--   * `S4.Def_RP_EtPBC_A_O2Gen1`: S4-EtPBC-A, O2 Gen1: point classes along maps, chart facts on `P¹`
--   * `S4.Def_RP_EtPBC_A_PBCP1`: S4-EtPBC-A, G0': base change in degrees `≥ 3`, and proper base change for `P¹_S` modulo degrees `1, 2`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_100
import Definitions.Def_RPLib_FX_EtPBC_101
import Definitions.Def_RPLib_FX_EtPBC_103
import Definitions.Def_RPLib_FX_EtPBC_138

/-!
# Proper base change for the projective line, library file 145

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovHat6`: S4-EtPBC-A, R4-T2 (A2c-3f): the level reductions of the completed charts are surjective
* `S4.Def_RP_EtPBC_A_CovHat8`: S4-EtPBC-A, R4-T2 (A2c-4a): shifts of fractions by `T₀`, `T₁`
* `S4.Def_RP_EtPBC_A_CovGl2`: S4-EtPBC-A, R4-T2 (G1c, part 2b): gluing finite etale chart algebras over `Y_{V'}`
* `S4.Def_RP_EtPBC_A_StkBC`: S4-EtPBC-A, L1f: the base change map on stalks
* `S4.Def_RP_EtPBC_A_NbExt2`: S4-EtPBC-A, M2 F8a: extending a clopen of `Y_s` to an etale neighbourhood
* `S4.Def_RP_EtPBC_A_NbExt3`: S4-EtPBC-A, M2 F8b + F9: surjectivity of base change in degree 0 for `π_* M_Y`
* `S4.Def_RP_EtPBC_A_NInd`: S4-EtPBC-A, M4(C,D,F): noetherian induction on supports
* `S4.Def_RP_EtPBC_A_O2Rel5`: S4-EtPBC-A, O2 REL (O2Rel5): the relation over all points outside a cofinite open
* `S4.Def_RP_EtPBC_A_O2Gen1`: S4-EtPBC-A, O2 Gen1: point classes along maps, chart facts on `P¹`
* `S4.Def_RP_EtPBC_A_PBCP1`: S4-EtPBC-A, G0': base change in degrees `≥ 3`, and proper base change for `P¹_S` modulo degrees `1, 2`
-/

set_option autoImplicit false

set_option linter.defProp false

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

/-- **`θ₀ k` is surjective.** -/
theorem θ₀_surj [IsNoetherianRing R] {g : ℕ} (α : Fin g → R) (hα : ∀ i, α i ∈ p)
    (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite) (hB₁ : (eval₂RingHom ιB₁ t₁).Finite)
    (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d) (k : ℕ) :
    Function.Surjective (θ₀ C H hts k) := by
  intro e
  obtain ⟨n, y₁, hy₁⟩ := (C k).aw₁.1 ((C k).ψ₀ e)
  obtain ⟨d, hnd, hDd⟩ : ∃ d, n ≤ d ∧ D ≤ d := ⟨max n D, le_max_left _ _, le_max_right _ _⟩
  have hv := lhv hts (C k)
  have hmem : (e, (C k).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁) ^ (d - n) * y₁) ∈ (C k).sec d := by
    rw [TwoCov.mem_sec]
    show (C k).ψ₀ e = (C k).u ^ d * (C k).ψ₁ ((C k).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁) ^ (d - n) * y₁)
    have hvd : (C k).ψ₁ ((C k).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁)) ^ (d - n) *
        (C k).ψ₁ ((C k).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁)) ^ n =
        (C k).ψ₁ ((C k).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁)) ^ d := by
      rw [← pow_add, Nat.sub_add_cancel hnd]
    have hud : (C k).u ^ d * (C k).ψ₁ ((C k).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁)) ^ d = 1 := by
      rw [← mul_pow, hv, one_pow]
    rw [map_mul, map_pow, ← hy₁]
    linear_combination (-(C k).ψ₀ e) * hud - ((C k).u ^ d * (C k).ψ₀ e) * hvd
  obtain ⟨x, hx, hx1, -⟩ :=
    gam_lev_surj C H ιB₀ ιB₁ p hts α hα hιB hB₀ hB₁ hJ₀ hJ₁ (hs d hDd) (hfil d hDd) k _ hmem
  exact ⟨frac₀ C H hts d x hx, hx1⟩

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

theorem frac₀_mT₁ {d : ℕ} {y : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hy : y ∈ Gam C H d)
    (h : mT₁ C y ∈ Gam C H (d + 1)) :
    frac₀ C H hts (d + 1) (mT₁ C y) h = β₀ C H hts hφ₁ hu₁ t₀ * frac₀ C H hts d y hy := by
  refine hE₀_ext hts (d + 1) rfl ?_
  have e1 := frac₀_spec hts hy
  have hinv := liftN₁_inv C hts hφ₁ hu₁
  rw [frac₀_spec]
  show jL₁ C y.2 = jL₁ C (sFm C ^ (d + 1)) *
    (liftN₁ C hφ₁ hu₁ (φ₀ t₀) * (frac₀ C H hts d y hy : (∀ k, (C k).E₀) × L₁ C).2)
  rw [pow_succ (sFm C) d, map_mul]
  linear_combination (-(jL₁ C (sFm C ^ d) * (frac₀ C H hts d y hy : (∀ k, (C k).E₀) × L₁ C).2)) * hinv - e1

end MT

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovGl2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1c, part 2b): gluing finite etale chart algebras over `Y_{V'}`

Chart algebras `E₀`, `E₁`, `E₀₁` over `R' ⊗ Γ(Y₀)`, `R' ⊗ Γ(Y₁)`, `R' ⊗ Γ(Y₀₁)`, glued by localizations `ψ₀`, `ψ₁` (the
data of `CoverLift`), give a relative gluing datum **`glD`** over the chart cover `covV`; its glued scheme maps to
`Y_{V'}` by **`toBase`**, which is finite and etale when `E₀`, `E₁` are.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV)

variable [IsAffine V] [IsFinite π] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R'] {E₀ E₁ E₀₁ : Type u}
  [CommRing E₀] [CommRing E₁] [CommRing E₀₁] [Algebra (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) E₀]
  [Algebra (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) E₁] [Algebra (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1)) E₀₁]
  (ψ₀ : E₀ →+* E₀₁) (ψ₁ : E₁ →+* E₀₁)
  (hψ₀ : ∀ (r : R') (b : Γ(Y, Yc K gV π 0)), ψ₀ (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) E₀ (r ⊗ₜ b)) =
    algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1)) E₀₁ (r ⊗ₜ φY0 K gV π b))
  (hψ₁ : ∀ (r : R') (b : Γ(Y, Yc K gV π 1)), ψ₁ (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) E₁ (r ⊗ₜ b)) =
    algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1)) E₀₁ (r ⊗ₜ φY1 K gV π b))
  (aw₀ : IsAwayMap ψ₀ (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) E₀
    ((1 : R') ⊗ₜ algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0) Polynomial.X)))
  (aw₁ : IsAwayMap ψ₁ (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) E₁
    ((1 : R') ⊗ₜ algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 1) Polynomial.X)))

include hψ₁ aw₁ in
/-- **The right localization square is a pullback.** -/
theorem pb1 : IsPullback (Spec.map (CommRingCat.ofHom ψ₁))
    (Spec.map (CommRingCat.ofHom (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1)) E₀₁)))
    (Spec.map (CommRingCat.ofHom (algebraMap (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) E₁))) (a1 K gV π R') :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (isPushout_loc (φY1 K gV π) _ (away1 K gV π) (unit1 K gV π) ψ₁ hψ₁ aw₁)

section FinEt

end FinEt

section Et

end Et

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

variable (F : EtSh Λ P) (n : ℕ) (Q : (S.Etale)ᵒᵖ ⥤ ModuleCat.{u} Λ)
  (e : ∀ V : S.Etale, Q.obj (op V) ≃+ Ext.{u} (freeSh Λ ((etPull g).obj V)) F n)

variable {Λ g s F n Q e}

theorem germBC_map (he : GermNat Λ g F n Q e) {j j' : Nbhd s} (a : j' ⟶ j) (z : Q.obj (op j.1)) :
    germBC Λ g s F n Q e j' (Q.map a.1.op z) = germBC Λ g s F n Q e j z :=
  (congrArg (Delta.bc (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s) j' F n)
    (he a.1 z)).trans
    (Delta.bc_res (L := pull (fibι g s) Λ) (A := nbhdSys Λ g s) (B := unitSh Λ (fib g s)) (u := bcUnit Λ g s)
      (bcUnit_comp Λ g s) a F n (e j.1 z))

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_NbExt2 =====
section

/-!
# S4-EtPBC-A, M2 F8a: extending a clopen of `Y_s` to an etale neighbourhood

* `ysj_map`: `ysj j' ≫ (restriction along a : j' ⟶ j) = ysj j`;
* `etale_hV`, `nbR` (the neighbourhood `Spec R' ⟶ V ⟶ S` through `x'`), `nbRHom : nbR ⟶ j`;
* **`exists_clopen_nbhd`**: for an affine noetherian neighbourhood `j` and a clopen `O ⊆ Y_s` there is an affine
  noetherian `j' ⟶ j` and a clopen `C ⊆ Y_{j'}` with `ysj j' ⁻¹' C = O`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3

universe u

section Map

end Map

section Nbhd

end Nbhd

variable (K : Type u) [Field K] {S : Scheme.{u}} (gK : S ⟶ Spec (CommRingCat.of K)) (s : GeomPt S)
  {Y : Scheme.{u}} (π : Y ⟶ PV K gK)

/-- **Extension of a clopen of `Y_s` to a neighbourhood.** -/
theorem exists_clopen_nbhd [IsIso (s.pt ≫ gK)] [IsFinite π] (j : Nbhd s) [IsAffine j.1.left]
    [IsNoetherianRing Γ(j.1.left, ⊤)] (O : Set ↑(pullback π (fibι (qV K gK) s))) (hO : IsClopen O) :
    ∃ (j' : Nbhd s) (_ : j' ⟶ j), IsAffine j'.1.left ∧ IsNoetherianRing Γ(j'.1.left, ⊤) ∧
      ∃ C : Set ↑(pullback (pullback.snd j'.1.hom (qV K gK)) π), IsClopen C ∧
        ∀ q : ↑(pullback π (fibι (qV K gK) s)), ysj (qV K gK) s π j' q ∈ C ↔ q ∈ O := by
  let C₀ : (Yx K ((nbh s j) ≫ gK) (piVV K gK π (nbh s j)) (xV K gK s (nbv s j))).Opens :=
    eY'V K gK s π (nbh s j) (nbv s j) (nbv_w s j) ⁻¹ᵁ (⟨O, hO.isOpen⟩ : (pullback π (fibι (qV K gK) s)).Opens)
  have hC₀ : IsClosed (C₀ : Set ↑(Yx K ((nbh s j) ≫ gK) (piVV K gK π (nbh s j)) (xV K gK s (nbv s j)))) :=
    hO.isClosed.preimage (eY'V K gK s π (nbh s j) (nbv s j) (nbv_w s j)).continuous
  obtain ⟨R', _, _, _, x', hx', C, hC, hCC⟩ := exists_clopen_ext K ((nbh s j) ≫ gK) (piVV K gK π (nbh s j))
    (xV K gK s (nbv s j)) (xV_g K gK s (nbh s j) (nbv s j) (nbv_w s j)) C₀ hC₀
  have e : ysj (qV K gK) s π (nbR K gK s j R' x' hx') ≫ kapV K gK π (nbh s j) R' =
      eYV K gK s π (nbh s j) (nbv s j) (nbv_w s j) ≫
        yxMap K ((nbh s j) ≫ gK) (piVV K gK π (nbh s j)) R' (xV K gK s (nbv s j)) x' hx' :=
    ysV_kapV K gK s π (nbh s j) (nbv s j) R' x' ((s.pt ≫ gK) ≫ x') hx' rfl (nbv_w s j)
  have e2 : ∀ q : ↑(pullback π (fibι (qV K gK) s)),
      eY'V K gK s π (nbh s j) (nbv s j) (nbv_w s j) (eYV K gK s π (nbh s j) (nbv s j) (nbv_w s j) q) = q :=
    fun q => congrArg (fun φ => φ.base q) (eYV_eY'V K gK s π (nbh s j) (nbv s j) (nbv_w s j))
  refine ⟨nbR K gK s j R' x' hx', nbRHom K gK s j R' x' hx', ?_, ?_,
    (kapV K gK π (nbh s j) R') ⁻¹' (C : Set ↑(YV K ((nbh s j) ≫ gK) (piVV K gK π (nbh s j)) R')),
    ⟨hC.preimage (kapV K gK π (nbh s j) R').continuous, C.isOpen.preimage (kapV K gK π (nbh s j) R').continuous⟩,
    fun q => ?_⟩
  · show IsAffine (Spec (CommRingCat.of R'))
    infer_instance
  · haveI : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing Γ(j.1.left, ⊤) R'
    show IsNoetherianRing Γ(Spec (CommRingCat.of R'), ⊤)
    exact isNoetherianRing_of_ringEquiv R' (Scheme.ΓSpecIso (CommRingCat.of R')).symm.commRingCatIsoToRingEquiv
  · have hq : kapV K gK π (nbh s j) R' (ysj (qV K gK) s π (nbR K gK s j R' x' hx') q) =
        yxMap K ((nbh s j) ≫ gK) (piVV K gK π (nbh s j)) R' (xV K gK s (nbv s j)) x' hx'
          (eYV K gK s π (nbh s j) (nbv s j) (nbv_w s j) q) := congrArg (fun φ => φ.base q) e
    show kapV K gK π (nbh s j) R' (ysj (qV K gK) s π (nbR K gK s j R' x' hx') q) ∈ (C : Set _) ↔ q ∈ O
    rw [hq]
    have h3 : eYV K gK s π (nbh s j) (nbv s j) (nbv_w s j) q ∈
        yxMap K ((nbh s j) ≫ gK) (piVV K gK π (nbh s j)) R' (xV K gK s (nbv s j)) x' hx' ⁻¹ᵁ C ↔
        eYV K gK s π (nbh s j) (nbv s j) (nbv_w s j) q ∈ C₀ := by rw [hCC]
    refine h3.trans ?_
    show eY'V K gK s π (nbh s j) (nbv s j) (nbv_w s j) (eYV K gK s π (nbh s j) (nbv s j) (nbv_w s j) q) ∈ O ↔ q ∈ O
    rw [e2 q]

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_NbExt3 =====
section

/-!
# S4-EtPBC-A, M2 F8b + F9: surjectivity of base change in degree 0 for `π_* M_Y`

* `exists_affine_nbhd`: an affine noetherian neighbourhood of `s` (S locally noetherian);
* `exists_sec_vv`: a section `z` over some `Y_j` with `cval z ∘ ysj j = vv b` (induction over the finitely many values,
  each step `exists_clopen_nbhd` + `exists_indicator` + restriction);
* **`bcSurj_push_const`**: `BCSurj Λ (qV K gK) s 0 (π_* M_Y)` for `π : Y ⟶ P¹_S` finite.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.Supp RamanujanPetersson.EtPBC.Z3

universe u

variable {Λ : Type u} [CommRing Λ] (K : Type u) [Field K] {S : Scheme.{u}} (gK : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) {Y : Scheme.{u}} (π : Y ⟶ PV K gK) {M : ModuleCat.{u} Λ}

/-- **A section over a neighbourhood realising the value function `vv b`.** -/
theorem exists_sec_vv [IsIso (s.pt ≫ gK)] [IsFinite π] [IsLocallyNoetherian S]
    (b : unitSh Λ (fib (qV K gK) s) ⟶ (pull (fibι (qV K gK) s) Λ).obj ((push π Λ).obj (constSh Λ Y M))) :
    ∃ (j : Nbhd s) (z : (constSh Λ Y M).obj.obj (op ((etPull π).obj ((etPull (qV K gK)).obj j.1)))),
      ∀ q, cval z (ysj (qV K gK) s π j q) = vv (fibι (qV K gK) s) π b q := by
  classical
  have hlc := isLocallyConstant_vv (fibι (qV K gK) s) π b
  have : CompactSpace ↑(pullback π (fibι (qV K gK) s)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd π (fibι (qV K gK) s) ≫ pullback.snd (qV K gK) s.pt)
  have hfin := hlc.range_finite
  have key : ∀ T : Finset M, ∃ (j : Nbhd s) (_ : IsAffine j.1.left) (_ : IsNoetherianRing Γ(j.1.left, ⊤))
      (z : (constSh Λ Y M).obj.obj (op ((etPull π).obj ((etPull (qV K gK)).obj j.1)))),
      ∀ q, cval z (ysj (qV K gK) s π j q) =
        if vv (fibι (qV K gK) s) π b q ∈ T then vv (fibι (qV K gK) s) π b q else 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      obtain ⟨j, hA, hN⟩ := exists_affine_nbhd s
      exact ⟨j, hA, hN, 0, fun q => (cval_zero _).trans (if_neg (Finset.notMem_empty _)).symm⟩
    | @insert m T hm ih =>
      obtain ⟨j, hA, hN, z, hz⟩ := ih
      obtain ⟨j', a, hA', hN', C, hC, hCq⟩ := exists_clopen_nbhd K gK s π j
        {q | vv (fibι (qV K gK) s) π b q = m} (hlc.isClopen_fiber m)
      obtain ⟨c, hc⟩ := exists_indicator (T := (etPull π).obj ((etPull (qV K gK)).obj j'.1)) C hC m
      refine ⟨j', hA', hN', ((constSh Λ Y M).obj.map ((etPull π).map ((etPull (qV K gK)).map a.1)).op).hom z + c,
        fun q => ?_⟩
      have hy : ((etPull π).map ((etPull (qV K gK)).map a.1)).left (ysj (qV K gK) s π j' q) =
          ysj (qV K gK) s π j q := congrArg (fun φ => φ.base q) (ysj_map (qV K gK) s π a)
      have hci : C.indicator (fun _ => m) (ysj (qV K gK) s π j' q) =
          if vv (fibι (qV K gK) s) π b q = m then m else 0 := by
        by_cases h : vv (fibι (qV K gK) s) π b q = m
        · exact (Set.indicator_of_mem ((hCq q).2 h) _).trans (if_pos h).symm
        · exact (Set.indicator_of_notMem (fun h' => h ((hCq q).1 h')) _).trans (if_neg h).symm
      refine ((cval_add _ _ _).trans (congrArg₂ (· + ·) ((cval_map _ _ _).trans ((congrArg (cval z) hy).trans (hz q)))
        ((hc _).trans hci))).trans ?_
      by_cases h : vv (fibι (qV K gK) s) π b q = m
      · have h2 : vv (fibι (qV K gK) s) π b q ∉ T := fun h' => hm (h ▸ h')
        rw [if_pos h, if_neg h2, zero_add, if_pos (Finset.mem_insert.2 (Or.inl h)), h]
      · rw [if_neg h, add_zero]
        exact if_congr (by rw [Finset.mem_insert, or_iff_right h]) rfl rfl
  obtain ⟨j, -, -, z, hz⟩ := key hfin.toFinset
  exact ⟨j, z, fun q => (hz q).trans (if_pos (hfin.mem_toFinset.2 ⟨q, rfl⟩))⟩

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_NInd =====
section

/-!
# S4-EtPBC-A, M4(C,D,F): noetherian induction on supports

* `FGT Λ F`: `F` is a quotient of a finite sum `∐ Λ[W j]` with every `(W j).left` affine;
* `fgt_image`, `fgt_quotCut`; `mono_lift_of_stalk` (a stalkwise criterion for `biprod.lift a b` to be mono);
  `bcSurj_of_isZero`;
* `GenStep Λ g s`: the generic step: an `FGT` sheaf `F` with stalks zero off a nonempty closed `Z` maps to a sheaf
  with `BCSurj 0`, injectively on stalks over `V ∩ Z ≠ ∅` for some open `V`;
* **`embC_of_fgt`**: under `GenStep` (and `P` noetherian) every `FGT` sheaf embeds into a sheaf with `BCSurj 0`;
* **`bcSurj_zero_all`**: under `GenStep`, `BCSurj 0` holds for every sheaf (`P_s` compact, `g` universally closed).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- **Noetherian induction**: every `FGT` sheaf embeds into a sheaf with `BCSurj 0`. -/
theorem embC_of_fgt [NoetherianSpace P] (hE : GenStep Λ g s) (F : EtSh Λ P) (hF : FGT Λ F) : EmbC g s F := by
  suffices h : ∀ Z : Closeds P, ∀ F : EtSh Λ P, FGT Λ F → (∀ x ∉ (Z : Set P), IsZero (stalk Λ F x)) → EmbC g s F from
    h ⊤ F hF fun x hx => absurd (Set.mem_univ x) hx
  refine fun Z => WellFoundedLT.induction
    (motive := fun Z : Closeds P => ∀ F : EtSh Λ P, FGT Λ F → (∀ x ∉ (Z : Set P), IsZero (stalk Λ F x)) → EmbC g s F) Z ?_
  intro Z ih F hF hZ
  by_cases hne : (Z : Set P).Nonempty
  · obtain ⟨V, H, φ, hH, ⟨x₀, hx₀V, hx₀Z⟩, hmono⟩ := hE Z Z.isClosed hne F hF hZ
    let Z' : Closeds P := ⟨(Z : Set P) \ (V : Set P), Z.isClosed.sdiff V.isOpen⟩
    have hlt : Z' < Z := SetLike.lt_iff_le_and_exists.2 ⟨fun x hx => hx.1, x₀, hx₀Z, fun h => h.2 hx₀V⟩
    have hQ : EmbC g s (quotCut Λ V F) := by
      refine ih Z' hlt _ (fgt_quotCut V hF) fun x hx => ?_
      by_cases hxV : x ∈ V
      · exact isZero_stalk_quotCut V F (geomPtAt x) (mem_center_geomPtAt (W := (V : Set P)) hxV)
      · have hxZ : x ∉ (Z : Set P) := fun h => hx ⟨h, hxV⟩
        have := isIso_stalk_quotCutπ V F (geomPtAt x) (not_mem_center_geomPtAt (W := (V : Set P)) hxV)
        exact (hZ x hxZ).of_iso (asIso (((geomPtAt x).stalkF Λ).map (quotCutπ Λ V F))).symm
    have hm : Mono (biprod.lift φ (quotCutπ Λ V F)) := by
      apply mono_lift_of_stalk
      intro x
      by_cases hxV : x ∈ V
      · left
        by_cases hxZ : x ∈ (Z : Set P)
        · exact hmono x ⟨hxV, hxZ⟩
        · exact (hZ x hxZ).mono _
      · right
        exact @IsIso.mono_of_iso _ _ _ _ _
          (isIso_stalk_quotCutπ V F (geomPtAt x) (not_mem_center_geomPtAt (W := (V : Set P)) hxV))
    exact @embC_of_mono _ _ _ _ g s _ _ _ (biprod.lift φ (quotCutπ Λ V F)) hm (embC_of_bcSurj g s hH) hQ
  · have h0 : IsZero F := (isZero_iff_stalk Λ F).2 fun x => hZ x fun h => hne ⟨x, h⟩
    exact embC_of_bcSurj g s (bcSurj_of_isZero g s h0)

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Rel5 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Rel5): the relation over all points outside a cofinite open

REL PLAN v2 (s126), file R3, index plumbing. For a cofinite open `U₀` whose outside points are closed, the points
`x ∉ U₀`, `x ≠ z₀` form a finite index type with relation nbhds `opEt (U₀ ∪ {x})` and opens `{x}ᶜ`:
* **`mem_opEt_hom`**: `(opEt U).hom v ∈ U`;
* **`term_mem_cofinite`**: the term at `z₀` lies in `G` when every point `x ∉ U₀`, `x ≠ z₀` is good or its term
  (for ANY open `V = U₀ ∪ {x}`) is `0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} (U₀ : P.Opens)

/-- **The term at `z₀` lies in `G`** when every other point outside the cofinite open `U₀` is good or has a zero
term. -/
theorem term_mem_cofinite {F : EtSh Λ P} (G : AddSubgroup (Ext.{u} (freeSh Λ (etId P)) F 2)) (good : P → Prop)
    (hG : ∀ x, good x → ∀ β, IsLoc Λ F x β → β ∈ G) (κ : Ext.{u} (freeSh Λ (opEt U₀)) F 1)
    {S₀ : P.Etale} {z₀ : P} {Uz₀ : P.Opens} (h₀ : U₀ ≤ Uz₀) (hz₀ : ∀ x : P, x ∈ Uz₀ ↔ x ≠ z₀)
    (hS₀ : Subsingleton ((geomPtAt z₀).point.fiber.obj S₀)) (hN₀ : Nonempty ((geomPtAt z₀).point.fiber.obj S₀))
    (hR₀ : ∀ v : S₀.left, S₀.hom v ∈ U₀ ∨ S₀.hom v = z₀)
    (hfin : ((U₀ : Set P)ᶜ).Finite) (hcl : ∀ x : P, x ∉ U₀ → IsClosed ({x} : Set P)) (hzU : z₀ ∉ U₀)
    (hk : ∀ x : P, x ∉ U₀ → x ≠ z₀ → good x ∨ ∀ (V : P.Opens) (_hV : ∀ y : P, y ∈ V ↔ y ∈ U₀ ∨ y = x)
      (Uz : P.Opens) (h : U₀ ≤ Uz) (hz : ∀ y : P, y ∈ Uz ↔ y ≠ x)
      (hS : Subsingleton ((geomPtAt x).point.fiber.obj (opEt V)))
      (hN : Nonempty ((geomPtAt x).point.fiber.obj (opEt V)))
      (hR : ∀ v : (opEt V).left, (opEt V).hom v ∈ U₀ ∨ (opEt V).hom v = x),
      (locC_shortExact (Λ := Λ) (opEt V) h x hz hS hN hR).extClass.comp
        ((Ext.mk₀ (freeMap Λ (prT (opEt V) (opEt U₀)))).comp κ (zero_add 1)) (show 1 + 1 = 2 from rfl) = 0) :
    (locC_shortExact (Λ := Λ) S₀ h₀ z₀ hz₀ hS₀ hN₀ hR₀).extClass.comp
      ((Ext.mk₀ (freeMap Λ (prT S₀ (opEt U₀)))).comp κ (zero_add 1)) (show 1 + 1 = 2 from rfl) ∈ G := by
  classical
  have hfin' : Set.Finite {x : P | x ∉ U₀ ∧ x ≠ z₀} := hfin.subset fun x hx => hx.1
  have : Fintype {x : P // x ∉ U₀ ∧ x ≠ z₀} := hfin'.fintype
  have hopen : ∀ j : {x : P // x ∉ U₀ ∧ x ≠ z₀}, IsOpen ((U₀ : Set P) ∪ {j.1}) := by
    intro j
    rw [← isClosed_compl_iff, Set.compl_union]
    have hf : ((U₀ : Set P)ᶜ ∩ {j.1}ᶜ).Finite := hfin.subset Set.inter_subset_left
    rw [← Set.biUnion_of_singleton ((U₀ : Set P)ᶜ ∩ {j.1}ᶜ)]
    exact hf.isClosed_biUnion fun x hx => hcl x hx.1
  let V : {x : P // x ∉ U₀ ∧ x ≠ z₀} → P.Opens := fun j => ⟨(U₀ : Set P) ∪ {j.1}, hopen j⟩
  let Uz : {x : P // x ∉ U₀ ∧ x ≠ z₀} → P.Opens := fun j => ⟨{j.1}ᶜ, (hcl j.1 j.2.1).isOpen_compl⟩
  have hV : ∀ (j : {x : P // x ∉ U₀ ∧ x ≠ z₀}) (y : P), y ∈ V j ↔ y ∈ U₀ ∨ y = j.1 := fun _ _ => Iff.rfl
  have h : ∀ j : {x : P // x ∉ U₀ ∧ x ≠ z₀}, U₀ ≤ Uz j := fun j y hy hyj => j.2.1 (hyj ▸ hy)
  have hz : ∀ (j : {x : P // x ∉ U₀ ∧ x ≠ z₀}) (y : P), y ∈ Uz j ↔ y ≠ j.1 := fun _ _ => Iff.rfl
  have hD : ∀ j : {x : P // x ∉ U₀ ∧ x ≠ z₀}, Subsingleton ((geomPtAt j.1).point.fiber.obj (opEt (V j))) :=
    fun j => subsingleton_fib_opEt (V j) j.1
  have hDn : ∀ j : {x : P // x ∉ U₀ ∧ x ≠ z₀}, Nonempty ((geomPtAt j.1).point.fiber.obj (opEt (V j))) :=
    fun j => nonempty_fib_opEt (V j) j.1 (Or.inr rfl)
  have hDr : ∀ (j : {x : P // x ∉ U₀ ∧ x ≠ z₀}) (v : (opEt (V j)).left),
      (opEt (V j)).hom v ∈ U₀ ∨ (opEt (V j)).hom v = j.1 :=
    fun j v => (hV j _).1 (mem_opEt_hom (V j) v)
  have hU : ∀ x : P, x ∈ U₀ ↔ x ≠ z₀ ∧ ∀ j : {x : P // x ∉ U₀ ∧ x ≠ z₀}, x ≠ j.1 := by
    intro x
    constructor
    · intro hx
      exact ⟨fun e => hzU (e ▸ hx), fun j e => j.2.1 (e ▸ hx)⟩
    · rintro ⟨h1, h2⟩
      by_contra hx
      exact h2 ⟨x, hx, h1⟩ rfl
  exact term_mem_option U₀ G good hG κ h₀ hz₀ hS₀ hN₀ hR₀ (fun j => opEt (V j)) (fun j => j.1)
    Subtype.val_injective (fun j => j.2.2) hU hD hDn hDr Uz h hz
    (fun j => (hk j.1 j.2.1 j.2.2).imp_right fun hb => hb (V j) (hV j) (Uz j) (h j) (hz j) (hD j) (hDn j) (hDr j))

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gen1 =====
section

/-!
# S4-EtPBC-A, O2 Gen1: point classes along maps, chart facts on `P¹`

* `ptCls_comp`: `PtCls c R x → PtCls c T (x ∘ Λ[r])`; `compSub r G` (`x ↦ x ∘ Λ[r]` pulled back subgroup).
* `isClosed_of_isLoc`: an `IsLoc` point is closed.
* chart facts for any open immersion `c : A¹ ⟶ P¹`: `chart_ne_genPt`, `chart_hclA`, `chart_hGal`, `chart_hclc`,
  `A1_hpt`, `exists_A1pt_of_mem_range`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.CurveHn RamanujanPetersson.EtCompact.PushStk RamanujanPetersson.EtCompact.PushBC

section PtCompSub

end PtCompSub

section CompSub

variable {Λ : Type} [CommRing Λ] {P : Scheme.{0}}

theorem mem_compSub {R T : P.Etale} (r : R ⟶ T) (G : AddSubgroup (Ext.{0} (freeSh Λ (etId P)) (freeSh Λ T) 2))
    (x : Ext.{0} (freeSh Λ (etId P)) (freeSh Λ R) 2) :
    x ∈ compSub r G ↔ x.comp (Ext.mk₀ (freeMap Λ r)) (add_zero 2) ∈ G := Iff.rfl

end CompSub

section Chart

end Chart

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

/-- **Base change is surjective on germs in degrees `≥ 3`** for the `P¹`-bundle at a rational point. -/
theorem p1Bundle_bcSurj_add_three (q : ℕ) (G : EtSh Λ (pullback (P1.toSpecK K) gS)) :
    BCSurj Λ (pullback.snd (P1.toSpecK K) gS) s (q + 3) G :=
  bcSurj_of_subsingleton _ s (q + 3) G
    ⟨fun a b => (fib_H_add_three_eq_zero K l hl m hΛ gS s _ q a).trans
      (fib_H_add_three_eq_zero K l hl m hΛ gS s _ q b).symm⟩

end P1Vanish3

end RamanujanPetersson.EtPBC

end

end


