-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_168
-- name    : RPLib_FX_EtPBC_168
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:00:12.106078+00:00
-- url     : https://prove2.me/theorems/0ebef9b1-a77d-59c7-a10c-c2e8f723422c
-- title:
--   Proper base change for the projective line, library file 168
-- statement:
--   File 168 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovHat3`: S4-EtPBC-A, R4-T2 (A2c-3c): structure maps of the completed charts and the localization property
--   * `S4.Def_RP_EtPBC_A_CovHat11`: S4-EtPBC-A, R4-T2 (A2c-3h): the level reductions of the completed overlap
--   * `S4.Def_RP_EtPBC_A_CovFib`: S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover
--   * `S4.Def_RP_EtPBC_A_O2T9b`: S4-EtPBC-A, O2 S6a (O2T9b): the residual of a one-point class is a one-point class with EMPTY fibre
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_112
import Definitions.Def_RPLib_FX_EtPBC_160
import Definitions.Def_RPLib_FX_EtPBC_161

/-!
# Proper base change for the projective line, library file 168

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovHat3`: S4-EtPBC-A, R4-T2 (A2c-3c): structure maps of the completed charts and the localization property
* `S4.Def_RP_EtPBC_A_CovHat11`: S4-EtPBC-A, R4-T2 (A2c-3h): the level reductions of the completed overlap
* `S4.Def_RP_EtPBC_A_CovFib`: S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover
* `S4.Def_RP_EtPBC_A_O2T9b`: S4-EtPBC-A, O2 S6a (O2T9b): the residual of a one-point class is a one-point class with EMPTY fibre
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

/-- **`Ê = Ê₁[1/t₁]`.** -/
theorem aw_hψ₁ : IsAwayMap (hψ₁ C H hts) (β₁ C H hφ₀ hu₀ t₁) := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨a, b, x, hx, h1, h2⟩ := (mem_hE C H hts y).1 hy
    have hinvb : jL₀ C (tFm C) ^ b * liftN₀ C hφ₀ hu₀ (φ₁ t₁) ^ b = 1 := by
      rw [← mul_pow, liftN₀_inv C hts hφ₀ hu₀, one_pow]
    have hm : (liftN₀ C hφ₀ hu₀ (φ₁ t₁) ^ b * y.1, x.2) ∈ hE₁ C H := by
      refine (mem_hE₁ C H _).2 ⟨a + b, x, hx, ?_, rfl⟩
      show jL₀ C (tFm C ^ (a + b)) * (liftN₀ C hφ₀ hu₀ (φ₁ t₁) ^ b * y.1) = jL₀ C x.1
      simp only [pow_add, map_mul, map_pow] at h1 ⊢
      linear_combination (jL₀ C (tFm C) ^ a * y.1) * hinvb + h1
    refine ⟨b, ⟨_, hm⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
    · rfl
    · show jL₁ C (fB₁ C t₁) ^ b * y.2 = jL₁ C x.2
      rw [← h2, map_pow]
  · rintro ⟨z, hz⟩ h0
    have h01 : z.1 = 0 := congrArg (fun w : hE C H hts => (w : L₀ C × L₁ C).1) h0
    have h02 : jL₁ C z.2 = 0 := congrArg (fun w : hE C H hts => (w : L₀ C × L₁ C).2) h0
    obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (sFm C)) (L₁ C) z.2).1 h02
    refine ⟨m, Subtype.ext (Prod.ext ?_ ?_)⟩
    · show liftN₀ C hφ₀ hu₀ (φ₁ t₁) ^ m * z.1 = 0
      rw [h01, mul_zero]
    · show fB₁ C t₁ ^ m * z.2 = 0
      exact hm

end Hat3

end RamanujanPetersson.EtPBC.Cov

end

end

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

/-- **`θ ∘ ψ̂₁ = ψ₁ ∘ θ₁`.** -/
def θ_hψ₁ (k : ℕ) (z : hE₁ C H) : θ C H hts k (hψ₁ C H hts z) = (C k).ψ₁ (θ₁ C H k z) := by
  obtain ⟨d, x, hx, h1, h2⟩ := (mem_hE₁ C H _).1 z.2
  show ev₀ C hts k (z : L₀ C × ∀ k, (C k).E₁).1 = (C k).ψ₁ ((z : L₀ C × ∀ k, (C k).E₁).2 k)
  have e1 := congrArg (ev₀ C hts k) h1
  rw [map_mul, ev₀_jL₀, ev₀_jL₀, Pi.pow_apply, map_pow] at e1
  have e1' : (C k).u ^ d * ev₀ C hts k (z : L₀ C × ∀ k, (C k).E₁).1 = (C k).ψ₀ (x.1 k) := e1
  have e2 := ((mem_gam C H x).1 hx k).2.2
  have hud : (C k).u ^ d * (C k).ψ₁ ((C k).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁)) ^ d = 1 := by
    rw [← mul_pow, lhv hts (C k), one_pow]
  rw [h2]
  linear_combination (C k).ψ₁ ((C k).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁)) ^ d * e1' +
    (C k).ψ₁ ((C k).a₁ (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁)) ^ d * e2 -
    (ev₀ C hts k (z : L₀ C × ∀ k, (C k).E₁).1 - (C k).ψ₁ (x.2 k)) * hud

end Ov

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovFib =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover

For lift data `L : LiftD K gV π x q hx` of a fibre cover `q : T ⟶ Y_x`: the glued cover `dL L` of `Y_{V'}`
(`V' = Spec L.R'`), the lift `xL L` of `x`, and **`ψL L : U_x ⟶ T`** on `U_x = (dL L).glued ×_{Y_{V'}} Y_x`, glued
from the chart lifts `gW` (`g0`, `g1`; `overlap` on `Y₀₁`), with **`ψL_q`**: `ψL L ≫ q = pullback.snd`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN algKY algT CoverLift.cR CoverLift.aR CoverLift.c₀ CoverLift.c₁ CoverLift.c₀₁ CoverLift.a₀ CoverLift.a₁ CoverLift.a₀₁

universe u

variable {K : Type u} [Field K] {V : Scheme.{u}} {gV : V ⟶ Spec (CommRingCat.of K)} {Y : Scheme.{u}}
  {π : Y ⟶ PV K gV} {x : Spec (CommRingCat.of K) ⟶ V} [IsAffine V] [IsFinite π] {hx : x ≫ gV = 𝟙 _}
  {T : Scheme.{u}} {q : T ⟶ Yx K gV π x} [IsAffineHom q] (L : LiftD K gV π x q hx)

theorem ov_g0 : letI := algKV K gV;
    (cvL L).trans WalkingSpan.Hom.fst ≫ g0 L =
      gW L.θ₀ L.sθ₀ (wz L ≫ Spec.map (CommRingCat.ofHom L.ψ₀)) (ov_hk0 L) ≫ (hT0 (q := q)).fromSpec := by
  letI := algKV K gV
  rw [g0, ← Category.assoc, gW_comp]
  exact congrArg (· ≫ (hT0 (q := q)).fromSpec) (gW_congr L.θ₀ L.sθ₀ (ov_e0 L) _ _)

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T9b =====
section

/-!
# S4-EtPBC-A, O2 S6a (O2T9b): the residual of a one-point class is a one-point class with EMPTY fibre

* `PtCls Λ c hN hΛ T x`: `x = pcD c' ∘ Λ[s]` for an affine Dedekind presentation `Spec B` of a point `c (X = a)`;
* **`isLoc_free_res`**: a one-point class `β` at `z = c (X = a)` with coefficients `Λ[T]` (`T` separated, finite fibre)
  is `β' ∘ Λ[r]` modulo point classes, `r : R ⟶ T`, `β'` a one-point class at `z` for `Λ[R]` and `R` with EMPTY fibre
  over `z`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk RamanujanPetersson.EtPBC.EtDed

section PtCls

variable {k : Type} [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] {P : Scheme.{0}} (c : A1 k ⟶ P)
  [IsOpenImmersion c] {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0) (hΛ : ∀ x : Λ, N • x = 0)

variable (Λ) in
/-- **Point classes** with coefficients `Λ[T]`: `pcD c' ∘ Λ[s]` for an affine Dedekind presentation `Spec B` of a
point `c (X = a)` and `s : Spec B ⟶ T`. -/
def PtCls (T : P.Etale) (x : Ext.{0} (freeSh Λ (etId P)) (freeSh Λ T) 2) : Prop :=
  ∃ (a : k) (B : CommRingCat.{0}) (φ : CommRingCat.of k[X] ⟶ B) (_ : Etale (Spec.map φ ≫ c)) (Uz : P.Opens)
    (hUz : ∀ u : Spec B, (chEt c φ).hom u ∈ Uz ↔ φ.hom (X - C a) ∉ u.asIdeal)
    (hS : (locC Λ (chEt c φ) (le_refl Uz)).ShortExact) (s : chEt c φ ⟶ T) (c' : Λ),
    φ.hom.Etale ∧ IsDedekindDomain B ∧ φ.hom (X - C a) ≠ 0 ∧ (Ideal.span {φ.hom (X - C a)}).IsPrime ∧
    (∀ x : P, x ∈ Uz ↔ x ≠ c (A1pt k a)) ∧
    x = (pcD c φ a hN hΛ hUz hS c').comp (Ext.mk₀ (freeMap Λ s)) (add_zero 2)

end PtCls

section Emp

end Emp

section Res

end Res

end RamanujanPetersson.EtPBC.EtMV

end

end


