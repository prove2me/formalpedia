-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_161
-- name    : RPLib_FX_EtPBC_161
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:57:41.648792+00:00
-- url     : https://prove2.me/theorems/1f3b1a8e-08dc-571d-b83e-7da82a77f320
-- title:
--   Proper base change for the projective line, library file 161
-- statement:
--   File 161 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovGl2`: S4-EtPBC-A, R4-T2 (G1c, part 2b): gluing finite etale chart algebras over `Y_{V'}`
--   * `S4.Def_RP_EtPBC_A_CovFib`: S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover
--   * `S4.Def_RP_EtPBC_A_CovSj`: S4-EtPBC-A, R4-T2 (G1e): making the lifted cover surjective
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_153

/-!
# Proper base change for the projective line, library file 161

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovGl2`: S4-EtPBC-A, R4-T2 (G1c, part 2b): gluing finite etale chart algebras over `Y_{V'}`
* `S4.Def_RP_EtPBC_A_CovFib`: S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover
* `S4.Def_RP_EtPBC_A_CovSj`: S4-EtPBC-A, R4-T2 (G1e): making the lifted cover surjective
-/

set_option autoImplicit false

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

section FinEt

variable [Module.Finite (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) E₀] [Module.Finite (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) E₁]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- **The glued cover is finite over `Y_{V'}`.** -/
instance isFinite_toBase : IsFinite (glD K gV π R' ψ₀ ψ₁ hψ₀ hψ₁ aw₀ aw₁).toBase := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) (covV K gV π R')]
  intro i
  rw [Scheme.Cover.pullbackHom,
    ← ((glD K gV π R' ψ₀ ψ₁ hψ₀ hψ₁ aw₀ aw₁).isPullback_natTrans_ι_toBase i).flip.isoPullback_inv_snd,
    MorphismProperty.cancel_left_of_respectsIso @IsFinite]
  exact isFinite_app K gV π R' ψ₀ ψ₁ hψ₀ hψ₁ aw₀ aw₁ i

end FinEt

section Et

variable [Algebra.Etale (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) E₀] [Algebra.Etale (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) E₁]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- **The glued cover is etale over `Y_{V'}`.** -/
instance etale_toBase : Etale (glD K gV π R' ψ₀ ψ₁ hψ₀ hψ₁ aw₀ aw₁).toBase := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Etale) (covV K gV π R')]
  intro i
  rw [Scheme.Cover.pullbackHom,
    ← ((glD K gV π R' ψ₀ ψ₁ hψ₀ hψ₁ aw₀ aw₁).isPullback_natTrans_ι_toBase i).flip.isoPullback_inv_snd,
    MorphismProperty.cancel_left_of_respectsIso @Etale]
  exact etale_app K gV π R' ψ₀ ψ₁ hψ₀ hψ₁ aw₀ aw₁ i

end Et

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

abbrev wz : letI := algKV K gV; PL L WalkingSpan.zero ⟶ Spec (CommRingCat.of L.E₀₁) := pullback.snd _ _

/-- `P_j ⟶ U_x ⟶ Y_x ⟶ Spec K`. -/
abbrev vL (j : WalkingSpan) : PL L j ⟶ Spec (CommRingCat.of K) :=
  pullback.fst _ _ ≫ pullback.snd (dL L).toBase (yxL L) ≫ sx K gV π x

theorem hv0 : letI := algKV K gV; w0 L ≫ Spec.map (CommRingCat.ofHom (rE (A := Γ(V, ⊤)) (B := Γ(Y, Yc K gV π 0)) (R' := L.R')
    (E := L.E₀))) = vL L WalkingSpan.left ≫ xL L := by
  letI := algKV K gV
  have key := pb_key (covV K gV π L.R') (dL L) (yxL L) WalkingSpan.left
  have e1 : Spec.map (CommRingCat.ofHom (rE (A := Γ(V, ⊤)) (B := Γ(Y, Yc K gV π 0)) (R' := L.R') (E := L.E₀))) =
      Spec.map (CommRingCat.ofHom (algebraMap (L.R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) L.E₀)) ≫ ch0 K gV π L.R' ≫
        pullback.snd _ _ := by
    rw [ch0, chY_snd, ← Spec.map_comp] <;> rfl
  rw [e1]
  refine ((reassoc_of% key) (pullback.snd _ _)).trans ?_
  simp only [vL, yxL, yxMap, Category.assoc, pullback.lift_snd] <;> rfl

theorem hv1 : letI := algKV K gV; w1 L ≫ Spec.map (CommRingCat.ofHom (rE (A := Γ(V, ⊤)) (B := Γ(Y, Yc K gV π 1)) (R' := L.R')
    (E := L.E₁))) = vL L WalkingSpan.right ≫ xL L := by
  letI := algKV K gV
  have key := pb_key (covV K gV π L.R') (dL L) (yxL L) WalkingSpan.right
  have e1 : Spec.map (CommRingCat.ofHom (rE (A := Γ(V, ⊤)) (B := Γ(Y, Yc K gV π 1)) (R' := L.R') (E := L.E₁))) =
      Spec.map (CommRingCat.ofHom (algebraMap (L.R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) L.E₁)) ≫ ch1 K gV π L.R' ≫
        pullback.snd _ _ := by
    rw [ch1, chY_snd, ← Spec.map_comp] <;> rfl
  rw [e1]
  refine ((reassoc_of% key) (pullback.snd _ _)).trans ?_
  simp only [vL, yxL, yxMap, Category.assoc, pullback.lift_snd] <;> rfl

theorem hk0 : letI := algKV K gV; RingHom.ker L.θ₀ ≤ RingHom.ker (εW (w0 L)) :=
  letI := algKV K gV; ker_le_εW L.χ' L.θ₀ L.kθ₀ (w0 L) (vL L WalkingSpan.left) (hv0 L)

theorem hk1 : letI := algKV K gV; RingHom.ker L.θ₁ ≤ RingHom.ker (εW (w1 L)) :=
  letI := algKV K gV; ker_le_εW L.χ' L.θ₁ L.kθ₁ (w1 L) (vL L WalkingSpan.right) (hv1 L)

/-- The lift on the chart over `Y₀`. -/
def g0 : PL L WalkingSpan.left ⟶ T := letI := algKV K gV; gW L.θ₀ L.sθ₀ (w0 L) (hk0 L) ≫ (hT0 (q := q)).fromSpec

/-- The lift on the chart over `Y₁`. -/
def g1 : PL L WalkingSpan.right ⟶ T := letI := algKV K gV; gW L.θ₁ L.sθ₁ (w1 L) (hk1 L) ≫ (hT1 (q := q)).fromSpec

theorem ov_e0 : letI := algKV K gV;
    (cvL L).trans WalkingSpan.Hom.fst ≫ w0 L = wz L ≫ Spec.map (CommRingCat.ofHom L.ψ₀) := by
  letI := algKV K gV
  exact (pullback.lift_snd _ _ _).trans (congrArg (pullback.snd _ _ ≫ ·) (ov_tr0 L))

theorem ov_e1 : letI := algKV K gV;
    (cvL L).trans WalkingSpan.Hom.snd ≫ w1 L = wz L ≫ Spec.map (CommRingCat.ofHom L.ψ₁) := by
  letI := algKV K gV
  exact (pullback.lift_snd _ _ _).trans (congrArg (pullback.snd _ _ ≫ ·) (ov_tr1 L))

theorem ov_hk0 : letI := algKV K gV;
    RingHom.ker L.θ₀ ≤ RingHom.ker (εW (wz L ≫ Spec.map (CommRingCat.ofHom L.ψ₀))) := by
  letI := algKV K gV
  rw [← ov_e0 L]
  exact ker_comp L.θ₀ _ (w0 L) (hk0 L)

theorem ov_hk1 : letI := algKV K gV;
    RingHom.ker L.θ₁ ≤ RingHom.ker (εW (wz L ≫ Spec.map (CommRingCat.ofHom L.ψ₁))) := by
  letI := algKV K gV
  rw [← ov_e1 L]
  exact ker_comp L.θ₁ _ (w1 L) (hk1 L)

theorem ov_glue : letI := algKV K gV;
    ∃ c : PL L WalkingSpan.zero ⟶ Spec (CommRingCat.of Γ(T, q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ (Yc K gV π 0 ⊓ Yc K gV π 1)))),
      gW L.θ₀ L.sθ₀ _ (ov_hk0 L) = c ≫ Spec.map (CommRingCat.ofHom (ψT0 K gV π x q)) ∧
      gW L.θ₁ L.sθ₁ _ (ov_hk1 L) = c ≫ Spec.map (CommRingCat.ofHom (ψT1 K gV π x q)) := by
  letI := algKV K gV
  exact gW_glue L.θ₀ L.sθ₀ L.θ₁ L.sθ₁ L.θ₀₁ L.ψ₀ L.ψ₁ (ψT0 K gV π x q) (ψT1 K gV π x q) L.cθ₀
    L.cθ₁ _ L.aw₀ (unitL0 L) (awpL0 L) (wz L) (ov_hk0 L) (ov_hk1 L)

/-- The chart lifts, indexed by `WalkingSpan`. -/
def gL : (j : WalkingSpan) → PL L j ⟶ T
  | none => (cvL L).trans WalkingSpan.Hom.fst ≫ g0 L
  | some WalkingPair.left => g0 L
  | some WalkingPair.right => g1 L

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovSj =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1e): making the lifted cover surjective

For a finite etale `ρ : U ⟶ Y'` the range is clopen; `ρs ρ : U ⨿ Z ⟶ Y'` with `Z` the complement of the range is
finite and surjective. If `m : S ⟶ Y'` has range inside the range of `ρ`, every lift `pullback ρ m ⟶ T` over `S`
extends to `pullback (ρs ρ) m ⟶ T` (**`exists_surj_ext`**). For the lifted charts, `range_yxL`: the range of
`yxL L` lies in the range of `(dL L).toBase` when `q` is surjective; **`exists_surj_L`**.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

universe u

section Surj

end Surj

section Lifted

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN algKY algT CoverLift.cR CoverLift.aR CoverLift.eR CoverLift.c₀ CoverLift.c₁ CoverLift.c₀₁ CoverLift.a₀ CoverLift.a₁ CoverLift.a₀₁ CoverLift.f₀ CoverLift.f₁ CoverLift.et₀ CoverLift.et₁

variable {K : Type u} [Field K] {V : Scheme.{u}} {gV : V ⟶ Spec (CommRingCat.of K)} {Y : Scheme.{u}}
  {π : Y ⟶ PV K gV} {x : Spec (CommRingCat.of K) ⟶ V} [IsAffine V] [IsFinite π] {hx : x ≫ gV = 𝟙 _}
  {T : Scheme.{u}} {q : T ⟶ Yx K gV π x} [IsAffineHom q] (L : LiftD K gV π x q hx)

theorem eqY0 : letI := algKV K gV;
    Spec.map (CommRingCat.ofHom (algebraMap (L.R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) L.E₀)) ≫
      chY K gV π L.R' (isAffineOpen_Yc K gV π 0) (struct_res K gV π 0) =
        (dL L).cover.f WalkingSpan.left ≫ (dL L).toBase := by
  letI := algKV K gV
  exact (Scheme.Cover.RelativeGluingData.ι_toBase (dL L) WalkingSpan.left).symm

theorem eqY1 : letI := algKV K gV;
    Spec.map (CommRingCat.ofHom (algebraMap (L.R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) L.E₁)) ≫
      chY K gV π L.R' (isAffineOpen_Yc K gV π 1) (struct_res K gV π 1) =
        (dL L).cover.f WalkingSpan.right ≫ (dL L).toBase := by
  letI := algKV K gV
  exact (Scheme.Cover.RelativeGluingData.ι_toBase (dL L) WalkingSpan.right).symm

end Lifted

end RamanujanPetersson.EtPBC.Cov

end

end


