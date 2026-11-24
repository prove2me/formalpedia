-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:08:35.33464+00:00
-- url     : https://prove2.me/theorems/6ca08e58-06da-4643-b69c-bffc9c5fa26b
-- title:
--   Glob Aut
-- statement:
--   Definitions and structural lemmas for Glob Aut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/GlobAut.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.S
abbrev uMat {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
open MeasureTheory NumberField Matrix Finset IsDedekindDomain
open scoped TensorProduct InnerProductSpace ComplexOrder
abbrev Af (F : Type) [Field F] [NumberField F] : Type := FiniteAdeleRing (𝓞 F) F
section Lat
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
abbrev IntAf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Subring (E ⊗[F] Af F) :=
  Formalism.UG.tensInt (F := F) (Af F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)
def lamAf (L : Submodule (𝓞 E) (Fin n → E)) : Submodule (IntAf F E) (Fin n → E ⊗[F] Af F) :=
  Submodule.span (IntAf F E)
    (Set.range fun x : L => fun i => Formalism.UG.inclE (F := F) (Af F) ((x : Fin n → E) i))
end Lat
structure AutInst : Type 1 where
  F : Type
  E : Type
  [fF : Field F]
  [nF : NumberField F]
  [fE : Field E]
  [nE : NumberField E]
  [sE : StarRing E]
  [aFE : Algebra F E]
  cm : Formalism.BasicNotions.CMData F E
  n : ℕ

  J : Matrix (Fin n) (Fin n) E
  J_herm : Formalism.UG.IsHerm (starRingEnd E) J
  J_det : J.det ≠ 0

  L : Submodule (𝓞 E) (Fin n → E)
  L_span : Submodule.span E (L : Set (Fin n → E)) = ⊤
  L_fg : L.FG
  L_dual : ∀ x : Fin n → E, x ∈ L ↔
    ∀ y ∈ L, Formalism.UG.hform (starRingEnd E) J y x ∈ (algebraMap (𝓞 E) E).range

  ε : InfinitePlace F → Fin n → Bool
  φ : InfinitePlace F → (E →+* ℂ)
  φ_over : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a
  P : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ
  P_unit : ∀ v, IsUnit (P v)
  P_spec : ∀ v, (P v)ᴴ * J.map (φ v) * P v = Formalism.REAL.Jm (ε v)

  [topf : TopologicalSpace (Formalism.UG.UPts cm.sig J (Af F))]
  [topf_group : IsTopologicalGroup (Formalism.UG.UPts cm.sig J (Af F))]

  topf_open : ∀ g : ℕ, 1 ≤ g → IsOpen {x : Formalism.UG.UPts cm.sig J (Af F) |
    (x : GL (Fin n) (E ⊗[F] Af F)) ∈ Formalism.UG.stabGL (lamAf (F := F) L) ∧
      ∀ y ∈ lamAf (F := F) L, ∃ z ∈ lamAf (F := F) L,
        ((x : GL (Fin n) (E ⊗[F] Af F)) - 1 : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ y = (g : E ⊗[F] Af F) • z}
  topf_basis : ∀ U ∈ nhds (1 : Formalism.UG.UPts cm.sig J (Af F)), ∃ g : ℕ, 1 ≤ g ∧
    {x : Formalism.UG.UPts cm.sig J (Af F) |
      (x : GL (Fin n) (E ⊗[F] Af F)) ∈ Formalism.UG.stabGL (lamAf (F := F) L) ∧
      ∀ y ∈ lamAf (F := F) L, ∃ z ∈ lamAf (F := F) L,
        ((x : GL (Fin n) (E ⊗[F] Af F)) - 1 : Matrix (Fin n) (Fin n) (E ⊗[F] Af F)) *ᵥ y = (g : E ⊗[F] Af F) • z} ⊆ U
attribute [instance] AutInst.fF AutInst.nF AutInst.fE AutInst.nE AutInst.sE AutInst.aFE AutInst.topf
  AutInst.topf_group
namespace AutInst
variable (I : AutInst)
abbrev Gf : Type := Formalism.UG.UPts I.cm.sig I.J (Af I.F)
instance : MeasurableSpace I.Gf := borel _
instance : BorelSpace I.Gf := ⟨rfl⟩
abbrev Ginf : Type := ∀ v : InfinitePlace I.F, Formalism.REAL.UJ (I.ε v)
abbrev GA : Type := I.Ginf × I.Gf
abbrev fmat (x : I.Gf) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) :=
  ((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
abbrev Lf : Submodule (IntAf I.F I.E) (Fin I.n → I.E ⊗[I.F] Af I.F) := lamAf (F := I.F) I.L
def Kset : Set I.Gf := {x | (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf}
def Kg (g : ℕ) : Set I.Gf :=
  {x | x ∈ I.Kset ∧ ∀ y ∈ I.Lf, ∃ z ∈ I.Lf, (I.fmat x - 1) *ᵥ y = (g : I.E ⊗[I.F] Af I.F) • z}
def UnipMod (l : ℕ) (x : I.Gf) : Prop :=
  ∀ y ∈ I.Lf, ∃ z ∈ I.Lf, ((I.fmat x - 1) ^ I.n) *ᵥ y = (l : I.E ⊗[I.F] Af I.F) • z
def GFset : Set I.GA :=
  {x | ∃ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
    (∀ v, uMat (x.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
    I.fmat x.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))}
def muA (μf : Measure I.Gf) [SigmaFinite μf] : Measure I.GA :=
  (Measure.pi fun v => Formalism.REAL.muG (I.ε v)).prod μf
def IsFundDom (μ : Measure I.GA) (fund : Set I.GA) : Prop :=
  MeasurableSet fund ∧ (∀ y : I.GA, ∃ γ ∈ I.GFset, γ * y ∈ fund) ∧
    ∀ γ ∈ I.GFset, γ ≠ 1 → μ ((fun y => γ * y) '' fund ∩ fund) = 0
def rep (fund : Set I.GA) (y : I.GA) : I.GA := by
  classical
  exact if h : ∃ γ ∈ I.GFset, γ * y ∈ fund then h.choose * y else y
abbrev L2 (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA) : Type :=
  Lp ℂ 2 ((I.muA μf).restrict fund)
def ext {μf : Measure I.Gf} [SigmaFinite μf] {fund : Set I.GA} (Fv : I.L2 μf fund) : I.GA → ℂ :=
  fun y => (Fv : I.GA → ℂ) (I.rep fund y)
def IsRightReg (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) : Prop :=
  ∀ g Fv, ((R g Fv : I.L2 μf fund) : I.GA → ℂ) =ᵐ[(I.muA μf).restrict fund] fun x => I.ext Fv (x * g)
def IsRConv (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (φ : I.GA → ℂ)
    (T : I.L2 μf fund →L[ℂ] I.L2 μf fund) : Prop :=
  Integrable φ (I.muA μf) ∧ ∀ x y : I.L2 μf fund, ⟪x, T y⟫_ℂ = ∫ g, φ g * ⟪x, R g y⟫_ℂ ∂(I.muA μf)
def IsRConvF (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (e : I.Gf → ℂ)
    (T : I.L2 μf fund →L[ℂ] I.L2 μf fund) : Prop :=
  Integrable e μf ∧ ∀ x y : I.L2 μf fund, ⟪x, T y⟫_ℂ = ∫ g, e g * ⟪x, R (1, g) y⟫_ℂ ∂μf
def IsIsot (W : Submodule I.E (Fin I.n → I.E)) : Prop :=
  W ≠ ⊥ ∧ ∀ x ∈ W, ∀ y ∈ W, Formalism.UG.hform (starRingEnd I.E) I.J x y = 0
def InUnipRad {A : Type} [CommRing A] (s : A →+* A) (JA : Matrix (Fin I.n) (Fin I.n) A)
    (WA : Submodule A (Fin I.n → A)) (g : Matrix (Fin I.n) (Fin I.n) A) : Prop :=
  let perp : Set (Fin I.n → A) := {y | ∀ x ∈ WA, Formalism.UG.hform s JA x y = 0}
  (∀ x ∈ WA, (g - 1) *ᵥ x = 0) ∧ (∀ y ∈ perp, (g - 1) *ᵥ y ∈ WA) ∧ ∀ y, (g - 1) *ᵥ y ∈ perp
def NA (W : Submodule I.E (Fin I.n → I.E)) : Set I.GA :=
  {x | (∀ v, I.InUnipRad (starRingEnd ℂ) (I.J.map (I.φ v))
      (Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)))
      (I.P v * uMat (x.1 v) * (I.P v)⁻¹)) ∧
    I.InUnipRad (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)))
      (Submodule.span (I.E ⊗[I.F] Af I.F)
        ((fun w : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (w i)) '' (W : Set _)))
      (I.fmat x.2)}
def IsNQuotMeas (W : Submodule I.E (Fin I.n → I.E)) (ν : Measure I.GA) : Prop :=
  IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν (I.NA W)ᶜ = 0 ∧
    ∀ f : I.GA → ℂ, (∀ γ ∈ I.GFset ∩ I.NA W, ∀ y, f (γ * y) = f y) →
      ∀ n₀ ∈ I.NA W, ∫ m, f (m * n₀) ∂ν = ∫ m, f m ∂ν
def IsCuspFn (μ : Measure I.GA) (f : I.GA → ℂ) : Prop :=
  ∀ W : Submodule I.E (Fin I.n → I.E), I.IsIsot W → ∀ ν : Measure I.GA, I.IsNQuotMeas W ν →
    ∀ᵐ x ∂μ, ∫ m, f (m * x) ∂ν = 0
variable {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
def IsHilbTensor (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v))
    {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) : Prop :=
  (∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) ∧
    (∀ g x, σs g (tens x) = tens fun v => σ v (uMat (g v)) (x v)) ∧
    Dense (Submodule.span ℂ (Set.range tens) : Set Hs)
def HomS {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) : Submodule ℂ (Hs →L[ℂ] I.L2 μf fund) where
  carrier := {T | ∀ g : I.Ginf, T.comp (σs g) = (R (g, 1)).comp T}
  add_mem' := by
    intro a b ha hb g
    simp only [Set.mem_ofPred_eq] at *
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, ha g, hb g]
  zero_mem' := by
    intro g
    simp
  smul_mem' := by
    intro c a ha g
    simp only [Set.mem_ofPred_eq] at *
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, ha g]
def eHom {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) :
    Submodule ℂ (Hs →L[ℂ] I.L2 μf fund) :=
  (I.HomS σs μf fund R).map
    ((ContinuousLinearMap.compL ℂ Hs (I.L2 μf fund) (I.L2 μf fund) Re) :
      (Hs →L[ℂ] I.L2 μf fund) →ₗ[ℂ] (Hs →L[ℂ] I.L2 μf fund))
def Dcount {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) : ℕ :=
  Module.finrank ℂ (I.eHom σs μf fund R Re)
def vol (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA) : ℝ := ((I.muA μf) fund).toReal
def Dstar (d : ℝ) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA) (e : I.Gf → ℂ) : ℝ :=
  d * I.vol μf fund * (e 1).re
def convF (μf : Measure I.Gf) (a b : I.Gf → ℂ) : I.Gf → ℂ := fun x => ∫ y, a y * b (y⁻¹ * x) ∂μf
def IsPosType (e : I.Gf → ℂ) : Prop :=
  ∀ (m : ℕ) (x : Fin m → I.Gf) (c : Fin m → ℂ), 0 ≤ ∑ i, ∑ j, star (c i) * c j * e ((x i)⁻¹ * x j)
def IsAdmIdem (μf : Measure I.Gf) (g g₀ : ℕ) (e : I.Gf → ℂ) : Prop :=
  IsLocallyConstant e ∧ I.convF μf e e = e ∧ (∀ x, e x⁻¹ = star (e x)) ∧ I.IsPosType e ∧
    (∀ x, e x ≠ 0 → x ∈ I.Kset) ∧ (∀ x, ∀ k ∈ I.Kg g, ∀ k' ∈ I.Kg g, e (k * x * k') = e x) ∧
    ∀ x, e x ≠ 0 → I.UnipMod g₀ x
def f : ℕ := Module.finrank ℚ I.F
def rd : ℝ := |(discr I.E : ℝ)| ^ ((1 : ℝ) / (2 * (I.f : ℝ)))
def pAt (v : InfinitePlace I.F) : ℕ := (univ.filter fun a => I.ε v a = true).card
def qAt (v : InfinitePlace I.F) : ℕ := (univ.filter fun a => I.ε v a = false).card
end AutInst
structure RowsAut : Type 1 where
  I : AutInst
  μf : Measure I.Gf
  [haar : μf.IsHaarMeasure]
  [sf : SigmaFinite μf]
  fund : Set I.GA
  fund_spec : I.IsFundDom (I.muA μf) fund
  lam : InfinitePlace I.F → Fin I.n → ℝ
  H : InfinitePlace I.F → Type
  [hN : ∀ v, NormedAddCommGroup (H v)]
  [hI : ∀ v, InnerProductSpace ℂ (H v)]
  [hC : ∀ v, CompleteSpace (H v)]
  σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)
  w : ∀ v, H v
  Hs : Type
  [sN : NormedAddCommGroup Hs]
  [sI : InnerProductSpace ℂ Hs]
  [sC : CompleteSpace Hs]
  σs : I.Ginf → (Hs →L[ℂ] Hs)
  tens : (∀ v, H v) → Hs
  tens_spec : I.IsHilbTensor σ σs tens
  R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)
  R_spec : I.IsRightReg μf fund R
  g : ℕ
  g₀ : ℕ
  e : I.Gf → ℂ
  e_adm : I.IsAdmIdem μf g g₀ e
  Re : I.L2 μf fund →L[ℂ] I.L2 μf fund
  Re_spec : I.IsRConvF μf fund R e Re
attribute [instance] RowsAut.haar RowsAut.sf RowsAut.hN RowsAut.hI RowsAut.hC RowsAut.sN RowsAut.sI RowsAut.sC
def RowsAut.D (B : RowsAut) : ℕ := B.I.Dcount B.σs B.μf B.fund B.R B.Re
end Formalism.MainNotions.S


