-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_ExistsFlagModelBaseMetric
-- name    : Development_AutomorphicSpectrum_Statements_MetricStatements_ExistsFlagModelBaseMetric
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T09:23:10.014958+00:00
-- url     : https://prove2.me/theorems/5d217953-bdec-5ce8-a218-999a4472fcdf
-- title:
--   Exists Flag Model Base Metric
-- statement:
--   Definitions and structural lemmas for Exists Flag Model Base Metric, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Statements/MetricStatements/ExistsFlagModelBaseMetric.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_GlueApplyOfNotInFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_IsCtrOf_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap)
section Relations
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S S' S'' : Finset ℕ}
  {Ω Ω' Ω'' : Type} [Field Ω] [Field Ω'] [Field Ω''] {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']
  {J : K → Type} {J' : K' → Type} {J'' : K'' → Type} {x : (Σ k, J k) → Ω} {x' : (Σ k, J' k) → Ω'}
  {x'' : (Σ k, J'' k) → Ω''}
def HodgeOver (A' : HodgeCpt Y S' x') (A : HodgeCpt Y S x) (h : A'.X ⟶ A.X) (i : Ω →+* Ω') (j : A.Li →+ A'.Li) :
    Prop :=
  GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ h i ∧ A'.f = h ≫ A.f ∧ A'.cst = i.comp A.cst ∧ IsExtOver i j ∧
    ∀ w, (A'.M.pt (j w)).left ≫ A'.m.φ = spMap (dualMap i) ≫ (A.M.pt w).left ≫ A.m.φ
abbrev WBases (A : HodgeCpt Y S x) : Type := ∀ τ : CMType H, Module.Basis (Fin D.p) Ω (A.Vgen (.inl τ))
abbrev OmBases (A : HodgeCpt Y S x) : Type :=
  ∀ τ : CMType H, Module.Basis (Fin D.q) Ω (Module.Dual Ω (A.Vgen (.inr τ)))
def BasesOver {A' : HodgeCpt Y S' x'} {A : HodgeCpt Y S x} (i : Ω →+* Ω') (j : A.Li →+ A'.Li)
    (bW' : WBases A') (bO' : OmBases A') (bW : WBases A) (bO : OmBases A) : Prop :=
  (∀ τ a, (bW' τ a : A'.Li) = j (bW τ a)) ∧
    ∀ τ a (v : A.Vgen (.inr τ)) (v' : A'.Vgen (.inr τ)), (v' : A'.Li) = j v → bO' τ a v' = i (bO τ a v)
def HasSncBoundary [CharZero Ω] [∀ k, Fintype (J k)] (A : HodgeCpt Y S x) (n : ℕ) : Prop :=
  ∃ bd : Ideal (MRing J), Cmp.IsSncModel x n bd ∧
    ∀ (z : Spec (CommRingCat.of ℂ) ⟶ A.X) w, CoordsAt A.ξ x z w → (w ∈ mcPts bd ↔ ¬ A.Interior z)
variable {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}
def FlagTie.IsTotal (tie : FlagTie M 𝔐) (𝔐' : HodgeCpt Y S y) (Fl : 𝔐'.Flag)
    (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Φ) : Prop :=
  (∃ (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li), HodgeOver 𝔐' 𝔐 pr (algebraMap M.Ω Φ) j ∧ 𝔐'.R = 𝔐.R ∧
    (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) ∧
    (∀ τ (k : Fin D.p), Fl.b (.inl τ) k = colFrame (fun a => j (tie.eW τ a)) (wBlock (M.g τ)) k) ∧
    ∀ τ (v : Fin D.q → 𝔐.Vgen (.inr τ)), (∀ a b, tie.eO τ a (v b) = if a = b then 1 else 0) →
      ∀ k : Fin D.q, Fl.b (.inr τ) k = colFrame (fun a => j (v a)) (omBlock (M.g τ))ᵀ⁻¹ k.rev) ∧
  Fl.RootLines xdeg e ∧ (∀ τ i, M.dy (τ, i) = -∑ k ∈ Finset.Iic i, xdeg (τ, k)) ∧
  ∀ τ i, (∏ k ∈ Finset.Iic i, e (τ, k)) * detFac D.p i (M.g τ) *
    (M.blk (τ, i)).elim (algebraMap M.Ω Φ (M.lam (τ, i))) (fun _ => 1) = 1
end Relations
def BaseMetric.IsConj {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
    {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) : Prop :=
  (∀ x x', SameOrbit (BM.Rb.lift x' x') (fun q => starRingEnd ℂ (BM.Rb.lift x x q)) →
    (x' ∈ ReciprocityTheory.AnForm.P.bdry BM.s ↔ x ∈ ReciprocityTheory.AnForm.P.bdry BM.s) ∧
      ReciprocityTheory.AnForm.P.rW BM.L BM.s x' = ReciprocityTheory.AnForm.P.rW BM.L BM.s x) ∧
  ∀ p, ∀ z ∈ mcPts (mCoordIdeal y), ∀ x, x ∉ ReciprocityTheory.AnForm.P.bdry BM.s →
    SameOrbit (basePart M.blk z) (BM.Rb.lift x x) → (BM.hom p).h (fun q => starRingEnd ℂ (z q)) = (BM.hom p).h z
def FlagModelExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω]
    (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀)
    (n d : ℕ) (bW : WBases 𝔐) (bO : OmBases 𝔐), IsArithVar (mCoordIdeal x₀) (n + 1) → 𝔐.IsCover d →
    ∃ (K : Type) (_ : Fintype K) (ι : K → Type) (_ : ∀ k, Fintype (ι k)) (Φ : Type) (_ : Field Φ)
      (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐₁ : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐₁)
      (κ : K₀ → NonPluckerBlocks M.blk) (v : (Σ k, J₀ k) → Σ k, baseIdx ι M.blk k) (φ : Ω →+* M.Ω) (π : 𝔐₁.X ⟶ 𝔐.X)
      (j : 𝔐.Li →+ 𝔐₁.Li) (𝔐' : HodgeCpt Y S y) (Fl : 𝔐'.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ)
      (e : CMType H × Fin (D.p + D.q) → Φ),
      (IsBlockMap κ v ∧ (∀ q, M.x (v q) = φ (x₀ q)) ∧ Function.Bijective φ ∧ IsIso π ∧ HodgeOver 𝔐₁ 𝔐 π φ j ∧
        𝔐₁.R = 𝔐.R ∧ BasesOver φ j tie.eW tie.eO bW bO) ∧
      (𝔐₁.IsCover d ∧ IsArithVar (mCoordIdeal M.x) (n + 1) ∧ ∀ m, HasSncBoundary 𝔐 m → HasSncBoundary 𝔐₁ m) ∧
      IsArithVar (mCoordIdeal y) (n + Fintype.card (CMType H) * (D.p.choose 2 + D.q.choose 2) + 1) ∧
      tie.IsTotal 𝔐' Fl xdeg e ∧ Fl.deg = d
def CoverExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S' : Finset ℕ)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ)
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ')
    (M : FlagModel y (CMType H) (D.p + D.q) D.p) (M' : FlagModel y' (CMType H) (D.p + D.q) D.p)
    (𝔐 : HodgeCpt Y S M.x) (𝔐' : HodgeCpt Y S' M'.x) (tie : FlagTie M 𝔐) (tie' : FlagTie M' 𝔐')
    (κ : NonPluckerBlocks M.blk → NonPluckerBlocks M'.blk) (v : (Σ k, baseIdx ι M.blk k) → Σ k, baseIdx ι' M'.blk k)
    (φ : M.Ω →+* M'.Ω) (h : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (d d' : ℕ),
    IsBlockMap κ v → (∀ q, M'.x (v q) = φ (M.x q)) → HodgeOver 𝔐' 𝔐 h φ j →
    BasesOver φ j tie'.eW tie'.eO tie.eW tie.eO → 𝔐.IsCover d → 𝔐'.IsCover d' →
    ∃ Cv : FlagCover M' M, Cv.κ = κ ∧ Cv.v = v ∧ Cv.φ = φ ∧ d * Cv.deg = d'
def BaseMetricExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ)
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ)
    (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐) (d : ℕ),
    1 ≤ D.p → 1 ≤ D.q → 𝔐.IsCover d → HasSncBoundary 𝔐 (Fintype.card (CMType H) * D.p * D.q) →
    ∃ BM : BaseMetric M (Fintype.card (CMType H) * D.p * D.q), BM.IsHodge tie ∧ BM.IsConj
def TieSt : Prop := FlagModelExists ∧ CoverExists ∧ BaseMetricExists
section Tests
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S S' S'' : Finset ℕ}
  {Ω Ω' Ω'' : Type} [Field Ω] [Field Ω'] [Field Ω''] {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']
  {J : K → Type} {J' : K' → Type} {J'' : K'' → Type} {x : (Σ k, J k) → Ω} {x' : (Σ k, J' k) → Ω'}
  {x'' : (Σ k, J'' k) → Ω''}
theorem HodgeOver.trans {A'' : HodgeCpt Y S'' x''} {A' : HodgeCpt Y S' x'} {A : HodgeCpt Y S x} {h' : A''.X ⟶ A'.X}
    {h : A'.X ⟶ A.X} {i' : Ω' →+* Ω''} {i : Ω →+* Ω'} {j' : A'.Li →+ A''.Li} {j : A.Li →+ A'.Li}
    (a : HodgeOver A'' A' h' i' j') (b : HodgeOver A' A h i j) :
    HodgeOver A'' A (h' ≫ h) (i'.comp i) (j'.comp j) := by
  have e : dualMap (i'.comp i) = (dualMap i').comp (dualMap i) := RingHom.ext fun a => by
    ext <;> simp [dualMap]
  refine ⟨?_, by rw [a.2.1, b.2.1, Category.assoc], by rw [a.2.2.1, b.2.2.1, RingHom.comp_assoc],
    ⟨fun t w => ?_, fun n v hv => a.2.2.2.1.2 n _ (b.2.2.2.1.2 n v hv)⟩, fun w => ?_⟩
  · show _ = Spec.map (CommRingCat.ofHom i ≫ CommRingCat.ofHom i') ≫ _
    rw [← Category.assoc, a.1, Category.assoc, b.1, Spec.map_comp, Category.assoc]
  · show j' (j (t • w)) = i' (i t) • j' (j w)
    rw [b.2.2.2.1.1, a.2.2.2.1.1]
  · show (A''.M.pt (j' (j w))).left ≫ _ = _
    rw [a.2.2.2.2, b.2.2.2.2, e]
    show _ = Spec.map (CommRingCat.ofHom (dualMap i) ≫ CommRingCat.ofHom (dualMap i')) ≫ _
    rw [Spec.map_comp, Category.assoc]
variable {A' : HodgeCpt Y S' x'} {A : HodgeCpt Y S x} {h : A'.X ⟶ A.X} {i : Ω →+* Ω'} {j : A.Li →+ A'.Li}
example (τ : CMType H) (a : Fin D.q) :
    HodgeCpt.rootIdx D (τ, ⟨D.p + a, by omega⟩) = ⟨.inr τ, a.rev⟩ := by
  have : ¬ D.p + (a : ℕ) < D.p := by omega
  simp only [HodgeCpt.rootIdx, this, dif_neg, not_false_eq_true]
  congr 1
  exact Fin.ext (by simp [Fin.rev]; omega)
variable {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
example (xdeg : Unit × Fin 2 → Bool → ℤ)
    (h : ∀ i, (FlagEx.MH (![1, 1, 0] : Fin 3 → ℚ) rfl (Or.inl one_ne_zero)).dy ((), i) =
      -∑ k ∈ Finset.Iic i, xdeg ((), k)) :
    (xdeg ((), 0) false = 1 ∧ xdeg ((), 0) true = -1) ∧ xdeg ((), 1) false = 0 ∧ xdeg ((), 1) true = 1 := by
  have hb : ∀ p, FlagEx.blkH p ≠ some false := fun p h => by simpa using (FlagEx.blkH_some h).2
  have ht : ¬ ∀ p, FlagEx.blkH p ≠ some true := fun h => h ((), 0) rfl
  let M := FlagEx.MH (![1, 1, 0] : Fin 3 → ℚ) rfl (Or.inl one_ne_zero)
  have a₀ := (show M.dy ((), 0) false = -1 from dif_pos hb).symm.trans (congrFun (h 0) false)
  have a₁ := (show M.dy ((), 0) true = 1 from (dif_neg ht).trans (if_pos rfl)).symm.trans (congrFun (h 0) true)
  have b₀ := (show M.dy ((), 1) false = -1 from dif_pos hb).symm.trans (congrFun (h 1) false)
  have b₁ := (show M.dy ((), 1) true = 0 from (dif_neg ht).trans (if_neg (by decide))).symm.trans
    (congrFun (h 1) true)
  have e₀ : Finset.Iic (0 : Fin 2) = {0} := by decide
  have e₁ : Finset.Iic (1 : Fin 2) = {0, 1} := by decide
  simp only [e₀, e₁, Finset.sum_singleton, Pi.neg_apply, Finset.sum_pair (show (0 : Fin 2) ≠ 1 by decide),
    Pi.add_apply] at a₀ a₁ b₀ b₁
  omega
variable {Ψ : Type} {N j n : ℕ} {M : FlagModel y Ψ N j}
end Tests
section Chain
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S S' : Finset ℕ}
  {Ω : Type} [Field Ω] [CharZero Ω] {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]
  {x₀ : (Σ k, J₀ k) → Ω}
end Chain
end GlobalTheory.CompanionTheory.Ar.PB


