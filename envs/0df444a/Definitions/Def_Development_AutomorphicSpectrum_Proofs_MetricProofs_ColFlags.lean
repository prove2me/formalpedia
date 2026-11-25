-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ColFlags
-- name    : Development_AutomorphicSpectrum_Proofs_MetricProofs_ColFlags
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T09:39:47.036352+00:00
-- url     : https://prove2.me/theorems/8b493543-531a-4e98-9fc6-77b326d95e1b
-- title:
--   Col Flags
-- statement:
--   Definitions and structural lemmas for Col Flags, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/ColFlags.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_ExistsFlagModelBaseMetric
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_CoordTieCompEquiv
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
namespace GlobalTheory.CompanionTheory.Ar.PB.FMX
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar.FlagBun
section Pure
variable (Ψ : Type) (p q : ℕ)
abbrev rk : Ψ ⊕ Ψ → ℕ := Sum.elim (fun _ => p) (fun _ => q)
abbrev StepIx : Type := Σ s : Ψ ⊕ Ψ, Fin (rk Ψ p q s)
def stepOf (r : Ψ × Fin (p + q)) : StepIx Ψ p q :=
  if h : (r.2 : ℕ) < p then ⟨.inl r.1, ⟨r.2, h⟩⟩
  else ⟨.inr r.1, ⟨r.2 - p, by have := r.2.2; show _ < q; omega⟩⟩
variable {Ψ p q}
def idx {K₀ : Type} (J₀ : K₀ → Type) (n : Ψ ⊕ Ψ → ℕ) : K₀ ⊕ StepIx Ψ p q → Type :=
  Sum.elim J₀ fun t => Fin ((t.2 : ℕ) + 1) → Fin (n t.1)
instance {K₀ : Type} (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (n : Ψ ⊕ Ψ → ℕ) (k : K₀ ⊕ StepIx Ψ p q) :
    Fintype (idx J₀ n k) := by
  rcases k with k | t
  · exact inferInstanceAs (Fintype (J₀ k))
  · exact inferInstanceAs (Fintype (Fin ((t.2 : ℕ) + 1) → Fin (n t.1)))
variable (Ψ p q) in
open Classical in

def blkF (K₀ : Type) (r : Ψ × Fin (p + q)) : Option (K₀ ⊕ StepIx Ψ p q) :=
  if IsProperStep (p + q) p r.2 then some (.inr (stepOf Ψ p q r)) else none
variable (Ω : Type) [Field Ω]
variable (p q) in

def gMat (τ : Ψ) : Matrix (Fin (p + q)) (Fin (p + q)) (GenField Ω (rk Ψ p q)) :=
  (Matrix.fromBlocks (genU Ω (rk Ψ p q) (.inr τ)) 0 0 (genU Ω (rk Ψ p q) (.inl τ))).submatrix
    (blockEquiv p q).symm (blockEquiv p q).symm
variable {Ω}
variable {n : Ψ ⊕ Ψ → ℕ} (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
def fMat (s : Ψ ⊕ Ψ) : Matrix (Fin (n s)) (Fin (rk Ψ p q s)) (GenField Ω (rk Ψ p q)) :=
  (A s).map (algebraMap Ω (GenField Ω (rk Ψ p q))) * genU Ω (rk Ψ p q) s
variable {K₀ : Type} {J₀ : K₀ → Type} (x₀ : (Σ k, J₀ k) → Ω)
def yv : (Σ k, idx (p := p) (q := q) J₀ n k) → GenField Ω (rk Ψ p q)
  | ⟨.inl k, i⟩ => algebraMap Ω _ (x₀ ⟨k, i⟩)
  | ⟨.inr t, J⟩ => ((fMat A t.1).submatrix J (Fin.castLE t.2.2)).det
def xv : (Σ k, idx (p := p) (q := q) J₀ n k) → Ω
  | ⟨.inl k, i⟩ => x₀ ⟨k, i⟩
  | ⟨.inr t, J⟩ => ((A t.1).submatrix J (Fin.castLE t.2.2)).det
variable [Fintype Ψ] [Fintype K₀] [∀ k, Fintype (J₀ k)]
def xb : (Σ k : NonPluckerBlocks (blkF Ψ p q K₀), baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀) k) → Ω :=
  fun r => xv A x₀ ⟨r.1.1, r.2⟩
variable (p q) in

def posOf : ∀ s : Ψ ⊕ Ψ, Fin (rk Ψ p q s) → Fin (p + q)
  | .inl _ => wEmb p q
  | .inr _ => omEmb p q
open Classical in

def aExt (s : Ψ ⊕ Ψ) : Matrix (Fin (n s)) (Fin (p + q)) Ω :=
  fun j a => ∑ l, if posOf p q s l = a then A s j l else 0
def coefF : (Σ k, idx (p := p) (q := q) J₀ n k) → Finset (Fin (p + q)) → Ω
  | ⟨.inl _, _⟩, _ => 0
  | ⟨.inr t, J⟩, I => if e : I.card = (t.2 : ℕ) + 1 then ((aExt A t.1).submatrix J (I.orderEmbOfFin e)).det else 0
def rkW (i : Fin (p + q)) : ℕ := min ((i : ℕ) + 1) p
def rkO (i : Fin (p + q)) : ℕ := (i : ℕ) + 1 - min ((i : ℕ) + 1) p
open Classical in

def twist (m : Ψ ⊕ Ψ → ℕ) (r : Ψ × Fin (p + q)) : K₀ ⊕ StepIx Ψ p q → ℤ
  | .inl _ => (rkW r.2 * m (.inl r.1) + rkO r.2 * m (.inr r.1) : ℕ)
  | .inr t =>
    -((if t.1 = .inl r.1 ∧ (t.2 : ℕ) + 1 = p ∧ p ≤ (r.2 : ℕ) + 1 then 1 else 0) +
      (if t.1 = .inr r.1 ∧ (t.2 : ℕ) + 1 = q ∧ (r.2 : ℕ) + 1 = p + q then 1 else 0))
end Pure
section Bundles
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω}
abbrev EE (A : HodgeCpt Y S x) : Type := A.Li × ∀ τ : CMType H, Module.Dual Ω (A.Vgen (.inr τ))
def inW (A : HodgeCpt Y S x) : A.Li →ₗ[Ω] EE A := LinearMap.inl Ω _ _
open Classical in

def inO (A : HodgeCpt Y S x) (τ : CMType H) : Module.Dual Ω (A.Vgen (.inr τ)) →ₗ[Ω] EE A :=
  (LinearMap.inr Ω _ _).comp (LinearMap.single Ω (fun τ : CMType H => Module.Dual Ω (A.Vgen (.inr τ))) τ)
def LL (A : HodgeCpt Y S x) : CMType H ⊕ CMType H → Lat A.ξ (EE A)
  | .inl τ => (A.V (.inl τ)).map (inW A)
  | .inr τ => (omBundle A τ).map (inO A τ)
def VV (A : HodgeCpt Y S x) : CMType H ⊕ CMType H → Submodule Ω (EE A)
  | .inl τ => (A.Vgen (.inl τ)).map (inW A)
  | .inr τ => (⊤ : Submodule Ω _).map (inO A τ)
def cc (A : HodgeCpt Y S x) (bW : WBases A) (bO : OmBases A) :
    ∀ s : CMType H ⊕ CMType H, Fin (rk (CMType H) D.p D.q s) → EE A
  | .inl τ => fun a => inW A (bW τ a)
  | .inr τ => fun a => inO A τ (bO τ a)
def aOf (A : HodgeCpt Y S x) (bW : WBases A) (bO : OmBases A) {n : CMType H ⊕ CMType H → ℕ}
    (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE A)) (s : CMType H ⊕ CMType H) :
    Matrix (Fin (n s)) (Fin (rk (CMType H) D.p D.q s)) Ω :=
  Matrix.of fun j a => φ s j (cc A bW bO s a)
abbrev seg {K : Type} [Fintype K] {J : K → Type} {Ω : Type} [Field Ω] (x : (Σ k, J k) → Ω) : ((k : K) → J k) → Ω :=
  fun c' => ∏ k, x ⟨k, c' k⟩
def reTie (A : HodgeCpt Y S x) {K' : Type} [Fintype K'] {J' : K' → Type} (x' : (Σ k, J' k) → Ω)
    (h : CoordTie ℤ A.ξ (seg x')) : HodgeCpt Y S x' :=
  { A with tie := h }
end Bundles
section Model
variable {Ψ : Type} [Fintype Ψ] {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
  (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
  {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ)
def bF (r : Ψ × Fin (p + q)) (k : NonPluckerBlocks (blkF Ψ p q K₀)) : ℤ := twist m r k.1
def FramesOK : Prop :=
  ∀ Q : Ideal (MRing (baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀))), Q.IsPrime → IsRelevant Q →
    mCoordIdeal (xb A x₀) ≤ Q →
    ∃ F : FrameData (idx (p := p) (q := q) J₀ n) Ψ (p + q) Ω (blkF Ψ p q K₀),
      ((∀ τ, IsBlockDiag p (F.T τ) ∧ (F.T τ).det ≠ 0) ∧
      (∀ r k, blkF Ψ p q K₀ r = some k → ∀ (i : idx J₀ n k) (h : Matrix (Fin (p + q)) (Fin (p + q)) Ω),
        IsBlockDiag p h →
        detFac p r.2 (F.T r.1) * ∑ I, coefF A ⟨k, i⟩ I * minorIJ (F.T r.1 * h) I (stepCols (p + q) p r.2) =
          (∏ k', xb A x₀ ⟨k', F.c k'⟩ ^ bF m r k') * ∑ I, F.u ⟨k, i⟩ I * minorIJ h I (stepCols (p + q) p r.2)) ∧
      (∀ r k, blkF Ψ p q K₀ r = some k → ∀ I I', IsStepRows (p + q) p r.2 I → IsStepRows (p + q) p r.2 I' →
        ∑ i : idx J₀ n k, F.u' I ⟨k, i⟩ * F.u ⟨k, i⟩ I' = if I = I' then 1 else 0) ∧
      ∀ r, blkF Ψ p q K₀ r = none →
        detFac p r.2 (F.T r.1) * 1 = (∏ k', xb A x₀ ⟨k', F.c k'⟩ ^ bF m r k') * F.υ r) ∧
      ((∀ k, (MvPolynomial.X ⟨k, F.c k⟩ : MRing (baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀))) ∉ Q) ∧
        (∀ r I, RegAt (xb A x₀) Q (F.u r I) ∧ RegAt (xb A x₀) Q (F.u' I r)) ∧
        ∀ r, blkF Ψ p q K₀ r = none → F.υ r ≠ 0 ∧ RegAt (xb A x₀) Q (F.υ r) ∧ RegAt (xb A x₀) Q (F.υ r)⁻¹)
def ModelOK : Prop :=
  (∀ r, blkF Ψ p q K₀ r = none ↔ ¬ IsProperStep (p + q) p r.2) ∧
  (∀ r r' k, blkF Ψ p q K₀ r = some k → blkF Ψ p q K₀ r' = some k → r = r') ∧
  (∀ k, ∃ i, xb A x₀ ⟨k, i⟩ ≠ 0) ∧
  (∀ r, basePart (blkF Ψ p q K₀) (yv A x₀) r = algebraMap Ω (GenField Ω (rk Ψ p q)) (xb A x₀ r)) ∧
  (∀ τ : Ψ, IsBlockDiag p (gMat p q Ω τ)) ∧
  IsGenericFlag Ω p (gMat (Ψ := Ψ) p q Ω) ∧
  (∀ r k, blkF Ψ p q K₀ r = some k → ∀ i : idx J₀ n k,
    yv A x₀ ⟨k, i⟩ = ∑ I, algebraMap Ω (GenField Ω (rk Ψ p q)) (coefF A ⟨k, i⟩ I) *
      minorIJ (gMat p q Ω r.1) I (stepCols (p + q) p r.2)) ∧
  FramesOK A x₀ m
def model [CharZero Ω] (h : ModelOK A x₀ m) : FlagModel (yv (p := p) (q := q) A x₀) Ψ (p + q) p where
  j_le := Nat.le_add_right _ _
  Ω := Ω
  blk := blkF Ψ p q K₀
  blk_none := h.1
  blk_inj := h.2.1
  x := xb A x₀
  x_ne := h.2.2.1
  y_base := h.2.2.2.1
  g := gMat p q Ω
  g_block := h.2.2.2.2.1
  g_indep := h.2.2.2.2.2.1
  coef := coefF A
  y_step := h.2.2.2.2.2.2.1
  b := bF m
  lam := fun _ => 1
  frames := h.2.2.2.2.2.2.2
end Model
section Forms
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω}
def FormsOK (A : HodgeCpt Y S x) (bW : WBases A) (bO : OmBases A) {n : CMType H ⊕ CMType H → ℕ}
    (m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE A)) : Prop :=
  (∀ s, (LL A s).IsVB (rk (CMType H) D.p D.q s) (VV A s)) ∧
  (∀ s, LinearIndependent Ω (cc A bW bO s) ∧ Submodule.span Ω (Set.range (cc A bW bO s)) = VV A s) ∧
  (∀ s, IsTwistGen A.ξ (seg x) (LL A s) (m s) (φ s)) ∧
  ∀ s, ∃ B : Matrix (Fin (rk (CMType H) D.p D.q s)) (Fin (n s)) Ω, B * aOf A bW bO φ s = 1
variable {K' : Type} [Fintype K'] {J' : K' → Type}
  {y : (Σ k, J' k) → GenField Ω (rk (CMType H) D.p D.q)}
def ColFlags (A : HodgeCpt Y S x) (bW : WBases A) (bO : OmBases A) {A' : HodgeCpt Y S y} (j : A.Li →+ A'.Li)
    (Fl : A'.Flag) : Prop :=
  (∀ τ (k : Fin D.p), Fl.b (.inl τ) k = colFrame (fun a => j (bW τ a)) (wBlock (gMat D.p D.q Ω τ)) k) ∧
    ∀ τ (v : Fin D.q → A.Vgen (.inr τ)), (∀ a b, bO τ a (v b) = if a = b then 1 else 0) →
      ∀ k : Fin D.q, Fl.b (.inr τ) k = colFrame (fun a => j (v a)) (omBlock (gMat D.p D.q Ω τ))ᵀ⁻¹ k.rev
end Forms
end GlobalTheory.CompanionTheory.Ar.PB.FMX


