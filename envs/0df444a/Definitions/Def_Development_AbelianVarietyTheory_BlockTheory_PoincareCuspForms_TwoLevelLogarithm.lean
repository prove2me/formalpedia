-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_TwoLevelLogarithm
-- name    : Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_TwoLevelLogarithm
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T01:22:53.012442+00:00
-- url     : https://prove2.me/theorems/fbad7573-fe62-4b90-b487-ca238a56e637
-- title:
--   Two Level Logarithm
-- statement:
--   Definitions and structural lemmas for Two Level Logarithm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/TwoLevelLogarithm.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def castFrame {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (x : Frame Ψ r) : Frame Ψ' r :=
  fun τ => x ⟨τ.1, h.symm ▸ τ.2⟩
def castWt {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (la : Wt Ψ' r) : Wt Ψ r :=
  fun τ => la ⟨τ.1, h ▸ τ.2⟩
def deMul (Ψ : Finset (E →+* ℂ)) (r p0 s : ℕ) : Wt Ψ r :=
  fun _ i => if (i : ℕ) < p0 then -((s / 2 : ℕ) : ℤ) else ((s / 2 : ℕ) : ℤ)
def GapsGe {Ψ : Finset (E →+* ℂ)} (p0 : ℕ) (la : Wt Ψ r) (a : ℤ) : Prop :=
  ∀ (τ : Ψ) (i j : Fin r), (j : ℕ) = i + 1 → (j : ℕ) ≠ p0 → a ≤ la τ i - la τ j
def PairGe {Ψ : Finset (E →+* ℂ)} (la : Wt Ψ r) (a : ℝ) : Prop :=
  ∀ (τ : Ψ) (i j : Fin r), (i : ℕ) = 0 → (j : ℕ) = r - 1 → a ≤ ((la τ j - la τ i : ℤ) : ℝ)
structure TwoLevels (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (U C : Type) [Group U] [MulAction U C] where
  Ψ : Finset (E →+* ℂ)
  Gm : Matrix (Fin r) (Fin r) E
  p0 : ℕ
  ξ0 : E
  comp : C → DataX E r
  comp_Ψ : ∀ c, (comp c).Ψ = Ψ
  comp_Gm : ∀ c, (comp c).Gm = Gm
  comp_basePoint : ∀ c, (comp c).p0 = p0
  comp_ξ0 : ∀ c, (comp c).ξ0 = ξ0

  χ_one : ∀ c la, ∀ γ ∈ (comp c).Γ, (comp c).χ la γ = 1

  Γ_L' : ∀ c, ∀ γ ∈ (comp c).Γ, ∀ v,
    v ∈ (comp c).L' ↔ Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v ∈ (comp c).L'

  tr : U → C → GL (Fin r) E
  tr_herm : ∀ u c v w, herm Gm (Matrix.mulVec (tr u c : Matrix (Fin r) (Fin r) E) v)
    (Matrix.mulVec (tr u c : Matrix (Fin r) (Fin r) E) w) = herm Gm v w
  tr_Λ : ∀ u c v,
    v ∈ (comp c).Λ ↔ Matrix.mulVec (tr u c : Matrix (Fin r) (Fin r) E) v ∈ (comp (u • c)).Λ
  tr_L' : ∀ u c v,
    v ∈ (comp c).L' ↔ Matrix.mulVec (tr u c : Matrix (Fin r) (Fin r) E) v ∈ (comp (u • c)).L'
  tr_conj : ∀ u c γ, γ ∈ (comp c).Γ ↔ tr u c * γ * (tr u c)⁻¹ ∈ (comp (u • c)).Γ
  tr_mul : ∀ u v c, tr (u * v) c * (tr u (v • c) * tr v c)⁻¹ ∈ (comp ((u * v) • c)).Γ

  tr_faithful : ∀ u c, u • c = c → tr u c ∈ (comp c).Γ → u = 1
namespace TwoLevels
variable {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C)
def dom : Set (Frame M.Ψ r) := GG M.Ψ M.Gm M.p0
def dimX : ℕ := M.Ψ.card * (M.p0 * (r - M.p0))
def dimY : ℕ := M.Ψ.card * (r * (r - 1) / 2)
def upper (c : C) : Set (GL (Fin r) E) :=
  {β | ∃ u : U, u • c = c ∧ ∃ γ ∈ (M.comp c).Γ, β = γ * M.tr u c}
def UnipotentOver (g : ℕ) : Prop :=
  ∀ c, ∀ β ∈ M.upper c, ∀ P : Ideal (𝓞 E), P.IsPrime → (g : 𝓞 E) ∈ P → ∀ v ∈ (M.comp c).L',
    Matrix.mulVec (((β : Matrix (Fin r) (Fin r) E) - 1) ^ r) v ∈ P • (M.comp c).L'
def SS (la : Wt M.Ψ r) : Set (C → Frame M.Ψ r → ℂ) :=
  {F | ∀ c, (fun x => F c (castFrame (M.comp_Ψ c) x)) ∈ (M.comp c).SS (castWt (M.comp_Ψ c) la)}
def pull (h : U) (F : C → Frame M.Ψ r → ℂ) : C → Frame M.Ψ r → ℂ :=
  fun c x => F (h • c) (lact (M.tr h c) x)
def res (F : C → Frame M.Ψ r → ℂ) : C → M.dom → ℂ := fun c x => F c x.1
def cusp (la : Wt M.Ψ r) : Submodule ℂ (C → M.dom → ℂ) := Submodule.span ℂ (M.res '' M.SS la)
def cuspPsi (la : Wt M.Ψ r) (ψ : U →* ℂˣ) : Submodule ℂ (C → M.dom → ℂ) :=
  Submodule.span ℂ (M.res '' {F | F ∈ M.SS la ∧
    ∀ h c, ∀ x ∈ M.dom, M.pull h F c x = ((ψ h : ℂˣ) : ℂ) * F c x})
def detTr [Fintype U] [DecidableEq U] (F : C → Frame M.Ψ r → ℂ) (c : C) (x : Frame M.Ψ r) : ℂ :=
  (Matrix.of fun h h' : U => M.pull (h * h') F c x).det
end TwoLevels
def SplitsCompletely (E : Type) [Field E] [NumberField E] (g : ℕ) : Prop :=
  g.Prime ∧ {P : Ideal (𝓞 E) | P.IsPrime ∧ (g : 𝓞 E) ∈ P}.ncard = Module.finrank ℚ E
def LevelHyp {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C) : Prop :=
  ∃ g : ℕ, SplitsCompletely E g ∧ 3 * r < g ∧ M.UnipotentOver g
def IndependentTranslates (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (U C : Type) [Group U] [Fintype U] [DecidableEq U] [Finite C] [MulAction U C]
    (M : TwoLevels E r U C), LevelHyp M →
    ∀ s : ℕ, Even s → 2 * r + 50 * r ^ 2 * M.dimX + 1 ≤ s →
      ∃ u0 ∈ M.SS (deMul M.Ψ r M.p0 s), ∀ c : C, ∃ x ∈ M.dom, M.detTr u0 c x ≠ 0
def sqSum (X : Data E r) (la : Wt X.Ψ r) {n : ℕ} (w : Fin n → Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℝ :=
  ∑ k, X.pnorm la (w k) x ^ 2
def IsFlat (X : Data E r) (L Fp : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ) : Prop :=
  ∃ (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (Δ : MvPolynomial (Fin (nd X)) ℂ)
    (thp : Frame X.Ψ r → ℂ),
    (∃ a : Fin N → ℂ, ∀ x ∈ X.dom, w0 x = ∑ j, a j * w j x) ∧
    (∀ k, ∃ a : Fin N → ℂ, ∀ x ∈ X.dom, s k x = ∑ j, a j * w j x) ∧
    (∃ x ∈ X.dom, ∀ k, s k x = 0) ∧
    (∀ x ∈ X.dom, (∀ k, s k x = 0) → w0 x ≠ 0) ∧
    (∀ O : Set (Frame X.Ψ r), IsOpen O → (∀ x ∈ X.dom, (∀ k, s k x = 0) → x ∈ O) →
      (∀ x ∈ O, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ O) →
      ∃ K : ℝ, ∀ x ∈ X.dom, x ∉ O → sqSum X L w x ≤ K * sqSum X L s x) ∧
    (∃ K : ℝ, ∀ x ∈ X.dom, sqSum X L w x ≤ K * (X.pnorm L w0 x ^ 2 + sqSum X L s x)) ∧
    MvPolynomial.constantCoeff Δ ≠ 0 ∧
    (∀ x ∈ X.dom, w0 x ≠ 0 → MvPolynomial.eval (fun k => s k x / w0 x) Δ ≠ 0 →
      (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
        s k (cpt X x z) / w0 (cpt X x z) : V (nd X))) 0).det ≠ 0 ∧ thp x ≠ 0) ∧
    (∀ K : Set (Fin (nd X) → ℂ), IsCompact K → (∀ z ∈ K, MvPolynomial.eval z Δ ≠ 0) →
      ∃ Q : Set (Frame X.Ψ r), IsCompact Q ∧ Q ⊆ X.dom ∧ ∀ x ∈ X.dom, w0 x ≠ 0 →
        (fun k => s k x / w0 x) ∈ K → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ Q) ∧
    thp ∈ X.SS Fp
def ThetaInputs (X : Data E r) (L Fp : Wt X.Ψ r) (T : ℕ) : Prop :=
  ∃ (N : ℕ) (w : Fin N → Frame X.Ψ r → ℂ) (th1 th2 η : Frame X.Ψ r → ℂ) (φ : Frame X.Ψ r → ℝ)
    (i g0 : ℕ) (c : ℝ),
    (∀ j, w j ∈ X.SS L) ∧ (∀ x ∈ X.dom, ∃ j, w j x ≠ 0) ∧ IsFlat X L Fp w ∧
    X.IsBddSec (2 • L - deMul X.Ψ r X.p0 2) th1 ∧ (∃ x ∈ X.dom, th1 x ≠ 0) ∧
    X.IsBddSec ((nd X + 4) • L - Fp) th2 ∧ (∃ x ∈ X.dom, th2 x ≠ 0) ∧
    1 ≤ i ∧ 1 ≤ g0 ∧ Even g0 ∧ 0 < c ∧ (T : ℝ) * c * g0 ≤ 1 ∧
    X.IsSec (deMul X.Ψ r X.p0 (i * g0)) η ∧ (∃ x ∈ X.dom, η x ≠ 0) ∧
    (∀ x ∈ X.dom, 0 ≤ φ x) ∧
    (∃ K : ℝ, ∀ x ∈ X.dom,
      X.pnorm (deMul X.Ψ r X.p0 (i * g0)) η x ≤ K * Real.exp (-(i * φ x))) ∧
    ∃ K : ℝ, ∀ x ∈ X.dom, Real.exp (-(2 * c * φ x)) ≤ K * sqSum X L w x
def kLog (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Wt Ψ r := fun _ a => 2 * (a : ℤ) - ((r : ℤ) - 1)
def ShareIndefinite (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C]
    (M : TwoLevels E r U C), LevelHyp M → 0 < M.p0 → M.p0 < r →
    ∀ (L Fp : Wt M.Ψ r) (T s : ℕ),
      2 ≤ M.dimY → 11 * M.dimY ^ 2 ≤ T →
      Even s → 2 * r + 50 * r ^ 2 * M.dimX + 1 ≤ s → s ≤ T →
      GapsGe M.p0 L 1 → PairGe L (1.9 * T) →
      GapsGe M.p0 (Fp - kLog M.Ψ r - (M.dimY + 2) • L) 0 →
      PairGe (Fp - kLog M.Ψ r - (M.dimY + 2) • L) 1 →
      (∀ c, ThetaInputs (M.comp c).toData (castWt (M.comp_Ψ c) L) (castWt (M.comp_Ψ c) Fp) T) →
      ∀ ψ : U →* ℂˣ,
        Module.Finite ℂ (M.cusp (Fp + T • L)) ∧
        (1 - (M.dimY : ℝ) * (M.dimY + 6) / T) * Module.finrank ℂ (M.cusp (Fp + T • L)) ≤
          (Nat.card U : ℝ) * Module.finrank ℂ (M.cuspPsi (Fp + T • L) ψ)
def ShareDefinite (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C]
    (M : TwoLevels E r U C), LevelHyp M → (M.p0 = 0 ∨ M.p0 = r) →
    ∀ (κ : Wt M.Ψ r) (ψ : U →* ℂˣ),
      Module.Finite ℂ (M.cusp κ) ∧
      Nat.card U * Module.finrank ℂ (M.cuspPsi κ ψ) = Module.finrank ℂ (M.cusp κ)
def EpsBound : Prop :=
  ∀ (f k D T : ℕ) (P : ℝ), 2 ≤ f * k → 6 ≤ D → ((f * k : ℕ) : ℝ) ≤ P →
    P ^ 3 * (D : ℝ) ^ 3 * k * f ≤ T →
    (D : ℝ) * (D + 6) / T ≤ (((f * k : ℕ) : ℝ) ^ 3)⁻¹ / 4
def Statement (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  IndependentTranslates E ∧ ShareIndefinite E ∧ ShareDefinite E ∧ EpsBound
def TwoLevels.regular (X : DataX E r) (U : Type) [Group U]
    (hχ : ∀ la, ∀ γ ∈ X.Γ, X.χ la γ = 1)
    (hL : ∀ γ ∈ X.Γ, ∀ v, v ∈ X.L' ↔ Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v ∈ X.L') :
    TwoLevels E r U U where
  Ψ := X.Ψ
  Gm := X.Gm
  p0 := X.p0
  ξ0 := X.ξ0
  comp := fun _ => X
  comp_Ψ := fun _ => rfl
  comp_Gm := fun _ => rfl
  comp_basePoint := fun _ => rfl
  comp_ξ0 := fun _ => rfl
  χ_one := fun _ => hχ
  Γ_L' := fun _ => hL
  tr := fun _ _ => 1
  tr_herm := by intro u c v w; simp
  tr_Λ := by intro u c v; simp
  tr_L' := by intro u c v; simp
  tr_conj := by intro u c γ; simp
  tr_mul := by intro u v c; simp
  tr_faithful := by intro u c h _; simpa using h
end
end GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds


