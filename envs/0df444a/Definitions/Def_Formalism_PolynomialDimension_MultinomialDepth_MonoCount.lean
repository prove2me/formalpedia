-- Prove2me | Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
-- name    : Formalism_PolynomialDimension_MultinomialDepth_MonoCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:35.534181+00:00
-- url     : https://prove2.me/theorems/1a3939da-7658-4404-8762-d33bb819c175
-- title:
--   Mono Count
-- statement:
--   Definitions and structural lemmas for Mono Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.CountingSumsFrames
open Formalism.GM.DimensionMonotonicity Finset
namespace GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
noncomputable def qlist (S : Finset (Fin r → ℤ)) (c : ℤ) : List ℤ := ((S.image GlW.casI).erase c).toList
end GlX
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM.DimensionMonotonicity Finset
namespace GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
end GlX
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM.DimensionMonotonicity Finset
namespace GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
def act : List (Fin r × Fin r) → V →ₗ[K] V
  | [] => LinearMap.id
  | ab :: w => G.E ab.1 ab.2 ∘ₗ act w
noncomputable def Lv (v : V) : (List (Fin r × Fin r) →₀ K) →ₗ[K] V :=
  Finsupp.linearCombination K (fun w => act G w v)
noncomputable def tr {h h' : V} (hk : LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h')) :
    LinearMap.range (Lv G h) →ₗ[K] V :=
  (LinearMap.ker (Lv G h)).liftQ (Lv G h') hk ∘ₗ (Lv G h).quotKerEquivRange.symm.toLinearMap
theorem tr_apply {h h' : V} (hk : LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h'))
    (c : List (Fin r × Fin r) →₀ K) : tr G hk ⟨Lv G h c, LinearMap.mem_range_self _ c⟩ = Lv G h' c := by
  unfold tr
  rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.quotKerEquivRange_symm_apply_image,
    Submodule.mkQ_apply, Submodule.liftQ_apply]
end GlX
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Formalism.GM.DimensionMonotonicity Finset
namespace GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
theorem tr_mem {h h' : V} (hk : LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h')) (y : LinearMap.range (Lv G h)) :
    tr G hk y ∈ LinearMap.range (Lv G h') := by
  obtain ⟨y, c, rfl⟩ := y
  rw [tr_apply]
  exact LinearMap.mem_range_self _ _
end GlX
section Proj
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
end Proj
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open MvPolynomial Finset
section Ext
variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]
def frst (m : σ →₀ ℕ) : σ →₀ ℕ := m.filter fs
def ltr (m : σ →₀ ℕ) : σ →₀ ℕ := m.filter (fun v => ¬ fs v)
def IsF (g : MvPolynomial σ K) : Prop := ∀ m ∈ g.support, ∀ v, m v ≠ 0 → fs v
def IsL (q : MvPolynomial σ K) : Prop := ∀ m ∈ q.support, ∀ v, m v ≠ 0 → ¬ fs v
noncomputable def ext (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  (basisMonomials σ K).constr K (fun m => φ (monomial (frst fs m) 1) * monomial (ltr fs m) 1)
noncomputable def slc (m : σ →₀ ℕ) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  (basisMonomials σ K).constr K (fun m' => if ltr fs m' = m then monomial (frst fs m') 1 else 0)
end Ext
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
def fsj (N r j0 : ℕ) : Fin N × Fin r → Prop := fun v => (v.1 : ℕ) < j0
instance (N r j0 : ℕ) : DecidablePred (fsj N r j0) := fun v => Nat.decLt _ _
def wlat (N r j0 : ℕ) : Fin N × Fin r → ℤ := fun v => if (v.1 : ℕ) < j0 then 0 else 1
def wfir (N r j0 : ℕ) : Fin N × Fin r → ℤ := fun v => if (v.1 : ℕ) < j0 then 1 else 0
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
def Mup {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (j0 : ℕ) : Fin q → WithTop ℤ :=
  fun k => if J k < j0 then M k else ⊤
noncomputable def Cset (p : ℕ) [Fact p.Prime] [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  Pol p r (Lz L j0) ⊓ ⨅ k, YCond p L (J k) (Mup J M j0 k)
noncomputable def psi (p : ℕ) [Fact p.Prime] (L : Letters N) (j0 : ℕ) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  weightedHomogeneousComponent (wL N r) (fun i => ((Lz L j0).deg i : ℤ))
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
noncomputable def YYs (p : ℕ) [Fact p.Prime] [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  Y p L J M ⊓ Submodule.span ℚ_[p] {x | ∃ g ∈ (GA p L j0).gS {F},
    ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)}, x = g * q}
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open Finset
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
def GlX.HWs {K V : Type} [Field K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r) (μ : Fin r → ℤ) :
    Submodule K V where
  carrier := {v | G.IsHW μ v}
  add_mem' := by
    intro x y hx hy
    exact ⟨by show G.comp μ (x + y) = x + y; rw [map_add, hx.1, hy.1],
      fun a b hab => by rw [map_add, hx.2 a b hab, hy.2 a b hab, add_zero]⟩
  zero_mem' := ⟨by show G.comp μ 0 = 0; exact map_zero _, fun a b _ => map_zero _⟩
  smul_mem' := by
    intro c x hx
    exact ⟨by show G.comp μ (c • x) = c • x; rw [map_smul, hx.1],
      fun a b hab => by rw [map_smul, hx.2 a b hab, smul_zero]⟩
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
section Comparison₂
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm
end Comparison₂
end Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
noncomputable def FrL (p : ℕ) [Fact p.Prime] [NeZero N] (L : Letters N) (T : TieData) (i : Fin T.t) (ρ : Fin r) (n0 : ℕ) :
    MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  (rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2))).toLinearMap ∘ₗ
    (LinearMap.mulLeft ℚ_[p] (X (Fin.last (T.pos i + 1), ρ) ^ (n0 - (L.takeD (T.pos i + 1)).total))) ∘ₗ
    (aeval (freezeSub p (L.takeD (T.pos i + 1)) ρ)).toLinearMap
section Comparison₂
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm
end Comparison₂
end Formalism.CountingSumsFrames


