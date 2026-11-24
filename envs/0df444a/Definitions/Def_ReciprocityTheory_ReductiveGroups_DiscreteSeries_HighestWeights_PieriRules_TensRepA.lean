-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_TensRepA
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_TensRepA
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:12:48.170174+00:00
-- url     : https://prove2.me/theorems/67ba8dd0-8871-453b-b46d-741dda92a569
-- title:
--   Tens Rep A
-- statement:
--   Definitions and structural lemmas for Tens Rep A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PieriRules/TensRepA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open scoped InnerProductSpace
namespace ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
section Gen
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι] [DecidableEq ι]
def piIn (i : ι) : V →L[ℂ] PiLp 2 (fun _ : ι => V) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => V)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ (fun _ : ι => V) i
theorem piIn_apply (i : ι) (v : V) (j : ι) : piIn i v j = Pi.single (M := fun _ : ι => V) i v j := rfl
theorem piIn_same (i : ι) (v : V) : piIn i v i = v :=
  (piIn_apply i v i).trans (Pi.single_eq_same (M := fun _ : ι => V) i v)
theorem piIn_ne {i j : ι} (h : j ≠ i) (v : V) : piIn i v j = 0 :=
  (piIn_apply i v j).trans (Pi.single_eq_of_ne (M := fun _ : ι => V) h v)
def tensL (m : Matrix ι ι ℂ) (S : V →L[ℂ] V) : PiLp 2 (fun _ : ι => V) →L[ℂ] PiLp 2 (fun _ : ι => V) :=
  ∑ i, ∑ j, m i j • (piIn i ∘L S ∘L PiLp.proj 2 (fun _ : ι => V) j)
@[simp] theorem tensL_apply (m : Matrix ι ι ℂ) (S : V →L[ℂ] V) (x : PiLp 2 (fun _ : ι => V)) (i : ι) :
    tensL m S x i = ∑ j, m i j • S (x j) := by
  simp only [tensL, _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    PiLp.proj_apply]
  rw [Finset.sum_eq_single i]
  · simp only [piIn_same]
  · intro k _ hk
    simp only [piIn_ne (Ne.symm hk), smul_zero, Finset.sum_const_zero]
  · simp
theorem tensL_mul (m m' : Matrix ι ι ℂ) (S S' : V →L[ℂ] V) :
    tensL (m * m') (S * S') = tensL m S * tensL m' S' := by
  refine ContinuousLinearMap.ext fun x => PiLp.ext fun i => ?_
  have hSS : ∀ v : V, (S * S') v = S (S' v) := fun v => rfl
  show tensL (m * m') (S * S') x i = tensL m S (tensL m' S' x) i
  simp only [tensL_apply, hSS, Matrix.mul_apply, map_sum, map_smul,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm
theorem tensL_one : tensL (1 : Matrix ι ι ℂ) (1 : V →L[ℂ] V) = 1 := by
  refine ContinuousLinearMap.ext fun x => PiLp.ext fun i => ?_
  simp [Matrix.one_apply, ite_smul]
theorem tensL_star [CompleteSpace V] (m : Matrix ι ι ℂ) (S : V →L[ℂ] V) :
    star (tensL m S) = tensL (star m) (star S) := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [PiLp.inner_apply, tensL_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left, starRingEnd_apply, star_star]
  exact Finset.sum_comm
theorem tensL_mem_unitary [CompleteSpace V] {m : Matrix ι ι ℂ} {S : V →L[ℂ] V}
    (hm : m ∈ unitary (Matrix ι ι ℂ)) (hS : S ∈ unitary (V →L[ℂ] V)) :
    tensL m S ∈ unitary (PiLp 2 (fun _ : ι => V) →L[ℂ] PiLp 2 (fun _ : ι => V)) := by
  rw [Unitary.mem_iff] at hm hS ⊢
  rw [tensL_star, ← tensL_mul, ← tensL_mul, hm.1, hm.2, hS.1, hS.2, tensL_one]
  exact ⟨rfl, rfl⟩
variable {G : Type*} [Monoid G] [CompleteSpace V]
def tensHom (ρ : G →* unitary (Matrix ι ι ℂ)) (σ : G →* unitary (V →L[ℂ] V)) :
    G →* unitary (PiLp 2 (fun _ : ι => V) →L[ℂ] PiLp 2 (fun _ : ι => V)) where
  toFun g := ⟨tensL ((ρ g : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) ((σ g : unitary (V →L[ℂ] V)) : V →L[ℂ] V),
    tensL_mem_unitary (ρ g).2 (σ g).2⟩
  map_one' := Subtype.ext (by simp only [map_one, OneMemClass.coe_one, tensL_one])
  map_mul' g h := Subtype.ext (by simp only [map_mul, Submonoid.coe_mul, tensL_mul])
end Gen
section KT
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {ι : Type} [Fintype ι] [DecidableEq ι]
  (ρ : KG ε →* unitary (Matrix ι ι ℂ))
def tensOp (k : KG ε) : PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V) :=
  tensL ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) (T.op k)
def tensTau : KG ε →* unitary (PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)) :=
  tensHom ρ T.τ
example (τ : KG ε →* unitary (PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)))
    (hc : Continuous τ)
    (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      HasDerivAt (fun t : ℝ => ((τ (γ t) : unitary (PiLp 2 (fun _ : ι => T.V) →L[ℂ]
        PiLp 2 (fun _ : ι => T.V))) : PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)))
        (D X) 0)
    (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hu : ∀ a b, ((D (Matrix.single a b 1) : PiLp 2 (fun _ : ι => T.V) →L[ℂ] PiLp 2 (fun _ : ι => T.V)) :
        Module.End ℂ (PiLp 2 (fun _ : ι => T.V))) =
          tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1)) a b) :
    (⟨PiLp 2 (fun _ : ι => T.V), τ, hc, D, hd⟩ : KRep ε).units =
      tensAct (kunits T) (fun a b => dρ (Matrix.single a b 1)) := by
  funext a b
  exact hu a b
end KT
end ReciprocityTheory.ChartRestriction.DS.HW


