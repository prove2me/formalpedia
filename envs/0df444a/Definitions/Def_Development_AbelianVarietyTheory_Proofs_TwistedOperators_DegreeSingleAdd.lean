-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DegreeSingleAdd
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_DegreeSingleAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:44:55.92981+00:00
-- url     : https://prove2.me/theorems/8fa9ccfa-935c-46b6-8fcc-94c8815cbfca
-- title:
--   Degree Single Add
-- statement:
--   Definitions and structural lemmas for Degree Single Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DegreeSingleAdd.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
namespace GlobalTheory.InducedPBW
section General
variable {R : Type*} [CommRing R] {ι : Type*} {V : Type*} [AddCommGroup V] [Module R V]
def zv (α : ι →₀ ℕ) : V →ₗ[R] (MvPolynomial ι R ⊗[R] V) :=
  TensorProduct.mk R (MvPolynomial ι R) V (monomial α 1)
def mulX (i : ι) : Module.End R (MvPolynomial ι R ⊗[R] V) :=
  LinearMap.rTensor V (LinearMap.mulLeft R (X i))
lemma mulX_zv (i : ι) (α : ι →₀ ℕ) (v : V) :
    mulX i (zv (R := R) α v) = zv (Finsupp.single i 1 + α) v := by
  simp [mulX, zv, X, monomial_mul]
def degLt (R : Type*) [CommRing R] (ι : Type*) (V : Type*) [AddCommGroup V] [Module R V] (n : ℕ) :
    Submodule R (MvPolynomial ι R ⊗[R] V) :=
  Submodule.span R {m | ∃ (α : ι →₀ ℕ) (v : V), α.degree < n ∧ m = zv α v}
lemma zv_mem {n : ℕ} {α : ι →₀ ℕ} (h : α.degree < n) (v : V) : zv α v ∈ degLt R ι V n :=
  Submodule.subset_span ⟨α, v, h, rfl⟩
lemma degLt_mono {n m : ℕ} (h : n ≤ m) : degLt R ι V n ≤ degLt R ι V m :=
  Submodule.span_mono fun _ ⟨α, v, h1, h2⟩ => ⟨α, v, h1.trans_le h, h2⟩
lemma map_degLt {W : Type*} [AddCommGroup W] [Module R W] {n : ℕ}
    (f : (MvPolynomial ι R ⊗[R] V) →ₗ[R] W) (N : Submodule R W)
    (h : ∀ α v, α.degree < n → f (zv α v) ∈ N) : ∀ m ∈ degLt R ι V n, f m ∈ N := by
  have : degLt R ι V n ≤ N.comap f := Submodule.span_le.mpr (by
    rintro _ ⟨α, v, h1, rfl⟩
    exact h α v h1)
  exact fun m hm => this hm
lemma ext_zv {W : Type*} [AddCommGroup W] [Module R W]
    {f f' : (MvPolynomial ι R ⊗[R] V) →ₗ[R] W}
    (h : ∀ α v, f (zv α v) = f' (zv α v)) : f = f' := by
  apply TensorProduct.ext
  apply (basisMonomials ι R).ext
  intro α
  ext v
  simpa [zv] using h α v
lemma degree_single_add (i : ι) (α : ι →₀ ℕ) :
    (Finsupp.single i 1 + α).degree = α.degree + 1 := by
  simp [add_comm]
lemma mulX_mem {n : ℕ} (i : ι) : ∀ m ∈ degLt R ι V n, mulX i m ∈ degLt R ι V (n + 1) :=
  map_degLt _ _ fun α v h => by
    rw [mulX_zv]
    exact zv_mem (by rw [degree_single_add]; omega) v
variable {g : Type*} [LieRing g] [LieAlgebra R g]
lemma exists_extend (D : (ι →₀ ℕ) → g →ₗ[R] V →ₗ[R] (MvPolynomial ι R ⊗[R] V)) :
    ∃ δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V), ∀ x α v, δ x (zv α v) = D α x v := by
  refine ⟨{ toFun := fun x => TensorProduct.lift ((basisMonomials ι R).constr R fun α => D α x)
            map_add' := ?_, map_smul' := ?_ }, ?_⟩
  all_goals
    have key : ∀ (x : g) α v, TensorProduct.lift ((basisMonomials ι R).constr R fun α => D α x)
        (zv α v) = D α x v := by
      intro x α v
      have := (basisMonomials ι R).constr_basis R (fun α => D α x) α
      simp only [coe_basisMonomials] at this
      simp [zv, this]
  · intro x y
    exact ext_zv fun α v => by rw [LinearMap.add_apply, key, key, key]; simp
  · intro r x
    exact ext_zv fun α v => by rw [LinearMap.smul_apply, key, key]; simp
  · exact key
def extend (D : (ι →₀ ℕ) → g →ₗ[R] V →ₗ[R] (MvPolynomial ι R ⊗[R] V)) :
    g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V) := (exists_extend D).choose
lemma extend_zv (D : (ι →₀ ℕ) → g →ₗ[R] V →ₗ[R] (MvPolynomial ι R ⊗[R] V)) (x α v) :
    extend D x (zv α v) = D α x v := (exists_extend D).choose_spec x α v
variable [Fintype ι] [LinearOrder ι] (e : ι → g) (c : ι → g →ₗ[R] R) (act : g →ₗ[R] Module.End R V)
def mulLin : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V) := ∑ i, (c i).smulRight (mulX i)
omit [LinearOrder ι] in
lemma mulLin_apply (x : g) (m : MvPolynomial ι R ⊗[R] V) :
    mulLin c x m = ∑ i, c i x • mulX i m := by
  simp [mulLin, LinearMap.sum_apply]
omit [LinearOrder ι] in
lemma mulLin_mem {n : ℕ} (x : g) : ∀ m ∈ degLt R ι V n, mulLin c x m ∈ degLt R ι V (n + 1) := by
  intro m hm
  rw [mulLin_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (mulX_mem i m hm)
def rho (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) :
    g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V) := mulLin c + δ
def strip (s : Finset ι) : g →ₗ[R] g := LinearMap.id - ∑ j ∈ s, (c j).smulRight (e j)
def straighten (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) (i : ι) :
    g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V) :=
  (LinearMap.mulLeft R (rho c δ (e i)) ∘ₗ δ -
    rho c δ ∘ₗ (LieAlgebra.ad R g (e i))) ∘ₗ strip e c (Finset.univ.filter (· ≤ i))
lemma straighten_apply (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) (i : ι) (x m) :
    straighten e c δ i x m =
      rho c δ (e i) (δ (strip e c (Finset.univ.filter (· ≤ i)) x) m) +
      rho c δ ⁅strip e c (Finset.univ.filter (· ≤ i)) x, e i⁆ m := by
  rw [← lie_skew (strip e c (Finset.univ.filter (· ≤ i)) x), map_neg]
  simp [straighten, sub_eq_add_neg]
def step (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) :
    g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V) :=
  extend fun α => if h : α.support.Nonempty then
    (straighten e c δ (α.support.min' h)).compl₂ (zv (α - Finsupp.single (α.support.min' h) 1))
  else (act ∘ₗ strip e c Finset.univ).compr₂ (zv 0)
lemma step_zero (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) (x v) :
    step e c act δ x (zv 0 v) = zv 0 (act (strip e c Finset.univ x) v) := by
  simp [step, extend_zv]
lemma step_succ (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) (i : ι) (J : ι →₀ ℕ)
    (hJ : ∀ j ∈ J.support, i ≤ j) (x v) :
    step e c act δ x (zv (Finsupp.single i 1 + J) v) = straighten e c δ i x (zv J v) := by
  have hi : i ∈ (Finsupp.single i 1 + J).support := by simp
  have hmin : (Finsupp.single i 1 + J).support.min' ⟨i, hi⟩ = i := by
    apply le_antisymm (Finset.min'_le _ _ hi)
    apply Finset.le_min'
    intro j hj
    rcases Finset.mem_union.mp (Finsupp.support_add hj) with h1 | h1
    · exact (Finset.mem_singleton.mp (Finsupp.support_single_subset h1)).ge
    · exact hJ j h1
  simp [step, extend_zv, hmin]
omit [Fintype ι] in
lemma exponent_cases (α : ι →₀ ℕ) :
    α = 0 ∨ ∃ (i : ι) (J : ι →₀ ℕ), (∀ j ∈ J.support, i ≤ j) ∧ α = Finsupp.single i 1 + J := by
  by_cases h : α.support.Nonempty
  · right
    refine ⟨α.support.min' h, α - Finsupp.single (α.support.min' h) 1, fun j hj => ?_, ?_⟩
    · exact Finset.min'_le _ _ (Finsupp.support_tsub hj)
    · rw [add_comm, tsub_add_cancel_of_le]
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp (Finset.min'_mem _ h))
  · left
    simpa using h
def Pres (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) : Prop :=
  ∀ n x, ∀ m ∈ degLt R ι V n, δ x m ∈ degLt R ι V n
omit [LinearOrder ι] in
lemma Pres.rho_mem {δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)} (h : Pres δ) (n x) :
    ∀ m ∈ degLt R ι V n, rho c δ x m ∈ degLt R ι V (n + 1) := fun m hm =>
  Submodule.add_mem _ (mulLin_mem c x m hm) (degLt_mono (Nat.le_succ n) (h n x m hm))
lemma Pres.step {δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)} (h : Pres δ) :
    Pres (step e c act δ) := by
  intro n x
  refine map_degLt _ _ fun α v hα => ?_
  rcases exponent_cases α with rfl | ⟨i, J, hJ, rfl⟩
  · rw [step_zero]; exact zv_mem hα _
  · rw [step_succ e c act δ i J hJ, straighten_apply]
    rw [degree_single_add] at hα
    have hz : zv J v ∈ degLt R ι V (J.degree + 1) := zv_mem (by omega) v
    refine degLt_mono (show J.degree + 1 + 1 ≤ n by omega) (Submodule.add_mem _ ?_ ?_)
    · exact h.rho_mem c _ _ _ (h _ _ _ hz)
    · exact h.rho_mem c _ _ _ hz
section Fixed
variable {e c act} {δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)}
  (hce : ∀ i j, c i (e j) = if i = j then 1 else 0)
include hce
variable (hf : step e c act δ = δ)
include hf
def defect (c : ι → g →ₗ[R] R) (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V))
    (m : MvPolynomial ι R ⊗[R] V) : g →ₗ[R] g →ₗ[R] (MvPolynomial ι R ⊗[R] V) :=
  LinearMap.mk₂ R (fun x y => rho c δ x (rho c δ y m) - rho c δ y (rho c δ x m) - rho c δ ⁅x, y⁆ m)
    (by intros; simp only [add_lie, map_add, LinearMap.add_apply]; abel)
    (by intros; simp only [smul_lie, map_smul, LinearMap.smul_apply, smul_sub])
    (by intros; simp only [lie_add, map_add, LinearMap.add_apply]; abel)
    (by intros; simp only [lie_smul, map_smul, LinearMap.smul_apply, smul_sub])
end Fixed
end General
end GlobalTheory.InducedPBW


