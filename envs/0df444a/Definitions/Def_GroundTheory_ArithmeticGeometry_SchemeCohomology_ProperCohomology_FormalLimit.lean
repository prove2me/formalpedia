-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_FormalLimit
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_FormalLimit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:34.495524+00:00
-- url     : https://prove2.me/theorems/75278248-b0ca-4d91-b253-0898cd8d6f50
-- title:
--   Formal Limit
-- statement:
--   Definitions and structural lemmas for Formal Limit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/FormalLimit.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
section Tower
variable {A : Type u} [CommRing A] {E : ℕ → Type u} [∀ n, AddCommGroup (E n)]
  [∀ n, Module A (E n)] (τ : ∀ n, E (n + 1) →ₗ[A] E n)
def towerLimit : Submodule A (∀ n, E n) where
  carrier := {x | ∀ n, τ n (x (n + 1)) = x n}
  add_mem' {x y} hx hy n := by
    change τ n (x (n + 1) + y (n + 1)) = x n + y n
    rw [map_add, hx n, hy n]
  zero_mem' n := by
    change τ n 0 = 0
    exact map_zero _
  smul_mem' a x hx n := by
    change τ n (a • x (n + 1)) = a • x n
    rw [map_smul, hx n]
def towerComp (n : ℕ) : (k : ℕ) → E (n + k) →ₗ[A] E n
  | 0 => LinearMap.id
  | k + 1 => (towerComp n k).comp (τ (n + k))
@[simp] lemma towerComp_zero (n : ℕ) : towerComp τ n 0 = LinearMap.id := rfl
lemma towerComp_apply_of_mem {x : ∀ n, E n} (hx : x ∈ towerLimit τ) (n k : ℕ) :
    towerComp τ n k (x (n + k)) = x n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change towerComp τ n k (τ (n + k) (x (n + k + 1))) = x n
    rw [hx (n + k)]
    exact ih
theorem towerLimit_eq_bot {c : ℕ} (hc : ∀ n, towerComp τ n c = 0) : towerLimit τ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  funext n
  rw [← towerComp_apply_of_mem τ hx n c, hc n, LinearMap.zero_apply]
  rfl
end Tower
section Exact
variable {A : Type u} [CommRing A]
  {P E Q : ℕ → Type u} [∀ n, AddCommGroup (P n)] [∀ n, Module A (P n)]
  [∀ n, AddCommGroup (E n)] [∀ n, Module A (E n)] [∀ n, AddCommGroup (Q n)]
  [∀ n, Module A (Q n)]
  (τP : ∀ n, P (n + 1) →ₗ[A] P n) (τE : ∀ n, E (n + 1) →ₗ[A] E n) (τQ : ∀ n, Q (n + 1) →ₗ[A] Q n)
  (ι : ∀ n, P n →ₗ[A] E n) (π : ∀ n, E n →ₗ[A] Q n)
  (hι : ∀ n, (τE n).comp (ι (n + 1)) = (ι n).comp (τP n))
  (hπ : ∀ n, (τQ n).comp (π (n + 1)) = (π n).comp (τE n))
variable (hinj : ∀ n, Function.Injective (ι n))
  (hex : ∀ n, LinearMap.range (ι n) = LinearMap.ker (π n))
def towerLimitMap : towerLimit τP →ₗ[A] towerLimit τE where
  toFun x := ⟨fun n => ι n (x.1 n), fun n => by
    have := congrArg (fun f => f (x.1 (n + 1))) (hι n)
    simp only [LinearMap.comp_apply] at this
    rw [this, x.2 n]⟩
  map_add' x y := by
    ext n
    exact map_add (ι n) _ _
  map_smul' a x := by
    ext n
    exact map_smul (ι n) _ _
include hι hπ hinj hex in

theorem bijective_towerLimitMap {c : ℕ} (hc : ∀ n, towerComp τQ n c = 0) :
    Function.Bijective (towerLimitMap τP τE ι hι) := by
  constructor
  · intro x y hxy
    ext n
    exact hinj n (congrArg (fun z : towerLimit τE => z.1 n) hxy)
  · intro e
    have hQ : ∀ n, π n (e.1 n) = 0 := by
      have hmem : (fun n => π n (e.1 n)) ∈ towerLimit τQ := fun n => by
        have := congrArg (fun f => f (e.1 (n + 1))) (hπ n)
        simp only [LinearMap.comp_apply] at this
        rw [this, e.2 n]
      rw [towerLimit_eq_bot τQ hc] at hmem
      intro n
      exact congrFun ((Submodule.mem_bot A).1 hmem) n
    have hp : ∀ n, ∃ p, ι n p = e.1 n := fun n => by
      have : e.1 n ∈ LinearMap.range (ι n) := by
        rw [hex n]
        exact hQ n
      exact this
    choose p hp using hp
    refine ⟨⟨p, fun n => hinj n ?_⟩, ?_⟩
    · have := congrArg (fun f => f (p (n + 1))) (hι n)
      simp only [LinearMap.comp_apply] at this
      rw [← this, hp, hp, e.2 n]
    · ext n
      exact hp n
def towerLimitEquivOfExact {c : ℕ} (hc : ∀ n, towerComp τQ n c = 0) :
    towerLimit τP ≃ₗ[A] towerLimit τE :=
  LinearEquiv.ofBijective (towerLimitMap τP τE ι hι)
    (bijective_towerLimitMap τP τE τQ ι π hι hπ hinj hex hc)
end Exact
section Adic
variable {A : Type u} [CommRing A] (I : Ideal A) {H : Type u} [AddCommGroup H] [Module A H]
  (K : ℕ → Submodule A H) (hK : Antitone K)
def quotTower : ∀ n, (H ⧸ K (n + 1)) →ₗ[A] (H ⧸ K n) :=
  fun n => Submodule.factor (hK (Nat.le_succ n))
lemma eq_factor_of_mem_towerLimit {x : ∀ n, H ⧸ K n} (hx : x ∈ towerLimit (E := fun n => H ⧸ K n) (quotTower K hK))
    {m n : ℕ} (h : m ≤ n) : x m = Submodule.factor (hK h) (x n) := by
  induction n, h using Nat.le_induction with
  | base =>
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x m)
    rw [← hy]
    rfl
  | succ n hmn ih =>
    rw [ih, ← hx n]
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x (n + 1))
    rw [← hy]
    rfl
variable {I K}
def adicCompletionToTowerLimit (h₁ : ∀ n, I ^ (n + 1) • (⊤ : Submodule A H) ≤ K n) :
    AdicCompletion I H →ₗ[A] towerLimit (E := fun n => H ⧸ K n) (quotTower K hK) where
  toFun x := ⟨fun n => Submodule.factor (h₁ n) (x.1 (n + 1)), fun n => by
    show quotTower K hK n (Submodule.factor (h₁ (n + 1)) (x.1 (n + 1 + 1))) =
      Submodule.factor (h₁ n) (x.1 (n + 1))
    rw [← x.2 (Nat.le_succ (n + 1))]
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x.1 (n + 1 + 1))
    rw [← hy]
    rfl⟩
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact map_add (Submodule.factor (h₁ n)) _ _
  map_smul' a x := by
    apply Subtype.ext
    funext n
    exact map_smul (Submodule.factor (h₁ n)) _ _
def towerLimitToAdicCompletion {c : ℕ} (h₂ : ∀ n, K (n + c) ≤ I ^ n • (⊤ : Submodule A H)) :
    towerLimit (E := fun n => H ⧸ K n) (quotTower K hK) →ₗ[A] AdicCompletion I H where
  toFun y := ⟨fun n => Submodule.factor (h₂ n) (y.1 (n + c)), fun {m n} hmn => by
    show AdicCompletion.transitionMap I H hmn (Submodule.factor (h₂ n) (y.1 (n + c))) =
      Submodule.factor (h₂ m) (y.1 (m + c))
    rw [eq_factor_of_mem_towerLimit K hK y.2 (Nat.add_le_add_right hmn c)]
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (y.1 (n + c))
    rw [← hz]
    rfl⟩
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact map_add (Submodule.factor (h₂ n)) _ _
  map_smul' a x := by
    apply Subtype.ext
    funext n
    exact map_smul (Submodule.factor (h₂ n)) _ _
def adicCompletionEquivTowerLimit (h₁ : ∀ n, I ^ (n + 1) • (⊤ : Submodule A H) ≤ K n)
    {c : ℕ} (h₂ : ∀ n, K (n + c) ≤ I ^ n • (⊤ : Submodule A H)) :
    AdicCompletion I H ≃ₗ[A] towerLimit (E := fun n => H ⧸ K n) (quotTower K hK) :=
  LinearEquiv.ofLinearMap (adicCompletionToTowerLimit hK h₁) (towerLimitToAdicCompletion hK h₂)
    (LinearMap.ext fun y => Subtype.ext <| funext fun n => by
      show Submodule.factor (h₁ n) (Submodule.factor (h₂ (n + 1)) (y.1 (n + 1 + c))) = y.1 n
      rw [eq_factor_of_mem_towerLimit K hK y.2 (show n ≤ n + 1 + c by omega)]
      obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (y.1 (n + 1 + c))
      rw [← hz]
      rfl)
    (LinearMap.ext fun x => Subtype.ext <| funext fun n => by
      show Submodule.factor (h₂ n) (Submodule.factor (h₁ (n + c)) (x.1 (n + c + 1))) = x.1 n
      rw [← x.2 (show n ≤ n + c + 1 by omega)]
      obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (x.1 (n + c + 1))
      rw [← hz]
      rfl)
end Adic
end
end GroundTheory.Arith.SchemeCoh


