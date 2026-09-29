-- Prove2me | solution 1 for AutomorphicForm.exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/8d9e5dfa-3ab1-50c6-bcd1-b8ccd1e3c4c3

import Mathlib
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Theorems.Thm_MeasureTheory_exists_measurableEquiv_measurePreserving_pi_apply_succ_eq_inv_mul_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory MeasureTheory.Measure TopologicalSpace Function

noncomputable section

namespace P2mTwistedShiftDescent

open AutomorphicForm

section Algebra

variable {G : Type*} [Group G]

def rho (θ : G →* G) (m : ℕ) : (Fin (m + 1) → G) →* (Fin (m + 1) → G) :=
  MonoidHom.pi fun j : Fin (m + 1) =>
    Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
                (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
      (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j

variable (θ : G →* G) {m : ℕ}

@[scoped simp] theorem rho_apply_last (x : Fin (m + 1) → G) : rho θ m x (Fin.last m) = θ (x 0) := by
  simp [rho, MonoidHom.pi_apply, Fin.lastCases_last]

@[scoped simp] theorem rho_apply_castSucc (x : Fin (m + 1) → G) (k : Fin m) :
    rho θ m x k.castSucc = x k.succ := by
  simp [rho, MonoidHom.pi_apply, Fin.lastCases_castSucc]

def listProd {n : ℕ} (g : Fin n → G) : G := (List.ofFn g).prod

def string {n : ℕ} (g : Fin n → G) (h : G) : Fin (n + 1) → G :=
  Fin.snoc g ((listProd g)⁻¹ * h)

@[scoped simp] theorem string_castSucc {n : ℕ} (g : Fin n → G) (h : G) (k : Fin n) :
    string g h (Fin.castSucc k) = g k := by
  simp [string]

@[scoped simp] theorem string_last {n : ℕ} (g : Fin n → G) (h : G) :
    string g h (Fin.last n) = (listProd g)⁻¹ * h := by
  simp [string]

theorem listProd_zero (g : Fin 0 → G) : listProd g = 1 := by
  simp [listProd]

theorem listProd_succ {n : ℕ} (g : Fin (n + 1) → G) :
    listProd g = listProd (fun k : Fin n => g (Fin.castSucc k)) * g (Fin.last n) := by
  unfold listProd
  rw [List.ofFn_succ', List.prod_concat]

theorem listProd_telescope : ∀ {n : ℕ} (x : Fin (n + 1) → G) (E : Fin n → G),
    listProd (fun k : Fin n => (x (Fin.castSucc k))⁻¹ * E k * x (Fin.succ k)) =
      (x 0)⁻¹ * listProd E * x (Fin.last n)
  | 0, x, E => by simp [listProd_zero]
  | n + 1, x, E => by
      rw [listProd_succ, listProd_succ E]
      have ih := listProd_telescope (fun k : Fin (n + 1) => x (Fin.castSucc k)) (fun k => E (Fin.castSucc k))
      have hfun : (fun k : Fin n => (x (Fin.castSucc (Fin.castSucc k)))⁻¹ * E (Fin.castSucc k) *
          x (Fin.castSucc (Fin.succ k))) =
          fun k : Fin n => (x (Fin.castSucc (Fin.castSucc k)))⁻¹ * E (Fin.castSucc k) *
            x (Fin.succ (Fin.castSucc k)) := by
        funext k; rw [Fin.succ_castSucc]
      rw [← hfun, ih, Fin.succ_last]
      simp only [Fin.castSucc_zero]
      group

theorem continuous_listProd [TopologicalSpace G] [IsTopologicalGroup G] :
    ∀ {n : ℕ}, Continuous (listProd : (Fin n → G) → G)
  | 0 => by
      have h : (listProd : (Fin 0 → G) → G) = fun _ => 1 := funext listProd_zero
      rw [h]; exact continuous_const
  | n + 1 => by
      have h : (listProd : (Fin (n + 1) → G) → G) =
          fun g => listProd (fun k : Fin n => g (Fin.castSucc k)) * g (Fin.last n) := funext listProd_succ
      rw [h]
      exact (continuous_listProd.comp (continuous_pi fun k => continuous_apply _)).mul (continuous_apply _)

def partialProd (δ : Fin (m + 1) → G) (j : ℕ) : G := ((List.ofFn δ).take j).prod

theorem partialProd_zero (δ : Fin (m + 1) → G) : partialProd δ 0 = 1 := by
  simp [partialProd]

theorem partialProd_succ (δ : Fin (m + 1) → G) (j : ℕ) (hj : j < m + 1) :
    partialProd δ (j + 1) = partialProd δ j * δ ⟨j, hj⟩ := by
  unfold partialProd
  have hlen : j < (List.ofFn δ).length := by rw [List.length_ofFn]; exact hj
  rw [List.prod_take_succ _ _ hlen, List.getElem_ofFn]

theorem partialProd_length (δ : Fin (m + 1) → G) : partialProd δ (m + 1) = listProd δ := by
  unfold partialProd listProd
  rw [List.take_of_length_le (by rw [List.length_ofFn])]

theorem mem_sigmaCentralizer_rho_iff (δ t : Fin (m + 1) → G) :
    t ∈ sigmaCentralizer (rho θ m) δ ↔
      (∀ k : Fin m, t k.castSucc * δ k.castSucc = δ k.castSucc * t k.succ) ∧
        t (Fin.last m) * δ (Fin.last m) = δ (Fin.last m) * θ (t 0) := by
  rw [mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul, funext_iff, Fin.forall_fin_succ']
  simp only [Pi.mul_apply, rho_apply_castSucc, rho_apply_last]

variable {θ}

theorem apply_eq_of_mem {δ t : Fin (m + 1) → G} (ht : t ∈ sigmaCentralizer (rho θ m) δ) :
    ∀ (j : ℕ) (hj : j < m + 1), t ⟨j, hj⟩ = (partialProd δ j)⁻¹ * t 0 * partialProd δ j
  | 0, hj => by simp [partialProd_zero]
  | j + 1, hj => by
      have hj' : j < m + 1 := Nat.lt_of_succ_lt hj
      have hjm : j < m := Nat.lt_of_succ_lt_succ hj
      have ih := apply_eq_of_mem ht j hj'
      have hrel := ((mem_sigmaCentralizer_rho_iff θ δ t).1 ht).1 ⟨j, hjm⟩

      have hcs : (Fin.castSucc (⟨j, hjm⟩ : Fin m) : Fin (m + 1)) = ⟨j, hj'⟩ := rfl
      have hsc : (Fin.succ (⟨j, hjm⟩ : Fin m) : Fin (m + 1)) = ⟨j + 1, hj⟩ := rfl
      rw [hcs, hsc] at hrel
      rw [partialProd_succ δ j hj']
      have h1 : t ⟨j + 1, hj⟩ = (δ ⟨j, hj'⟩)⁻¹ * t ⟨j, hj'⟩ * δ ⟨j, hj'⟩ := by
        rw [mul_assoc, eq_inv_mul_iff_mul_eq]; exact hrel.symm
      rw [h1, ih]
      group

theorem apply_zero_mem {δ t : Fin (m + 1) → G} (ht : t ∈ sigmaCentralizer (rho θ m) δ) :
    t 0 ∈ sigmaCentralizer θ (listProd δ) := by
  rw [mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul]
  have hlast := ((mem_sigmaCentralizer_rho_iff θ δ t).1 ht).2
  have hm := apply_eq_of_mem ht m (Nat.lt_succ_self m)
  have hlm : (Fin.last m : Fin (m + 1)) = ⟨m, Nat.lt_succ_self m⟩ := rfl
  rw [hlm] at hlast
  rw [hm] at hlast

  rw [← partialProd_length, partialProd_succ δ m (Nat.lt_succ_self m)]
  calc t 0 * (partialProd δ m * δ ⟨m, Nat.lt_succ_self m⟩)
      = partialProd δ m * ((partialProd δ m)⁻¹ * t 0 * partialProd δ m * δ ⟨m, Nat.lt_succ_self m⟩) := by
        group
    _ = partialProd δ m * (δ ⟨m, Nat.lt_succ_self m⟩ * θ (t 0)) := by rw [hlast]
    _ = partialProd δ m * δ ⟨m, Nat.lt_succ_self m⟩ * θ (t 0) := by group

def lift (δ : Fin (m + 1) → G) (t₀ : G) : Fin (m + 1) → G :=
  fun j => (partialProd δ j)⁻¹ * t₀ * partialProd δ j

theorem lift_apply (δ : Fin (m + 1) → G) (t₀ : G) (j : Fin (m + 1)) :
    lift δ t₀ j = (partialProd δ j)⁻¹ * t₀ * partialProd δ j := rfl

theorem lift_zero (δ : Fin (m + 1) → G) (t₀ : G) : lift δ t₀ 0 = t₀ := by
  rw [lift_apply]
  simp [partialProd_zero]

theorem lift_mem {δ : Fin (m + 1) → G} {t₀ : G} (ht₀ : t₀ ∈ sigmaCentralizer θ (listProd δ)) :
    lift δ t₀ ∈ sigmaCentralizer (rho θ m) δ := by
  rw [mem_sigmaCentralizer_rho_iff]
  refine ⟨fun k => ?_, ?_⟩
  · rw [lift_apply, lift_apply]
    have hcs : ((Fin.castSucc k : Fin (m + 1)) : ℕ) = k := rfl
    have hsc : ((Fin.succ k : Fin (m + 1)) : ℕ) = k + 1 := rfl
    rw [hcs, hsc, partialProd_succ δ k (Nat.lt_succ_of_lt k.2)]
    have hk : (⟨(k : ℕ), Nat.lt_succ_of_lt k.2⟩ : Fin (m + 1)) = Fin.castSucc k := rfl
    rw [hk]
    group
  · rw [lift_apply, lift_zero]
    have hlm : ((Fin.last m : Fin (m + 1)) : ℕ) = m := rfl
    rw [hlm]
    rw [mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul, ← partialProd_length,
      partialProd_succ δ m (Nat.lt_succ_self m)] at ht₀
    have hl : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) = Fin.last m := rfl
    rw [hl] at ht₀

    calc (partialProd δ m)⁻¹ * t₀ * partialProd δ m * δ (Fin.last m)
        = (partialProd δ m)⁻¹ * (t₀ * (partialProd δ m * δ (Fin.last m))) := by group
      _ = (partialProd δ m)⁻¹ * (partialProd δ m * δ (Fin.last m) * θ t₀) := by rw [ht₀]
      _ = δ (Fin.last m) * θ t₀ := by group

theorem lift_apply_zero_eq {δ t : Fin (m + 1) → G} (ht : t ∈ sigmaCentralizer (rho θ m) δ) :
    lift δ (t 0) = t := by
  funext j
  rw [lift_apply]
  exact (apply_eq_of_mem ht j j.2).symm

theorem lift_mul (δ : Fin (m + 1) → G) (a b : G) : lift δ (a * b) = lift δ a * lift δ b := by
  funext j
  simp only [lift_apply, Pi.mul_apply]
  group

def baseEquiv (δ : Fin (m + 1) → G) :
    sigmaCentralizer (rho θ m) δ ≃* sigmaCentralizer θ (listProd δ) where
  toFun t := ⟨(t : Fin (m + 1) → G) 0, apply_zero_mem t.2⟩
  invFun t₀ := ⟨lift δ (t₀ : G), lift_mem t₀.2⟩
  left_inv t := Subtype.ext (lift_apply_zero_eq t.2)
  right_inv t₀ := Subtype.ext (lift_zero δ _)
  map_mul' s t := Subtype.ext rfl

@[scoped simp] theorem coe_baseEquiv (δ : Fin (m + 1) → G) (t : sigmaCentralizer (rho θ m) δ) :
    ((baseEquiv δ t : sigmaCentralizer θ (listProd δ)) : G) = (t : Fin (m + 1) → G) 0 := rfl

theorem coe_baseEquiv_symm (δ : Fin (m + 1) → G) (t₀ : sigmaCentralizer θ (listProd δ)) :
    (((baseEquiv (θ := θ) δ).symm t₀ : sigmaCentralizer (rho θ m) δ) : Fin (m + 1) → G) =
      lift δ (t₀ : G) := rfl

def baseEquivₜ [TopologicalSpace G] [IsTopologicalGroup G] (δ : Fin (m + 1) → G) :
    sigmaCentralizer (rho θ m) δ ≃ₜ* sigmaCentralizer θ (listProd δ) where
  toMulEquiv := baseEquiv δ
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_apply 0).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    refine continuous_pi fun j => ?_
    simp only [lift_apply]
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

theorem baseEquivₜ_apply [TopologicalSpace G] [IsTopologicalGroup G] (δ : Fin (m + 1) → G)
    (t : sigmaCentralizer (rho θ m) δ) : baseEquivₜ (θ := θ) δ t = baseEquiv δ t := rfl

end Algebra

section Theta

variable {G : Type*} [Group G] (θ : G →* G) {m : ℕ} (δ : Fin (m + 1) → G)
  (Θ : (Fin (m + 1) → G) → Fin (m + 1) → G)
  (hΘ0 : ∀ x, Θ x 0 = x 0)
  (hΘs : ∀ x (k : Fin m), Θ x k.succ = (x k.castSucc)⁻¹ * δ k.castSucc * x k.succ)

include hΘs in

theorem twistedConj_eq_string (x : Fin (m + 1) → G) :
    x⁻¹ * δ * rho θ m x = string (Fin.tail (Θ x)) ((x 0)⁻¹ * listProd δ * θ (x 0)) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · rw [string_last, Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, rho_apply_last]
    have htail : (Fin.tail (Θ x) : Fin m → G) =
        fun k : Fin m => (x (Fin.castSucc k))⁻¹ * δ (Fin.castSucc k) * x (Fin.succ k) :=
      funext fun k => hΘs x k
    rw [htail, listProd_telescope, listProd_succ δ]
    group
  · rw [string_castSucc, Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, rho_apply_castSucc]
    exact (hΘs x k).symm

include hΘ0 hΘs in

theorem theta_mul_of_mem {t : Fin (m + 1) → G} (ht : t ∈ sigmaCentralizer (rho θ m) δ)
    (x : Fin (m + 1) → G) : Θ (t * x) = Fin.cons (t 0 * x 0) (Fin.tail (Θ x)) := by
  have hT := ((mem_sigmaCentralizer_rho_iff θ δ t).1 ht).1
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · rw [hΘ0, Fin.cons_zero, Pi.mul_apply]
  · rw [Fin.cons_succ, Fin.tail, hΘs, hΘs, Pi.mul_apply, Pi.mul_apply]
    have hk := hT k
    have hD : (t (Fin.castSucc k))⁻¹ * δ (Fin.castSucc k) * t (Fin.succ k) = δ (Fin.castSucc k) := by
      rw [mul_assoc, inv_mul_eq_iff_eq_mul]; exact hk.symm
    calc (t (Fin.castSucc k) * x (Fin.castSucc k))⁻¹ * δ (Fin.castSucc k) * (t (Fin.succ k) * x (Fin.succ k))
        = (x (Fin.castSucc k))⁻¹ * ((t (Fin.castSucc k))⁻¹ * δ (Fin.castSucc k) * t (Fin.succ k)) *
            x (Fin.succ k) := by group
      _ = (x (Fin.castSucc k))⁻¹ * δ (Fin.castSucc k) * x (Fin.succ k) := by rw [hD]

include hΘ0 in

theorem symm_apply_zero (Θ' : (Fin (m + 1) → G) → Fin (m + 1) → G) (hΘ' : ∀ y, Θ (Θ' y) = y)
    (y : Fin (m + 1) → G) : Θ' y 0 = y 0 := by
  rw [← hΘ0 (Θ' y), hΘ' y]

include hΘs in

theorem symm_apply_succ (Θ' : (Fin (m + 1) → G) → Fin (m + 1) → G) (hΘ' : ∀ y, Θ (Θ' y) = y)
    (y : Fin (m + 1) → G) (k : Fin m) :
    Θ' y k.succ = (δ k.castSucc)⁻¹ * Θ' y k.castSucc * y k.succ := by
  have h := hΘs (Θ' y) k
  rw [hΘ' y] at h

  rw [mul_assoc, eq_inv_mul_iff_mul_eq] at h
  rw [mul_assoc, eq_inv_mul_iff_mul_eq]
  exact h.symm

include hΘ0 hΘs in

theorem continuous_symm [TopologicalSpace G] [IsTopologicalGroup G]
    (Θ' : (Fin (m + 1) → G) → Fin (m + 1) → G) (hΘ' : ∀ y, Θ (Θ' y) = y) : Continuous Θ' := by
  refine continuous_pi fun j => ?_
  refine Fin.induction ?_ (fun k ih => ?_) j
  · have h : (fun y => Θ' y 0) = fun y => y 0 := funext (symm_apply_zero Θ hΘ0 Θ' hΘ')
    rw [h]; exact continuous_apply 0
  · have h : (fun y => Θ' y k.succ) = fun y => (δ k.castSucc)⁻¹ * Θ' y k.castSucc * y k.succ :=
      funext fun y => symm_apply_succ δ Θ hΘs Θ' hΘ' y k
    rw [h]
    exact (continuous_const.mul ih).mul (continuous_apply _)

include hΘ0 hΘs in

theorem continuous_theta [TopologicalSpace G] [IsTopologicalGroup G] : Continuous Θ := by
  refine continuous_pi fun j => Fin.cases ?_ (fun k => ?_) j
  · simp_rw [hΘ0]; exact continuous_apply 0
  · simp_rw [hΘs]
    exact (((continuous_apply _).inv).mul continuous_const).mul (continuous_apply _)

end Theta

section Straighten

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (θ : G →* G) {m : ℕ} (δ : Fin (m + 1) → G)
  (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant]

theorem continuous_cons {X : Type*} [TopologicalSpace X] {n : ℕ} :
    Continuous fun p : X × (Fin n → X) => (Fin.cons p.1 p.2 : Fin (n + 1) → X) := by
  refine continuous_pi fun j => Fin.cases ?_ (fun k => ?_) j
  · simp only [Fin.cons_zero]; exact continuous_fst
  · simp only [Fin.cons_succ]; exact (continuous_apply k).comp continuous_snd

theorem exists_straighten :
    ∃ (e : sigmaCentralizer (rho θ m) δ ≃ₜ* sigmaCentralizer θ (listProd δ))
      (X : G × (Fin m → G) ≃ₜ (Fin (m + 1) → G)),
      (∀ t, ((e t : sigmaCentralizer θ (listProd δ)) : G) = (t : Fin (m + 1) → G) 0) ∧
      MeasurePreserving X (μ.prod (Measure.pi fun _ => μ)) (Measure.pi fun _ => μ) ∧
      (∀ p : G × (Fin m → G), X p 0 = p.1) ∧
      (∀ p : G × (Fin m → G),
        (X p)⁻¹ * δ * rho θ m (X p) = string p.2 (p.1⁻¹ * listProd δ * θ p.1)) ∧
      (∀ (t : sigmaCentralizer (rho θ m) δ) (p : G × (Fin m → G)),
        (t : Fin (m + 1) → G) * X p = X (((e t : sigmaCentralizer θ (listProd δ)) : G) * p.1, p.2)) := by

  obtain ⟨Θ, hΘmp, hΘ⟩ :=
    MeasureTheory.exists_measurableEquiv_measurePreserving_pi_apply_succ_eq_inv_mul_mul μ δ
  have hΘ0 : ∀ x, Θ x 0 = x 0 := fun x => (hΘ x).1
  have hΘs : ∀ x (k : Fin m), Θ x k.succ = (x k.castSucc)⁻¹ * δ k.castSucc * x k.succ :=
    fun x k => (hΘ x).2 k
  have hΘ' : ∀ y, Θ (Θ.symm y) = y := fun y => Θ.apply_symm_apply y
  have hΘc : Continuous Θ := continuous_theta δ Θ hΘ0 hΘs
  have hΘsc : Continuous Θ.symm := continuous_symm δ Θ hΘ0 hΘs Θ.symm hΘ'

  let X : G × (Fin m → G) ≃ₜ (Fin (m + 1) → G) :=
    { toFun := fun p => Θ.symm (Fin.cons p.1 p.2)
      invFun := fun x => (Θ x 0, Fin.tail (Θ x))
      left_inv := fun p => by
        simp only [hΘ', Fin.cons_zero, Fin.tail_cons]
      right_inv := fun x => by
        simp only [Fin.cons_self_tail, MeasurableEquiv.symm_apply_apply]
      continuous_toFun := hΘsc.comp continuous_cons
      continuous_invFun :=
        ((continuous_apply 0).comp hΘc).prodMk ((continuous_pi fun k => continuous_apply _).comp hΘc) }
  have hXapply : ∀ p : G × (Fin m → G), X p = Θ.symm (Fin.cons p.1 p.2) := fun p => rfl
  have hΘX : ∀ p : G × (Fin m → G), Θ (X p) = Fin.cons p.1 p.2 := fun p => by rw [hXapply, hΘ']
  have hX0 : ∀ p : G × (Fin m → G), X p 0 = p.1 := fun p => by
    rw [← hΘ0 (X p), hΘX, Fin.cons_zero]
  have hXtail : ∀ p : G × (Fin m → G), Fin.tail (Θ (X p)) = p.2 := fun p => by
    rw [hΘX, Fin.tail_cons]
  refine ⟨baseEquivₜ δ, X, fun t => rfl, ?_, hX0, fun p => ?_, fun t p => ?_⟩
  ·
    set e₀ := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => G) 0 with he₀
    have he₀mp : MeasurePreserving e₀.symm (μ.prod (Measure.pi fun _ => μ)) (Measure.pi fun _ => μ) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0).symm
    have hcomp : (X : G × (Fin m → G) → Fin (m + 1) → G) = Θ.symm ∘ e₀.symm := by
      funext p
      rw [Function.comp_apply, hXapply, he₀, MeasurableEquiv.piFinSuccAbove_symm_apply]
      congr 1
      funext j
      rw [Fin.insertNthEquiv_apply, Fin.insertNth_zero']
    rw [hcomp]
    exact hΘmp.symm.comp he₀mp
  ·
    rw [twistedConj_eq_string θ δ Θ hΘs (X p), hXtail, hX0]
  ·
    apply Θ.injective
    change Θ ((t : Fin (m + 1) → G) * X p) = Θ (X (((t : Fin (m + 1) → G) 0) * p.1, p.2))
    rw [theta_mul_of_mem θ δ Θ hΘ0 hΘs t.2 (X p), hXtail, hX0, hΘX]

end Straighten

end P2mTwistedShiftDescent
p2m_reactivate "P2MW.S_AutomorphicForm_exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift.P2mTwistedShiftDescent"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift.P2mTwistedShiftDescent"

open MeasureTheory in
theorem solution
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (θ : G →* G) {m : ℕ} (δ : Fin (m + 1) → G)
    (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] :
    ∃ (e : AutomorphicForm.sigmaCentralizer
            (MonoidHom.pi fun j : Fin (m + 1) =>
              Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
                (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
                (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) δ ≃ₜ*
          AutomorphicForm.sigmaCentralizer θ (List.ofFn δ).prod)
      (X : G × (Fin m → G) ≃ₜ (Fin (m + 1) → G)),
      (∀ t, ((e t : AutomorphicForm.sigmaCentralizer θ (List.ofFn δ).prod) : G) =
        (t : Fin (m + 1) → G) 0) ∧
      MeasurePreserving X (μ.prod (Measure.pi fun _ => μ)) (Measure.pi fun _ => μ) ∧
      (∀ p : G × (Fin m → G), X p 0 = p.1) ∧
      (∀ p : G × (Fin m → G),
        (X p)⁻¹ * δ *
            (MonoidHom.pi fun j : Fin (m + 1) =>
              Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
                (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
                (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) (X p) =
          Fin.snoc p.2 (((List.ofFn p.2).prod)⁻¹ * (p.1⁻¹ * (List.ofFn δ).prod * θ p.1))) ∧
      (∀ (t : AutomorphicForm.sigmaCentralizer
              (MonoidHom.pi fun j : Fin (m + 1) =>
                Fin.lastCases (motive := fun _ => (Fin (m + 1) → G) →* G)
                (θ.comp (Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) 0))
                  (fun k : Fin m => Pi.evalMonoidHom (fun _ : Fin (m + 1) => G) k.succ) j) δ)
          (p : G × (Fin m → G)),
        (t : Fin (m + 1) → G) * X p =
          X (((e t : AutomorphicForm.sigmaCentralizer θ (List.ofFn δ).prod) : G) * p.1, p.2)) :=
  by
  have h := P2mTwistedShiftDescent.exists_straighten θ δ μ
  dsimp only [P2mTwistedShiftDescent.rho, P2mTwistedShiftDescent.listProd,
    P2mTwistedShiftDescent.string] at h
  exact h

end S_AutomorphicForm_exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift
end P2MW
export P2MW.S_AutomorphicForm_exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift (solution)
