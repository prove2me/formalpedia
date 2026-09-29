-- Prove2me | solution 1 for AutomorphicForm.flowChart_add_single_eq_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f56cc5a7-0a67-5551-ad18-b6da441663cb

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_flowChart_add_single_eq_mul_conj

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.InfinitePlace
open AutomorphicForm
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel
open scoped Classical

namespace CCProof

variable (K : Type) [Field K] [NumberField K]

abbrev Letter : Type :=
  (Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕ (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)

theorem prod_ofFn_update {G : Type*} [Group G] :
    ∀ (n : ℕ) (f g : Fin n → G) (j : Fin n) (c : G),
      (∀ i, i ≠ j → g i = f i) → g j = f j * c →
        (List.ofFn g).prod = (List.ofFn f).prod * ((((List.ofFn f).drop (j.val + 1)).prod)⁻¹ * c * ((List.ofFn f).drop (j.val + 1)).prod)
  | 0, f, g, j, c, _, _ => j.elim0
  | n + 1, f, g, j, c, hne, hj => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    refine Fin.cases ?_ (fun j' => ?_) j hne hj
    · intro hne hj
      have htail : (List.ofFn fun i : Fin n => g i.succ) = List.ofFn fun i : Fin n => f i.succ := by
        congr 1; funext i; exact hne _ (Fin.succ_ne_zero i)
      rw [htail, hj]
      simp only [Fin.val_zero, zero_add, List.drop_succ_cons, List.drop_zero]
      group
    · intro hne hj
      have ih := prod_ofFn_update n (fun i => f i.succ) (fun i => g i.succ) j' c
        (fun i hi => hne _ fun h => hi (Fin.succ_injective _ h)) hj
      have h0 : g 0 = f 0 := hne 0 (Fin.succ_ne_zero j').symm
      rw [ih, h0]
      simp only [Fin.val_succ, List.drop_succ_cons, mul_assoc]

theorem conj_list_prod {G M : Type*} [Group G] [Group M] (φ : M →* G) :
    ∀ (L : List (G × M)), (∀ p ∈ L, ∀ a : M, p.1⁻¹ * φ a * p.1 = φ (p.2⁻¹ * a * p.2)) →
      ∀ a : M, ((L.map Prod.fst).prod)⁻¹ * φ a * (L.map Prod.fst).prod =
        φ (((L.map Prod.snd).prod)⁻¹ * a * (L.map Prod.snd).prod)
  | [], _, a => by simp
  | p :: L, h, a => by
    have hp := h p List.mem_cons_self
    have ih := conj_list_prod φ L (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [List.map_cons, List.prod_cons, mul_inv_rev]
    calc (L.map Prod.fst).prod⁻¹ * p.1⁻¹ * φ a * (p.1 * (L.map Prod.fst).prod)
        = (L.map Prod.fst).prod⁻¹ * (p.1⁻¹ * φ a * p.1) * (L.map Prod.fst).prod := by group
      _ = (L.map Prod.fst).prod⁻¹ * φ (p.2⁻¹ * a * p.2) * (L.map Prod.fst).prod := by rw [hp]
      _ = φ ((L.map Prod.snd).prod⁻¹ * (p.2⁻¹ * a * p.2) * (L.map Prod.snd).prod) := ih _
      _ = φ ((L.map Prod.snd).prod⁻¹ * p.2⁻¹ * a * (p.2 * (L.map Prod.snd).prod)) := by group

theorem eq_of_forall_archComponent_eq {g h : GL (Fin 2) (InfiniteAdeleRing K)}
    (hc : ∀ w : InfinitePlace K, archComponent K w g = archComponent K w h) : g = h := by
  apply Units.ext
  ext i j
  funext w
  have := congrArg (fun m : GL (Fin 2) w.Completion => (m : Matrix (Fin 2) (Fin 2) w.Completion) i j) (hc w)
  simp only [archComponent_apply] at this
  exact this

theorem placed_comm_of_ne {w w' : InfinitePlace K} (hww : w ≠ w') (a : GL (Fin 2) w.Completion) (b : GL (Fin 2) w'.Completion) :
    adelicArchGLInclAt K w a * adelicArchGLInclAt K w' b = adelicArchGLInclAt K w' b * adelicArchGLInclAt K w a := by
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [map_mul, map_mul]
    refine eq_of_forall_archComponent_eq K fun v => ?_
    rw [map_mul, map_mul]
    show archComponent K v (glArch (𝓞 K) K (adelicArchGLIncl K (archGLIncl K w a))) *
        archComponent K v (glArch (𝓞 K) K (adelicArchGLIncl K (archGLIncl K w' b))) =
      archComponent K v (glArch (𝓞 K) K (adelicArchGLIncl K (archGLIncl K w' b))) *
        archComponent K v (glArch (𝓞 K) K (adelicArchGLIncl K (archGLIncl K w a)))
    rw [glArch_adelicArchGLIncl, glArch_adelicArchGLIncl]
    by_cases hv : v = w
    · subst hv
      rw [archComponent_archGLIncl_of_ne K hww, mul_one, one_mul]
    · rw [archComponent_archGLIncl_of_ne K hv, one_mul, mul_one]
  · rw [map_mul, map_mul]
    show glFin (𝓞 K) K (adelicArchGLIncl K (archGLIncl K w a)) * glFin (𝓞 K) K (adelicArchGLIncl K (archGLIncl K w' b)) =
      glFin (𝓞 K) K (adelicArchGLIncl K (archGLIncl K w' b)) * glFin (𝓞 K) K (adelicArchGLIncl K (archGLIncl K w a))
    rw [glFin_adelicArchGLIncl, glFin_adelicArchGLIncl]

theorem conj_eq_self_of_ne {w w' : InfinitePlace K} (hww : w ≠ w') (f : GL (Fin 2) w'.Completion) (a : GL (Fin 2) w.Completion) :
    (adelicArchGLInclAt K w' f)⁻¹ * adelicArchGLInclAt K w a * adelicArchGLInclAt K w' f = adelicArchGLInclAt K w a := by
  rw [mul_assoc, placed_comm_of_ne K hww a f, ← mul_assoc, inv_mul_cancel, one_mul]

theorem conjR {w : InfinitePlace K} (hw : w.IsReal) (f a : GL (Fin 2) ℝ) :
    (archRealGLAt hw f)⁻¹ * archRealGLAt hw a * archRealGLAt hw f = archRealGLAt (F := K) hw (f⁻¹ * a * f) := by
  rw [map_mul, map_mul, map_inv]

theorem conjC {w : InfinitePlace K} (hw : w.IsComplex) (f a : GL (Fin 2) ℂ) :
    (archComplexGLAt hw f)⁻¹ * archComplexGLAt hw a * archComplexGLAt hw f = archComplexGLAt (F := K) hw (f⁻¹ * a * f) := by
  rw [map_mul, map_mul, map_inv]

end CCProof

open CCProof in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (L₀ : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)))
    (j : Fin L₀.length) (t : Fin L₀.length → ℝ) (s : ℝ) :
    let flow : ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) → ℝ → AdelicGL2 (𝓞 K) K :=
      fun d t => Sum.elim (fun d => archFlowAt d.2.1 d.2.2 t) (fun d => archFlowAtComplex d.2.1 d.2.2 t) d
    let chart : (Fin L₀.length → ℝ) → AdelicGL2 (𝓞 K) K :=
      fun t => (List.ofFn fun i => flow (L₀.get i) (t i)).prod
    let tailMatR : InfinitePlace K → GL (Fin 2) ℝ := fun w =>
      ((List.ofFn fun i : Fin L₀.length => match L₀.get i with
        | Sum.inl d => if d.1 = w then archFlowMatrix d.2.2 (t i) else 1
        | Sum.inr _ => (1 : GL (Fin 2) ℝ)).drop (j.val + 1)).prod
    let tailMatC : InfinitePlace K → GL (Fin 2) ℂ := fun w =>
      ((List.ofFn fun i : Fin L₀.length => match L₀.get i with
        | Sum.inr d => if d.1 = w then archFlowMatrixComplex d.2.2 (t i) else 1
        | Sum.inl _ => (1 : GL (Fin 2) ℂ)).drop (j.val + 1)).prod
    match L₀.get j with
    | Sum.inl d => chart (t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) =
        chart t * archRealGLAt d.2.1 ((tailMatR d.1)⁻¹ * archFlowMatrix d.2.2 s * tailMatR d.1)
    | Sum.inr d => chart (t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) =
        chart t * archComplexGLAt d.2.1 ((tailMatC d.1)⁻¹ * archFlowMatrixComplex d.2.2 s * tailMatC d.1) := by
  intro flow chart tailMatR tailMatC

  have hfac : ∀ i : Fin L₀.length, i ≠ j →
      flow (L₀.get i) ((t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) i) = flow (L₀.get i) (t i) := by
    intro i hi
    simp [hi]
  have hj' : (t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) j = t j + s := by simp
  have hprod : ∀ c : AdelicGL2 (𝓞 K) K, flow (L₀.get j) (t j + s) = flow (L₀.get j) (t j) * c →
      chart (t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) =
        chart t * ((((List.ofFn fun i => flow (L₀.get i) (t i)).drop (j.val + 1)).prod)⁻¹ * c *
          ((List.ofFn fun i => flow (L₀.get i) (t i)).drop (j.val + 1)).prod) := by
    intro c hc
    exact prod_ofFn_update L₀.length (fun i => flow (L₀.get i) (t i))
      (fun i => flow (L₀.get i) ((t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) i)) j c hfac
      (by show flow (L₀.get j) ((t + s • (Pi.single j (1 : ℝ) : Fin L₀.length → ℝ)) j) = flow (L₀.get j) (t j) * c; rw [hj', hc])
  rcases hj : L₀.get j with ⟨w, hw, dj⟩ | ⟨w, hw, dj⟩
  ·
    simp only
    have hsplit : flow (Sum.inl ⟨w, hw, dj⟩) (t j + s) = flow (Sum.inl ⟨w, hw, dj⟩) (t j) * archFlowAt hw dj s := by
      show archFlowAt hw dj (t j + s) = archFlowAt hw dj (t j) * archFlowAt hw dj s
      exact archFlowAt_add hw dj (t j) s
    rw [hj] at hprod
    rw [hprod (archFlowAt hw dj s) hsplit]
    congr 1

    let μ : Fin L₀.length → GL (Fin 2) ℝ := fun i => match L₀.get i with
      | Sum.inl d => if d.1 = w then archFlowMatrix d.2.2 (t i) else 1
      | Sum.inr _ => (1 : GL (Fin 2) ℝ)
    have key : ∀ (i : Fin L₀.length) (a : GL (Fin 2) ℝ),
        (flow (L₀.get i) (t i))⁻¹ * archRealGLAt hw a * flow (L₀.get i) (t i) = archRealGLAt hw ((μ i)⁻¹ * a * μ i) := by
      intro i a
      simp only [μ]
      rcases hi : L₀.get i with ⟨w', hw', di⟩ | ⟨w', hw', di⟩
      · simp only
        by_cases hww : w' = w
        · subst hww
          rw [if_pos rfl]
          exact conjR K hw _ _
        · rw [if_neg hww, inv_one, one_mul, mul_one]
          show (adelicArchGLInclAt K w' _)⁻¹ * adelicArchGLInclAt K w _ * adelicArchGLInclAt K w' _ = adelicArchGLInclAt K w _
          exact conj_eq_self_of_ne K (Ne.symm hww) _ _
      · simp only [inv_one, one_mul, mul_one]
        have hww : w ≠ w' := fun h => by subst h; exact (not_isReal_iff_isComplex.mpr hw') hw
        show (adelicArchGLInclAt K w' _)⁻¹ * adelicArchGLInclAt K w _ * adelicArchGLInclAt K w' _ = adelicArchGLInclAt K w _
        exact conj_eq_self_of_ne K hww _ _
    have hL := conj_list_prod (archRealGLAt (F := K) hw)
      (((List.ofFn fun i : Fin L₀.length => (flow (L₀.get i) (t i), μ i))).drop (j.val + 1))
      (fun p hp a => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_drop hp)
        exact key i a)
      (archFlowMatrix dj s)
    rw [List.map_drop, List.map_drop, List.map_ofFn, List.map_ofFn] at hL
    exact hL
  ·
    simp only
    have hsplit : flow (Sum.inr ⟨w, hw, dj⟩) (t j + s) = flow (Sum.inr ⟨w, hw, dj⟩) (t j) * archFlowAtComplex hw dj s := by
      show archFlowAtComplex hw dj (t j + s) = archFlowAtComplex hw dj (t j) * archFlowAtComplex hw dj s
      exact archFlowAtComplex_add hw dj (t j) s
    rw [hj] at hprod
    rw [hprod (archFlowAtComplex hw dj s) hsplit]
    congr 1
    let μ : Fin L₀.length → GL (Fin 2) ℂ := fun i => match L₀.get i with
      | Sum.inr d => if d.1 = w then archFlowMatrixComplex d.2.2 (t i) else 1
      | Sum.inl _ => (1 : GL (Fin 2) ℂ)
    have key : ∀ (i : Fin L₀.length) (a : GL (Fin 2) ℂ),
        (flow (L₀.get i) (t i))⁻¹ * archComplexGLAt hw a * flow (L₀.get i) (t i) = archComplexGLAt hw ((μ i)⁻¹ * a * μ i) := by
      intro i a
      simp only [μ]
      rcases hi : L₀.get i with ⟨w', hw', di⟩ | ⟨w', hw', di⟩
      · simp only [inv_one, one_mul, mul_one]
        have hww : w ≠ w' := fun h => by subst h; exact (not_isReal_iff_isComplex.mpr hw) hw'
        show (adelicArchGLInclAt K w' _)⁻¹ * adelicArchGLInclAt K w _ * adelicArchGLInclAt K w' _ = adelicArchGLInclAt K w _
        exact conj_eq_self_of_ne K hww _ _
      · simp only
        by_cases hww : w' = w
        · subst hww
          rw [if_pos rfl]
          exact conjC K hw _ _
        · rw [if_neg hww, inv_one, one_mul, mul_one]
          show (adelicArchGLInclAt K w' _)⁻¹ * adelicArchGLInclAt K w _ * adelicArchGLInclAt K w' _ = adelicArchGLInclAt K w _
          exact conj_eq_self_of_ne K (Ne.symm hww) _ _
    have hL := conj_list_prod (archComplexGLAt (F := K) hw)
      (((List.ofFn fun i : Fin L₀.length => (flow (L₀.get i) (t i), μ i))).drop (j.val + 1))
      (fun p hp a => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_drop hp)
        exact key i a)
      (archFlowMatrixComplex dj s)
    rw [List.map_drop, List.map_drop, List.map_ofFn, List.map_ofFn] at hL
    exact hL

end S_AutomorphicForm_flowChart_add_single_eq_mul_conj
end P2MW
export P2MW.S_AutomorphicForm_flowChart_add_single_eq_mul_conj (solution)
