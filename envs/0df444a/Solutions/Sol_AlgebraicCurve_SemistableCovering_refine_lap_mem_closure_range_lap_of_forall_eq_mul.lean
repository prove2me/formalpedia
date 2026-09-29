-- Prove2me | solution 1 for AlgebraicCurve.SemistableCovering.refine_lap_mem_closure_range_lap_of_forall_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b9f8c29a-0f93-5fa3-aacc-30ba306dbbf2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableCovering_refine_lap_mem_closure_range_lap_of_forall_eq_mul

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace RefineLap

def lapOf {V E : Type*} [Fintype E] [DecidableEq V] (ends : E → V × V) : V → (V → ℤ) := fun v =>
  ∑ ε : E, ((if (ends ε).1 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
    (if (ends ε).2 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))

def seg {V E : Type*} [DecidableEq V] (ends : E → V × V) (ε : E) : V → ℤ :=
  (Pi.single (ends ε).1 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ)

theorem lapOf_apply_eq_sum_seg {V E : Type*} [Fintype E] [DecidableEq V] (ends : E → V × V) (u : V) :
    lapOf ends u = ∑ ε, ((if (ends ε).1 = u then (1 : ℤ) else 0) - (if (ends ε).2 = u then (1 : ℤ) else 0)) •
      seg ends ε := by
  unfold lapOf seg
  refine Finset.sum_congr rfl fun ε _ => ?_
  by_cases hp : (ends ε).1 = u <;> by_cases hq : (ends ε).2 = u
  · rw [if_pos hp, if_pos hq, if_pos hp, if_pos hq, ← hp, hq.trans hp.symm]; simp
  · rw [if_pos hp, if_neg hq, if_pos hp, if_neg hq, ← hp]; simp
  · rw [if_neg hp, if_pos hq, if_neg hp, if_pos hq, ← hq]; simp [neg_sub]
  · rw [if_neg hp, if_neg hq, if_neg hp, if_neg hq]; simp

theorem sum_smul_lapOf {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (ends : E → V × V) (τ : V → ℤ) :
    ∑ u, τ u • lapOf ends u = ∑ ε, (τ (ends ε).1 - τ (ends ε).2) • seg ends ε := by
  unfold lapOf
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ε _ => ?_
  simp only [smul_add, Finset.sum_add_distrib, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  unfold seg
  rw [← neg_sub (Pi.single (ends ε).1 1 : V → ℤ) (Pi.single (ends ε).2 1), smul_neg, ← sub_eq_add_neg, ← sub_smul]

theorem sum_smul_lapOf_mem {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (ends : E → V × V) (τ : V → ℤ) :
    ∑ u, τ u • lapOf ends u ∈ AddSubgroup.closure (Set.range (lapOf ends)) :=
  AddSubgroup.sum_mem _ fun u _ => AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self u)) _

theorem sum_range_single_sub_single {V : Type*} [DecidableEq V] (f : ℕ → V) (a M : ℕ) :
    ∑ j ∈ Finset.range M, ((Pi.single (f (a + j)) 1 : V → ℤ) - Pi.single (f (a + j + 1)) 1) =
      (Pi.single (f a) 1 : V → ℤ) - Pi.single (f (a + M)) 1 := by
  have := Finset.sum_range_sub' (fun j => (Pi.single (f (a + j)) 1 : V → ℤ)) M
  simpa [Nat.add_assoc] using this

end RefineLap

open RefineLap in
theorem solution
    (n m : ℕ) (src tgt : Fin m → Fin n) (W : Fin m → ℕ) (hW : ∀ e, 0 < W e) (M : ℕ) (hM : 0 < M)
    (W' : Fin m → ℕ) (hW' : ∀ e, W' e = M * W e) :
    let V := Fin n ⊕ (Σ e : Fin m, Fin (W e - 1))
    let ends : (Σ e : Fin m, Fin (W e)) → V × V := fun ε =>
      (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
       if h1 : ε.2.1 + 1 = W ε.1 then Sum.inl (tgt ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)
    let lap : V → (V → ℤ) := fun v => ∑ ε : Σ e : Fin m, Fin (W e),
      ((if (ends ε).1 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
       (if (ends ε).2 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))
    let V' := Fin n ⊕ (Σ e : Fin m, Fin (W' e - 1))
    let ends' : (Σ e : Fin m, Fin (W' e)) → V' × V' := fun ε =>
      (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
       if h1 : ε.2.1 + 1 = W' ε.1 then Sum.inl (tgt ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)
    let lap' : V' → (V' → ℤ) := fun v => ∑ ε : Σ e : Fin m, Fin (W' e),
      ((if (ends' ε).1 = v then (Pi.single v 1 : V' → ℤ) - (Pi.single (ends' ε).2 1 : V' → ℤ) else 0) +
       (if (ends' ε).2 = v then (Pi.single v 1 : V' → ℤ) - (Pi.single (ends' ε).1 1 : V' → ℤ) else 0))
    let ι : V → V' := Sum.elim (fun i => Sum.inl i) (fun p => Sum.inr ⟨p.1, ⟨M * (p.2.1 + 1) - 1, by
      have h1 := p.2.2; have h2 : M * (p.2.1 + 1) < M * W p.1 := Nat.mul_lt_mul_of_pos_left (by omega) hM
      have h3 : 0 < M * (p.2.1 + 1) := Nat.mul_pos hM (Nat.succ_pos _); have h4 := hW' p.1; omega⟩⟩)
    let ρ : (V → ℤ) →+ (V' → ℤ) := AddMonoidHom.pi fun v' =>
      ∑ v ∈ Finset.univ.filter (fun v => ι v = v'), Pi.evalAddMonoidHom (fun _ : V => ℤ) v
    Function.Injective ι ∧
    (∀ (x : V → ℤ) (v' : V'), ρ x v' = ∑ v ∈ Finset.univ.filter (fun v => ι v = v'), x v) ∧
    (∀ (x : V → ℤ) (v : V), ρ x (ι v) = x v) ∧
    (∀ (x : V → ℤ) (v' : V'), (∀ v, ι v ≠ v') → ρ x v' = 0) ∧
    (∀ (v : V) (c : ℤ), ρ (Pi.single v c) = Pi.single (ι v) c) ∧
    (∀ u : V, ρ (lap u) ∈ AddSubgroup.closure (Set.range lap')) ∧
    AddSubgroup.closure (Set.range lap) ≤ (AddSubgroup.closure (Set.range lap')).comap ρ := by
  intro V ends lap V' ends' lap' ι ρ
  have hW0 : ∀ e, W e ≠ 0 := fun e => (hW e).ne'
  have hW'0 : ∀ e, W' e ≠ 0 := fun e => by rw [hW' e]; exact (Nat.mul_pos hM (hW e)).ne'

  have hρ : ∀ (x : V → ℤ) (v' : V'), ρ x v' = ∑ v ∈ Finset.univ.filter (fun v => ι v = v'), x v := by
    intro x v'
    simp only [ρ, AddMonoidHom.pi_apply, AddMonoidHom.finsetSum_apply, Pi.evalAddMonoidHom_apply]
  have hι : Function.Injective ι := by
    rintro (i | ⟨e, d⟩) (i' | ⟨e', d'⟩) h
    · simp only [ι, Sum.elim_inl] at h
      rw [Sum.inl_injective h]
    · simp [ι] at h
    · simp [ι] at h
    · simp only [ι, Sum.elim_inr] at h
      have h' := Sum.inr_injective h
      have he : e = e' := congrArg Sigma.fst h'
      subst he
      have hv : M * (d.1 + 1) - 1 = M * (d'.1 + 1) - 1 :=
        congrArg (fun p : (Σ e : Fin m, Fin (W' e - 1)) => (p.2 : ℕ)) h'
      have hd := d.2; have hd' := d'.2
      have h3 : 0 < M * (d.1 + 1) := Nat.mul_pos hM (Nat.succ_pos _)
      have h3' : 0 < M * (d'.1 + 1) := Nat.mul_pos hM (Nat.succ_pos _)
      have h4 : M * (d.1 + 1) = M * (d'.1 + 1) := by omega
      have h5 : d.1 + 1 = d'.1 + 1 := Nat.eq_of_mul_eq_mul_left hM h4
      have h6 : d = d' := Fin.ext (by omega)
      subst h6
      rfl
  have hρι : ∀ (x : V → ℤ) (v : V), ρ x (ι v) = x v := by
    intro x v
    rw [hρ, Finset.sum_eq_single_of_mem v (by simp)
      (fun b hb hne => absurd (hι (Finset.mem_filter.mp hb).2) hne)]
  have hρ0 : ∀ (x : V → ℤ) (v' : V'), (∀ v, ι v ≠ v') → ρ x v' = 0 := by
    intro x v' h
    rw [hρ]
    exact Finset.sum_eq_zero fun v hv => absurd (Finset.mem_filter.mp hv).2 (h v)
  have hρs : ∀ (v : V) (c : ℤ), ρ (Pi.single v c) = Pi.single (ι v) c := by
    intro v c
    funext v'
    by_cases h : ∃ v₀, ι v₀ = v'
    · obtain ⟨v₀, rfl⟩ := h
      rw [hρι]
      simp only [Pi.single_apply, hι.eq_iff]
    · simp only [not_exists] at h
      rw [hρ0 _ _ h, Pi.single_eq_of_ne (Ne.symm (h v))]

  have hlap : lap = lapOf ends := rfl
  have hlap' : lap' = lapOf ends' := rfl
  let pos : ∀ e : Fin m, ℕ → V := fun e p =>
    if h0 : p = 0 then Sum.inl (src e) else if hw : p < W e then Sum.inr ⟨e, ⟨p - 1, by omega⟩⟩ else Sum.inl (tgt e)
  let pos' : ∀ e : Fin m, ℕ → V' := fun e p =>
    if h0 : p = 0 then Sum.inl (src e) else if hw : p < W' e then Sum.inr ⟨e, ⟨p - 1, by omega⟩⟩ else Sum.inl (tgt e)
  have hends : ∀ (e : Fin m) (j : Fin (W e)), ends ⟨e, j⟩ = (pos e j, pos e (j + 1)) := by
    intro e j
    have hj := j.2
    simp only [ends, pos]
    ext
    · by_cases h0 : (j : ℕ) = 0
      · simp [h0]
      · simp [h0, hj]
    · by_cases h1 : (j : ℕ) + 1 = W e
      · simp [h1, hW0 e]
      · have : (j : ℕ) + 1 < W e := by omega
        simp [h1, this]
  have hends' : ∀ (e : Fin m) (j : Fin (W' e)), ends' ⟨e, j⟩ = (pos' e j, pos' e (j + 1)) := by
    intro e j
    have hj := j.2
    simp only [ends', pos']
    ext
    · by_cases h0 : (j : ℕ) = 0
      · simp [h0]
      · simp [h0, hj]
    · by_cases h1 : (j : ℕ) + 1 = W' e
      · simp [h1, hW'0 e]
      · have : (j : ℕ) + 1 < W' e := by omega
        simp [h1, this]
  have hpos0 : ∀ e : Fin m, pos e 0 = Sum.inl (src e) := fun e => by simp [pos]
  have hposw : ∀ e : Fin m, pos e (W e) = Sum.inl (tgt e) := fun e => by simp [pos, hW0 e]
  have hpos0' : ∀ e : Fin m, pos' e 0 = Sum.inl (src e) := fun e => by simp [pos']
  have hposw' : ∀ e : Fin m, pos' e (W' e) = Sum.inl (tgt e) := fun e => by simp [pos', hW'0 e]
  have hposinr' : ∀ (e : Fin m) (p : ℕ) (h0 : p ≠ 0) (hp : p < W' e),
      pos' e p = Sum.inr ⟨e, ⟨p - 1, by omega⟩⟩ := by
    intro e p h0 hp
    simp [pos', h0, hp]
  have hinrV' : ∀ (e : Fin m) (A B : ℕ) (hA : A < W' e - 1) (hB : B < W' e - 1), A = B →
      (Sum.inr ⟨e, ⟨A, hA⟩⟩ : V') = Sum.inr ⟨e, ⟨B, hB⟩⟩ := by
    intro e A B hA hB h
    subst h
    rfl

  have hιpos : ∀ (e : Fin m) (k : ℕ), k ≤ W e → ι (pos e k) = pos' e (M * k) := by
    intro e k hk
    by_cases hk0 : k = 0
    · subst hk0
      rw [hpos0, Nat.mul_zero, hpos0']
      exact rfl
    · by_cases hkw : k < W e
      · have h1 : pos e k = Sum.inr ⟨e, ⟨k - 1, by omega⟩⟩ := by simp [pos, hk0, hkw]
        have h2 : M * k ≠ 0 := (Nat.mul_pos hM (Nat.pos_of_ne_zero hk0)).ne'
        have h3 : M * k < W' e := by rw [hW' e]; exact Nat.mul_lt_mul_of_pos_left hkw hM
        rw [h1, hposinr' e (M * k) h2 h3]
        refine hinrV' e _ _ _ _ ?_
        show M * (k - 1 + 1) - 1 = M * k - 1
        rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
      · have hkW : k = W e := by omega
        subst hkW
        rw [hposw, ← hW' e, hposw']
        exact rfl

  have hWe : ∀ e : Fin m, W e * M = W' e := fun e => by rw [hW' e, Nat.mul_comm]
  let eqv : ∀ e : Fin m, Fin (W e) × Fin M ≃ Fin (W' e) := fun e => finProdFinEquiv.trans (finCongr (hWe e))
  have heqv : ∀ (e : Fin m) (k : Fin (W e)) (j : Fin M), ((eqv e (k, j) : Fin (W' e)) : ℕ) = M * k + j := by
    intro e k j
    simp only [eqv, Equiv.trans_apply, finCongr_apply, Fin.val_cast, finProdFinEquiv_apply_val]
    omega

  have hmem : ∀ u : V, ρ (lap u) ∈ AddSubgroup.closure (Set.range lap') := by
    intro u

    let T : Fin m → ℕ → ℤ := fun e D =>
      (if pos e (D / M) = u then ((M : ℤ) - ((D % M : ℕ) : ℤ)) else 0) +
        (if pos e (D / M + 1) = u then ((D % M : ℕ) : ℤ) else 0)
    let τ : V' → ℤ :=
      Sum.elim (fun i => if (Sum.inl i : V) = u then (M : ℤ) else 0) (fun p => T p.1 (p.2.1 + 1))
    have hτpos : ∀ (e : Fin m) (D : ℕ), D ≤ W' e → τ (pos' e D) = T e D := by
      intro e D hD
      by_cases hD0 : D = 0
      · subst hD0
        rw [hpos0']
        simp [τ, T, hpos0]
      · by_cases hDw : D < W' e
        · rw [hposinr' e D hD0 hDw]
          show T e (D - 1 + 1) = T e D
          rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hD0)]
        · have hDW : D = W' e := by omega
          rw [hDW, hposw']
          simp only [τ, T, Sum.elim_inl]
          rw [hW' e, Nat.mul_div_cancel_left _ hM, Nat.mul_mod_right, hposw]
          simp
    have hT : ∀ (e : Fin m) (k j : ℕ), j < M →
        T e (M * k + j) - T e (M * k + j + 1) =
          (if pos e k = u then (1 : ℤ) else 0) - (if pos e (k + 1) = u then (1 : ℤ) else 0) := by
      intro e k j hj
      have hd1 : (M * k + j) / M = k := by rw [Nat.mul_add_div hM, Nat.div_eq_of_lt hj, Nat.add_zero]
      have hm1 : (M * k + j) % M = j := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
      by_cases hj1 : j + 1 < M
      · have hd2 : (M * k + j + 1) / M = k := by
          rw [Nat.add_assoc, Nat.mul_add_div hM, Nat.div_eq_of_lt hj1, Nat.add_zero]
        have hm2 : (M * k + j + 1) % M = j + 1 := by
          rw [Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt hj1]
        simp only [T, hd1, hm1, hd2, hm2]
        split_ifs <;> push_cast <;> ring
      · have hjM : j + 1 = M := by omega
        have he2 : M * k + j + 1 = M * (k + 1) := by rw [Nat.mul_succ]; omega
        have hd2 : (M * k + j + 1) / M = k + 1 := by rw [he2, Nat.mul_div_cancel_left _ hM]
        have hm2 : (M * k + j + 1) % M = 0 := by rw [he2, Nat.mul_mod_right]
        simp only [T, hd1, hm1, hd2, hm2, Nat.cast_zero, sub_zero, ite_self, add_zero]
        have hjz : ((j : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
        split_ifs <;> omega

    have h1 : ρ (lap u) = ∑ ε : Σ e : Fin m, Fin (W e),
        ((if (ends ε).1 = u then (1 : ℤ) else 0) - (if (ends ε).2 = u then (1 : ℤ) else 0)) •
          ((Pi.single (ι (ends ε).1) 1 : V' → ℤ) - Pi.single (ι (ends ε).2) 1) := by
      rw [hlap, lapOf_apply_eq_sum_seg, map_sum]
      refine Finset.sum_congr rfl fun ε _ => ?_
      simp only [seg, map_zsmul, map_sub, hρs]

    have h2 : ∀ (e : Fin m) (k : Fin (W e)),
        (Pi.single (ι (pos e k)) 1 : V' → ℤ) - Pi.single (ι (pos e ((k : ℕ) + 1))) 1 =
          ∑ j : Fin M, seg ends' ⟨e, eqv e (k, j)⟩ := by
      intro e k
      have hk := k.2
      rw [hιpos e k (le_of_lt hk), hιpos e (k + 1) hk, Nat.mul_succ,
        ← sum_range_single_sub_single (pos' e) (M * k) M, Finset.sum_range]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [seg, hends', heqv]
    have h3 : ρ (lap u) = ∑ e : Fin m, ∑ k : Fin (W e), ∑ j : Fin M,
        ((if pos e k = u then (1 : ℤ) else 0) - (if pos e ((k : ℕ) + 1) = u then (1 : ℤ) else 0)) •
          seg ends' ⟨e, eqv e (k, j)⟩ := by
      rw [h1, Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun k _ => ?_
      rw [hends]
      dsimp only
      rw [h2 e k, Finset.smul_sum]

    have h4 : ∑ x, τ x • lapOf ends' x = ∑ e : Fin m, ∑ k : Fin (W e), ∑ j : Fin M,
        ((if pos e k = u then (1 : ℤ) else 0) - (if pos e ((k : ℕ) + 1) = u then (1 : ℤ) else 0)) •
          seg ends' ⟨e, eqv e (k, j)⟩ := by
      rw [sum_smul_lapOf, Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [← Equiv.sum_comp (eqv e), Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
      congr 1
      rw [hends']
      dsimp only
      have hk := k.2
      have hj := j.2
      have hb : M * k + j + 1 ≤ W' e := by
        have h5 : M * (k.1 + 1) ≤ M * W e := Nat.mul_le_mul_left M (by omega)
        rw [Nat.mul_succ] at h5
        rw [hW' e]
        omega
      rw [heqv, hτpos e (M * k + j) (by omega), hτpos e (M * k + j + 1) hb, hT e k j hj]
    rw [h3, ← h4, hlap']
    exact sum_smul_lapOf_mem ends' τ

  refine ⟨hι, hρ, hρι, hρ0, hρs, hmem, ?_⟩
  rw [AddSubgroup.closure_le]
  rintro _ ⟨u, rfl⟩
  exact hmem u

end S_AlgebraicCurve_SemistableCovering_refine_lap_mem_closure_range_lap_of_forall_eq_mul
end P2MW
export P2MW.S_AlgebraicCurve_SemistableCovering_refine_lap_mem_closure_range_lap_of_forall_eq_mul (solution)
