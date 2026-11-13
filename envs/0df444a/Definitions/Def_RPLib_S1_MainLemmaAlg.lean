-- Prove2me | Definitions.Def_RPLib_S1_MainLemmaAlg
-- name    : RPLib_S1_MainLemmaAlg
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:14:07.694504+00:00
-- url     : https://prove2.me/theorems/c6c3083e-8433-47ce-aa12-f7217eafe67a
-- title:
--   Commuting averaging projections and a kernel-of-product lemma
-- statement:
--   Let $V$ be a vector space and $P_1,\dots,P_r$ commuting idempotent operators on $V$. If $(1-P_1)\cdots(1-P_r) v = 0$ then $v$ lies in $$\sum_{i=1}^r \operatorname{range}(P_i).$$ The file proves this and related facts for projections given by averages over finite cyclic group actions. It is the linear-algebra step of the Atkin-Lehner-Li Main Lemma.
--
--   **Formalization note.** This file is a library module of a formalization of the Ramanujan-Petersson conjecture for holomorphic cusp forms on $\Gamma_1(M)$. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, doi:10.1007/978-0-387-27226-9, Section 5.7

import Mathlib

/-!
# S1-MAINLEMMA-B, algebra part (AL): commuting projections and a kernel-of-product lemma

Library file of the Ramanujan-Petersson project (unit S1-MAINLEMMA-B).
-/

open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.MainLemmaB

section AL

variable {E H : Type*} [AddCommGroup E] [Module ℂ E] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] {ι : Type*}

/-- Common fixed space of the `P i`, `i ∈ l`. -/
def fixSp (l : List ι) (P : ι → Module.End ℂ E) : Submodule ℂ E :=
  ⨅ i ∈ l, LinearMap.ker (P i - 1)

lemma mem_fixSp {l : List ι} {P : ι → Module.End ℂ E} {v : E} :
    v ∈ fixSp l P ↔ ∀ i ∈ l, P i v = v := by
  simp [fixSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

/-- `W i = V0 ∩ Fix(Q i)`. -/
def Wsp (l : List ι) (P Q : ι → Module.End ℂ E) (i : ι) : Submodule ℂ E :=
  fixSp l P ⊓ LinearMap.ker (Q i - 1)

lemma mem_Wsp {l : List ι} {P Q : ι → Module.End ℂ E} {i : ι} {v : E} :
    v ∈ Wsp l P Q i ↔ (∀ j ∈ l, P j v = v) ∧ Q i v = v := by
  simp [Wsp, mem_fixSp, LinearMap.mem_ker, sub_eq_zero]

lemma prod_apply_eq_zero_of_fixed (Q : ι → Module.End ℂ E) :
    ∀ (l : List ι), l.Nodup → (∀ i ∈ l, ∀ j ∈ l, i ≠ j → Commute (Q i) (Q j)) →
      ∀ i ∈ l, ∀ v : E, Q i v = v → (l.map fun j => 1 - Q j).prod v = 0
  | [], _, _, i, hi, _, _ => by simp at hi
  | a :: l', hl, hc, i, hi, v, hv => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rcases List.mem_cons.mp hi with rfl | hi'
    · have hcomm : Commute (Q i) (l'.map fun j => 1 - Q j).prod := by
        apply Commute.list_prod_right
        intro y hy
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
        have hij : i ≠ j := fun h => hl.1 (h ▸ hj)
        exact (Commute.one_right _).sub_right (hc i (by simp) j (by simp [hj]) hij)
      have h2 : Q i ((l'.map fun j => 1 - Q j).prod v) = (l'.map fun j => 1 - Q j).prod v := by
        rw [← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply, hv]
      rw [LinearMap.sub_apply, Module.End.one_apply, h2, sub_self]
    · rw [prod_apply_eq_zero_of_fixed Q l' hl.2
        (fun i hi j hj => hc i (by simp [hi]) j (by simp [hj])) i hi' v hv, map_zero]

lemma prod_mul_eq (P Q : ι → Module.End ℂ E) :
    ∀ (l : List ι), l.Nodup → (∀ i ∈ l, ∀ j ∈ l, i ≠ j → Commute (P i) (Q j)) →
      (l.map fun i => P i * (1 - Q i)).prod = (l.map P).prod * (l.map fun i => 1 - Q i).prod
  | [], _, _ => by simp
  | a :: l', hl, hc => by
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.prod_cons]
    rw [prod_mul_eq P Q l' hl.2 (fun i hi j hj => hc i (by simp [hi]) j (by simp [hj]))]
    have hcm : Commute (1 - Q a) (l'.map P).prod := by
      apply Commute.list_prod_right
      intro y hy
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
      have hja : j ≠ a := fun h => hl.1 (h ▸ hj)
      exact (Commute.one_left _).sub_left (hc j (by simp [hj]) a (by simp) hja).symm
    calc P a * (1 - Q a) * ((l'.map P).prod * (l'.map fun i => 1 - Q i).prod)
        = P a * ((1 - Q a) * (l'.map P).prod) * (l'.map fun i => 1 - Q i).prod := by
          simp only [mul_assoc]
      _ = P a * ((l'.map P).prod * (1 - Q a)) * (l'.map fun i => 1 - Q i).prod := by rw [hcm.eq]
      _ = P a * (l'.map P).prod * ((1 - Q a) * (l'.map fun i => 1 - Q i).prod) := by
          simp only [mul_assoc]

variable (Φ : E →ₗ[ℂ] H)

omit [FiniteDimensional ℂ H] in
lemma inner_one_sub_symm {Q : Module.End ℂ E}
    (hQs : ∀ x y, ⟪Φ (Q x), Φ y⟫_ℂ = ⟪Φ x, Φ (Q y)⟫_ℂ) (x y : E) :
    ⟪Φ ((1 - Q) x), Φ y⟫_ℂ = ⟪Φ x, Φ ((1 - Q) y)⟫_ℂ := by
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, inner_sub_left, inner_sub_right, hQs]

/-- **Kernel-of-product lemma (AL).** -/
theorem mem_iSup_of_prod_eq_zero (hΦ : Function.Injective Φ)
    (l : List ι) (hl : l.Nodup) (P Q : ι → Module.End ℂ E)
    (hP2 : ∀ i, P i * P i = P i) (hQ2 : ∀ i, Q i * Q i = Q i)
    (hPs : ∀ i x y, ⟪Φ (P i x), Φ y⟫_ℂ = ⟪Φ x, Φ (P i y)⟫_ℂ)
    (hQs : ∀ i x y, ⟪Φ (Q i x), Φ y⟫_ℂ = ⟪Φ x, Φ (Q i y)⟫_ℂ)
    (hc : ∀ i ∈ l, ∀ j ∈ l, i ≠ j →
      Commute (P i) (P j) ∧ Commute (P i) (Q j) ∧ Commute (Q i) (Q j))
    (x : E) (hx : x ∈ fixSp l P) (h0 : (l.map fun i => 1 - Q i).prod x = 0) :
    x ∈ ⨆ i ∈ l, Wsp l P Q i := by
  classical
  set S : Submodule ℂ E := ⨆ i ∈ l, Wsp l P Q i with hSdef
  have hWS : ∀ i ∈ l, Wsp l P Q i ≤ S := fun i hi =>
    le_iSup₂ (f := fun j (_ : j ∈ l) => Wsp l P Q j) i hi
  have hSle : S ≤ fixSp l P := iSup₂_le fun i _ => inf_le_left
  set B : ι → Module.End ℂ E := fun i => P i * (1 - Q i) with hB
  -- (a) `B i` preserves `V0`
  have hBfix : ∀ i ∈ l, ∀ v ∈ fixSp l P, B i v ∈ fixSp l P := by
    intro i hi v hv
    rw [mem_fixSp] at hv ⊢
    intro j hj
    by_cases hij : j = i
    · subst hij
      simp only [hB, Module.End.mul_apply]
      rw [← Module.End.mul_apply (P j) (P j), hP2]
    · obtain ⟨hPP, hPQ, -⟩ := hc j hj i hi hij
      have e1 : P j (B i v) = B i (P j v) := by
        simp only [hB]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← mul_assoc, hPP.eq, mul_assoc,
          ((Commute.one_right _).sub_right hPQ).eq, mul_assoc]
      rw [e1, hv j hj]
  -- (b) `B i` maps `S` into `S`
  have hBS : ∀ i ∈ l, ∀ w ∈ S, B i w ∈ S := by
    intro i hi
    have : S ≤ S.comap (B i) := by
      refine iSup₂_le fun j hj => ?_
      intro w hw
      rw [Submodule.mem_comap]
      rw [mem_Wsp] at hw
      by_cases hij : j = i
      · subst hij
        have : B j w = 0 := by
          simp only [hB, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, hw.2,
            sub_self, map_zero]
        rw [this]
        exact S.zero_mem
      · refine hWS j hj ?_
        rw [mem_Wsp]
        refine ⟨(mem_fixSp.mp (hBfix i hi w (mem_fixSp.mpr hw.1))), ?_⟩
        obtain ⟨-, -, hQQ⟩ := hc j hj i hi hij
        obtain ⟨-, hPQ, -⟩ := hc i hi j hj (Ne.symm hij)
        have e1 : Q j (B i w) = B i (Q j w) := by
          simp only [hB]
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← mul_assoc, ← hPQ.eq, mul_assoc,
            ((Commute.one_right _).sub_right hQQ).eq, ← mul_assoc]
        rw [e1, hw.2]
    exact fun w hw => this hw
  -- `V∅`
  let good : E → Prop := fun v => v ∈ fixSp l P ∧ ∀ w ∈ S, ⟪Φ w, Φ v⟫_ℂ = 0
  have hBgood : ∀ i ∈ l, ∀ v, good v → good (B i v) := by
    intro i hi v hv
    refine ⟨hBfix i hi v hv.1, fun w hw => ?_⟩
    have hvP : P i v = v := mem_fixSp.mp hv.1 i hi
    have hwP : P i w = w := mem_fixSp.mp (hSle hw) i hi
    calc ⟪Φ w, Φ (B i v)⟫_ℂ = ⟪Φ (P i w), Φ ((1 - Q i) v)⟫_ℂ := by
          simp only [hB, Module.End.mul_apply]; rw [hPs]
      _ = ⟪Φ ((1 - Q i) (P i w)), Φ v⟫_ℂ := by rw [inner_one_sub_symm Φ (hQs i)]
      _ = ⟪Φ (P i ((1 - Q i) (P i w))), Φ v⟫_ℂ := by rw [hPs, hvP]
      _ = ⟪Φ (B i w), Φ v⟫_ℂ := by simp only [hB, Module.End.mul_apply, hwP]
      _ = 0 := hv.2 _ (hBS i hi w hw)
  have hBinj : ∀ i ∈ l, ∀ v, good v → B i v = 0 → v = 0 := by
    intro i hi v hv hBv
    have hvP : P i v = v := mem_fixSp.mp hv.1 i hi
    have hidem : (1 - Q i) * (1 - Q i) = 1 - Q i := by
      rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, hQ2 i]; abel
    have h1 : ⟪Φ ((1 - Q i) v), Φ ((1 - Q i) v)⟫_ℂ = 0 := by
      calc ⟪Φ ((1 - Q i) v), Φ ((1 - Q i) v)⟫_ℂ = ⟪Φ v, Φ ((1 - Q i) ((1 - Q i) v))⟫_ℂ := by
            rw [inner_one_sub_symm Φ (hQs i)]
        _ = ⟪Φ (P i v), Φ ((1 - Q i) v)⟫_ℂ := by rw [← Module.End.mul_apply, hidem, hvP]
        _ = ⟪Φ v, Φ (B i v)⟫_ℂ := by rw [hPs]; simp only [hB, Module.End.mul_apply]
        _ = 0 := by rw [hBv, map_zero, inner_zero_right]
    have h2 : (1 - Q i) v = 0 := hΦ (by rw [inner_self_eq_zero.mp h1, map_zero])
    have hQv : Q i v = v := by
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h2
      exact h2.symm
    have hvS : v ∈ S := hWS i hi (mem_Wsp.mpr ⟨mem_fixSp.mp hv.1, hQv⟩)
    exact hΦ (by rw [inner_self_eq_zero.mp (hv.2 v hvS), map_zero])
  have hpeel : ∀ m : List ι, (∀ i ∈ m, i ∈ l) → ∀ v, good v →
      good ((m.map B).prod v) ∧ ((m.map B).prod v = 0 → v = 0) := by
    intro m
    induction m with
    | nil => intro _ v hv; simpa using hv
    | cons a m' ih =>
      intro hm v hv
      obtain ⟨hg, hz⟩ := ih (fun i hi => hm i (by simp [hi])) v hv
      have ha : a ∈ l := hm a (by simp)
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      exact ⟨hBgood a ha _ hg, fun h => hz (hBinj a ha _ hg h)⟩
  -- decomposition `Φ x = Φ y + k'`
  obtain ⟨k1, hk1, k2, hk2, hsum⟩ := (S.map Φ).exists_add_mem_mem_orthogonal (Φ x)
  obtain ⟨y, hyS, rfl⟩ := Submodule.mem_map.mp hk1
  have hΦz : Φ (x - y) = k2 := by rw [map_sub, hsum]; abel
  have hgood : good (x - y) := by
    refine ⟨Submodule.sub_mem _ hx (hSle hyS), fun w hw => ?_⟩
    rw [hΦz]
    exact Submodule.inner_right_of_mem_orthogonal (Submodule.mem_map_of_mem hw) hk2
  have hprodS : S ≤ LinearMap.ker (l.map fun i => 1 - Q i).prod :=
    iSup₂_le fun i hi w hw => by
      rw [LinearMap.mem_ker]
      exact prod_apply_eq_zero_of_fixed Q l hl (fun i hi j hj hij => (hc i hi j hj hij).2.2) i hi w
        (mem_Wsp.mp hw).2
  have hz0 : (l.map fun i => 1 - Q i).prod (x - y) = 0 := by
    rw [map_sub, h0, LinearMap.mem_ker.mp (hprodS hyS), sub_zero]
  have hBz : (l.map B).prod (x - y) = 0 := by
    rw [hB, prod_mul_eq P Q l hl (fun i hi j hj hij => (hc i hi j hj hij).2.1), Module.End.mul_apply,
      hz0, map_zero]
  have := (hpeel l (fun i hi => hi) (x - y) hgood).2 hBz
  rw [sub_eq_zero] at this
  rw [this]
  exact hyS

end AL

section GP

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {G : Type*} [Group G] (σ : G →* Module.End ℂ E)

/-- The average of `σ` over a finite subgroup `X`. -/
def avg (X : Subgroup G) [Fintype X] : Module.End ℂ E :=
  (Nat.card X : ℂ)⁻¹ • ∑ x : X, σ x

omit [Module ℂ E] in
lemma natCard_ne_zero (X : Subgroup G) [Fintype X] : (Nat.card X : ℂ) ≠ 0 := by
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast Fintype.card_ne_zero

lemma avg_mul_of_forall {X : Subgroup G} [Fintype X] (A : Module.End ℂ E)
    (hA : ∀ x ∈ X, σ x * A = A) : avg σ X * A = A := by
  rw [avg, smul_mul_assoc, Finset.sum_mul, Finset.sum_congr rfl (fun (x : X) _ => hA (x : G) x.2),
    Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, inv_mul_cancel₀ (natCard_ne_zero X), one_smul]

lemma mul_avg {X : Subgroup G} [Fintype X] {g : G} (hg : g ∈ X) : σ g * avg σ X = avg σ X := by
  rw [avg, mul_smul_comm, Finset.mul_sum]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg⟩ : X)) _ _ (fun x => ?_)
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul]

lemma avg_idem (X : Subgroup G) [Fintype X] : avg σ X * avg σ X = avg σ X :=
  avg_mul_of_forall σ _ (fun _ hx => mul_avg σ hx)

lemma avg_apply_of_fixed {X : Subgroup G} [Fintype X] {v : E} (hv : ∀ x ∈ X, σ x v = v) :
    avg σ X v = v := by
  rw [avg, LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_congr rfl (fun (x : X) _ => hv (x : G) x.2),
    Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, inv_mul_cancel₀ (natCard_ne_zero X), one_smul]

lemma apply_eq_of_avg {X : Subgroup G} [Fintype X] {v : E} (hv : avg σ X v = v) {g : G}
    (hg : g ∈ X) : σ g v = v := by
  rw [← hv, ← Module.End.mul_apply, mul_avg σ hg]

lemma avg_commute {X Y : Subgroup G} [Fintype X] [Fintype Y]
    (h : ∀ x ∈ X, ∀ y ∈ Y, Commute x y) : Commute (avg σ X) (avg σ Y) := by
  unfold avg
  refine Commute.smul_left (Commute.smul_right ?_ _) _
  refine Commute.sum_left _ _ _ (fun x _ => Commute.sum_right _ _ _ (fun y _ => ?_))
  exact (h x x.2 y y.2).map σ

omit [Module ℂ E] in
lemma zpowers_commute {g h : G} (hgh : Commute g h) :
    ∀ x ∈ Subgroup.zpowers g, ∀ y ∈ Subgroup.zpowers h, Commute x y := by
  intro x hx y hy
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact hgh.zpow_zpow m n

variable {H0 : Type*} [NormedAddCommGroup H0] [InnerProductSpace ℂ H0] [Fintype G]

/-- `Φ x = (Φ0 (σ g x))_g` in `ℓ²(G, H0)`: a `σ`-invariant hermitian embedding. -/
def invEmb (Φ0 : E →ₗ[ℂ] H0) : E →ₗ[ℂ] PiLp 2 (fun _ : G => H0) :=
  (WithLp.linearEquiv 2 ℂ (G → H0)).symm.toLinearMap ∘ₗ LinearMap.pi (fun g => Φ0 ∘ₗ σ g)

omit [Fintype G] in
lemma invEmb_apply (Φ0 : E →ₗ[ℂ] H0) (x : E) (g : G) : invEmb σ Φ0 x g = Φ0 (σ g x) := rfl

lemma inner_invEmb (Φ0 : E →ₗ[ℂ] H0) (x y : E) :
    ⟪invEmb σ Φ0 x, invEmb σ Φ0 y⟫_ℂ = ∑ g, ⟪Φ0 (σ g x), Φ0 (σ g y)⟫_ℂ := by
  rw [PiLp.inner_apply]
  rfl

lemma inner_invEmb_map (Φ0 : E →ₗ[ℂ] H0) (h : G) (x y : E) :
    ⟪invEmb σ Φ0 (σ h x), invEmb σ Φ0 (σ h y)⟫_ℂ = ⟪invEmb σ Φ0 x, invEmb σ Φ0 y⟫_ℂ := by
  rw [inner_invEmb, inner_invEmb]
  refine Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun g => ?_)
  simp only [Equiv.coe_mulRight, map_mul, Module.End.mul_apply]

omit [Fintype G] in
lemma invEmb_injective (Φ0 : E →ₗ[ℂ] H0) (hΦ0 : Function.Injective Φ0) :
    Function.Injective (invEmb σ Φ0) := by
  intro x y hxy
  have h1 := congrArg (fun z : PiLp 2 (fun _ : G => H0) => z 1) hxy
  simp only [invEmb_apply, map_one, Module.End.one_apply] at h1
  exact hΦ0 h1

lemma avg_symm (Φ0 : E →ₗ[ℂ] H0) (X : Subgroup G) [Fintype X] (x y : E) :
    ⟪invEmb σ Φ0 (avg σ X x), invEmb σ Φ0 y⟫_ℂ = ⟪invEmb σ Φ0 x, invEmb σ Φ0 (avg σ X y)⟫_ℂ := by
  have key : ∀ a : G, ⟪invEmb σ Φ0 (σ a x), invEmb σ Φ0 y⟫_ℂ =
      ⟪invEmb σ Φ0 x, invEmb σ Φ0 (σ a⁻¹ y)⟫_ℂ := by
    intro a
    have hy : σ a (σ a⁻¹ y) = y := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    calc ⟪invEmb σ Φ0 (σ a x), invEmb σ Φ0 y⟫_ℂ
        = ⟪invEmb σ Φ0 (σ a x), invEmb σ Φ0 (σ a (σ a⁻¹ y))⟫_ℂ := by rw [hy]
      _ = _ := inner_invEmb_map σ Φ0 a x _
  have hc : (starRingEnd ℂ) ((Nat.card X : ℂ)⁻¹) = (Nat.card X : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_natCast]
  simp only [avg, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, inner_smul_left,
    inner_smul_right, sum_inner, inner_sum, key, hc]
  congr 1
  exact Fintype.sum_equiv (Equiv.inv X) _ _ (fun a => by simp)

/-- **GP + AL.** For a finite group acting on a finite-dimensional space, commuting averages
satisfy the kernel-of-product lemma. -/
theorem mem_iSup_of_avg [FiniteDimensional ℂ E] {ι : Type*} (l : List ι) (hl : l.Nodup)
    (a b : ι → Subgroup G) [∀ i, Fintype (a i)] [∀ i, Fintype (b i)]
    (hc : ∀ i ∈ l, ∀ j ∈ l, i ≠ j → (∀ x ∈ a i, ∀ y ∈ a j, Commute x y) ∧
      (∀ x ∈ a i, ∀ y ∈ b j, Commute x y) ∧ (∀ x ∈ b i, ∀ y ∈ b j, Commute x y))
    (x : E) (hx : ∀ i ∈ l, ∀ g ∈ a i, σ g x = x)
    (h0 : (l.map fun i => 1 - avg σ (b i)).prod x = 0) :
    x ∈ ⨆ i ∈ l, Wsp l (fun i => avg σ (a i)) (fun i => avg σ (b i)) i := by
  let e0 : E →ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E)) :=
    (WithLp.linearEquiv 2 ℂ (Fin (Module.finrank ℂ E) → ℂ)).symm.toLinearMap ∘ₗ
      (Module.finBasis ℂ E).equivFun.toLinearMap
  have he0 : Function.Injective e0 :=
    (WithLp.linearEquiv 2 ℂ _).symm.injective.comp (Module.finBasis ℂ E).equivFun.injective
  refine mem_iSup_of_prod_eq_zero (invEmb σ e0) (invEmb_injective σ e0 he0) l hl _ _
    (fun i => avg_idem σ _) (fun i => avg_idem σ _) (fun i => avg_symm σ e0 _)
    (fun i => avg_symm σ e0 _) (fun i hi j hj hij => ?_) x ?_ h0
  · obtain ⟨h1, h2, h3⟩ := hc i hi j hj hij
    exact ⟨avg_commute σ h1, avg_commute σ h2, avg_commute σ h3⟩
  · rw [mem_fixSp]
    exact fun i hi => avg_apply_of_fixed σ (hx i hi)

end GP

end RamanujanPetersson.MainLemmaB


