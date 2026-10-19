-- Prove2me | Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
-- name    : OAI_Combinatorics_HoneycombCorridor_IntegerPotential
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:26:16.126145+00:00
-- url     : https://prove2.me/theorems/e43b7fa3-8f87-4dfd-92bc-68800c29942e
-- title:
--   Finite integer flows on the honeycomb and their face potentials
-- statement:
--   Faces of the honeycomb lattice are indexed by $(i,j)\in\mathbb Z^2$, and an integer flow is described by three finitely supported functions $q_0,q_1,q_2:\mathbb Z^2\to\mathbb Z$, one per edge direction.
--
--   1. **Row prefix sums.** For finitely supported $f$, $\mathrm{facePrefix}(f)(i,j)=\sum_{a_1\le i}f(a_1,j)$, so that consecutive differences recover $f$. The face radius is the largest $|a_1|+|a_2|$ on the support, and the prefix vanishes left of it and outside its rows.
--   2. **Finite honeycomb flows.** A finite honeycomb flow is a triple $(q_0,q_1,q_2)$ conserved at every vertex:
--   $$
--   q_0(i,j)+q_1(i,j)+q_2(i,j)=0,\qquad q_0(i,j+1)+q_1(i,j)+q_2(i+1,j)=0 .
--   $$
--   3. **Potential.** The flow potential is the row prefix of $q_0$. It vanishes to the right of the support of $q_2$, so it is finitely supported, and every finite conserved flow is the boundary of this finite face potential $p$: $q_0(i,j)=p(i,j)-p(i-1,j)$, $q_1(i,j)=p(i-1,j+1)-p(i,j)$, $q_2(i,j)=p(i-1,j)-p(i-1,j+1)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/IntegerPotential.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/IntegerPotential.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HoneycombBridgeFiniteness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

abbrev FaceIndex := ℤ × ℤ

noncomputable def facePrefix (f : FaceIndex →₀ ℤ) (i j : ℤ) : ℤ :=
  ∑ a ∈ f.support, if a.2 = j ∧ a.1 ≤ i then f a else 0

theorem facePrefix_difference (f : FaceIndex →₀ ℤ) (i j : ℤ) :
    facePrefix f i j - facePrefix f (i - 1) j = f (i,j) := by
  classical
  unfold facePrefix
  rw [← Finset.sum_sub_distrib]
  have ht (a : FaceIndex) :
      (if a.2 = j ∧ a.1 ≤ i then f a else 0) -
        (if a.2 = j ∧ a.1 ≤ i - 1 then f a else 0) =
        if a = (i,j) then f a else 0 := by
    rcases a with ⟨x,y⟩
    by_cases hy : y = j
    · subst y
      by_cases hx : x = i
      · subst x
        simp
      · have hh : x ≤ i ↔ x ≤ i - 1 := by omega
        simp [hx,hh]
    · simp [hy]
  simp_rw [ht]
  by_cases hm : (i,j) ∈ f.support
  · simp [hm]
  · have hz : f (i,j) = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hm
    simp [hm, hz]

def InFaceBox (M : ℕ) (a : FaceIndex) : Prop :=
  -(M : ℤ) ≤ a.1 ∧ a.1 ≤ M ∧ -(M : ℤ) ≤ a.2 ∧ a.2 ≤ M

noncomputable def faceRadius (f : FaceIndex →₀ ℤ) : ℕ :=
  f.support.sup fun a => a.1.natAbs + a.2.natAbs

theorem mem_support_in_box (f : FaceIndex →₀ ℤ) (a : FaceIndex)
    (ha : a ∈ f.support) : InFaceBox (faceRadius f) a := by
  have h : a.1.natAbs + a.2.natAbs ≤ faceRadius f := Finset.le_sup (f := fun a : FaceIndex => a.1.natAbs + a.2.natAbs) ha
  have hx : a.1.natAbs ≤ faceRadius f := le_trans (Nat.le_add_right _ _) h
  have hy : a.2.natAbs ≤ faceRadius f := le_trans (Nat.le_add_left _ _) h
  have hxi : |a.1| ≤ (faceRadius f : ℤ) := by simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr hx)
  have hyi : |a.2| ≤ (faceRadius f : ℤ) := by simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr hy)
  exact ⟨(abs_le.mp hxi).1,(abs_le.mp hxi).2,(abs_le.mp hyi).1,(abs_le.mp hyi).2⟩

theorem facePrefix_left_zero (f : FaceIndex →₀ ℤ) (i j : ℤ)
    (hi : i < -(faceRadius f : ℤ)) : facePrefix f i j = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a ha
  have hb := (mem_support_in_box f a ha).1
  have hx : ¬a.1 ≤ i := by omega
  simp [hx]

theorem facePrefix_row_zero (f : FaceIndex →₀ ℤ) (i j : ℤ)
    (hj : j < -(faceRadius f : ℤ) ∨ (faceRadius f : ℤ) < j) :
    facePrefix f i j = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a ha
  have hb := mem_support_in_box f a ha
  have hy : a.2 ≠ j := by intro h; rcases hb with ⟨h1,h2,h3,h4⟩; omega
  simp [hy]

theorem int_function_constant {f : ℤ → ℤ} (hf : ∀ i, f (i + 1) = f i)
    (i j : ℤ) : f i = f j := by
  have hzero (n : ℤ) : f n = f 0 := by
    induction n using Int.induction_on with
    | zero => rfl
    | succ n hn => exact (hf n).trans hn
    | pred n hn =>
      calc f (-(n : ℤ) - 1) = f (-n) := by simpa using (hf (-(n : ℤ) - 1)).symm
           _ = f 0 := hn
  exact (hzero i).trans (hzero j).symm

structure FiniteHoneycombFlow where
  q0 : FaceIndex →₀ ℤ
  q1 : FaceIndex →₀ ℤ
  q2 : FaceIndex →₀ ℤ
  up_conservation : ∀ i j, q0 (i,j) + q1 (i,j) + q2 (i,j) = 0
  down_conservation : ∀ i j, q0 (i,j+1) + q1 (i,j) + q2 (i+1,j) = 0

noncomputable def flowPotential (q : FiniteHoneycombFlow) (i j : ℤ) : ℤ :=
  facePrefix q.q0 i j

theorem flow_difference (q : FiniteHoneycombFlow) (i j : ℤ) :
    q.q0 (i,j+1) - q.q0 (i,j) = q.q2 (i,j) - q.q2 (i+1,j) := by
  have hu := q.up_conservation i j
  have hd := q.down_conservation i j
  omega

theorem flowPotential_vertical (q : FiniteHoneycombFlow) (i j : ℤ) :
    flowPotential q i (j+1) - flowPotential q i j = -q.q2 (i+1,j) := by
  let H : ℤ → ℤ := fun k =>
    flowPotential q k (j+1) - flowPotential q k j + q.q2 (k+1,j)
  have hH : ∀ k, H (k+1) = H k := by
    intro k
    have h1 := facePrefix_difference q.q0 (k+1) (j+1)
    have h2 := facePrefix_difference q.q0 (k+1) j
    have hd := flow_difference q (k+1) j
    simp only [add_sub_cancel_right] at h1 h2
    dsimp [H,flowPotential]
    omega
  let k : ℤ := -(faceRadius q.q0 : ℤ) - (faceRadius q.q2 : ℤ) - 2
  have hk0 : k < -(faceRadius q.q0 : ℤ) := by dsimp [k]; omega
  have hk2 : q.q2 (k+1,j) = 0 := by
    by_contra hne
    have hm := Finsupp.mem_support_iff.mpr hne
    have hb := (mem_support_in_box q.q2 (k+1,j) hm).1
    dsimp [k] at hb
    omega
  have hHz : H k = 0 := by
    dsimp [H,flowPotential]
    rw [facePrefix_left_zero _ _ _ hk0,facePrefix_left_zero _ _ _ hk0,hk2]
    norm_num
  have h := (int_function_constant hH i k).trans hHz
  dsimp [H] at h
  omega

theorem flowPotential_right_zero (q : FiniteHoneycombFlow) (i j : ℤ)
    (hi : (faceRadius q.q2 : ℤ) ≤ i) : flowPotential q i j = 0 := by
  have hconstant : ∀ k, flowPotential q i (k+1) = flowPotential q i k := by
    intro k
    have hq : q.q2 (i+1,k) = 0 := by
      by_contra hne
      have hb := (mem_support_in_box q.q2 (i+1,k)
        (Finsupp.mem_support_iff.mpr hne)).2.1
      omega
    have h := flowPotential_vertical q i k
    rw [hq] at h
    omega
  let k : ℤ := (faceRadius q.q0 : ℤ) + 1
  have hz : flowPotential q i k = 0 :=
    facePrefix_row_zero q.q0 i k (Or.inr (by dsimp [k]; omega))
  exact (int_function_constant hconstant j k).trans hz

theorem flowPotential_finite_support (q : FiniteHoneycombFlow) :
    Set.Finite {a : FaceIndex | flowPotential q a.1 a.2 ≠ 0} := by
  let M : ℤ := (faceRadius q.q0 : ℤ) + faceRadius q.q2 + 1
  apply (Set.finite_Icc (-M, -M) (M, M)).subset
  intro a ha
  change flowPotential q a.1 a.2 ≠ 0 at ha
  have hleft : -(faceRadius q.q0 : ℤ) ≤ a.1 := by
    by_contra h
    exact ha (facePrefix_left_zero q.q0 a.1 a.2 (by omega))
  have hright : a.1 < (faceRadius q.q2 : ℤ) := by
    by_contra h
    exact ha (flowPotential_right_zero q a.1 a.2 (by omega))
  have hbottom : -(faceRadius q.q0 : ℤ) ≤ a.2 := by
    by_contra h
    exact ha (facePrefix_row_zero q.q0 a.1 a.2 (Or.inl (by omega)))
  have htop : a.2 ≤ (faceRadius q.q0 : ℤ) := by
    by_contra h
    exact ha (facePrefix_row_zero q.q0 a.1 a.2 (Or.inr (by omega)))
  change (-M ≤ a.1 ∧ -M ≤ a.2) ∧ a.1 ≤ M ∧ a.2 ≤ M
  dsimp [M]
  omega

noncomputable def finiteFlowPotential (q : FiniteHoneycombFlow) : FaceIndex →₀ ℤ :=
  Finsupp.ofSupportFinite (fun a => flowPotential q a.1 a.2)
    (flowPotential_finite_support q)

theorem finite_flow_is_face_boundary (q : FiniteHoneycombFlow) :
    ∃ p : FaceIndex →₀ ℤ, ∀ i j,
      q.q0 (i,j) = p (i,j) - p (i-1,j) ∧
      q.q1 (i,j) = p (i-1,j+1) - p (i,j) ∧
      q.q2 (i,j) = p (i-1,j) - p (i-1,j+1) := by
  refine ⟨finiteFlowPotential q, ?_⟩
  intro i j
  have h0 := facePrefix_difference q.q0 i j
  have h2 := flowPotential_vertical q (i-1) j
  have hu := q.up_conservation i j
  simp only [sub_add_cancel] at h2
  simp only [finiteFlowPotential,Finsupp.ofSupportFinite_coe,flowPotential]
  dsimp [flowPotential] at h2
  omega

end PolynomialVacuumBridge.Corridor

end

end OAI


