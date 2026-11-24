-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
-- name    : QuantumLTF_Membership_Supplement_thm410_router_blocks
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-24T06:01:06.908793+00:00
-- url     : https://prove2.me/theorems/7063602d-7562-41a2-9c9e-5656ecb6ee76
-- title:
--   Parallel coherent SWAP router, two-level unitaries, and comparison/diagonal-sign blocks in `gates12`
-- statement:
--   This module formalizes the parallel coherent binary SWAP router and the elementary $2$-level and diagonal-sign block constructions in the `gates12` + `nonOracleDepth` circuit model.
--
--   1. **Parallel controlled-NOT (`ctrlNotN`):** Maps $|c\rangle|x\rangle \mapsto |c\rangle|x \oplus c^n\rangle$ on $1+n$ wires with $3n$ gates and depth $\le 2\lceil\log_2(n+1)\rceil + 3$ via a balanced fanout tree.
--
--   2. **Coherent binary SWAP router (`coherentRouter`):** Given an $\ell$-bit LSB address register $W$, an active control bit $f_c$, a $q_w$-qubit data register, $h_{\mathrm{tree}} \le \ell$, and $2^{h_{\mathrm{tree}}}$ leaf circuits acting on disjoint $(1+q_w+a_{\mathrm{leaf}})$-wire blocks with size $\le g$ and depth $\le d$, the router simultaneously pre-fans out all $h_{\mathrm{tree}}$ address bits in parallel before $h_{\mathrm{tree}}$ constant-depth Fredkin SWAP levels and parallel leaf execution:
--
--   $$G \le 24(\ell+2) + 16(2^{h_{\mathrm{tree}}}-1)(q_w+1) + 2^{h_{\mathrm{tree}}} g, \qquad D \le 20\lceil\log_2(\ell+2)\rceil + 16 h_{\mathrm{tree}} + 2\lceil\log_2(q_w+1)\rceil + d + 6.$$
--
--   3. **Two-level controlled unitaries (`twoLevelCtrlGate`, `ctrlTwoLevelGate`):** Implements any $2$-level unitary acting on distinct basis states $u \neq v \in \{0,1\}^{q_w}$ with $O(q_w)$ gates and $O(q_w)$ depth.
--
--   4. **Ripple-carry threshold and diagonal sign gates (`ltConstCircuit`, `ltPhaseSignGate`, `ctrlLtPhaseSignGate`, `u0DiagSignGate`, `ctrlU0DiagSignGate`):** Implements fixed-threshold comparison $< H$ and the diagonal sign operators $(-1)^{\min\{i,h\}}$ ($D_t$) and $(-1)^{i+1}$ ($U_0$) in $O(q_w)$ gates and $O(q_w)$ depth.
--
--   Together, these components enable coherent multiplexing over $O(k)$ Krawtchouk-walk block unitaries in $O(\log n + \log k)$ non-oracle depth.
--
--   **Formalization Note.** All declarations live in namespace `Thm410Router`, importing `Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives`.
-- source:
--   Krivcenko, Nguyen, de Wolf (2026), Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Appendix C.5, pp. 95-99

import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives

set_option autoImplicit false

/-! ============================================================================
    BEGIN Thm410Router
    ============================================================================ -/

namespace Thm410Router

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open Thm49Primitives

/-! ### 1. Core `LayeredCircuit`, `ImplementsOnClean`, `mapWires`, and `parMergeFin` Helpers -/

def padZero (main anc : ℕ) (x : Qubits main) : Qubits (main + anc) :=
  Fin.addCases x (fun _ => false)

@[simp] lemma padZero_castAdd (main anc : ℕ) (x : Qubits main) (i : Fin main) :
    padZero main anc x (Fin.castAdd anc i) = x i :=
  Fin.addCases_left i

@[simp] lemma padZero_natAdd (main anc : ℕ) (x : Qubits main) (j : Fin anc) :
    padZero main anc x (Fin.natAdd main j) = false :=
  Fin.addCases_right j

lemma padZero_inj (main anc : ℕ) : Function.Injective (padZero main anc) := by
  intro x₁ x₂ h
  funext i
  have := congrFun h (Fin.castAdd anc i)
  simpa using this

lemma eq_padZero_of_clean {main anc : ℕ} (z : Qubits (main + anc))
    (hz : ∀ j : Fin anc, z (Fin.natAdd main j) = false) :
    z = padZero main anc (fun i => z (Fin.castAdd anc i)) := by
  funext w
  refine Fin.addCases (fun i => ?_) (fun j => ?_) w
  · simp
  · simp [hz j]

lemma implementsOnClean_of_act {main anc : ℕ} (lc : LayeredCircuit (main + anc))
    (U : Matrix (Qubits main) (Qubits main) ℂ)
    (hact : ∀ x : Qubits main,
      act lc.unitary (ket (padZero main anc x)) =
        ∑ y : Qubits main, U y x • ket (padZero main anc y)) :
    lc.ImplementsOnClean U := by
  intro y z hz
  have hz_eq := eq_padZero_of_clean z hz
  set x : Qubits main := fun i => z (Fin.castAdd anc i)
  have hentry : lc.unitary y z = inner ℂ (ket y) (act lc.unitary (ket z)) := by
    rw [act_ket_eq, inner_sum]
    simp [inner_smul_right, ket, EuclideanSpace.inner_single_left]
  rw [hentry, hz_eq, hact x, inner_sum]
  simp only [inner_smul_right, ket, EuclideanSpace.inner_single_left, PiLp.single_apply,
    map_one, mul_ite, mul_one, mul_zero]
  by_cases hy : ∀ j : Fin anc, y (Fin.natAdd main j) = false
  · rw [if_pos hy]
    have hy_eq := eq_padZero_of_clean y hy
    set y0 : Qubits main := fun i => y (Fin.castAdd anc i)
    rw [Finset.sum_eq_single y0]
    · rw [if_pos hy_eq]
    · intro y' _ hy'
      have hne : padZero main anc y' ≠ y := by
        intro h
        apply hy'
        apply padZero_inj main anc
        exact h.trans hy_eq
      rw [if_neg hne.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hy]
    refine Finset.sum_eq_zero fun y' _ => ?_
    have hne : padZero main anc y' ≠ y := by
      intro h
      apply hy
      intro j
      rw [← h]
      simp
    rw [if_neg hne.symm]

lemma implementsOnClean_of_act_perm {main anc : ℕ} (lc : LayeredCircuit (main + anc))
    (f : Qubits main → Qubits main)
    (hact : ∀ x : Qubits main,
      act lc.unitary (ket (padZero main anc x)) = ket (padZero main anc (f x))) :
    lc.ImplementsOnClean (permMat f) := by
  apply implementsOnClean_of_act
  intro x
  rw [hact x]
  symm
  rw [Finset.sum_eq_single (f x)]
  · simp [permMat]
  · intro y _ hy
    simp [permMat, hy]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma act_ket_of_implementsOnClean {main anc : ℕ} {lc : LayeredCircuit (main + anc)}
    {U : Matrix (Qubits main) (Qubits main) ℂ} (hlc : lc.ImplementsOnClean U)
    (x : Qubits main) :
    act lc.unitary (ket (padZero main anc x)) =
      ∑ y : Qubits main, U y x • ket (padZero main anc y) := by
  classical
  rw [act_ket_eq]
  have hz : ∀ j : Fin anc, padZero main anc x (Fin.natAdd main j) = false := fun j => by simp
  have hsub : (∑ y : Qubits (main + anc), lc.unitary y (padZero main anc x) • ket y) =
      ∑ y ∈ Finset.univ.image (padZero main anc), lc.unitary y (padZero main anc x) • ket y := by
    rw [← Finset.sum_subset (Finset.subset_univ _)]
    intro y _ hy
    rw [hlc y (padZero main anc x) hz]
    by_cases hyc : ∀ j : Fin anc, y (Fin.natAdd main j) = false
    · exfalso; apply hy
      rw [Finset.mem_image]
      exact ⟨fun i => y (Fin.castAdd anc i), Finset.mem_univ _, (eq_padZero_of_clean y hyc).symm⟩
    · rw [if_neg hyc, zero_smul]
  rw [hsub, Finset.sum_image (fun y₁ _ y₂ _ h => padZero_inj main anc h)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hlc (padZero main anc y) (padZero main anc x) hz]
  have hyc : ∀ j : Fin anc, padZero main anc y (Fin.natAdd main j) = false := fun j => by simp
  rw [if_pos hyc]
  simp only [padZero_castAdd]

lemma act_ket_of_implementsOnClean_perm {main anc : ℕ} {lc : LayeredCircuit (main + anc)}
    {f : Qubits main → Qubits main} (hlc : lc.ImplementsOnClean (permMat f))
    (x : Qubits main) :
    act lc.unitary (ket (padZero main anc x)) = ket (padZero main anc (f x)) := by
  rw [act_ket_of_implementsOnClean hlc x, Finset.sum_eq_single (f x)]
  · simp [permMat]
  · intro y _ hy; simp [permMat, hy]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma pauliZGate_usesOnly {m : ℕ} (w : Fin m) : (pauliZGate w).UsesOnly {w} :=
  gate1_usesOnly pauliZ pauliZ_mem_unitaryGroup w

lemma act_pauliZGate_ket {m : ℕ} (w : Fin m) (x : Qubits m) :
    act (pauliZGate w).unitary (ket x) = (if x w then (-1 : ℂ) else 1) • ket x := by
  rw [pauliZGate, LayeredCircuit.single_unitary, act_ket_eq]
  rw [Finset.sum_eq_single x]
  · rw [pauliZApp, embedOp_gate1App_entry]
    rw [if_pos (fun _ _ => rfl)]
    cases x w <;> simp [pauliZ]
  · intro y _ hy
    rw [pauliZApp, embedOp_gate1App_entry]
    by_cases hoff : ∀ a : Fin m, a ≠ w → y a = x a
    · rw [if_pos hoff]
      have hyw : y w ≠ x w := fun heq => hy (funext fun a => by
        by_cases ha : a = w
        · subst ha; exact heq
        · exact hoff a ha)
      simp [pauliZ, hyw, zero_smul]
    · rw [if_neg hoff, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma act_mapWires_ket {m₀ m : ℕ} (lc : LayeredCircuit m₀) (emb : Fin m₀ ↪ Fin m)
    (z : Qubits m) (x' : Qubits m₀)
    (hact : act lc.unitary (ket (z ∘ emb)) = ket x')
    (z' : Qubits m) (hz'_in : z' ∘ emb = x')
    (hz'_out : ∀ i : Fin m, i ∉ Set.range emb → z' i = z i) :
    act (lc.mapWires emb).unitary (ket z) = ket z' := by
  rw [LayeredCircuit.mapWires_unitary, act_ket_eq]
  have hentry : ∀ y : Qubits m,
      embedOp lc.unitary emb y z = if y = z' then 1 else 0 := by
    intro y
    simp only [embedOp, Matrix.of_apply]
    have hU : lc.unitary (y ∘ emb) (z ∘ emb) = if y ∘ emb = x' then 1 else 0 := by
      have hy := congrFun (congrArg WithLp.ofLp hact) (y ∘ emb)
      simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, ket, PiLp.single_apply] at hy
      rw [Finset.sum_eq_single (z ∘ emb)] at hy
      · simpa using hy
      · intro u _ hu; simp [hu]
      · intro h; exact absurd (Finset.mem_univ _) h
    by_cases hyz : y = z'
    · subst hyz
      rw [if_pos hz'_out, hU, hz'_in, if_pos rfl, if_pos rfl]
    · rw [if_neg hyz]
      split_ifs with hout
      · rw [hU]
        split_ifs with hUeq
        · exfalso; apply hyz; funext i
          by_cases hi : i ∈ Set.range emb
          · obtain ⟨j, rfl⟩ := hi
            exact (congrFun hUeq j).trans (congrFun hz'_in j).symm
          · exact (hout i hi).trans (hz'_out i hi).symm
        · rfl
      · rfl
  rw [Finset.sum_eq_single z']
  · rw [hentry z', if_pos rfl, one_smul]
  · intro y _ hy
    rw [hentry y, if_neg hy, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma act_mapWires_ket_sum {m₀ m : ℕ} {κ : Type*} [Fintype κ]
    (lc : LayeredCircuit m₀) (emb : Fin m₀ ↪ Fin m)
    (z : Qubits m) (α : κ → ℂ) (x' : κ → Qubits m₀) (z' : κ → Qubits m)
    (hact : act lc.unitary (ket (z ∘ emb)) = ∑ j : κ, α j • ket (x' j))
    (hz'_in : ∀ j : κ, z' j ∘ emb = x' j)
    (hz'_out : ∀ (j : κ) (i : Fin m), i ∉ Set.range emb → z' j i = z i) :
    act (lc.mapWires emb).unitary (ket z) = ∑ j : κ, α j • ket (z' j) := by
  classical
  rw [LayeredCircuit.mapWires_unitary, act_ket_eq]
  have hU : ∀ y₀ : Qubits m₀,
      lc.unitary y₀ (z ∘ emb) = ∑ j : κ, α j * (if y₀ = x' j then 1 else 0) := by
    intro y₀
    have hy := congrFun (congrArg WithLp.ofLp hact) y₀
    simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, ket, PiLp.single_apply,
      WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hy
    rw [Finset.sum_eq_single (z ∘ emb)] at hy
    · simpa using hy
    · intro u _ hu; simp [hu]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hexp : ∀ y : Qubits m,
      embedOp lc.unitary emb y z = ∑ j : κ, α j * (if y = z' j then 1 else 0) := by
    intro y
    simp only [embedOp, Matrix.of_apply]
    by_cases hout : ∀ i : Fin m, i ∉ Set.range emb → y i = z i
    · rw [if_pos hout, hU (y ∘ emb)]
      refine Finset.sum_congr rfl fun j _ => ?_
      have heq : (y = z' j) ↔ (y ∘ emb = x' j) := by
        constructor
        · intro h; rw [h, hz'_in j]
        · intro h; funext i
          by_cases hi : i ∈ Set.range emb
          · obtain ⟨b, rfl⟩ := hi
            exact (congrFun h b).trans (congrFun (hz'_in j) b).symm
          · exact (hout i hi).trans (hz'_out j i hi).symm
      by_cases hj : y = z' j
      · rw [if_pos hj, if_pos (heq.mp hj)]
      · rw [if_neg hj, if_neg (fun h => hj (heq.mpr h))]
    · rw [if_neg hout]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      have hne : y ≠ z' j := fun h => hout (fun i hi => by rw [h, hz'_out j i hi])
      rw [if_neg hne, mul_zero]
  simp_rw [hexp, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (z' j)]
  · simp
  · intro y _ hy; simp [hy]
  · intro h; exact absurd (Finset.mem_univ _) h

noncomputable def updateOn {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (z : Qubits m)
    (x' : Qubits m₀) : Qubits m :=
  fun w => open Classical in
    if h : ∃ i : Fin m₀, emb i = w then x' (Classical.choose h) else z w

lemma updateOn_apply_emb {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (z : Qubits m)
    (x' : Qubits m₀) (i : Fin m₀) :
    updateOn emb z x' (emb i) = x' i := by
  classical
  have h : ∃ j : Fin m₀, emb j = emb i := ⟨i, rfl⟩
  change (if h' : ∃ j, emb j = emb i then x' (Classical.choose h') else z (emb i)) = x' i
  rw [dif_pos h, emb.injective (Classical.choose_spec h)]

lemma updateOn_apply_not_mem {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (z : Qubits m)
    (x' : Qubits m₀) {w : Fin m} (hw : w ∉ Set.range emb) :
    updateOn emb z x' w = z w := by
  classical
  have h : ¬ ∃ j : Fin m₀, emb j = w := hw
  change (if h' : ∃ j, emb j = w then x' (Classical.choose h') else z w) = z w
  rw [dif_neg h]

lemma updateOn_comp {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (z : Qubits m) (x' : Qubits m₀) :
    updateOn emb z x' ∘ emb = x' :=
  funext (updateOn_apply_emb emb z x')

lemma act_mapWires_implementsOnClean {main anc m : ℕ} (lc : LayeredCircuit (main + anc))
    (U : Matrix (Qubits main) (Qubits main) ℂ) (hlc : lc.ImplementsOnClean U)
    (emb : Fin (main + anc) ↪ Fin m) (z : Qubits m)
    (hclean : ∀ j : Fin anc, z (emb (Fin.natAdd main j)) = false) :
    let embMain : Fin main ↪ Fin m := (Fin.castAddEmb anc).trans emb
    act (lc.mapWires emb).unitary (ket z) =
      ∑ y : Qubits main, U y (z ∘ embMain) • ket (updateOn embMain z y) := by
  intro embMain
  have hz_emb : z ∘ emb = padZero main anc (z ∘ embMain) := by
    funext w
    refine Fin.addCases (fun i => ?_) (fun j => ?_) w
    · simp [embMain]
    · simp [hclean j]
  have hact0 := act_ket_of_implementsOnClean hlc (z ∘ embMain)
  rw [← hz_emb] at hact0
  refine act_mapWires_ket_sum lc emb z (fun y => U y (z ∘ embMain))
    (fun y => padZero main anc y) (fun y => updateOn embMain z y) hact0 ?_ ?_
  · intro y
    funext w
    refine Fin.addCases (fun i => ?_) (fun j => ?_) w
    · have hcast : emb (Fin.castAdd anc i) = embMain i := rfl
      change updateOn embMain z y (emb (Fin.castAdd anc i)) = padZero main anc y (Fin.castAdd anc i)
      rw [hcast, updateOn_apply_emb, padZero_castAdd]
    · have hnot : emb (Fin.natAdd main j) ∉ Set.range embMain := by
        rintro ⟨i, hi⟩
        have hinj := emb.injective hi
        have := congrArg Fin.val hinj
        simp at this
        omega
      simp [updateOn_apply_not_mem _ _ _ hnot, hclean j]
  · intro y i hi
    apply updateOn_apply_not_mem
    rintro ⟨j, rfl⟩
    exact hi ⟨Fin.castAdd anc j, rfl⟩

/-! ### 2. `ctrlBlockMat`, `padAncClean`, `seqClean` -/

def ctrlBlockMat {q_w : ℕ} (U : Matrix (Qubits q_w) (Qubits q_w) ℂ) :
    Matrix (Qubits (1 + q_w)) (Qubits (1 + q_w)) ℂ :=
  Matrix.of fun y z =>
    if y 0 = z 0 then
      if y 0 then U (fun i => y (Fin.natAdd 1 i)) (fun i => z (Fin.natAdd 1 i))
      else if (fun i => y (Fin.natAdd 1 i)) = (fun i => z (Fin.natAdd 1 i)) then 1 else 0
    else 0

lemma ctrlBlockMat_one (q_w : ℕ) :
    ctrlBlockMat (1 : Matrix (Qubits q_w) (Qubits q_w) ℂ) = 1 := by
  ext y z
  simp only [ctrlBlockMat, Matrix.of_apply, Matrix.one_apply]
  by_cases hyz : y = z
  · subst hyz; simp
  · rw [if_neg hyz]
    by_cases h0 : y 0 = z 0
    · rw [if_pos h0]
      have htail : (fun i : Fin q_w => y (Fin.natAdd 1 i)) ≠ (fun i : Fin q_w => z (Fin.natAdd 1 i)) := by
        intro h
        apply hyz
        funext w
        by_cases hw : w.1 = 0
        · have hw0 : w = 0 := Fin.ext hw
          rw [hw0, h0]
        · have hlt := w.isLt
          have hw_eq : w = Fin.natAdd 1 ⟨w.1 - 1, by omega⟩ := Fin.ext (by simp; omega)
          rw [hw_eq]
          exact congrFun h _
      cases y 0 <;> simp [htail]
    · rw [if_neg h0]

lemma ctrlBlockMat_mul {q_w : ℕ} (A B : Matrix (Qubits q_w) (Qubits q_w) ℂ) :
    ctrlBlockMat (A * B) = ctrlBlockMat A * ctrlBlockMat B := by
  classical
  ext y z
  simp only [ctrlBlockMat, Matrix.of_apply, Matrix.mul_apply]
  by_cases h0 : y 0 = z 0
  · rw [if_pos h0]
    let liftZ : Qubits q_w → Qubits (1 + q_w) := fun v w =>
      if h : w.1 = 0 then z 0 else v ⟨w.1 - 1, by have := w.isLt; omega⟩
    have hsum : (∑ x : Qubits (1 + q_w),
        (if y 0 = x 0 then
          if y 0 then A (fun i => y (Fin.natAdd 1 i)) (fun i => x (Fin.natAdd 1 i))
          else if (fun i => y (Fin.natAdd 1 i)) = (fun i => x (Fin.natAdd 1 i)) then 1 else 0
        else 0) *
        (if x 0 = z 0 then
          if x 0 then B (fun i => x (Fin.natAdd 1 i)) (fun i => z (Fin.natAdd 1 i))
          else if (fun i => x (Fin.natAdd 1 i)) = (fun i => z (Fin.natAdd 1 i)) then 1 else 0
        else 0)) =
        ∑ x ∈ Finset.univ.image liftZ,
        (if y 0 = x 0 then
          if y 0 then A (fun i => y (Fin.natAdd 1 i)) (fun i => x (Fin.natAdd 1 i))
          else if (fun i => y (Fin.natAdd 1 i)) = (fun i => x (Fin.natAdd 1 i)) then 1 else 0
        else 0) *
        (if x 0 = z 0 then
          if x 0 then B (fun i => x (Fin.natAdd 1 i)) (fun i => z (Fin.natAdd 1 i))
          else if (fun i => x (Fin.natAdd 1 i)) = (fun i => z (Fin.natAdd 1 i)) then 1 else 0
        else 0) := by
      rw [← Finset.sum_subset (Finset.subset_univ _)]
      intro x _ hx
      by_cases hx0 : x 0 = z 0
      · exfalso; apply hx
        rw [Finset.mem_image]
        refine ⟨fun i => x (Fin.natAdd 1 i), Finset.mem_univ _, ?_⟩
        funext w
        dsimp only [liftZ]
        split_ifs with hw
        · have hw0 : w = 0 := Fin.ext hw
          rw [hw0, hx0]
        · congr 1; ext; simp; omega
      · rw [if_neg hx0, mul_zero]
    rw [hsum, Finset.sum_image]
    · have hl0 : ∀ v : Qubits q_w, liftZ v 0 = z 0 := fun _ => by simp [liftZ]
      have hlt : ∀ v : Qubits q_w, (fun i : Fin q_w => liftZ v (Fin.natAdd 1 i)) = v := fun v => by
        funext i
        dsimp only [liftZ]
        have hne0 : ((Fin.natAdd 1 i : Fin (1 + q_w)) : ℕ) ≠ 0 := by simp
        rw [dif_neg hne0]
        exact congrArg v (Fin.ext (by simp))
      have hsub_eq : (∑ v : Qubits q_w,
          (if y 0 = liftZ v 0 then
            if y 0 then A (fun i => y (Fin.natAdd 1 i)) (fun i => liftZ v (Fin.natAdd 1 i))
            else if (fun i => y (Fin.natAdd 1 i)) = (fun i => liftZ v (Fin.natAdd 1 i)) then 1 else 0
          else 0) *
          (if liftZ v 0 = z 0 then
            if liftZ v 0 then B (fun i => liftZ v (Fin.natAdd 1 i)) (fun i => z (Fin.natAdd 1 i))
            else if (fun i => liftZ v (Fin.natAdd 1 i)) = (fun i => z (Fin.natAdd 1 i)) then 1 else 0
          else 0)) =
          ∑ v : Qubits q_w,
            (if y 0 then A (fun i => y (Fin.natAdd 1 i)) v
             else if (fun i => y (Fin.natAdd 1 i)) = v then 1 else 0) *
            (if z 0 then B v (fun i => z (Fin.natAdd 1 i))
             else if v = (fun i => z (Fin.natAdd 1 i)) then 1 else 0) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [hl0 v, hlt v, if_pos h0, if_pos rfl]
      rw [hsub_eq]
      cases hz0 : z 0
      · have hy0 : y 0 = false := h0.trans hz0
        rw [hy0]
        simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases htail : (fun i => y (Fin.natAdd 1 i)) = (fun i => z (Fin.natAdd 1 i))
        · rw [if_pos htail, Finset.sum_eq_single (fun i => z (Fin.natAdd 1 i))]
          · simp [htail]
          · intro v _ hv; simp [hv]
          · intro h; exact absurd (Finset.mem_univ _) h
        · rw [if_neg htail]
          symm
          refine Finset.sum_eq_zero fun v _ => ?_
          by_cases hvy : (fun i => y (Fin.natAdd 1 i)) = v
          · have hvz : v ≠ (fun i => z (Fin.natAdd 1 i)) := fun h => htail (hvy.trans h)
            simp [hvz]
          · simp [hvy]
      · have hy0 : y 0 = true := h0.trans hz0
        rw [hy0]
        simp only [↓reduceIte]
    · intro v₁ _ v₂ _ h
      funext i
      have h1 := congrFun h (Fin.natAdd 1 i)
      have hne0 : ((Fin.natAdd 1 i : Fin (1 + q_w)) : ℕ) ≠ 0 := by simp
      dsimp only [liftZ] at h1
      rw [dif_neg hne0, dif_neg hne0] at h1
      have hi1 : (⟨(Fin.natAdd 1 i).1 - 1, by
          have := (Fin.natAdd 1 i).isLt; omega⟩ : Fin q_w) = i :=
        Fin.ext (by simp)
      rwa [hi1] at h1
  · rw [if_neg h0]
    symm
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hyx : y 0 = x 0
    · have hxz : x 0 ≠ z 0 := fun h => h0 (hyx.trans h)
      rw [if_neg hxz, mul_zero]
    · rw [if_neg hyx, zero_mul]

def padEmb (main anc₁ anc₂ : ℕ) (hle : anc₁ ≤ anc₂) :
    Fin (main + anc₁) ↪ Fin (main + anc₂) where
  toFun w := ⟨w.1, by omega⟩
  inj' a b h := Fin.ext (by
    have := congrArg Fin.val h
    exact this)

def padAncClean {main anc₁ anc₂ : ℕ} (hle : anc₁ ≤ anc₂)
    (lc : LayeredCircuit (main + anc₁)) : LayeredCircuit (main + anc₂) :=
  lc.mapWires (padEmb main anc₁ anc₂ hle)

@[simp] lemma padAncClean_size {main anc₁ anc₂ : ℕ} (hle : anc₁ ≤ anc₂)
    (lc : LayeredCircuit (main + anc₁)) : (padAncClean hle lc).size = lc.size :=
  LayeredCircuit.mapWires_size _ _

@[simp] lemma padAncClean_depth {main anc₁ anc₂ : ℕ} (hle : anc₁ ≤ anc₂)
    (lc : LayeredCircuit (main + anc₁)) : (padAncClean hle lc).depth = lc.depth :=
  LayeredCircuit.mapWires_depth _ _

lemma padAncClean_implements {main anc₁ anc₂ : ℕ} (hle : anc₁ ≤ anc₂)
    (lc : LayeredCircuit (main + anc₁)) (U : Matrix (Qubits main) (Qubits main) ℂ)
    (hlc : lc.ImplementsOnClean U) :
    (padAncClean hle lc).ImplementsOnClean U := by
  apply implementsOnClean_of_act
  intro x
  let emb := padEmb main anc₁ anc₂ hle
  have hclean : ∀ j : Fin anc₁,
      padZero main anc₂ x (emb (Fin.natAdd main j)) = false := fun j => by
    have heq : emb (Fin.natAdd main j) = Fin.natAdd main ⟨j.1, by omega⟩ := Fin.ext rfl
    rw [heq, padZero_natAdd]
  have hact := act_mapWires_implementsOnClean lc U hlc emb (padZero main anc₂ x) hclean
  have hmain_eq : (Fin.castAddEmb anc₁).trans emb = Fin.castAddEmb anc₂ := by
    ext i; rfl
  change act (lc.mapWires emb).unitary (ket (padZero main anc₂ x)) = _ at hact
  change act (lc.mapWires emb).unitary (ket (padZero main anc₂ x)) = _
  rw [hact]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hcomp : padZero main anc₂ x ∘ (Fin.castAddEmb anc₁).trans emb = x := by
    funext i; rw [hmain_eq]; exact padZero_castAdd main anc₂ x i
  rw [hcomp]
  congr 2
  funext w
  refine Fin.addCases (fun i => ?_) (fun j => ?_) w
  · have heq : Fin.castAdd anc₂ i = ((Fin.castAddEmb anc₁).trans emb) i := rfl
    rw [heq, updateOn_apply_emb, ← heq, padZero_castAdd]
  · have hnot : Fin.natAdd main j ∉ Set.range ((Fin.castAddEmb anc₁).trans emb) := by
      rintro ⟨i, hi⟩
      have hval := congrArg Fin.val hi
      change i.1 = main + j.1 at hval
      have hiLt := i.isLt
      omega
    rw [updateOn_apply_not_mem _ _ _ hnot, padZero_natAdd, padZero_natAdd]

def seqClean {main anc₁ anc₂ : ℕ} (lc₁ : LayeredCircuit (main + anc₁))
    (lc₂ : LayeredCircuit (main + anc₂)) : LayeredCircuit (main + max anc₁ anc₂) :=
  (padAncClean (le_max_left anc₁ anc₂) lc₁).seq (padAncClean (le_max_right anc₁ anc₂) lc₂)

@[simp] lemma seqClean_size {main anc₁ anc₂ : ℕ} (lc₁ : LayeredCircuit (main + anc₁))
    (lc₂ : LayeredCircuit (main + anc₂)) :
    (seqClean lc₁ lc₂).size = lc₁.size + lc₂.size := by
  simp [seqClean]

@[simp] lemma seqClean_depth {main anc₁ anc₂ : ℕ} (lc₁ : LayeredCircuit (main + anc₁))
    (lc₂ : LayeredCircuit (main + anc₂)) :
    (seqClean lc₁ lc₂).depth = lc₁.depth + lc₂.depth := by
  simp [seqClean]

lemma seqClean_implements {main anc₁ anc₂ : ℕ}
    (lc₁ : LayeredCircuit (main + anc₁)) (lc₂ : LayeredCircuit (main + anc₂))
    (U₁ U₂ : Matrix (Qubits main) (Qubits main) ℂ)
    (h₁ : lc₁.ImplementsOnClean U₁) (h₂ : lc₂.ImplementsOnClean U₂) :
    (seqClean lc₁ lc₂).ImplementsOnClean (U₂ * U₁) := by
  apply implementsOnClean_of_act
  intro x
  have hp1 := act_ket_of_implementsOnClean (padAncClean_implements (le_max_left anc₁ anc₂) lc₁ U₁ h₁) x
  have hp2 := fun y =>
    act_ket_of_implementsOnClean (padAncClean_implements (le_max_right anc₁ anc₂) lc₂ U₂ h₂) y
  dsimp only [seqClean]
  rw [LayeredCircuit.seq_unitary, act_mul, hp1, act_sum]
  simp_rw [act_smul, hp2, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp only [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun y _ => mul_comm _ _

/-! ### 3. Public `parMergeList` and `parMergeFin` -/

lemma foldr_disjoint_of_pairwise {m : ℕ} {S : Finset (Fin m)}
    {rest : List (LayeredCircuit m × Finset (Fin m))}
    (hhd : ∀ q ∈ rest, Disjoint S q.2) :
    Disjoint S (rest.foldr (fun p acc => p.2 ∪ acc) ∅) := by
  induction rest with
  | nil => simp
  | cons p rp ihr =>
    simp only [List.foldr_cons, Finset.disjoint_union_right]
    exact ⟨hhd p List.mem_cons_self, ihr fun q hq => hhd q (List.mem_cons_of_mem _ hq)⟩

def parMergeList {m : ℕ} :
    (xs : List (LayeredCircuit m × Finset (Fin m))) →
    (∀ p ∈ xs, p.1.UsesOnly p.2) →
    xs.Pairwise (fun p q => Disjoint p.2 q.2) →
    { lc : LayeredCircuit m //
      lc.UsesOnly (xs.foldr (fun p acc => p.2 ∪ acc) ∅) ∧
      lc.size = (xs.map (fun p => p.1.size)).sum ∧
      lc.depth ≤ xs.foldr (fun p acc => max p.1.depth acc) 0 }
  | [], _, _ => ⟨LayeredCircuit.id m, LayeredCircuit.id_usesOnly _, rfl, le_rfl⟩
  | (lc, S) :: rest, huses, hpw =>
    have huses_rest : ∀ p ∈ rest, p.1.UsesOnly p.2 := fun p hp =>
      huses p (List.mem_cons_of_mem _ hp)
    have hpw_rest : rest.Pairwise (fun p q => Disjoint p.2 q.2) :=
      (List.pairwise_cons.mp hpw).2
    let ih := parMergeList rest huses_rest hpw_rest
    have hdisj : Disjoint S (rest.foldr (fun p acc => p.2 ∪ acc) ∅) :=
      foldr_disjoint_of_pairwise (List.pairwise_cons.mp hpw).1
    let merged := LayeredCircuit.parMerge lc ih.1 (huses _ List.mem_cons_self) ih.2.1 hdisj
    ⟨merged,
      LayeredCircuit.parMerge_usesOnly lc ih.1 (huses _ List.mem_cons_self) ih.2.1 hdisj,
      by simp [merged, LayeredCircuit.parMerge_size, ih.2.2.1],
      by
        simp only [merged, LayeredCircuit.parMerge_depth, List.foldr_cons]
        exact max_le_max_left _ ih.2.2.2⟩

lemma foldr_max_le {m : ℕ} (xs : List (LayeredCircuit m × Finset (Fin m)))
    (B : ℕ) (hB : ∀ p ∈ xs, p.1.depth ≤ B) :
    xs.foldr (fun p acc => max p.1.depth acc) 0 ≤ B := by
  induction xs with
  | nil => simp
  | cons p rest ih =>
    simp only [List.foldr_cons]
    exact max_le (hB p List.mem_cons_self) (ih fun q hq => hB q (List.mem_cons_of_mem _ hq))

lemma act_parMergeList_ket {m : ℕ}
    (xs : List (LayeredCircuit m × Finset (Fin m)))
    (huses : ∀ p ∈ xs, p.1.UsesOnly p.2)
    (hpw : xs.Pairwise (fun p q => Disjoint p.2 q.2))
    (z z_next : Qubits m)
    (hact : ∀ p ∈ xs, ∃ x' : Qubits m,
      act p.1.unitary (ket z) = ket x' ∧ ∀ w ∈ p.2, x' w = z_next w) :
    act (parMergeList xs huses hpw).1.unitary (ket z) =
      ket (fun w => if w ∈ xs.foldr (fun p acc => p.2 ∪ acc) ∅ then z_next w else z w) := by
  induction xs with
  | nil => simp [parMergeList, LayeredCircuit.id_unitary, act_one]
  | cons p rest ih =>
    rcases p with ⟨lc, S⟩
    dsimp only [parMergeList]
    rw [LayeredCircuit.parMerge_unitary, act_mul]
    have huses_lc : lc.UsesOnly S := huses (lc, S) List.mem_cons_self
    rcases hact (lc, S) List.mem_cons_self with ⟨x', hx'_act, hx'_in⟩
    rw [hx'_act]
    have hih := ih (fun q hq => huses q (List.mem_cons_of_mem _ hq))
      (List.pairwise_cons.mp hpw).2 (fun q hq => hact q (List.mem_cons_of_mem _ hq))
    have huses_rest : ∀ q ∈ rest, q.1.UsesOnly q.2 := fun q hq =>
      huses q (List.mem_cons_of_mem _ hq)
    let ihRes := parMergeList rest huses_rest (List.pairwise_cons.mp hpw).2
    let S_rest : Finset (Fin m) := rest.foldr (fun q acc => q.2 ∪ acc) ∅
    have hdisj : Disjoint S S_rest :=
      foldr_disjoint_of_pairwise (List.pairwise_cons.mp hpw).1
    have hx'_out : ∀ w, w ∉ S → x' w = z w := fun w hw =>
      act_ket_usesOnly_outside huses_lc hx'_act hw
    have hagree : ∀ w ∈ S_rest, x' w = z w := fun w hw =>
      hx'_out w (Finset.disjoint_right.mp hdisj hw)
    have hstep := act_ket_agree_on_usesOnly ihRes.1 ihRes.2.1 hih hagree
    rw [hstep]
    congr 1
    funext w
    simp only [List.foldr_cons, Finset.mem_union]
    by_cases hwR : w ∈ S_rest
    · rw [if_pos hwR, if_pos hwR, if_pos (Or.inr hwR)]
    · by_cases hwS : w ∈ S
      · rw [if_neg hwR, hx'_in w hwS, if_pos (Or.inl hwS)]
      · rw [if_neg hwR, hx'_out w hwS, if_neg (not_or.mpr ⟨hwS, hwR⟩)]

lemma act_parMergeList_allId {m : ℕ}
    (xs : List (LayeredCircuit m × Finset (Fin m)))
    (huses : ∀ p ∈ xs, p.1.UsesOnly p.2)
    (hpw : xs.Pairwise (fun p q => Disjoint p.2 q.2))
    (z : Qubits m)
    (hid : ∀ p ∈ xs, act p.1.unitary (ket z) = ket z) :
    act (parMergeList xs huses hpw).1.unitary (ket z) = ket z := by
  have hact : ∀ p ∈ xs, ∃ x' : Qubits m, act p.1.unitary (ket z) = ket x' ∧ ∀ w ∈ p.2, x' w = z w :=
    fun p hp => ⟨z, hid p hp, fun _ _ => rfl⟩
  rw [act_parMergeList_ket xs huses hpw z z hact]
  congr 1
  funext w
  split_ifs <;> rfl

lemma act_parMergeList_singleActive {m : ℕ} {κ : Type*} [Fintype κ]
    (xs : List (LayeredCircuit m × Finset (Fin m)))
    (huses : ∀ p ∈ xs, p.1.UsesOnly p.2)
    (hpw : xs.Pairwise (fun p q => Disjoint p.2 q.2))
    (p₀ : LayeredCircuit m × Finset (Fin m))
    (hp₀_mem : p₀ ∈ xs) (hp₀_nodup : xs.Nodup)
    (z : Qubits m) (α : κ → ℂ) (z' : κ → Qubits m)
    (hactive : act p₀.1.unitary (ket z) = ∑ y : κ, α y • ket (z' y))
    (hagree_out : ∀ y : κ, ∀ w : Fin m, w ∉ p₀.2 → z' y w = z w)
    (hid : ∀ p ∈ xs, p ≠ p₀ → act p.1.unitary (ket z) = ket z) :
    act (parMergeList xs huses hpw).1.unitary (ket z) = ∑ y : κ, α y • ket (z' y) := by
  induction xs with
  | nil => cases hp₀_mem
  | cons p rest ih =>
    rcases p with ⟨lc, S⟩
    dsimp only [parMergeList]
    rw [LayeredCircuit.parMerge_unitary, act_mul]
    have huses_rest : ∀ q ∈ rest, q.1.UsesOnly q.2 := fun q hq => huses q (List.mem_cons_of_mem _ hq)
    have hpw_rest : rest.Pairwise (fun a b => Disjoint a.2 b.2) := (List.pairwise_cons.mp hpw).2
    have hnd_cons := List.nodup_cons.mp hp₀_nodup
    by_cases heq : (lc, S) = p₀
    · subst heq
      have hnot_rest : (lc, S) ∉ rest := hnd_cons.1
      rw [hactive, act_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [act_smul]
      congr 1
      have hrest_id : act (parMergeList rest huses_rest hpw_rest).1.unitary (ket z) = ket z := by
        apply act_parMergeList_allId
        intro q hq
        have hne : q ≠ (lc, S) := fun h => hnot_rest (h ▸ hq)
        exact hid q (List.mem_cons_of_mem _ hq) hne
      have hdisj : Disjoint S (rest.foldr (fun q acc => q.2 ∪ acc) ∅) :=
        foldr_disjoint_of_pairwise (List.pairwise_cons.mp hpw).1
      have hagree_y : ∀ w ∈ rest.foldr (fun q acc => q.2 ∪ acc) ∅, z' y w = z w := fun w hw =>
        hagree_out y w (Finset.disjoint_right.mp hdisj hw)
      have hres := act_ket_agree_on_usesOnly (parMergeList rest huses_rest hpw_rest).1
        (parMergeList rest huses_rest hpw_rest).2.1 hrest_id hagree_y
      rw [hres]
      congr 1
      funext w
      by_cases hw : w ∈ rest.foldr (fun q acc => q.2 ∪ acc) ∅
      · rw [if_pos hw, hagree_y w hw]
      · rw [if_neg hw]
    · have hp₀_rest : p₀ ∈ rest := by
        rw [List.mem_cons] at hp₀_mem
        rcases hp₀_mem with h | h
        · exact absurd h.symm heq
        · exact h
      rw [hid (lc, S) List.mem_cons_self heq]
      exact ih huses_rest hpw_rest hp₀_rest hnd_cons.2
        (fun q hq => hid q (List.mem_cons_of_mem _ hq))

private lemma sum_finRange_map {N : ℕ} (g : Fin N → ℕ) :
    ((List.finRange N).map g).sum = ∑ i : Fin N, g i := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map, Fin.sum_univ_succ]
    exact congrArg (g 0 + ·) (ih (g ∘ Fin.succ))

def parMergeFin {m N : ℕ} (f : Fin N → LayeredCircuit m) (S : Fin N → Finset (Fin m))
    (huses : ∀ i, (f i).UsesOnly (S i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    { lc : LayeredCircuit m //
      lc.UsesOnly (Finset.univ.biUnion S) ∧
      lc.size = ∑ i : Fin N, (f i).size ∧
      (∀ B, (∀ i, (f i).depth ≤ B) → lc.depth ≤ B) } :=
  let xs := (List.finRange N).map fun i => (f i, S i)
  have huses' : ∀ p ∈ xs, p.1.UsesOnly p.2 := by
    intro p hp
    simp only [xs, List.mem_map] at hp
    rcases hp with ⟨i, _, rfl⟩
    exact huses i
  have hpw' : xs.Pairwise fun p q => Disjoint p.2 q.2 := by
    dsimp only [xs]
    rw [List.pairwise_map]
    exact (List.nodup_iff_pairwise_ne.mp (List.nodup_finRange N)).imp fun hij => hdisj _ _ hij
  let res := parMergeList xs huses' hpw'
  have hfold_sub : xs.foldr (fun p acc => p.2 ∪ acc) ∅ ⊆ Finset.univ.biUnion S := by
    intro w hw
    have hgen : ∀ (L : List (Fin N)),
        w ∈ (L.map fun i => (f i, S i)).foldr (fun p acc => p.2 ∪ acc) ∅ →
        ∃ i ∈ L, w ∈ S i := by
      intro L
      induction L with
      | nil => simp
      | cons a rest ih =>
        simp only [List.map_cons, List.foldr_cons, Finset.mem_union]
        rintro (ha | hr)
        · exact ⟨a, List.mem_cons_self, ha⟩
        · obtain ⟨i, hi, hwi⟩ := ih hr
          exact ⟨i, List.mem_cons_of_mem _ hi, hwi⟩
    obtain ⟨i, _, hwi⟩ := hgen (List.finRange N) hw
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hwi⟩
  ⟨res.1, res.2.1.mono hfold_sub,
    by rw [res.2.2.1]; dsimp only [xs]; rw [List.map_map]; exact sum_finRange_map _,
    fun B hB => le_trans res.2.2.2 (foldr_max_le xs B fun p hp => by
      simp only [xs, List.mem_map] at hp
      rcases hp with ⟨i, _, rfl⟩
      exact hB i)⟩

lemma act_parMergeFin_ket {m N : ℕ}
    (f : Fin N → LayeredCircuit m) (S : Fin N → Finset (Fin m))
    (huses : ∀ i, (f i).UsesOnly (S i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (z z_next : Qubits m)
    (hact : ∀ i : Fin N, ∃ x' : Qubits m,
      act (f i).unitary (ket z) = ket x' ∧ ∀ w ∈ S i, x' w = z_next w) :
    act (parMergeFin f S huses hdisj).1.unitary (ket z) =
      ket (fun w => if w ∈ Finset.univ.biUnion S then z_next w else z w) := by
  dsimp only [parMergeFin]
  rw [act_parMergeList_ket _ _ _ z z_next (fun p hp => by
    simp only [List.mem_map] at hp
    rcases hp with ⟨i, _, rfl⟩
    exact hact i)]
  congr 1
  funext w
  have hiff : (w ∈ ((List.finRange N).map fun i => (f i, S i)).foldr (fun p acc => p.2 ∪ acc) ∅) ↔
      w ∈ Finset.univ.biUnion S := by
    have hgen : ∀ (L : List (Fin N)),
        (w ∈ (L.map fun i => (f i, S i)).foldr (fun p acc => p.2 ∪ acc) ∅) ↔ ∃ i ∈ L, w ∈ S i := by
      intro L
      induction L with
      | nil => simp
      | cons a rest ih =>
        simp only [List.map_cons, List.foldr_cons, Finset.mem_union, List.mem_cons, ih]
        constructor
        · rintro (ha | ⟨i, hi, hwi⟩)
          · exact ⟨a, Or.inl rfl, ha⟩
          · exact ⟨i, Or.inr hi, hwi⟩
        · rintro ⟨i, rfl | hi, hwi⟩
          · exact Or.inl hwi
          · exact Or.inr ⟨i, hi, hwi⟩
    rw [hgen (List.finRange N), Finset.mem_biUnion]
    simp
  by_cases hw : w ∈ Finset.univ.biUnion S
  · rw [if_pos (hiff.mpr hw), if_pos hw]
  · rw [if_neg (mt hiff.mp hw), if_neg hw]

lemma act_parMergeFin_singleActive {m N : ℕ} {κ : Type*} [Fintype κ]
    (f : Fin N → LayeredCircuit m) (S : Fin N → Finset (Fin m))
    (huses : ∀ i, (f i).UsesOnly (S i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (i₀ : Fin N) (hS_ne : ∀ i j : Fin N, i ≠ j → S i ≠ S j ∨ f i ≠ f j)
    (z : Qubits m) (α : κ → ℂ) (z' : κ → Qubits m)
    (hactive : act (f i₀).unitary (ket z) = ∑ y : κ, α y • ket (z' y))
    (hagree_out : ∀ y : κ, ∀ w : Fin m, w ∉ S i₀ → z' y w = z w)
    (hid : ∀ i : Fin N, i ≠ i₀ → act (f i).unitary (ket z) = ket z) :
    act (parMergeFin f S huses hdisj).1.unitary (ket z) = ∑ y : κ, α y • ket (z' y) := by
  dsimp only [parMergeFin]
  let xs := (List.finRange N).map fun i => (f i, S i)
  have hp₀_mem : (f i₀, S i₀) ∈ xs :=
    List.mem_map.mpr ⟨i₀, List.mem_finRange i₀, rfl⟩
  have hnd : xs.Nodup := by
    dsimp only [xs]
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    refine (List.nodup_iff_pairwise_ne.mp (List.nodup_finRange N)).imp fun {a b} hab heq => ?_
    rcases hS_ne a b hab with hS | hf
    · exact hS (congrArg Prod.snd heq)
    · exact hf (congrArg Prod.fst heq)
  apply act_parMergeList_singleActive xs _ _ (f i₀, S i₀) hp₀_mem hnd z α z' hactive hagree_out
  intro p hp hne
  simp only [xs, List.mem_map] at hp
  rcases hp with ⟨i, _, rfl⟩
  have hii₀ : i ≠ i₀ := fun h => hne (by subst h; rfl)
  exact hid i hii₀

lemma act_parMergeFin_allId {m N : ℕ}
    (f : Fin N → LayeredCircuit m) (S : Fin N → Finset (Fin m))
    (huses : ∀ i, (f i).UsesOnly (S i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (z : Qubits m)
    (hid : ∀ i : Fin N, act (f i).unitary (ket z) = ket z) :
    act (parMergeFin f S huses hdisj).1.unitary (ket z) = ket z := by
  rw [act_parMergeFin_ket f S huses hdisj z z (fun i => ⟨z, hid i, fun _ _ => rfl⟩)]
  congr 1; funext w; split_ifs <;> rfl

/-! ### 4. General `fanoutCircuit` and `ctrlNotN` -/

private def fanSlice {m : ℕ} (lo len : ℕ) : Finset (Fin (1 + m)) :=
  Finset.univ.filter fun w => 1 + lo ≤ w.1 ∧ w.1 < 1 + lo + len

private lemma fanSlice_disjoint (m lo mid len : ℕ) :
    Disjoint (fanSlice (m := m) lo mid) (fanSlice (m := m) (lo + mid) (len - mid)) := by
  rw [Finset.disjoint_left]
  intro w h1 h2
  simp only [fanSlice, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  omega

private lemma fanSlice_union_sub (m lo mid len : ℕ) (hmid : mid ≤ len) :
    fanSlice (m := m) lo mid ∪ fanSlice (m := m) (lo + mid) (len - mid) ⊆
      fanSlice (m := m) lo len := by
  intro w hw
  simp only [Finset.mem_union, fanSlice, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  omega

private def fanoutRange (m lo len : ℕ) (_hlen : 1 ≤ len) (hb : lo + len ≤ m) :
    { lc : LayeredCircuit (1 + m) // lc.UsesOnly (fanSlice lo len) } :=
  if h2 : len < 2 then
    ⟨LayeredCircuit.id (1 + m), LayeredCircuit.id_usesOnly _⟩
  else
    let mid := len / 2
    have hmid1 : 1 ≤ mid := by omega
    have hrem1 : 1 ≤ len - mid := by omega
    have hbL : lo + mid ≤ m := by omega
    have hbR : lo + mid + (len - mid) ≤ m := by omega
    let L := fanoutRange m lo mid hmid1 hbL
    let R := fanoutRange m (lo + mid) (len - mid) hrem1 hbR
    let wL : Fin (1 + m) := ⟨1 + lo, by omega⟩
    let wR : Fin (1 + m) := ⟨1 + (lo + mid), by omega⟩
    have hne : wL ≠ wR := by
      intro h; have := congrArg Fin.val h; dsimp [wL, wR] at this; omega
    let step := cnotGate wL wR hne
    let merged := LayeredCircuit.parMerge L.1 R.1 L.2 R.2 (fanSlice_disjoint m lo mid len)
    ⟨step.seq merged,
      LayeredCircuit.seq_usesOnly
        ((cnotGate_usesOnly wL wR hne).mono (by
          intro w hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · simp [fanSlice, wL]; omega
          · simp [fanSlice, wR]; omega))
        ((LayeredCircuit.parMerge_usesOnly L.1 R.1 L.2 R.2 _).mono
          (fanSlice_union_sub m lo mid len (by omega)))⟩
termination_by len

private lemma fanoutRange_size (m lo len : ℕ) (hlen : 1 ≤ len) (hb : lo + len ≤ m) :
    (fanoutRange m lo len hlen hb).1.size = len - 1 := by
  induction len using Nat.strong_induction_on generalizing lo with
  | h len ih =>
    unfold fanoutRange
    split_ifs with h2
    · simp; omega
    · dsimp only
      have hsL := ih (len / 2) (by omega) lo (by omega) (by omega)
      have hsR := ih (len - len / 2) (by omega) (lo + len / 2) (by omega) (by omega)
      simp only [LayeredCircuit.seq_size, LayeredCircuit.parMerge_size, cnotGate_size]
      rw [hsL, hsR]
      omega

private lemma fanoutRange_depth (m lo len : ℕ) (hlen : 1 ≤ len) (hb : lo + len ≤ m) :
    (fanoutRange m lo len hlen hb).1.depth ≤ Nat.clog 2 len := by
  induction len using Nat.strong_induction_on generalizing lo with
  | h len ih =>
    unfold fanoutRange
    split_ifs with h2
    · simp
    · dsimp only
      have hlen2 : 2 ≤ len := by omega
      have hdL := ih (len / 2) (by omega) lo (by omega) (by omega)
      have hdR := ih (len - len / 2) (by omega) (lo + len / 2) (by omega) (by omega)
      have hL_le : (fanoutRange m lo (len / 2) (by omega) (by omega)).1.depth ≤
          Nat.clog 2 ((len + 1) / 2) :=
        le_trans hdL clog2_half_le
      have hclog_sub : Nat.clog 2 (len - len / 2) = Nat.clog 2 ((len + 1) / 2) := by
        congr 1; omega
      have hR_le : (fanoutRange m (lo + len / 2) (len - len / 2) (by omega) (by omega)).1.depth ≤
          Nat.clog 2 ((len + 1) / 2) := hclog_sub ▸ hdR
      simp only [LayeredCircuit.seq_depth, LayeredCircuit.parMerge_depth, cnotGate_depth]
      rw [← clog2_rec hlen2, Nat.add_comm 1]
      exact Nat.add_le_add_right (max_le hL_le hR_le) 1

private lemma act_fanoutRange_ket (m lo len : ℕ) (hlen : 1 ≤ len) (hb : lo + len ≤ m)
    (c : Bool) (x : Qubits (1 + m))
    (hroot : x ⟨1 + lo, by omega⟩ = c)
    (hclean : ∀ k : ℕ, lo < k → ∀ (_hk2 : k < lo + len), x ⟨1 + k, by omega⟩ = false) :
    act (fanoutRange m lo len hlen hb).1.unitary (ket x) =
      ket (fun w => if 1 + lo ≤ w.1 ∧ w.1 < 1 + lo + len then c else x w) := by
  induction len using Nat.strong_induction_on generalizing lo x with
  | h len ih =>
    unfold fanoutRange
    split_ifs with h2
    · have hlen1 : len = 1 := by omega
      subst hlen1
      simp only [LayeredCircuit.id_unitary, act_one]
      congr 1
      funext w
      split_ifs with hw
      · have hw_eq : w = ⟨1 + lo, by omega⟩ := Fin.ext (by simp; omega)
        rw [hw_eq, hroot]
      · rfl
    · dsimp only
      set mid := len / 2
      have hmid1 : 1 ≤ mid := by omega
      have hrem1 : 1 ≤ len - mid := by omega
      have hmid_lt : mid < len := by omega
      have hrem_lt : len - mid < len := by omega
      have hbL : lo + mid ≤ m := by omega
      have hbR : lo + mid + (len - mid) ≤ m := by omega
      let wL : Fin (1 + m) := ⟨1 + lo, by omega⟩
      let wR : Fin (1 + m) := ⟨1 + (lo + mid), by omega⟩
      have hne : wL ≠ wR := by
        intro h; have := congrArg Fin.val h; dsimp [wL, wR] at this; omega
      simp only [LayeredCircuit.seq_unitary, act_mul, act_cnotGate_ket,
        LayeredCircuit.parMerge_unitary]
      let x1 : Qubits (1 + m) := Function.update x wR (xor (x wR) (x wL))
      have hx1_wL : x1 wL = c := by
        dsimp only [x1]
        rw [Function.update_of_ne hne, hroot]
      have hx1_wR : x1 wR = c := by
        have hzero : x wR = false := hclean (lo + mid) (by omega) (by omega)
        dsimp only [x1]
        rw [Function.update_self, hzero]
        change xor false (x ⟨1 + lo, by omega⟩) = c
        rw [hroot, Bool.false_xor]
      have hx1_cleanL : ∀ k : ℕ, lo < k → ∀ (_hk2 : k < lo + mid), x1 ⟨1 + k, by omega⟩ = false := by
        intro k hk1 hk2
        have hneR : (⟨1 + k, by omega⟩ : Fin (1 + m)) ≠ wR := by
          intro h; have := congrArg Fin.val h; dsimp [wR] at this; omega
        dsimp only [x1]
        rw [Function.update_of_ne hneR]
        exact hclean k hk1 (by omega)
      have hx1_cleanR : ∀ k : ℕ, lo + mid < k → ∀ (_hk2 : k < lo + mid + (len - mid)),
          x1 ⟨1 + k, by omega⟩ = false := by
        intro k hk1 hk2
        have hneR : (⟨1 + k, by omega⟩ : Fin (1 + m)) ≠ wR := by
          intro h; have := congrArg Fin.val h; dsimp [wR] at this; omega
        dsimp only [x1]
        rw [Function.update_of_ne hneR]
        exact hclean k (by omega) (by omega)
      have hL_act := ih mid hmid_lt lo hmid1 hbL x1 hx1_wL hx1_cleanL
      let x2 : Qubits (1 + m) := fun w =>
        if 1 + lo ≤ w.1 ∧ w.1 < 1 + lo + mid then c else x1 w
      have hL_act' : act (fanoutRange m lo mid hmid1 hbL).1.unitary (ket x1) = ket x2 := hL_act
      rw [hL_act']
      have hx2_wR : x2 wR = c := by
        have hnot : ¬ (1 + lo ≤ wR.1 ∧ wR.1 < 1 + lo + mid) := by
          dsimp [wR]; omega
        dsimp only [x2]
        rw [if_neg hnot, hx1_wR]
      have hx2_cleanR : ∀ k : ℕ, lo + mid < k → ∀ (_hk2 : k < lo + mid + (len - mid)),
          x2 ⟨1 + k, by omega⟩ = false := by
        intro k hk1 hk2
        have hnot : ¬ (1 + lo ≤ 1 + k ∧ 1 + k < 1 + lo + mid) := by omega
        dsimp only [x2]
        rw [if_neg hnot]
        exact hx1_cleanR k hk1 hk2
      have hR_act := ih (len - mid) hrem_lt (lo + mid) hrem1 hbR x2 hx2_wR hx2_cleanR
      rw [hR_act]
      congr 1
      funext w
      dsimp only [x2, x1]
      by_cases hwR : 1 + (lo + mid) ≤ w.1 ∧ w.1 < 1 + (lo + mid) + (len - mid)
      · rw [if_pos hwR, if_pos (by omega)]
      · rw [if_neg hwR]
        by_cases hwL : 1 + lo ≤ w.1 ∧ w.1 < 1 + lo + mid
        · rw [if_pos hwL, if_pos (by omega)]
        · rw [if_neg hwL, if_neg (by omega)]
          have hneR : w ≠ wR := by
            intro h; apply hwR; rw [h]; dsimp [wR]; omega
          rw [Function.update_of_ne hneR]

def fanoutCircuit (m : ℕ) : LayeredCircuit (1 + m) :=
  if hm : 1 ≤ m then
    let w0 : Fin (1 + m) := ⟨0, by omega⟩
    let a0 : Fin (1 + m) := ⟨1, by omega⟩
    have hne : w0 ≠ a0 := by intro h; have := congrArg Fin.val h; dsimp [w0, a0] at this; omega
    (cnotGate w0 a0 hne).seq (fanoutRange m 0 m hm (by omega)).1
  else
    LayeredCircuit.id (1 + m)

lemma fanoutCircuit_size (m : ℕ) : (fanoutCircuit m).size = m := by
  unfold fanoutCircuit
  split_ifs with hm
  · simp [fanoutRange_size m 0 m hm (by omega)]
    omega
  · simp; omega

lemma fanoutCircuit_depth (m : ℕ) : (fanoutCircuit m).depth ≤ Nat.clog 2 m + 1 := by
  unfold fanoutCircuit
  split_ifs with hm
  · simp only [LayeredCircuit.seq_depth, cnotGate_depth]
    have hd := fanoutRange_depth m 0 m hm (by omega)
    omega
  · simp

lemma fanoutCircuit_usesOnly (m : ℕ) : (fanoutCircuit m).UsesOnly Finset.univ :=
  fun _ _ _ _ _ => Finset.mem_univ _

lemma act_fanoutCircuit_ket (m : ℕ) (c : Bool) (x : Qubits (1 + m))
    (hx0 : x 0 = c)
    (hclean : ∀ j : Fin m, x (Fin.natAdd 1 j) = false) :
    act (fanoutCircuit m).unitary (ket x) = ket (fun _ => c) := by
  by_cases hm : 1 ≤ m
  · simp only [fanoutCircuit, dif_pos hm, LayeredCircuit.seq_unitary, act_mul, act_cnotGate_ket]
    let w0 : Fin (1 + m) := ⟨0, by omega⟩
    let a0 : Fin (1 + m) := ⟨1, by omega⟩
    let x1 : Qubits (1 + m) := Function.update x a0 (xor (x a0) (x w0))
    have hx1_a0 : x1 ⟨1 + 0, by omega⟩ = c := by
      have h0 := hclean ⟨0, hm⟩
      dsimp only [x1, a0, w0]
      rw [Function.update_self]
      have h0' : x ⟨1, by omega⟩ = false := h0
      have hx0' : x ⟨0, by omega⟩ = c := hx0
      rw [h0', hx0', Bool.false_xor]
    have hx1_clean : ∀ k : ℕ, 0 < k → ∀ (_hk2 : k < 0 + m), x1 ⟨1 + k, by omega⟩ = false := by
      intro k hk1 hk2
      have hne : (⟨1 + k, by omega⟩ : Fin (1 + m)) ≠ a0 := by
        intro h; have := congrArg Fin.val h; dsimp [a0] at this; omega
      dsimp only [x1]
      rw [Function.update_of_ne hne]
      exact hclean ⟨k, by omega⟩
    rw [act_fanoutRange_ket m 0 m hm (by omega) c x1 hx1_a0 hx1_clean]
    congr 1
    funext w
    by_cases hw : 1 + 0 ≤ w.1 ∧ w.1 < 1 + 0 + m
    · rw [if_pos hw]
    · rw [if_neg hw]
      have hw0 : w = 0 := Fin.ext (show w.1 = 0 by have := w.isLt; omega)
      have hwa : w ≠ a0 := by rw [hw0]; intro h; have := congrArg Fin.val h; dsimp [a0] at this; omega
      dsimp only [x1]
      rw [Function.update_of_ne hwa, hw0, hx0]
  · have hm0 : m = 0 := by omega
    subst hm0
    simp only [fanoutCircuit, dif_neg hm, LayeredCircuit.id_unitary, act_one]
    congr 1
    funext w
    have hw0 : w = 0 := Fin.ext (by have := w.isLt; omega)
    rw [hw0, hx0]

/-! #### `ctrlNotN` -/

def ctrlNotFn (n : ℕ) (x : Qubits (1 + n)) : Qubits (1 + n) :=
  fun i => if i.1 = 0 then x i else xor (x i) (x 0)

def ctrlNotMat (n : ℕ) : Matrix (Qubits (1 + n)) (Qubits (1 + n)) ℂ :=
  permMat (ctrlNotFn n)

lemma ctrlNotFn_invol (n : ℕ) (x : Qubits (1 + n)) :
    ctrlNotFn n (ctrlNotFn n x) = x := by
  funext i
  dsimp only [ctrlNotFn]
  by_cases hi : i.1 = 0
  · rw [if_pos hi, if_pos hi]
  · rw [if_neg hi, if_neg hi]
    have h0 : (0 : Fin (1 + n)).1 = 0 := rfl
    rw [if_pos h0]
    cases x i <;> cases x 0 <;> rfl

lemma ctrlNotMat_mem_unitaryGroup (n : ℕ) :
    ctrlNotMat n ∈ Matrix.unitaryGroup (Qubits (1 + n)) ℂ := by
  apply permMat_mem_unitaryGroup
  refine ⟨fun a b h => ?_, fun b => ⟨ctrlNotFn n b, ctrlNotFn_invol n b⟩⟩
  calc a = ctrlNotFn n (ctrlNotFn n a) := (ctrlNotFn_invol n a).symm
    _ = ctrlNotFn n (ctrlNotFn n b) := by rw [h]
    _ = b := ctrlNotFn_invol n b

private def ctrlNotFanEmb (n : ℕ) : Fin (1 + n) ↪ Fin (1 + n + n) where
  toFun w := if w.1 = 0 then ⟨0, by omega⟩ else ⟨n + w.1, by have := w.isLt; omega⟩
  inj' a b h := by
    have ha := a.isLt; have hb := b.isLt
    change (if a.1 = 0 then (⟨0, by omega⟩ : Fin (1 + n + n)) else ⟨n + a.1, by omega⟩) =
      (if b.1 = 0 then ⟨0, by omega⟩ else ⟨n + b.1, by omega⟩) at h
    split_ifs at h with ha0 hb0
    · exact Fin.ext (by omega)
    · have := congrArg Fin.val h; simp at this; omega
    · have := congrArg Fin.val h; simp at this; omega
    · have := congrArg Fin.val h; simp at this; exact Fin.ext (by omega)

private lemma ctrlNotFanEmb_apply (n : ℕ) (w : Fin (1 + n)) :
    ctrlNotFanEmb n w = if w.1 = 0 then ⟨0, by omega⟩ else ⟨n + w.1, by have := w.isLt; omega⟩ := rfl

@[simp] private lemma ctrlNotFanEmb_zero (n : ℕ) :
    ctrlNotFanEmb n 0 = ⟨0, by omega⟩ := by
  rw [ctrlNotFanEmb_apply]; rfl

@[simp] private lemma ctrlNotFanEmb_natAdd (n : ℕ) (j : Fin n) :
    ctrlNotFanEmb n (Fin.natAdd 1 j) = Fin.natAdd (1 + n) j := by
  rw [ctrlNotFanEmb_apply, if_neg (by simp)]
  ext; simp; omega

private lemma ctrlNotFanEmb_eq_iff (n : ℕ) (w : Fin (1 + n)) :
    1 + n ≤ (ctrlNotFanEmb n w).1 ↔ w.1 ≠ 0 := by
  rw [ctrlNotFanEmb_apply]
  split_ifs with h
  · simp [h]
  · simp [h]; omega

private def ctrlNotCnotWire (n : ℕ) (i : Fin n) : Fin (1 + n + n) :=
  ⟨1 + n + i.1, by have := i.isLt; omega⟩

private def ctrlNotTgtWire (n : ℕ) (i : Fin n) : Fin (1 + n + n) :=
  ⟨1 + i.1, by have := i.isLt; omega⟩

private lemma ctrlNot_wire_ne (n : ℕ) (i : Fin n) :
    ctrlNotCnotWire n i ≠ ctrlNotTgtWire n i := by
  intro h; have := congrArg Fin.val h; dsimp [ctrlNotCnotWire, ctrlNotTgtWire] at this; omega

private def ctrlNotCnotLayer (n : ℕ) : LayeredCircuit (1 + n + n) :=
  (parMergeFin
    (fun i : Fin n => cnotGate (ctrlNotCnotWire n i) (ctrlNotTgtWire n i) (ctrlNot_wire_ne n i))
    (fun i : Fin n => {ctrlNotCnotWire n i, ctrlNotTgtWire n i})
    (fun i => cnotGate_usesOnly _ _ _)
    (fun i j hij => by
      have hi := i.isLt; have hj := j.isLt
      rw [Finset.disjoint_left]
      intro w hwi hwj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwi hwj
      rcases hwi with rfl | rfl <;> rcases hwj with h | h <;>
        [have := congrArg Fin.val h; have := congrArg Fin.val h;
         have := congrArg Fin.val h; have := congrArg Fin.val h] <;>
        dsimp [ctrlNotCnotWire, ctrlNotTgtWire] at this <;> exact absurd (Fin.ext (by omega)) hij)).1

private lemma ctrlNotCnotLayer_size (n : ℕ) : (ctrlNotCnotLayer n).size = n := by
  dsimp only [ctrlNotCnotLayer]
  rw [(parMergeFin _ _ _ _).2.2.1]
  simp [cnotGate_size]

private lemma ctrlNotCnotLayer_depth (n : ℕ) : (ctrlNotCnotLayer n).depth ≤ 1 := by
  dsimp only [ctrlNotCnotLayer]
  exact (parMergeFin _ _ _ _).2.2.2 1 (fun _ => by simp)

def ctrlNotN (n : ℕ) : LayeredCircuit (1 + n + n) :=
  if n = 0 then LayeredCircuit.id (1 + n + n)
  else
    let fan := (fanoutCircuit n).mapWires (ctrlNotFanEmb n)
    fan.seq ((ctrlNotCnotLayer n).seq fan.adj)

lemma ctrlNotN_size (n : ℕ) : (ctrlNotN n).size = 3 * n := by
  unfold ctrlNotN
  split_ifs with hn
  · subst hn; simp
  · simp only [LayeredCircuit.seq_size, LayeredCircuit.adj_size, LayeredCircuit.mapWires_size,
      fanoutCircuit_size, ctrlNotCnotLayer_size]
    omega

lemma ctrlNotN_depth (n : ℕ) : (ctrlNotN n).depth ≤ 2 * Nat.clog 2 (n + 1) + 3 := by
  unfold ctrlNotN
  split_ifs with hn
  · subst hn; simp
  · simp only [LayeredCircuit.seq_depth, LayeredCircuit.adj_depth, LayeredCircuit.mapWires_depth]
    have hfan : (fanoutCircuit n).depth ≤ Nat.clog 2 n + 1 := fanoutCircuit_depth n
    have hclog : Nat.clog 2 n ≤ Nat.clog 2 (n + 1) := Nat.clog_mono_right 2 (by omega)
    have hc : (ctrlNotCnotLayer n).depth ≤ 1 := ctrlNotCnotLayer_depth n
    omega

lemma act_ctrlNotN_ket (n : ℕ) (x : Qubits (1 + n)) :
    act (ctrlNotN n).unitary (ket (padZero (1 + n) n x)) =
      ket (padZero (1 + n) n (ctrlNotFn n x)) := by
  by_cases hn : n = 0
  · subst hn
    simp only [ctrlNotN, ↓reduceIte, LayeredCircuit.id_unitary, act_one]
    congr 1; funext w
    have hw : w = Fin.castAdd 0 0 := Fin.ext (by have := w.isLt; omega)
    rw [hw, padZero_castAdd, padZero_castAdd]
    simp [ctrlNotFn]
  · simp only [ctrlNotN, if_neg hn, LayeredCircuit.seq_unitary, act_mul]
    let z := padZero (1 + n) n x
    let fan := (fanoutCircuit n).mapWires (ctrlNotFanEmb n)
    let z_fan : Qubits (1 + n + n) := fun w => if 1 + n ≤ w.1 then x 0 else z w
    have hfan_z : act fan.unitary (ket z) = ket z_fan := by
      dsimp only [fan]
      refine act_mapWires_ket (fanoutCircuit n) (ctrlNotFanEmb n) z (fun _ => x 0) ?_ z_fan ?_ ?_
      · refine act_fanoutCircuit_ket n (x 0) (z ∘ ctrlNotFanEmb n) ?_ ?_
        · change z (ctrlNotFanEmb n 0) = x 0
          rw [ctrlNotFanEmb_zero]
          exact padZero_castAdd (1 + n) n x 0
        · intro j
          change z (ctrlNotFanEmb n (Fin.natAdd 1 j)) = false
          rw [ctrlNotFanEmb_natAdd]
          exact padZero_natAdd (1 + n) n x j
      · funext w
        dsimp only [z_fan, Function.comp_apply]
        by_cases hw0 : w.1 = 0
        · have hw : w = 0 := Fin.ext hw0
          have hnot : ¬ 1 + n ≤ (ctrlNotFanEmb n w).1 := by
            rw [ctrlNotFanEmb_eq_iff]; simp [hw0]
          rw [if_neg hnot, hw, ctrlNotFanEmb_zero]
          exact padZero_castAdd (1 + n) n x 0
        · have hge : 1 + n ≤ (ctrlNotFanEmb n w).1 := (ctrlNotFanEmb_eq_iff n w).mpr hw0
          rw [if_pos hge]
      · intro i hi
        have hnot : ¬ 1 + n ≤ i.1 := by
          intro hge
          apply hi
          refine ⟨⟨i.1 - n, by have := i.isLt; omega⟩, ?_⟩
          rw [ctrlNotFanEmb_apply, if_neg (by simp; omega)]
          ext; simp; omega
        dsimp only [z_fan]
        rw [if_neg hnot]
    let z_out := padZero (1 + n) n (ctrlNotFn n x)
    let z_mid : Qubits (1 + n + n) := fun w => if 1 + n ≤ w.1 then x 0 else z_out w
    have hcnot_act : act (ctrlNotCnotLayer n).unitary (ket z_fan) = ket z_mid := by
      dsimp only [ctrlNotCnotLayer]
      have hact_each : ∀ i : Fin n, ∃ x' : Qubits (1 + n + n),
          act (cnotGate (ctrlNotCnotWire n i) (ctrlNotTgtWire n i) (ctrlNot_wire_ne n i)).unitary (ket z_fan) = ket x' ∧
          ∀ w ∈ ({ctrlNotCnotWire n i, ctrlNotTgtWire n i} : Finset (Fin (1 + n + n))),
            x' w = z_mid w := by
        intro i
        refine ⟨_, act_cnotGate_ket _ _ _ z_fan, fun w hw => ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · rw [Function.update_of_ne (ctrlNot_wire_ne n i)]
          simp [z_fan, z_mid, ctrlNotCnotWire]
        · rw [Function.update_self]
          have hctrl : z_fan (ctrlNotCnotWire n i) = x 0 := by
            simp [z_fan, ctrlNotCnotWire]
          have htgt_fan : z_fan (ctrlNotTgtWire n i) = x ⟨1 + i.1, by have := i.isLt; omega⟩ := by
            dsimp only [z_fan, z, ctrlNotTgtWire]
            rw [if_neg (by omega)]
            exact padZero_castAdd (1 + n) n x ⟨1 + i.1, by have := i.isLt; omega⟩
          have htgt_mid : z_mid (ctrlNotTgtWire n i) = xor (x ⟨1 + i.1, by have := i.isLt; omega⟩) (x 0) := by
            dsimp only [z_mid, z_out, ctrlNotTgtWire]
            rw [if_neg (by omega)]
            have hca : (⟨1 + i.1, by have := i.isLt; omega⟩ : Fin (1 + n + n)) =
                Fin.castAdd n ⟨1 + i.1, by have := i.isLt; omega⟩ := rfl
            rw [hca, padZero_castAdd]
            simp [ctrlNotFn]
          rw [hctrl, htgt_fan, htgt_mid]
      rw [act_parMergeFin_ket _ _ _ _ z_fan z_mid hact_each]
      congr 1
      funext w
      split_ifs with hw
      · rfl
      · dsimp only [z_fan, z_mid]
        by_cases hw_ge : 1 + n ≤ w.1
        · rw [if_pos hw_ge, if_pos hw_ge]
        · rw [if_neg hw_ge, if_neg hw_ge]
          by_cases hw0 : w.1 = 0
          · have hwe : w = Fin.castAdd n 0 := Fin.ext hw0
            rw [hwe]
            simp [z, z_out, ctrlNotFn]
          · exfalso; apply hw
            rw [Finset.mem_biUnion]
            refine ⟨⟨w.1 - 1, by omega⟩, Finset.mem_univ _, ?_⟩
            simp only [Finset.mem_insert, Finset.mem_singleton]
            right
            ext; simp [ctrlNotTgtWire]; omega
    have hfan_out : act fan.unitary (ket z_out) = ket z_mid := by
      dsimp only [fan]
      refine act_mapWires_ket (fanoutCircuit n) (ctrlNotFanEmb n) z_out (fun _ => x 0) ?_ z_mid ?_ ?_
      · refine act_fanoutCircuit_ket n (x 0) (z_out ∘ ctrlNotFanEmb n) ?_ ?_
        · change z_out (ctrlNotFanEmb n 0) = x 0
          rw [ctrlNotFanEmb_zero]
          have hca0 : (⟨0, by omega⟩ : Fin (1 + n + n)) = Fin.castAdd n 0 := rfl
          rw [hca0]; simp [z_out, ctrlNotFn]
        · intro j
          change z_out (ctrlNotFanEmb n (Fin.natAdd 1 j)) = false
          rw [ctrlNotFanEmb_natAdd]
          exact padZero_natAdd (1 + n) n _ j
      · funext w
        dsimp only [z_mid, Function.comp_apply]
        by_cases hw0 : w.1 = 0
        · have hw : w = 0 := Fin.ext hw0
          have hnot : ¬ 1 + n ≤ (ctrlNotFanEmb n w).1 := by
            rw [ctrlNotFanEmb_eq_iff]; simp [hw0]
          rw [if_neg hnot, hw, ctrlNotFanEmb_zero]
          have hca0 : (⟨0, by omega⟩ : Fin (1 + n + n)) = Fin.castAdd n 0 := rfl
          rw [hca0]; simp [z_out, ctrlNotFn]
        · have hge : 1 + n ≤ (ctrlNotFanEmb n w).1 := (ctrlNotFanEmb_eq_iff n w).mpr hw0
          rw [if_pos hge]
      · intro i hi
        have hnot : ¬ 1 + n ≤ i.1 := by
          intro hge
          apply hi
          refine ⟨⟨i.1 - n, by have := i.isLt; omega⟩, ?_⟩
          rw [ctrlNotFanEmb_apply, if_neg (by simp; omega)]
          ext; simp; omega
        dsimp only [z_mid]
        rw [if_neg hnot]
    have hfan_adj : act fan.adj.unitary (ket z_mid) = ket z_out := by
      rw [← hfan_out, ← act_mul, LayeredCircuit.adj_unitary,
        Matrix.mem_unitaryGroup_iff'.mp fan.unitary_mem_unitaryGroup, act_one]
    rw [hfan_z, hcnot_act, hfan_adj]

theorem ctrlNotN_implements (n : ℕ) : (ctrlNotN n).ImplementsOnClean (ctrlNotMat n) :=
  implementsOnClean_of_act_perm (ctrlNotN n) (ctrlNotFn n) (act_ctrlNotN_ket n)

/-! ### 5. Fredkin (`cswap3`, `cswapOn`) -/

def cswapFn (z : Qubits 3) : Qubits 3 :=
  if z 0 then ![z 0, z 2, z 1] else z

noncomputable def cswap3 : LayeredCircuit 3 :=
  (cnotGate 2 1 (by decide)).seq
    ((toffoliOn 0 1 2 (by decide) (by decide) (by decide)).seq
      (cnotGate 2 1 (by decide)))

@[simp] lemma cswap3_size : cswap3.size = 7 := rfl
@[simp] lemma cswap3_depth : cswap3.depth = 7 := rfl

lemma act_cswap3_ket (z : Qubits 3) :
    act cswap3.unitary (ket z) = ket (cswapFn z) := by
  dsimp only [cswap3]
  simp only [LayeredCircuit.seq_unitary, act_mul, act_cnotGate_ket, act_toffoliOn_ket]
  congr 1
  funext i
  cases h0 : z 0 <;> cases h1 : z 1 <;> cases h2 : z 2 <;>
    fin_cases i <;> simp [cswapFn, h0, h1, h2]

noncomputable def cswapOn {m : ℕ} (c a b : Fin m) (hca : c ≠ a) (hcb : c ≠ b) (hab : a ≠ b) :
    LayeredCircuit m :=
  cswap3.mapWires (wire3Emb c a b hca hcb hab)

@[simp] lemma cswapOn_size {m : ℕ} (c a b : Fin m) (hca : c ≠ a) (hcb : c ≠ b) (hab : a ≠ b) :
    (cswapOn c a b hca hcb hab).size = 7 := by
  simp [cswapOn]

@[simp] lemma cswapOn_depth {m : ℕ} (c a b : Fin m) (hca : c ≠ a) (hcb : c ≠ b) (hab : a ≠ b) :
    (cswapOn c a b hca hcb hab).depth = 7 := by
  simp [cswapOn]

lemma cswapOn_usesOnly {m : ℕ} (c a b : Fin m) (hca : c ≠ a) (hcb : c ≠ b) (hab : a ≠ b) :
    (cswapOn c a b hca hcb hab).UsesOnly {c, a, b} := by
  have h3 : cswap3.UsesOnly Finset.univ := fun _ _ _ _ _ => Finset.mem_univ _
  refine (LayeredCircuit.mapWires_usesOnly (wire3Emb c a b hca hcb hab) cswap3 h3).mono ?_
  intro x hx
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
  rcases hx with ⟨i, rfl⟩
  fin_cases i <;> simp

lemma act_cswapOn_ket {m : ℕ} (c a b : Fin m) (hca : c ≠ a) (hcb : c ≠ b) (hab : a ≠ b)
    (z : Qubits m) :
    act (cswapOn c a b hca hcb hab).unitary (ket z) =
      ket (fun w =>
        if z c then (if w = a then z b else if w = b then z a else z w) else z w) := by
  dsimp only [cswapOn]
  let emb := wire3Emb c a b hca hcb hab
  let z' : Qubits m := fun w =>
    if z c then (if w = a then z b else if w = b then z a else z w) else z w
  refine act_mapWires_ket cswap3 emb z (cswapFn (z ∘ emb)) (act_cswap3_ket _) z' ?_ ?_
  · funext i
    dsimp only [z', Function.comp_apply, cswapFn, emb]
    have h0 : z (wire3Emb c a b hca hcb hab 0) = z c := rfl
    have h1 : z (wire3Emb c a b hca hcb hab 1) = z a := rfl
    have h2 : z (wire3Emb c a b hca hcb hab 2) = z b := rfl
    cases hzc_val : z c
    · have h0' : z (wire3Emb c a b hca hcb hab 0) = false := h0.trans hzc_val
      have h_rhs : (if z (wire3Emb c a b hca hcb hab 0) = true then
          ![z (wire3Emb c a b hca hcb hab 0), z (wire3Emb c a b hca hcb hab 2), z (wire3Emb c a b hca hcb hab 1)]
          else z ∘ ⇑(wire3Emb c a b hca hcb hab)) = ![false, z a, z b] := by
        rw [if_neg (by rw [h0']; decide)]
        ext k; fin_cases k <;> [exact h0'; exact h1; exact h2]
      rw [if_neg (by decide), h_rhs]
      fin_cases i
      · exact h0'
      · exact h1
      · exact h2
    · have h0' : z (wire3Emb c a b hca hcb hab 0) = true := h0.trans hzc_val
      have h_rhs : (if z (wire3Emb c a b hca hcb hab 0) = true then
          ![z (wire3Emb c a b hca hcb hab 0), z (wire3Emb c a b hca hcb hab 2), z (wire3Emb c a b hca hcb hab 1)]
          else z ∘ ⇑(wire3Emb c a b hca hcb hab)) = ![true, z b, z a] := by
        rw [if_pos (by rw [h0'])]
        ext k; fin_cases k <;> [exact h0'; exact h2; exact h1]
      rw [if_pos rfl, h_rhs]
      fin_cases i
      · change (if c = a then z b else if c = b then z a else z c) = true
        rw [if_neg hca, if_neg hcb]; exact hzc_val
      · simp
      · simp [hab.symm]
  · intro i hi
    have hne_c : i ≠ c := fun h => hi ⟨0, h.symm⟩
    have hne_a : i ≠ a := fun h => hi ⟨1, h.symm⟩
    have hne_b : i ≠ b := fun h => hi ⟨2, h.symm⟩
    dsimp only [z']
    split_ifs <;> rfl

/-! ### 6. Coherent Parallel Pre-Fanout Binary SWAP Router (`coherentRouter`) -/

private lemma mul_add_lt_mul {a b c d : ℕ} (ha : a < b) (hc : c < d) :
    a * d + c < b * d := by
  calc a * d + c < a * d + d := Nat.add_lt_add_left hc _
    _ = (a + 1) * d := by rw [Nat.add_mul, one_mul]
    _ ≤ b * d := Nat.mul_le_mul_right d ha

private lemma mul_add_div_right (a c d : ℕ) (hd : 0 < d) (hc : c < d) :
    (a * d + c) / d = a := by
  rw [mul_comm a d, Nat.mul_add_div hd, Nat.div_eq_of_lt hc, add_zero]

private lemma mul_add_mod_right (a c d : ℕ) (hc : c < d) :
    (a * d + c) % d = c := by
  rw [mul_comm a d, Nat.mul_add_mod, Nat.mod_eq_of_lt hc]

private lemma div_lt_of_lt_mul' {a b c : ℕ} (h : a < b * c) : a / c < b :=
  Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq h (mul_comm b c))

private lemma eq_of_mul_add_eq {a₁ a₂ c₁ c₂ d : ℕ} (hc1 : c₁ < d) (hc2 : c₂ < d)
    (h : a₁ * d + c₁ = a₂ * d + c₂) : a₁ = a₂ ∧ c₁ = c₂ := by
  have hd : 0 < d := by omega
  have hdiv : (a₁ * d + c₁) / d = (a₂ * d + c₂) / d := congrArg (· / d) h
  have hmod : (a₁ * d + c₁) % d = (a₂ * d + c₂) % d := congrArg (· % d) h
  rw [mul_add_div_right a₁ c₁ d hd hc1, mul_add_div_right a₂ c₂ d hd hc2] at hdiv
  rw [mul_add_mod_right a₁ c₁ d hc1, mul_add_mod_right a₂ c₂ d hc2] at hmod
  exact ⟨hdiv, hmod⟩

private lemma sum_fin_two_pow (h : ℕ) : (∑ s : Fin h, 2 ^ s.1) = 2 ^ h - 1 := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, pow_succ']
    have hpos : 1 ≤ 2 ^ h := Nat.two_pow_pos h
    omega

private lemma bitsToNatLSB_split {ℓ k : ℕ} (hk : k ≤ ℓ) (v : Qubits ℓ) :
    bitsToNatLSB v =
      bitsToNatLSB (fun i : Fin k => v ⟨i.1, by omega⟩) +
      2 ^ k * bitsToNatLSB (fun i : Fin (ℓ - k) => v ⟨k + i.1, by omega⟩) := by
  dsimp only [bitsToNatLSB]
  let e : Fin (k + (ℓ - k)) ≃ Fin ℓ := finCongr (by omega)
  have h_eq : (∑ j : Fin ℓ, if v j then 2 ^ j.1 else 0) =
      ∑ i : Fin (k + (ℓ - k)), if v ⟨i.1, by have := i.isLt; omega⟩ then 2 ^ i.1 else 0 :=
    (Fintype.sum_equiv e (fun i => if v ⟨i.1, by have := i.isLt; omega⟩ then 2 ^ i.1 else 0)
      (fun j => if v j then 2 ^ j.1 else 0) (fun _ => rfl)).symm
  rw [h_eq, Fin.sum_univ_add, Finset.mul_sum]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun i _ => ?_)
  simp only [Fin.val_natAdd]
  rw [pow_add]
  split_ifs <;> ring

lemma bitsToNatLSB_lt_pow_iff {ℓ k : ℕ} (hk : k ≤ ℓ) (v : Qubits ℓ) :
    bitsToNatLSB v < 2 ^ k ↔ ∀ i : Fin (ℓ - k), v ⟨k + i.1, by omega⟩ = false := by
  rw [bitsToNatLSB_split hk v]
  set lo := bitsToNatLSB (fun i : Fin k => v ⟨i.1, by omega⟩)
  set hi := bitsToNatLSB (fun i : Fin (ℓ - k) => v ⟨k + i.1, by omega⟩)
  have hlo : lo < 2 ^ k := bitsToNatLSB_lt k _
  have hhi_iff : hi = 0 ↔ ∀ i : Fin (ℓ - k), v ⟨k + i.1, by omega⟩ = false := by
    dsimp only [hi, bitsToNatLSB]
    rw [Finset.sum_eq_zero_iff]
    constructor
    · intro h i
      have hi0 := h i (Finset.mem_univ _)
      by_contra hne
      have ht : v ⟨k + i.1, by omega⟩ = true := by cases hv : v ⟨k + i.1, by omega⟩ <;> simp_all
      rw [if_pos ht] at hi0
      exact Nat.ne_of_gt (Nat.two_pow_pos i.1) hi0
    · intro h i _
      simp [h i]
  constructor
  · intro hlt
    have hhi0 : hi = 0 := by
      by_contra hne
      have h1 : 1 ≤ hi := Nat.pos_of_ne_zero hne
      have hmul := Nat.mul_le_mul_left (2 ^ k) h1
      omega
    exact hhi_iff.mp hhi0
  · intro hzero
    rw [hhi_iff.mpr hzero, mul_zero, add_zero]
    exact hlo

lemma bitsToNatLSB_eq_prefix_of_lt {ℓ k : ℕ} (hk : k ≤ ℓ) (v : Qubits ℓ)
    (hlt : bitsToNatLSB v < 2 ^ k) :
    bitsToNatLSB v = bitsToNatLSB (fun i : Fin k => v ⟨i.1, by omega⟩) := by
  have htop := (bitsToNatLSB_lt_pow_iff hk v).mp hlt
  rw [bitsToNatLSB_split hk v]
  have hhi0 : bitsToNatLSB (fun i : Fin (ℓ - k) => v ⟨k + i.1, by omega⟩) = 0 := by
    dsimp only [bitsToNatLSB]
    exact Finset.sum_eq_zero fun i _ => by simp [htop i]
  rw [hhi0, mul_zero, add_zero]

def routePos (ℓ h_tree : ℕ) (hle : h_tree ≤ ℓ) (w : Qubits ℓ) (s : ℕ) : ℕ :=
  ∑ i : Fin h_tree, if h_tree - s ≤ i.1 then (if w ⟨i.1, by omega⟩ then 2 ^ i.1 else 0) else 0

lemma routePos_zero (ℓ h_tree : ℕ) (hle : h_tree ≤ ℓ) (w : Qubits ℓ) :
    routePos ℓ h_tree hle w 0 = 0 := by
  dsimp only [routePos]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hi : ¬ h_tree - 0 ≤ i.1 := by have := i.isLt; omega
  rw [if_neg hi]

lemma routePos_h_tree (ℓ h_tree : ℕ) (hle : h_tree ≤ ℓ) (w : Qubits ℓ) :
    routePos ℓ h_tree hle w h_tree = bitsToNatLSB (fun i : Fin h_tree => w ⟨i.1, by omega⟩) := by
  dsimp only [routePos, bitsToNatLSB]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : h_tree - h_tree ≤ i.1 := by omega
  rw [if_pos hi]

lemma routePos_lt (ℓ h_tree : ℕ) (hle : h_tree ≤ ℓ) (w : Qubits ℓ) (s : ℕ) :
    routePos ℓ h_tree hle w s < 2 ^ h_tree := by
  have hle_sum : routePos ℓ h_tree hle w s ≤ bitsToNatLSB (fun i : Fin h_tree => w ⟨i.1, by omega⟩) := by
    dsimp only [routePos, bitsToNatLSB]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hc : h_tree - s ≤ i.1
    · rw [if_pos hc]
    · rw [if_neg hc]; exact Nat.zero_le _
  exact Nat.lt_of_le_of_lt hle_sum (bitsToNatLSB_lt h_tree _)

lemma routePos_dvd (ℓ h_tree : ℕ) (hle : h_tree ≤ ℓ) (w : Qubits ℓ) (s : ℕ) (_hs : s ≤ h_tree) :
    2 ^ (h_tree - s) ∣ routePos ℓ h_tree hle w s := by
  dsimp only [routePos]
  refine Finset.dvd_sum fun i _ => ?_
  split_ifs with h1 h2
  · exact Nat.pow_dvd_pow 2 h1
  · exact dvd_zero _
  · exact dvd_zero _

lemma routePos_succ (ℓ h_tree : ℕ) (hle : h_tree ≤ ℓ) (w : Qubits ℓ) (s : ℕ) (hs : s < h_tree) :
    let j := h_tree - 1 - s
    routePos ℓ h_tree hle w (s + 1) =
      routePos ℓ h_tree hle w s + (if w ⟨j, by omega⟩ then 2 ^ j else 0) := by
  intro j
  have hj : j = h_tree - 1 - s := rfl
  dsimp only [routePos]
  have hsingle : ∀ i : Fin h_tree,
      (if h_tree - (s + 1) ≤ i.1 then (if w ⟨i.1, by omega⟩ then 2 ^ i.1 else 0) else 0) =
      (if h_tree - s ≤ i.1 then (if w ⟨i.1, by omega⟩ then 2 ^ i.1 else 0) else 0) +
      (if i = ⟨j, by omega⟩ then (if w ⟨j, by omega⟩ then 2 ^ j else 0) else 0) := by
    intro i
    by_cases heq : i = ⟨j, by omega⟩
    · subst heq
      have h1 : h_tree - (s + 1) ≤ j := by omega
      have h2 : ¬ h_tree - s ≤ j := by omega
      rw [if_pos h1, if_neg h2, if_pos rfl, zero_add]
    · have hne : i.1 ≠ j := fun h => heq (Fin.ext h)
      have hiff : h_tree - (s + 1) ≤ i.1 ↔ h_tree - s ≤ i.1 := by omega
      rw [if_neg heq, add_zero]
      by_cases h : h_tree - s ≤ i.1
      · rw [if_pos (hiff.mpr h), if_pos h]
      · rw [if_neg (mt hiff.mp h), if_neg h]
  simp only [hsingle, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-! #### Router Main/Ancilla Registers and Wire Layout -/

abbrev routerMain (ℓ q_w : ℕ) : ℕ := ℓ + 1 + q_w

def boolCons {n : ℕ} (b : Bool) (v : Qubits n) : Qubits (1 + n) :=
  fun k => if h : k.1 = 0 then b else v ⟨k.1 - 1, by have := k.isLt; omega⟩

@[simp] lemma boolCons_zero {n : ℕ} (b : Bool) (v : Qubits n) :
    boolCons b v 0 = b := rfl

@[simp] lemma boolCons_natAdd {n : ℕ} (b : Bool) (v : Qubits n) (i : Fin n) :
    boolCons b v (Fin.natAdd 1 i) = v i := by
  dsimp only [boolCons]
  rw [dif_neg (by simp)]
  congr 1; exact Fin.ext (by simp)

lemma boolCons_inj {n : ℕ} (b : Bool) : Function.Injective (boolCons (n := n) b) := by
  intro v₁ v₂ h
  funext i
  have := congrArg (fun f => f (Fin.natAdd 1 i)) h
  simpa using this

def routerAnc (ℓ q_w h_tree anc_leaf : ℕ) : ℕ :=
  ((ℓ - h_tree) + 1) +
  2 ^ h_tree +
  (2 ^ h_tree - 1) * q_w +
  2 ^ h_tree * anc_leaf +
  (2 ^ h_tree - 1) * (1 + q_w)

abbrev routerTotal (ℓ q_w h_tree anc_leaf : ℕ) : ℕ :=
  routerMain ℓ q_w + routerAnc ℓ q_w h_tree anc_leaf

def routerW {ℓ q_w : ℕ} (x : Qubits (routerMain ℓ q_w)) : Qubits ℓ :=
  fun i => x ⟨i.1, by dsimp [routerMain]; omega⟩

def routerFC {ℓ q_w : ℕ} (x : Qubits (routerMain ℓ q_w)) : Bool :=
  x ⟨ℓ, by dsimp [routerMain]; omega⟩

def routerReg {ℓ q_w : ℕ} (x : Qubits (routerMain ℓ q_w)) : Qubits q_w :=
  fun k => x ⟨ℓ + 1 + k.1, by dsimp [routerMain]; have := k.isLt; omega⟩

@[simp] lemma routerW_apply {ℓ q_w : ℕ} (x : Qubits (routerMain ℓ q_w)) (i : Fin ℓ) :
    routerW x i = x ⟨i.1, by dsimp [routerMain]; omega⟩ := rfl

@[simp] lemma routerFC_apply {ℓ q_w : ℕ} (x : Qubits (routerMain ℓ q_w)) :
    routerFC x = x ⟨ℓ, by dsimp [routerMain]; omega⟩ := rfl

@[simp] lemma routerReg_apply {ℓ q_w : ℕ} (x : Qubits (routerMain ℓ q_w)) (k : Fin q_w) :
    routerReg x k = x ⟨ℓ + 1 + k.1, by dsimp [routerMain]; have := k.isLt; omega⟩ := rfl

def packRouterMain {ℓ q_w : ℕ} (w : Qubits ℓ) (fc : Bool) (reg : Qubits q_w) :
    Qubits (routerMain ℓ q_w) :=
  fun i =>
    if h1 : i.1 < ℓ then w ⟨i.1, h1⟩
    else if h2 : i.1 = ℓ then fc
    else reg ⟨i.1 - (ℓ + 1), by dsimp [routerMain] at *; have := i.isLt; omega⟩

@[simp] lemma routerW_packRouterMain {ℓ q_w : ℕ} (w : Qubits ℓ) (fc : Bool) (reg : Qubits q_w) :
    routerW (packRouterMain w fc reg) = w := by
  funext i
  dsimp only [routerW, packRouterMain]
  rw [dif_pos i.isLt]

@[simp] lemma routerFC_packRouterMain {ℓ q_w : ℕ} (w : Qubits ℓ) (fc : Bool) (reg : Qubits q_w) :
    routerFC (packRouterMain w fc reg) = fc := by
  dsimp only [routerFC, packRouterMain]
  rw [dif_neg (by omega), dif_pos rfl]

@[simp] lemma routerReg_packRouterMain {ℓ q_w : ℕ} (w : Qubits ℓ) (fc : Bool) (reg : Qubits q_w) :
    routerReg (packRouterMain w fc reg) = reg := by
  funext k
  dsimp only [routerReg, packRouterMain]
  rw [dif_neg (by omega), dif_neg (by omega)]
  congr 1; exact Fin.ext (by simp)

lemma eq_packRouterMain {ℓ q_w : ℕ} (x : Qubits (routerMain ℓ q_w)) :
    x = packRouterMain (routerW x) (routerFC x) (routerReg x) := by
  funext i
  dsimp only [packRouterMain, routerW, routerFC, routerReg]
  split_ifs with h1 h2
  · rfl
  · congr 1; exact Fin.ext h2
  · congr 1; exact Fin.ext (by simp; have := i.isLt; omega)

private abbrev rEqOff (ℓ q_w : ℕ) : ℕ := routerMain ℓ q_w
private abbrev rActOff (ℓ q_w h_tree : ℕ) : ℕ := rEqOff ℓ q_w + ((ℓ - h_tree) + 1)
private abbrev rSlotOff (ℓ q_w h_tree : ℕ) : ℕ := rActOff ℓ q_w h_tree + 2 ^ h_tree
private abbrev rLeafAncOff (ℓ q_w h_tree : ℕ) : ℕ := rSlotOff ℓ q_w h_tree + (2 ^ h_tree - 1) * q_w
private abbrev rFanOff (ℓ q_w h_tree anc_leaf : ℕ) : ℕ :=
  rLeafAncOff ℓ q_w h_tree + 2 ^ h_tree * anc_leaf

private lemma rFanOff_add (ℓ q_w h_tree anc_leaf : ℕ) :
    rFanOff ℓ q_w h_tree anc_leaf + (2 ^ h_tree - 1) * (1 + q_w) =
      routerTotal ℓ q_w h_tree anc_leaf := by
  simp only [rFanOff, rLeafAncOff, rSlotOff, rActOff, rEqOff, routerTotal, routerAnc]
  omega

private def wRegW (ℓ q_w h_tree anc_leaf : ℕ) (i : Fin ℓ) :
    Fin (routerTotal ℓ q_w h_tree anc_leaf) :=
  ⟨i.1, by dsimp [routerTotal, routerMain]; have := i.isLt; omega⟩

private def wFC (ℓ q_w h_tree anc_leaf : ℕ) :
    Fin (routerTotal ℓ q_w h_tree anc_leaf) :=
  ⟨ℓ, by dsimp [routerTotal, routerMain]; omega⟩

private def wReg (ℓ q_w h_tree anc_leaf : ℕ) (k : Fin q_w) :
    Fin (routerTotal ℓ q_w h_tree anc_leaf) :=
  ⟨ℓ + 1 + k.1, by dsimp [routerTotal, routerMain]; have := k.isLt; omega⟩

private def wAncEq (ℓ q_w h_tree anc_leaf : ℕ) (j : Fin ((ℓ - h_tree) + 1)) :
    Fin (routerTotal ℓ q_w h_tree anc_leaf) :=
  ⟨rEqOff ℓ q_w + j.1, by
    have := j.isLt
    have := Nat.two_pow_pos h_tree
    dsimp [routerTotal, rEqOff, routerAnc]; omega⟩

private def wAct (ℓ q_w h_tree anc_leaf : ℕ) (t : Fin (2 ^ h_tree)) :
    Fin (routerTotal ℓ q_w h_tree anc_leaf) :=
  ⟨rActOff ℓ q_w h_tree + t.1, by
    have := t.isLt
    dsimp [routerTotal, rActOff, rEqOff, routerAnc]; omega⟩

private def wSlot (ℓ q_w h_tree anc_leaf : ℕ) (t : Fin (2 ^ h_tree)) (ht : 1 ≤ t.1)
    (k : Fin q_w) : Fin (routerTotal ℓ q_w h_tree anc_leaf) :=
  ⟨rSlotOff ℓ q_w h_tree + ((t.1 - 1) * q_w + k.1), by
    have hlt := mul_add_lt_mul (show t.1 - 1 < 2 ^ h_tree - 1 by have := t.isLt; omega) k.isLt
    dsimp [routerTotal, rSlotOff, rActOff, rEqOff, routerAnc]
    omega⟩

private def wLeafAnc (ℓ q_w h_tree anc_leaf : ℕ) (t : Fin (2 ^ h_tree)) (a : Fin anc_leaf) :
    Fin (routerTotal ℓ q_w h_tree anc_leaf) :=
  ⟨rLeafAncOff ℓ q_w h_tree + (t.1 * anc_leaf + a.1), by
    have hlt := mul_add_lt_mul t.isLt a.isLt
    dsimp [routerTotal, rLeafAncOff, rSlotOff, rActOff, rEqOff, routerAnc]
    omega⟩

private def wFanCopy (ℓ q_w h_tree anc_leaf : ℕ) (s : Fin h_tree) (p : Fin (2 ^ s.1))
    (k : Fin (1 + q_w)) : Fin (routerTotal ℓ q_w h_tree anc_leaf) :=
  ⟨rFanOff ℓ q_w h_tree anc_leaf + (((2 ^ s.1 - 1) + p.1) * (1 + q_w) + k.1), by
    have hs1 : s.1 + 1 ≤ h_tree := s.isLt
    have hpow : 2 ^ (s.1 + 1) ≤ 2 ^ h_tree := Nat.pow_le_pow_right (by norm_num) hs1
    have h2s : 1 ≤ 2 ^ s.1 := Nat.two_pow_pos s.1
    have hp : p.1 < 2 ^ s.1 := p.isLt
    have hpow' : 2 ^ (s.1 + 1) = 2 ^ s.1 + 2 ^ s.1 := by rw [pow_succ'] ; omega
    have hrow : (2 ^ s.1 - 1) + p.1 < 2 ^ h_tree - 1 := by omega
    have hlt := mul_add_lt_mul hrow k.isLt
    have htot := rFanOff_add ℓ q_w h_tree anc_leaf
    omega⟩

private def wSlotItem (ℓ q_w h_tree anc_leaf : ℕ) (t : Fin (2 ^ h_tree)) (k : Fin (1 + q_w)) :
    Fin (routerTotal ℓ q_w h_tree anc_leaf) :=
  if hk : k.1 = 0 then wAct ℓ q_w h_tree anc_leaf t
  else if ht : t.1 = 0 then wReg ℓ q_w h_tree anc_leaf ⟨k.1 - 1, by have := k.isLt; omega⟩
  else wSlot ℓ q_w h_tree anc_leaf t (by omega) ⟨k.1 - 1, by have := k.isLt; omega⟩

private lemma wRegW_lt (ℓ q_w h_tree anc_leaf : ℕ) (i : Fin ℓ) :
    (wRegW ℓ q_w h_tree anc_leaf i).1 < ℓ := i.isLt

private lemma wFC_val (ℓ q_w h_tree anc_leaf : ℕ) :
    (wFC ℓ q_w h_tree anc_leaf).1 = ℓ := rfl

private lemma wReg_bounds (ℓ q_w h_tree anc_leaf : ℕ) (k : Fin q_w) :
    ℓ + 1 ≤ (wReg ℓ q_w h_tree anc_leaf k).1 ∧
    (wReg ℓ q_w h_tree anc_leaf k).1 < rEqOff ℓ q_w := by
  dsimp [wReg, rEqOff, routerMain]; have := k.isLt; omega

private lemma wAncEq_bounds (ℓ q_w h_tree anc_leaf : ℕ) (j : Fin ((ℓ - h_tree) + 1)) :
    rEqOff ℓ q_w ≤ (wAncEq ℓ q_w h_tree anc_leaf j).1 ∧
    (wAncEq ℓ q_w h_tree anc_leaf j).1 < rActOff ℓ q_w h_tree := by
  dsimp [wAncEq, rActOff]; have := j.isLt; omega

private lemma wAct_bounds (ℓ q_w h_tree anc_leaf : ℕ) (t : Fin (2 ^ h_tree)) :
    rActOff ℓ q_w h_tree ≤ (wAct ℓ q_w h_tree anc_leaf t).1 ∧
    (wAct ℓ q_w h_tree anc_leaf t).1 < rSlotOff ℓ q_w h_tree := by
  dsimp [wAct, rSlotOff]; have := t.isLt; omega

private lemma wSlot_bounds (ℓ q_w h_tree anc_leaf : ℕ) (t : Fin (2 ^ h_tree)) (ht : 1 ≤ t.1)
    (k : Fin q_w) :
    rSlotOff ℓ q_w h_tree ≤ (wSlot ℓ q_w h_tree anc_leaf t ht k).1 ∧
    (wSlot ℓ q_w h_tree anc_leaf t ht k).1 < rLeafAncOff ℓ q_w h_tree := by
  have hlt := mul_add_lt_mul (show t.1 - 1 < 2 ^ h_tree - 1 by have := t.isLt; omega) k.isLt
  dsimp [wSlot, rLeafAncOff]; omega

private lemma wLeafAnc_bounds (ℓ q_w h_tree anc_leaf : ℕ) (t : Fin (2 ^ h_tree))
    (a : Fin anc_leaf) :
    rLeafAncOff ℓ q_w h_tree ≤ (wLeafAnc ℓ q_w h_tree anc_leaf t a).1 ∧
    (wLeafAnc ℓ q_w h_tree anc_leaf t a).1 < rFanOff ℓ q_w h_tree anc_leaf := by
  have hlt := mul_add_lt_mul t.isLt a.isLt
  dsimp [wLeafAnc, rFanOff]; omega

private lemma wFanCopy_ge (ℓ q_w h_tree anc_leaf : ℕ) (s : Fin h_tree) (p : Fin (2 ^ s.1))
    (k : Fin (1 + q_w)) :
    rFanOff ℓ q_w h_tree anc_leaf ≤ (wFanCopy ℓ q_w h_tree anc_leaf s p k).1 := by
  dsimp [wFanCopy]; omega

private lemma chain_offsets (ℓ q_w h_tree anc_leaf : ℕ) :
    ℓ < ℓ + 1 ∧ ℓ + 1 ≤ rEqOff ℓ q_w ∧ rEqOff ℓ q_w < rActOff ℓ q_w h_tree ∧
    rActOff ℓ q_w h_tree < rSlotOff ℓ q_w h_tree ∧
    rSlotOff ℓ q_w h_tree ≤ rLeafAncOff ℓ q_w h_tree ∧
    rLeafAncOff ℓ q_w h_tree ≤ rFanOff ℓ q_w h_tree anc_leaf := by
  have h2 : 1 ≤ 2 ^ h_tree := Nat.two_pow_pos h_tree
  refine ⟨Nat.lt_succ_self ℓ, Nat.le_add_right _ _, ?_, ?_, Nat.le_add_right _ _, Nat.le_add_right _ _⟩
  · change ℓ + 1 + q_w < ℓ + 1 + q_w + ((ℓ - h_tree) + 1); omega
  · change rActOff ℓ q_w h_tree < rActOff ℓ q_w h_tree + 2 ^ h_tree; omega

private lemma wSlotItem_bounds (ℓ q_w h_tree anc_leaf : ℕ) (t : Fin (2 ^ h_tree))
    (k : Fin (1 + q_w)) :
    (ℓ + 1 ≤ (wSlotItem ℓ q_w h_tree anc_leaf t k).1 ∧
     (wSlotItem ℓ q_w h_tree anc_leaf t k).1 < rEqOff ℓ q_w) ∨
    (rActOff ℓ q_w h_tree ≤ (wSlotItem ℓ q_w h_tree anc_leaf t k).1 ∧
     (wSlotItem ℓ q_w h_tree anc_leaf t k).1 < rLeafAncOff ℓ q_w h_tree) := by
  dsimp only [wSlotItem]
  split_ifs with hk ht
  · right
    have hb := wAct_bounds ℓ q_w h_tree anc_leaf t
    have hc := chain_offsets ℓ q_w h_tree anc_leaf
    omega
  · left
    exact wReg_bounds ℓ q_w h_tree anc_leaf ⟨k.1 - 1, by have := k.isLt; omega⟩
  · right
    have hb := wSlot_bounds ℓ q_w h_tree anc_leaf t (by omega) ⟨k.1 - 1, by have := k.isLt; omega⟩
    have hc := chain_offsets ℓ q_w h_tree anc_leaf
    omega

private lemma wSlotItem_inj {ℓ q_w h_tree anc_leaf : ℕ} {t₁ t₂ : Fin (2 ^ h_tree)}
    {k₁ k₂ : Fin (1 + q_w)}
    (h : wSlotItem ℓ q_w h_tree anc_leaf t₁ k₁ = wSlotItem ℓ q_w h_tree anc_leaf t₂ k₂) :
    t₁ = t₂ ∧ k₁ = k₂ := by
  have hval := congrArg Fin.val h
  have hc := chain_offsets ℓ q_w h_tree anc_leaf
  dsimp only [wSlotItem] at hval
  split_ifs at hval with hk1 hk2 ht1 ht2 ht1' ht2'
  · dsimp [wAct] at hval
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · have hb1 := wAct_bounds ℓ q_w h_tree anc_leaf t₁
    have hb2 := wReg_bounds ℓ q_w h_tree anc_leaf ⟨k₂.1 - 1, by have := k₂.isLt; omega⟩
    omega
  · have hb1 := wAct_bounds ℓ q_w h_tree anc_leaf t₁
    have hb2 := wSlot_bounds ℓ q_w h_tree anc_leaf t₂ (by omega) ⟨k₂.1 - 1, by have := k₂.isLt; omega⟩
    omega
  · have hb1 := wReg_bounds ℓ q_w h_tree anc_leaf ⟨k₁.1 - 1, by have := k₁.isLt; omega⟩
    have hb2 := wAct_bounds ℓ q_w h_tree anc_leaf t₂
    omega
  · dsimp [wReg] at hval
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · have hb1 := wReg_bounds ℓ q_w h_tree anc_leaf ⟨k₁.1 - 1, by have := k₁.isLt; omega⟩
    have hb2 := wSlot_bounds ℓ q_w h_tree anc_leaf t₂ (by omega) ⟨k₂.1 - 1, by have := k₂.isLt; omega⟩
    omega
  · have hb1 := wSlot_bounds ℓ q_w h_tree anc_leaf t₁ (by omega) ⟨k₁.1 - 1, by have := k₁.isLt; omega⟩
    have hb2 := wAct_bounds ℓ q_w h_tree anc_leaf t₂
    omega
  · have hb1 := wSlot_bounds ℓ q_w h_tree anc_leaf t₁ (by omega) ⟨k₁.1 - 1, by have := k₁.isLt; omega⟩
    have hb2 := wReg_bounds ℓ q_w h_tree anc_leaf ⟨k₂.1 - 1, by have := k₂.isLt; omega⟩
    omega
  · dsimp [wSlot] at hval
    have hk1' : k₁.1 - 1 < q_w := by have := k₁.isLt; omega
    have hk2' : k₂.1 - 1 < q_w := by have := k₂.isLt; omega
    have hmul : (t₁.1 - 1) * q_w + (k₁.1 - 1) = (t₂.1 - 1) * q_w + (k₂.1 - 1) := by omega
    have heq := eq_of_mul_add_eq hk1' hk2' hmul
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

private lemma wFanCopy_inj {ℓ q_w h_tree anc_leaf : ℕ}
    {s₁ s₂ : Fin h_tree} {p₁ : Fin (2 ^ s₁.1)} {p₂ : Fin (2 ^ s₂.1)}
    {k₁ k₂ : Fin (1 + q_w)}
    (h : wFanCopy ℓ q_w h_tree anc_leaf s₁ p₁ k₁ =
      wFanCopy ℓ q_w h_tree anc_leaf s₂ p₂ k₂) :
    s₁ = s₂ ∧ p₁.1 = p₂.1 ∧ k₁ = k₂ := by
  have hval := congrArg Fin.val h
  dsimp [wFanCopy] at hval
  have hmul : ((2 ^ s₁.1 - 1) + p₁.1) * (1 + q_w) + k₁.1 =
      ((2 ^ s₂.1 - 1) + p₂.1) * (1 + q_w) + k₂.1 := by omega
  have heq := eq_of_mul_add_eq k₁.isLt k₂.isLt hmul
  have hs_eq : s₁ = s₂ := by
    by_contra hne
    have hlt_or : s₁.1 < s₂.1 ∨ s₂.1 < s₁.1 := by
      rcases lt_trichotomy s₁.1 s₂.1 with hlt | heqs | hgt
      · exact Or.inl hlt
      · exact absurd (Fin.ext heqs) hne
      · exact Or.inr hgt
    rcases hlt_or with hlt | hlt
    · have hpow : 2 ^ (s₁.1 + 1) ≤ 2 ^ s₂.1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2s1 : 1 ≤ 2 ^ s₁.1 := Nat.two_pow_pos s₁.1
      have hpow' : 2 ^ (s₁.1 + 1) = 2 ^ s₁.1 + 2 ^ s₁.1 := by rw [pow_succ']; omega
      have hp1 := p₁.isLt
      omega
    · have hpow : 2 ^ (s₂.1 + 1) ≤ 2 ^ s₁.1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2s2 : 1 ≤ 2 ^ s₂.1 := Nat.two_pow_pos s₂.1
      have hpow' : 2 ^ (s₂.1 + 1) = 2 ^ s₂.1 + 2 ^ s₂.1 := by rw [pow_succ']; omega
      have hp2 := p₂.isLt
      omega
  subst hs_eq
  exact ⟨rfl, by omega, Fin.ext (by omega)⟩

private lemma wLeafAnc_inj {ℓ q_w h_tree anc_leaf : ℕ}
    {t₁ t₂ : Fin (2 ^ h_tree)} {a₁ a₂ : Fin anc_leaf}
    (h : wLeafAnc ℓ q_w h_tree anc_leaf t₁ a₁ =
      wLeafAnc ℓ q_w h_tree anc_leaf t₂ a₂) :
    t₁ = t₂ ∧ a₁ = a₂ := by
  have hval := congrArg Fin.val h
  dsimp [wLeafAnc] at hval
  have hmul : t₁.1 * anc_leaf + a₁.1 = t₂.1 * anc_leaf + a₂.1 := by omega
  have heq := eq_of_mul_add_eq a₁.isLt a₂.isLt hmul
  exact ⟨Fin.ext heq.1, Fin.ext heq.2⟩

private lemma wSlotItem_ne_wRegW (ℓ q_w h_tree anc_leaf : ℕ) (t : Fin (2 ^ h_tree))
    (k : Fin (1 + q_w)) (i : Fin ℓ) :
    wSlotItem ℓ q_w h_tree anc_leaf t k ≠ wRegW ℓ q_w h_tree anc_leaf i := by
  intro h; have := congrArg Fin.val h
  have hb := wSlotItem_bounds ℓ q_w h_tree anc_leaf t k
  have hi := wRegW_lt ℓ q_w h_tree anc_leaf i
  have hc := chain_offsets ℓ q_w h_tree anc_leaf
  rcases hb with hb | hb <;> omega

private lemma wSlotItem_ne_wFC (ℓ q_w h_tree anc_leaf : ℕ) (t : Fin (2 ^ h_tree))
    (k : Fin (1 + q_w)) :
    wSlotItem ℓ q_w h_tree anc_leaf t k ≠ wFC ℓ q_w h_tree anc_leaf := by
  intro h; have := congrArg Fin.val h
  have hb := wSlotItem_bounds ℓ q_w h_tree anc_leaf t k
  have hf := wFC_val ℓ q_w h_tree anc_leaf
  have hc := chain_offsets ℓ q_w h_tree anc_leaf
  rcases hb with hb | hb <;> omega

private lemma wSlotItem_ne_wAncEq (ℓ q_w h_tree anc_leaf : ℕ) (t : Fin (2 ^ h_tree))
    (k : Fin (1 + q_w)) (j : Fin ((ℓ - h_tree) + 1)) :
    wSlotItem ℓ q_w h_tree anc_leaf t k ≠ wAncEq ℓ q_w h_tree anc_leaf j := by
  intro h; have := congrArg Fin.val h
  have hb := wSlotItem_bounds ℓ q_w h_tree anc_leaf t k
  have ha := wAncEq_bounds ℓ q_w h_tree anc_leaf j
  rcases hb with hb | hb <;> omega

private lemma wSlotItem_ne_wLeafAnc (ℓ q_w h_tree anc_leaf : ℕ) (t₁ t₂ : Fin (2 ^ h_tree))
    (k : Fin (1 + q_w)) (a : Fin anc_leaf) :
    wSlotItem ℓ q_w h_tree anc_leaf t₁ k ≠ wLeafAnc ℓ q_w h_tree anc_leaf t₂ a := by
  intro h; have := congrArg Fin.val h
  have hb := wSlotItem_bounds ℓ q_w h_tree anc_leaf t₁ k
  have ha := wLeafAnc_bounds ℓ q_w h_tree anc_leaf t₂ a
  have hc := chain_offsets ℓ q_w h_tree anc_leaf
  rcases hb with hb | hb <;> omega

private lemma wSlotItem_ne_wFanCopy (ℓ q_w h_tree anc_leaf : ℕ) (t : Fin (2 ^ h_tree))
    (k : Fin (1 + q_w)) (s : Fin h_tree) (p : Fin (2 ^ s.1)) (k' : Fin (1 + q_w)) :
    wSlotItem ℓ q_w h_tree anc_leaf t k ≠ wFanCopy ℓ q_w h_tree anc_leaf s p k' := by
  intro h; have := congrArg Fin.val h
  have hb := wSlotItem_bounds ℓ q_w h_tree anc_leaf t k
  have hf := wFanCopy_ge ℓ q_w h_tree anc_leaf s p k'
  have hc := chain_offsets ℓ q_w h_tree anc_leaf
  rcases hb with hb | hb <;> omega

/-! #### Step 1: Root Equality & Activity Test (`routerEqRoot`) -/

private def routerEqWire (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ)
    (w : Fin ((ℓ - h_tree) + 1 + 1 + ((ℓ - h_tree) + 1))) :
    Fin (routerTotal ℓ q_w h_tree anc_leaf) :=
  let L := (ℓ - h_tree) + 1
  if h1 : w.1 < ℓ - h_tree then wRegW ℓ q_w h_tree anc_leaf ⟨h_tree + w.1, by omega⟩
  else if h2 : w.1 = ℓ - h_tree then wFC ℓ q_w h_tree anc_leaf
  else if _ : w.1 = L then wAct ℓ q_w h_tree anc_leaf ⟨0, Nat.two_pow_pos h_tree⟩
  else wAncEq ℓ q_w h_tree anc_leaf ⟨w.1 - (L + 1), by have := w.isLt; omega⟩

private def routerEqEmb (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ) :
    Fin ((ℓ - h_tree) + 1 + 1 + ((ℓ - h_tree) + 1)) ↪
      Fin (routerTotal ℓ q_w h_tree anc_leaf) where
  toFun := routerEqWire ℓ q_w h_tree anc_leaf h_le
  inj' a b hab := by
    have ha := a.isLt; have hb := b.isLt
    have hval := congrArg Fin.val hab
    dsimp only [routerEqWire] at hval
    have hc := chain_offsets ℓ q_w h_tree anc_leaf
    split_ifs at hval with ha1 hb1 hb2 hb3 ha2 hb1' hb2' hb3' ha3 hb1'' hb2'' hb3'' hb1''' hb2''' hb3'''
    all_goals
      try simp only [wRegW, wFC, wAct, wAncEq, rEqOff, rActOff, routerMain] at hval
    all_goals
      try exact Fin.ext (by omega)

private lemma routerEqEmb_apply (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ)
    (w : Fin ((ℓ - h_tree) + 1 + 1 + ((ℓ - h_tree) + 1))) :
    routerEqEmb ℓ q_w h_tree anc_leaf h_le w =
      let L := (ℓ - h_tree) + 1
      if h1 : w.1 < ℓ - h_tree then wRegW ℓ q_w h_tree anc_leaf ⟨h_tree + w.1, by omega⟩
      else if h2 : w.1 = ℓ - h_tree then wFC ℓ q_w h_tree anc_leaf
      else if _ : w.1 = L then wAct ℓ q_w h_tree anc_leaf ⟨0, Nat.two_pow_pos h_tree⟩
      else wAncEq ℓ q_w h_tree anc_leaf ⟨w.1 - (L + 1), by have := w.isLt; omega⟩ := rfl

private lemma routerEqEmb_cast_top (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ)
    (i : Fin (ℓ - h_tree)) :
    routerEqEmb ℓ q_w h_tree anc_leaf h_le
        (Fin.castAdd ((ℓ - h_tree) + 1) (Fin.castAdd 1 ⟨i.1, by omega⟩)) =
      wRegW ℓ q_w h_tree anc_leaf ⟨h_tree + i.1, by omega⟩ := by
  rw [routerEqEmb_apply]
  have hi : (Fin.castAdd ((ℓ - h_tree) + 1) (Fin.castAdd 1 (⟨i.1, by omega⟩ : Fin ((ℓ - h_tree) + 1)))).1 <
      ℓ - h_tree := i.isLt
  rw [dif_pos hi]
  rfl

private lemma routerEqEmb_cast_fc (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ) :
    routerEqEmb ℓ q_w h_tree anc_leaf h_le
        (Fin.castAdd ((ℓ - h_tree) + 1) (Fin.castAdd 1 ⟨ℓ - h_tree, by omega⟩)) =
      wFC ℓ q_w h_tree anc_leaf := by
  rw [routerEqEmb_apply]
  have h1 : ¬ (Fin.castAdd ((ℓ - h_tree) + 1) (Fin.castAdd 1 (⟨ℓ - h_tree, by omega⟩ : Fin ((ℓ - h_tree) + 1)))).1 <
      ℓ - h_tree := by simp
  have h2 : (Fin.castAdd ((ℓ - h_tree) + 1) (Fin.castAdd 1 (⟨ℓ - h_tree, by omega⟩ : Fin ((ℓ - h_tree) + 1)))).1 =
      ℓ - h_tree := by simp
  rw [dif_neg h1, dif_pos h2]

private lemma routerEqEmb_tgt (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ) :
    routerEqEmb ℓ q_w h_tree anc_leaf h_le
        (Fin.castAdd ((ℓ - h_tree) + 1) ⟨(ℓ - h_tree) + 1, by omega⟩) =
      wAct ℓ q_w h_tree anc_leaf ⟨0, Nat.two_pow_pos h_tree⟩ := by
  rw [routerEqEmb_apply]
  rw [dif_neg (by simp), dif_neg (by simp), dif_pos (by simp)]

private lemma routerEqEmb_natAdd (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ)
    (j : Fin ((ℓ - h_tree) + 1)) :
    routerEqEmb ℓ q_w h_tree anc_leaf h_le (Fin.natAdd ((ℓ - h_tree) + 1 + 1) j) =
      wAncEq ℓ q_w h_tree anc_leaf j := by
  rw [routerEqEmb_apply]
  rw [dif_neg (by simp; omega), dif_neg (by simp; omega), dif_neg (by simp; omega)]
  congr 1; exact Fin.ext (by simp)

private def routerRootPat (ℓ h_tree : ℕ) : Qubits ((ℓ - h_tree) + 1) :=
  fun i => decide (i.1 = ℓ - h_tree)

private noncomputable def routerEqRoot (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ) :
    LayeredCircuit (routerTotal ℓ q_w h_tree anc_leaf) :=
  (multiEqCtrl1 ((ℓ - h_tree) + 1) (routerRootPat ℓ h_tree) pauliX pauliX_mem_unitaryGroup).mapWires
    (routerEqEmb ℓ q_w h_tree anc_leaf h_le)

private lemma routerEqRoot_size (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ) :
    (routerEqRoot ℓ q_w h_tree anc_leaf h_le).size ≤ 12 * (ℓ + 2) := by
  dsimp only [routerEqRoot]
  rw [LayeredCircuit.mapWires_size]
  have h1 := multiEqCtrl1_size ((ℓ - h_tree) + 1) (routerRootPat ℓ h_tree) pauliX pauliX_mem_unitaryGroup
  omega

private lemma routerEqRoot_depth (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ) :
    (routerEqRoot ℓ q_w h_tree anc_leaf h_le).depth ≤ 10 * Nat.clog 2 (ℓ + 2) + 3 := by
  dsimp only [routerEqRoot]
  rw [LayeredCircuit.mapWires_depth]
  have h1 := multiEqCtrl1_depth ((ℓ - h_tree) + 1) (routerRootPat ℓ h_tree) pauliX pauliX_mem_unitaryGroup
  have hc : Nat.clog 2 ((ℓ - h_tree) + 1 + 1) ≤ Nat.clog 2 (ℓ + 2) :=
    Nat.clog_mono_right 2 (by omega)
  omega

private lemma act_routerEqRoot_ket (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ)
    (w : Qubits ℓ) (fc : Bool) (reg : Qubits q_w) :
    let z := padZero (routerMain ℓ q_w) (routerAnc ℓ q_w h_tree anc_leaf) (packRouterMain w fc reg)
    let actRoot := decide ((∀ i : Fin (ℓ - h_tree), w ⟨h_tree + i.1, by omega⟩ = false) ∧ fc = true)
    act (routerEqRoot ℓ q_w h_tree anc_leaf h_le).unitary (ket z) =
      ket (Function.update z (wAct ℓ q_w h_tree anc_leaf ⟨0, Nat.two_pow_pos h_tree⟩) actRoot) := by
  intro z actRoot
  dsimp only [routerEqRoot]
  let L := (ℓ - h_tree) + 1
  let emb := routerEqEmb ℓ q_w h_tree anc_leaf h_le
  let embMain : Fin (L + 1) ↪ Fin (routerTotal ℓ q_w h_tree anc_leaf) :=
    (Fin.castAddEmb L).trans emb
  have hclean : ∀ j : Fin L, z (emb (Fin.natAdd (L + 1) j)) = false := fun j => by
    have heq : emb (Fin.natAdd (L + 1) j) = wAncEq ℓ q_w h_tree anc_leaf j :=
      routerEqEmb_natAdd ℓ q_w h_tree anc_leaf h_le j
    rw [heq]
    have hnat : wAncEq ℓ q_w h_tree anc_leaf j =
        Fin.natAdd (routerMain ℓ q_w) ⟨j.1, by
          have := Nat.two_pow_pos h_tree; dsimp [routerAnc]; have := j.isLt; omega⟩ :=
      Fin.ext rfl
    rw [hnat]
    exact padZero_natAdd _ _ _ _
  have hact := act_mapWires_implementsOnClean
    (multiEqCtrl1 L (routerRootPat ℓ h_tree) pauliX pauliX_mem_unitaryGroup)
    (eqCtrlMat L (routerRootPat ℓ h_tree) pauliX)
    (multiEqCtrl1_implements L (routerRootPat ℓ h_tree) pauliX pauliX_mem_unitaryGroup)
    emb z hclean
  change act ((multiEqCtrl1 L (routerRootPat ℓ h_tree) pauliX pauliX_mem_unitaryGroup).mapWires emb).unitary
    (ket z) = _
  rw [hact]
  have hz_tgt : (z ∘ embMain) ⟨L, by omega⟩ = false := by
    have heq : embMain ⟨L, by omega⟩ = wAct ℓ q_w h_tree anc_leaf ⟨0, Nat.two_pow_pos h_tree⟩ :=
      routerEqEmb_tgt ℓ q_w h_tree anc_leaf h_le
    change z (embMain ⟨L, by omega⟩) = false
    rw [heq]
    have hnat : wAct ℓ q_w h_tree anc_leaf ⟨0, Nat.two_pow_pos h_tree⟩ =
        Fin.natAdd (routerMain ℓ q_w) ⟨L, by
          have := Nat.two_pow_pos h_tree; dsimp [routerAnc]; omega⟩ :=
      Fin.ext (by dsimp [wAct, rActOff, rEqOff])
    rw [hnat]
    exact padZero_natAdd _ _ _ _
  have hpat_iff : (∀ i : Fin L, (z ∘ embMain) ⟨i.1, by omega⟩ = routerRootPat ℓ h_tree i) ↔
      ((∀ i : Fin (ℓ - h_tree), w ⟨h_tree + i.1, by omega⟩ = false) ∧ fc = true) := by
    constructor
    · intro h
      refine ⟨fun i => ?_, ?_⟩
      · have hi := h ⟨i.1, by dsimp [L]; omega⟩
        change z (embMain ⟨i.1, by omega⟩) = routerRootPat ℓ h_tree ⟨i.1, by omega⟩ at hi
        have heq : embMain ⟨i.1, by omega⟩ = wRegW ℓ q_w h_tree anc_leaf ⟨h_tree + i.1, by omega⟩ :=
          routerEqEmb_cast_top ℓ q_w h_tree anc_leaf h_le i
        rw [heq] at hi
        have hcast : wRegW ℓ q_w h_tree anc_leaf ⟨h_tree + i.1, by omega⟩ =
            Fin.castAdd (routerAnc ℓ q_w h_tree anc_leaf) ⟨h_tree + i.1, by dsimp [routerMain]; omega⟩ := rfl
        dsimp only [z] at hi
        rw [hcast, padZero_castAdd] at hi
        have hw_eq : packRouterMain w fc reg ⟨h_tree + i.1, by dsimp [routerMain]; omega⟩ =
            w ⟨h_tree + i.1, by omega⟩ := by
          change routerW (packRouterMain w fc reg) ⟨h_tree + i.1, by omega⟩ = _
          rw [routerW_packRouterMain]
        rw [hw_eq] at hi
        simpa [routerRootPat, show i.1 ≠ ℓ - h_tree by have := i.isLt; omega] using hi
      · have hfc := h ⟨ℓ - h_tree, by dsimp [L]; omega⟩
        change z (embMain ⟨ℓ - h_tree, by omega⟩) = routerRootPat ℓ h_tree ⟨ℓ - h_tree, by omega⟩ at hfc
        have heq : embMain ⟨ℓ - h_tree, by omega⟩ = wFC ℓ q_w h_tree anc_leaf :=
          routerEqEmb_cast_fc ℓ q_w h_tree anc_leaf h_le
        rw [heq] at hfc
        have hcast : wFC ℓ q_w h_tree anc_leaf =
            Fin.castAdd (routerAnc ℓ q_w h_tree anc_leaf) ⟨ℓ, by dsimp [routerMain]; omega⟩ := rfl
        dsimp only [z] at hfc
        rw [hcast, padZero_castAdd] at hfc
        have hfc_eq : packRouterMain w fc reg ⟨ℓ, by dsimp [routerMain]; omega⟩ = fc :=
          routerFC_packRouterMain w fc reg
        rw [hfc_eq] at hfc
        simpa [routerRootPat] using hfc
    · rintro ⟨hw, rfl⟩ i
      by_cases hi : i.1 < ℓ - h_tree
      · change z (embMain ⟨i.1, by omega⟩) = routerRootPat ℓ h_tree i
        have heq : embMain ⟨i.1, by omega⟩ = wRegW ℓ q_w h_tree anc_leaf ⟨h_tree + i.1, by omega⟩ :=
          routerEqEmb_cast_top ℓ q_w h_tree anc_leaf h_le ⟨i.1, hi⟩
        rw [heq]
        have hcast : wRegW ℓ q_w h_tree anc_leaf ⟨h_tree + i.1, by omega⟩ =
            Fin.castAdd (routerAnc ℓ q_w h_tree anc_leaf) ⟨h_tree + i.1, by dsimp [routerMain]; omega⟩ := rfl
        dsimp only [z]
        rw [hcast, padZero_castAdd]
        have hw_eq : packRouterMain w true reg ⟨h_tree + i.1, by dsimp [routerMain]; omega⟩ =
            w ⟨h_tree + i.1, by omega⟩ := by
          change routerW (packRouterMain w true reg) ⟨h_tree + i.1, by omega⟩ = _
          rw [routerW_packRouterMain]
        rw [hw_eq, hw ⟨i.1, hi⟩]
        simp [routerRootPat, show i.1 ≠ ℓ - h_tree by omega]
      · have hi_eq : i.1 = ℓ - h_tree := by have := i.isLt; dsimp [L] at this; omega
        have hi_fin : (⟨i.1, by omega⟩ : Fin (L + 1)) =
            Fin.castAdd 1 ⟨ℓ - h_tree, by omega⟩ := Fin.ext (by simp [hi_eq])
        change z (embMain ⟨i.1, by omega⟩) = routerRootPat ℓ h_tree i
        rw [hi_fin]
        have heq : embMain (Fin.castAdd 1 ⟨ℓ - h_tree, by omega⟩) = wFC ℓ q_w h_tree anc_leaf :=
          routerEqEmb_cast_fc ℓ q_w h_tree anc_leaf h_le
        rw [heq]
        have hcast : wFC ℓ q_w h_tree anc_leaf =
            Fin.castAdd (routerAnc ℓ q_w h_tree anc_leaf) ⟨ℓ, by dsimp [routerMain]; omega⟩ := rfl
        dsimp only [z]
        rw [hcast, padZero_castAdd]
        have hfc_eq : packRouterMain w true reg ⟨ℓ, by dsimp [routerMain]; omega⟩ = true :=
          routerFC_packRouterMain w true reg
        rw [hfc_eq]
        simp [routerRootPat, hi_eq]
  let y₀ : Qubits (L + 1) := Function.update (z ∘ embMain) ⟨L, by omega⟩ actRoot
  rw [Finset.sum_eq_single y₀]
  · have hy0_eq : eqCtrlMat L (routerRootPat ℓ h_tree) pauliX y₀ (z ∘ embMain) = 1 := by
      simp only [eqCtrlMat, Matrix.of_apply]
      have haddr : ∀ i : Fin L, y₀ ⟨i.1, by omega⟩ = (z ∘ embMain) ⟨i.1, by omega⟩ := fun i => by
        dsimp only [y₀]
        exact Function.update_of_ne (by intro h; have := congrArg Fin.val h; dsimp at this; omega) _ _
      rw [if_pos haddr]
      simp only [y₀, Function.update_self, hz_tgt]
      split_ifs with hpat hfalse
      · have hact_true : actRoot = true := decide_eq_true (hpat_iff.mp hpat)
        rw [hact_true]; simp [pauliX]
      · rfl
      · exact absurd (decide_eq_false (mt hpat_iff.mpr hpat)) hfalse
    rw [hy0_eq, one_smul]
    congr 1
    funext wq
    by_cases hwq : wq = wAct ℓ q_w h_tree anc_leaf ⟨0, Nat.two_pow_pos h_tree⟩
    · subst hwq
      have hmem : wAct ℓ q_w h_tree anc_leaf ⟨0, Nat.two_pow_pos h_tree⟩ = embMain ⟨L, by omega⟩ :=
        (routerEqEmb_tgt ℓ q_w h_tree anc_leaf h_le).symm
      rw [Function.update_self, hmem, updateOn_apply_emb]
      dsimp only [y₀]; rw [Function.update_self]
    · rw [Function.update_of_ne hwq]
      by_cases hmem : wq ∈ Set.range embMain
      · rcases hmem with ⟨i, rfl⟩
        rw [updateOn_apply_emb]
        have hiL : i ≠ ⟨L, by omega⟩ := by
          intro heq; apply hwq; rw [heq]; exact routerEqEmb_tgt ℓ q_w h_tree anc_leaf h_le
        dsimp only [y₀]; rw [Function.update_of_ne hiL]; rfl
      · rw [updateOn_apply_not_mem _ _ _ hmem]
  · intro y _ hy
    have hent0 : eqCtrlMat L (routerRootPat ℓ h_tree) pauliX y (z ∘ embMain) = 0 := by
      simp only [eqCtrlMat, Matrix.of_apply]
      split_ifs with haddr hpat hy_eq
      · have hact_true : actRoot = true := decide_eq_true (hpat_iff.mp hpat)
        have hyl : y ⟨L, by omega⟩ ≠ actRoot := by
          intro hyl_eq
          apply hy
          funext i
          by_cases hi : i.1 < L
          · dsimp only [y₀]
            rw [Function.update_of_ne (by
              intro h; have h1 := congrArg Fin.val h; change i.1 = L at h1; omega)]
            exact haddr ⟨i.1, hi⟩
          · have hiL : i = ⟨L, by omega⟩ := Fin.ext (show i.1 = L by have := i.isLt; omega)
            rw [hiL]
            dsimp only [y₀]
            rw [Function.update_self, hyl_eq]
        rw [hact_true] at hyl
        rw [hz_tgt]
        have hyf : y ⟨L, by omega⟩ = false := by cases hy' : y ⟨L, by omega⟩ <;> simp_all
        rw [hyf]; simp [pauliX]
      · have hact_false : actRoot = false := decide_eq_false (mt hpat_iff.mpr hpat)
        have hyl : y ⟨L, by omega⟩ ≠ actRoot := by
          intro hyl_eq
          apply hy
          funext i
          by_cases hi : i.1 < L
          · dsimp only [y₀]
            rw [Function.update_of_ne (by
              intro h; have h1 := congrArg Fin.val h; change i.1 = L at h1; omega)]
            exact haddr ⟨i.1, hi⟩
          · have hiL : i = ⟨L, by omega⟩ := Fin.ext (show i.1 = L by have := i.isLt; omega)
            rw [hiL]
            dsimp only [y₀]
            rw [Function.update_self, hyl_eq]
        rw [hact_false] at hyl
        rw [hz_tgt] at hy_eq
        exact absurd hy_eq hyl
      · rfl
      · rfl
    rw [hent0, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! #### Step 2: Parallel Pre-Fanout of All `h_tree` Address Bits (`routerPreFanout`) -/

private def routerFanWire (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ) (s : Fin h_tree)
    (w : Fin (1 + 2 ^ s.1 * (1 + q_w))) : Fin (routerTotal ℓ q_w h_tree anc_leaf) :=
  if _ : w.1 = 0 then
    wRegW ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - s.1, by omega⟩
  else
    let idx := w.1 - 1
    let p : Fin (2 ^ s.1) := ⟨idx / (1 + q_w), div_lt_of_lt_mul' (by have := w.isLt; omega)⟩
    let k : Fin (1 + q_w) := ⟨idx % (1 + q_w), Nat.mod_lt _ (by omega)⟩
    wFanCopy ℓ q_w h_tree anc_leaf s p k

private def routerFanEmb (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ) (s : Fin h_tree) :
    Fin (1 + 2 ^ s.1 * (1 + q_w)) ↪ Fin (routerTotal ℓ q_w h_tree anc_leaf) where
  toFun := routerFanWire ℓ q_w h_tree anc_leaf h_le s
  inj' a b hab := by
    have ha := a.isLt; have hb := b.isLt
    have hval := congrArg Fin.val hab
    have hc := chain_offsets ℓ q_w h_tree anc_leaf
    dsimp only [routerFanWire] at hval
    by_cases ha0 : a.1 = 0 <;> by_cases hb0 : b.1 = 0
    · exact Fin.ext (by omega)
    · exfalso
      rw [dif_pos ha0, dif_neg hb0] at hval
      have hb_ge := wFanCopy_ge ℓ q_w h_tree anc_leaf s
        ⟨(b.1 - 1) / (1 + q_w), div_lt_of_lt_mul' (by omega)⟩
        ⟨(b.1 - 1) % (1 + q_w), Nat.mod_lt _ (by omega)⟩
      have ha_lt := wRegW_lt ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - s.1, by omega⟩
      omega
    · exfalso
      rw [dif_neg ha0, dif_pos hb0] at hval
      have ha_ge := wFanCopy_ge ℓ q_w h_tree anc_leaf s
        ⟨(a.1 - 1) / (1 + q_w), div_lt_of_lt_mul' (by omega)⟩
        ⟨(a.1 - 1) % (1 + q_w), Nat.mod_lt _ (by omega)⟩
      have hb_lt := wRegW_lt ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - s.1, by omega⟩
      omega
    · rw [dif_neg ha0, dif_neg hb0] at hval
      have heq : wFanCopy ℓ q_w h_tree anc_leaf s
          ⟨(a.1 - 1) / (1 + q_w), div_lt_of_lt_mul' (by omega)⟩
          ⟨(a.1 - 1) % (1 + q_w), Nat.mod_lt _ (by omega)⟩ =
          wFanCopy ℓ q_w h_tree anc_leaf s
          ⟨(b.1 - 1) / (1 + q_w), div_lt_of_lt_mul' (by omega)⟩
          ⟨(b.1 - 1) % (1 + q_w), Nat.mod_lt _ (by omega)⟩ := Fin.ext hval
      rcases wFanCopy_inj heq with ⟨_, hp, hk⟩
      have hk' : (a.1 - 1) % (1 + q_w) = (b.1 - 1) % (1 + q_w) :=
        @congrArg (Fin (1 + q_w)) ℕ _ _ Fin.val hk
      have had := Nat.div_add_mod (a.1 - 1) (1 + q_w)
      have hbd := Nat.div_add_mod (b.1 - 1) (1 + q_w)
      dsimp only at hp
      rw [hp, hk'] at had
      exact Fin.ext (by omega)

private lemma routerFanEmb_apply (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ) (s : Fin h_tree)
    (w : Fin (1 + 2 ^ s.1 * (1 + q_w))) :
    routerFanEmb ℓ q_w h_tree anc_leaf h_le s w =
      if _ : w.1 = 0 then
        wRegW ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - s.1, by omega⟩
      else
        wFanCopy ℓ q_w h_tree anc_leaf s
          ⟨(w.1 - 1) / (1 + q_w), div_lt_of_lt_mul' (by have := w.isLt; omega)⟩
          ⟨(w.1 - 1) % (1 + q_w), Nat.mod_lt _ (by omega)⟩ := rfl

private lemma routerFanEmb_zero (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ) (s : Fin h_tree) :
    routerFanEmb ℓ q_w h_tree anc_leaf h_le s 0 =
      wRegW ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - s.1, by omega⟩ := by
  have h0 : (0 : Fin (1 + 2 ^ s.1 * (1 + q_w))).1 = 0 := rfl
  rw [routerFanEmb_apply, dif_pos h0]

private lemma routerFanEmb_natAdd (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ) (s : Fin h_tree)
    (idx : Fin (2 ^ s.1 * (1 + q_w))) :
    routerFanEmb ℓ q_w h_tree anc_leaf h_le s (Fin.natAdd 1 idx) =
      wFanCopy ℓ q_w h_tree anc_leaf s
        ⟨idx.1 / (1 + q_w), div_lt_of_lt_mul' idx.isLt⟩
        ⟨idx.1 % (1 + q_w), Nat.mod_lt _ (by omega)⟩ := by
  rw [routerFanEmb_apply, dif_neg (by simp)]
  congr 1 <;> exact Fin.ext (by simp)

private def routerFanSet (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ) (s : Fin h_tree) :
    Finset (Fin (routerTotal ℓ q_w h_tree anc_leaf)) :=
  Finset.univ.image (routerFanEmb ℓ q_w h_tree anc_leaf h_le s)

private lemma routerFanSet_disjoint (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ)
    (s₁ s₂ : Fin h_tree) (hs : s₁ ≠ s₂) :
    Disjoint (routerFanSet ℓ q_w h_tree anc_leaf h_le s₁)
      (routerFanSet ℓ q_w h_tree anc_leaf h_le s₂) := by
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  simp only [routerFanSet, Finset.mem_image, Finset.mem_univ, true_and] at hw1 hw2
  rcases hw1 with ⟨a, rfl⟩
  rcases hw2 with ⟨b, hb⟩
  have hval := congrArg Fin.val hb
  have hc := chain_offsets ℓ q_w h_tree anc_leaf
  rw [routerFanEmb_apply, routerFanEmb_apply] at hval
  split_ifs at hval with hb0 ha0 ha0'
  · dsimp [wRegW] at hval
    have : s₁.1 = s₂.1 := by have := s₁.isLt; have := s₂.isLt; omega
    exact hs (Fin.ext this)
  · have hlt := wRegW_lt ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - s₂.1, by omega⟩
    have hge := wFanCopy_ge ℓ q_w h_tree anc_leaf s₁
      ⟨(a.1 - 1) / (1 + q_w), div_lt_of_lt_mul' (by have := a.isLt; omega)⟩
      ⟨(a.1 - 1) % (1 + q_w), Nat.mod_lt _ (by omega)⟩
    omega
  · have hge := wFanCopy_ge ℓ q_w h_tree anc_leaf s₂
      ⟨(b.1 - 1) / (1 + q_w), div_lt_of_lt_mul' (by have := b.isLt; omega)⟩
      ⟨(b.1 - 1) % (1 + q_w), Nat.mod_lt _ (by omega)⟩
    have hlt := wRegW_lt ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - s₁.1, by omega⟩
    omega
  · have heq : wFanCopy ℓ q_w h_tree anc_leaf s₁ _ _ =
        wFanCopy ℓ q_w h_tree anc_leaf s₂ _ _ := Fin.ext hval.symm
    exact hs (wFanCopy_inj heq).1

private def routerPreFanout (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ) :
    LayeredCircuit (routerTotal ℓ q_w h_tree anc_leaf) :=
  (parMergeFin
    (fun s : Fin h_tree =>
      (fanoutCircuit (2 ^ s.1 * (1 + q_w))).mapWires (routerFanEmb ℓ q_w h_tree anc_leaf h_le s))
    (routerFanSet ℓ q_w h_tree anc_leaf h_le)
    (fun s => (LayeredCircuit.mapWires_usesOnly _ _ (fanoutCircuit_usesOnly _)).mono
      (by intro w hw; simpa [routerFanSet] using hw))
    (routerFanSet_disjoint ℓ q_w h_tree anc_leaf h_le)).1

private lemma routerPreFanout_size (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ) :
    (routerPreFanout ℓ q_w h_tree anc_leaf h_le).size = (2 ^ h_tree - 1) * (1 + q_w) := by
  dsimp only [routerPreFanout]
  rw [(parMergeFin _ _ _ _).2.2.1]
  have hterm : ∀ s : Fin h_tree,
      ((fanoutCircuit (2 ^ s.1 * (1 + q_w))).mapWires
        (routerFanEmb ℓ q_w h_tree anc_leaf h_le s)).size = 2 ^ s.1 * (1 + q_w) := fun s => by
    rw [LayeredCircuit.mapWires_size, fanoutCircuit_size]
  simp_rw [hterm]
  rw [← Finset.sum_mul, sum_fin_two_pow]

private lemma routerPreFanout_depth (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ) :
    (routerPreFanout ℓ q_w h_tree anc_leaf h_le).depth ≤ h_tree + Nat.clog 2 (q_w + 1) := by
  dsimp only [routerPreFanout]
  refine (parMergeFin _ _ _ _).2.2.2 _ fun s => ?_
  rw [LayeredCircuit.mapWires_depth]
  have hf := fanoutCircuit_depth (2 ^ s.1 * (1 + q_w))
  have hclog : Nat.clog 2 (2 ^ s.1 * (1 + q_w)) ≤ s.1 + Nat.clog 2 (q_w + 1) := by
    rw [Nat.clog_le_iff_le_pow (by norm_num : 1 < 2), pow_add, Nat.add_comm 1 q_w]
    exact Nat.mul_le_mul_left _ (Nat.le_pow_clog (by norm_num : 1 < 2) (q_w + 1))
  have hs1 : s.1 + 1 ≤ h_tree := s.isLt
  omega

private lemma routerPreFanout_usesOnly (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ) :
    (routerPreFanout ℓ q_w h_tree anc_leaf h_le).UsesOnly
      (Finset.univ.biUnion (routerFanSet ℓ q_w h_tree anc_leaf h_le)) :=
  (parMergeFin _ _ _ _).2.1

private lemma act_routerPreFanout_ket (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ)
    (z : Qubits (routerTotal ℓ q_w h_tree anc_leaf))
    (hclean : ∀ (s : Fin h_tree) (p : Fin (2 ^ s.1)) (k : Fin (1 + q_w)),
      z (wFanCopy ℓ q_w h_tree anc_leaf s p k) = false) :
    act (routerPreFanout ℓ q_w h_tree anc_leaf h_le).unitary (ket z) =
      ket (fun wq =>
        if h : ∃ (s : Fin h_tree) (p : Fin (2 ^ s.1)) (k : Fin (1 + q_w)),
            wFanCopy ℓ q_w h_tree anc_leaf s p k = wq then
          z (wRegW ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - (Classical.choose h).1, by omega⟩)
        else z wq) := by
  classical
  dsimp only [routerPreFanout]
  let z_next : Qubits (routerTotal ℓ q_w h_tree anc_leaf) := fun wq =>
    if h : ∃ (s : Fin h_tree) (p : Fin (2 ^ s.1)) (k : Fin (1 + q_w)),
        wFanCopy ℓ q_w h_tree anc_leaf s p k = wq then
      z (wRegW ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - (Classical.choose h).1, by omega⟩)
    else z wq
  have hact_each : ∀ s : Fin h_tree, ∃ x' : Qubits (routerTotal ℓ q_w h_tree anc_leaf),
      act ((fanoutCircuit (2 ^ s.1 * (1 + q_w))).mapWires
        (routerFanEmb ℓ q_w h_tree anc_leaf h_le s)).unitary (ket z) = ket x' ∧
      ∀ wq ∈ routerFanSet ℓ q_w h_tree anc_leaf h_le s, x' wq = z_next wq := by
    intro s
    let emb := routerFanEmb ℓ q_w h_tree anc_leaf h_le s
    let bitW := wRegW ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - s.1, by omega⟩
    let x' : Qubits (routerTotal ℓ q_w h_tree anc_leaf) := fun wq =>
      if wq ∈ routerFanSet ℓ q_w h_tree anc_leaf h_le s then z bitW else z wq
    have hfan_act : act (fanoutCircuit (2 ^ s.1 * (1 + q_w))).unitary (ket (z ∘ emb)) =
        ket (fun _ => z bitW) := by
      refine act_fanoutCircuit_ket (2 ^ s.1 * (1 + q_w)) (z bitW) (z ∘ emb) ?_ ?_
      · change z (emb 0) = z bitW
        rw [routerFanEmb_zero]
      · intro idx
        change z (emb (Fin.natAdd 1 idx)) = false
        rw [routerFanEmb_natAdd]
        exact hclean s _ _
    have hmap_act : act ((fanoutCircuit (2 ^ s.1 * (1 + q_w))).mapWires emb).unitary (ket z) =
        ket x' := by
      refine act_mapWires_ket _ emb z _ hfan_act x' ?_ ?_
      · funext i
        change x' (emb i) = z bitW
        dsimp only [x']
        rw [if_pos (by simp [routerFanSet, emb])]
      · intro i hi
        dsimp only [x']
        rw [if_neg (by simpa [routerFanSet] using hi)]
    refine ⟨x', hmap_act, fun wq hwq => ?_⟩
    dsimp only [x']
    rw [if_pos hwq]
    simp only [routerFanSet, Finset.mem_image, Finset.mem_univ, true_and] at hwq
    rcases hwq with ⟨a, rfl⟩
    by_cases ha0 : a.1 = 0
    · have ha : a = 0 := Fin.ext ha0
      subst ha
      rw [routerFanEmb_zero]
      have hnot : ¬ ∃ (s' : Fin h_tree) (p' : Fin (2 ^ s'.1)) (k' : Fin (1 + q_w)),
          wFanCopy ℓ q_w h_tree anc_leaf s' p' k' = bitW := by
        rintro ⟨s', p', k', h⟩
        have hlt := wRegW_lt ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - s.1, by omega⟩
        have hge := wFanCopy_ge ℓ q_w h_tree anc_leaf s' p' k'
        have hc := chain_offsets ℓ q_w h_tree anc_leaf
        have := congrArg Fin.val h
        omega
      dsimp only [z_next]
      rw [dif_neg hnot]
    · let p₀ : Fin (2 ^ s.1) :=
        ⟨(a.1 - 1) / (1 + q_w), div_lt_of_lt_mul' (by have := a.isLt; omega)⟩
      let k₀ : Fin (1 + q_w) := ⟨(a.1 - 1) % (1 + q_w), Nat.mod_lt _ (by omega)⟩
      have hemb_eq : emb a = wFanCopy ℓ q_w h_tree anc_leaf s p₀ k₀ := by
        dsimp only [emb]; rw [routerFanEmb_apply, dif_neg ha0]
      have hex : ∃ (s' : Fin h_tree) (p' : Fin (2 ^ s'.1)) (k' : Fin (1 + q_w)),
          wFanCopy ℓ q_w h_tree anc_leaf s' p' k' = emb a := ⟨s, p₀, k₀, hemb_eq.symm⟩
      dsimp only [z_next]
      rw [dif_pos hex]
      rcases Classical.choose_spec hex with ⟨p', k', hspec⟩
      have hs_eq : Classical.choose hex = s :=
        (wFanCopy_inj (hspec.trans hemb_eq)).1
      have hreg_eq : wRegW ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - (Classical.choose hex).1, by omega⟩ =
          bitW := by
        congr 1; exact Fin.ext (by simp [hs_eq])
      rw [hreg_eq]
  rw [act_parMergeFin_ket _ _ _ _ z z_next hact_each]
  congr 1
  funext wq
  by_cases hmem : wq ∈ Finset.univ.biUnion (routerFanSet ℓ q_w h_tree anc_leaf h_le)
  · rw [if_pos hmem]
  · rw [if_neg hmem]
    have hnot : ¬ ∃ (s : Fin h_tree) (p : Fin (2 ^ s.1)) (k : Fin (1 + q_w)),
        wFanCopy ℓ q_w h_tree anc_leaf s p k = wq := by
      rintro ⟨s, p, k, rfl⟩
      apply hmem
      rw [Finset.mem_biUnion]
      refine ⟨s, Finset.mem_univ _, ?_⟩
      simp only [routerFanSet, Finset.mem_image, Finset.mem_univ, true_and]
      let idx : Fin (2 ^ s.1 * (1 + q_w)) :=
        ⟨p.1 * (1 + q_w) + k.1, mul_add_lt_mul p.isLt k.isLt⟩
      refine ⟨Fin.natAdd 1 idx, ?_⟩
      rw [routerFanEmb_natAdd]
      have hdiv : idx.1 / (1 + q_w) = p.1 :=
        mul_add_div_right p.1 k.1 (1 + q_w) (by omega) k.isLt
      have hmod : idx.1 % (1 + q_w) = k.1 :=
        mul_add_mod_right p.1 k.1 (1 + q_w) k.isLt
      congr 1
      · exact Fin.ext hdiv
      · exact Fin.ext hmod
    rw [dif_neg hnot]

/-! #### Step 3: `h_tree`-Level Constant-Depth Fredkin Routing Tree (`routerTree`) -/

private lemma routerTree_node_lt {h_tree : ℕ} (s : Fin h_tree) (p : Fin (2 ^ s.1)) :
    let j := h_tree - 1 - s.1
    p.1 * 2 ^ (j + 1) + 2 ^ j < 2 ^ h_tree := by
  intro j
  have h1 : p.1 + 1 ≤ 2 ^ s.1 := p.isLt
  have h2j : 2 ^ j < 2 ^ (j + 1) := by rw [pow_succ']; have := Nat.two_pow_pos j; omega
  have hexp : s.1 + (j + 1) = h_tree := by dsimp [j]; have := s.isLt; omega
  calc p.1 * 2 ^ (j + 1) + 2 ^ j
      < (p.1 + 1) * 2 ^ (j + 1) := by rw [Nat.add_mul, one_mul]; exact Nat.add_lt_add_left h2j _
    _ ≤ 2 ^ s.1 * 2 ^ (j + 1) := Nat.mul_le_mul_right _ h1
    _ = 2 ^ h_tree := by rw [← pow_add, hexp]

private lemma routerTree_nodeL_lt {h_tree : ℕ} (s : Fin h_tree) (p : Fin (2 ^ s.1)) :
    let j := h_tree - 1 - s.1
    p.1 * 2 ^ (j + 1) < 2 ^ h_tree :=
  Nat.lt_trans (Nat.lt_add_of_pos_right (Nat.two_pow_pos _)) (routerTree_node_lt s p)

private lemma routerTree_slot_disjoint_pair {h_tree : ℕ} (s : Fin h_tree)
    (p₁ p₂ : Fin (2 ^ s.1)) (r₁ r₂ : ℕ)
    (hr1 : r₁ < 2 ^ (h_tree - 1 - s.1 + 1)) (hr2 : r₂ < 2 ^ (h_tree - 1 - s.1 + 1))
    (heq : p₁.1 * 2 ^ (h_tree - 1 - s.1 + 1) + r₁ =
      p₂.1 * 2 ^ (h_tree - 1 - s.1 + 1) + r₂) :
    p₁ = p₂ ∧ r₁ = r₂ := by
  rcases eq_of_mul_add_eq hr1 hr2 heq with ⟨hp, hr⟩
  exact ⟨Fin.ext hp, hr⟩

private def routerTreeP {q_w : ℕ} {s_val : ℕ} (idx : Fin (2 ^ s_val * (1 + q_w))) : Fin (2 ^ s_val) :=
  ⟨idx.1 / (1 + q_w), div_lt_of_lt_mul' idx.isLt⟩

private def routerTreeK {q_w : ℕ} {s_val : ℕ} (idx : Fin (2 ^ s_val * (1 + q_w))) : Fin (1 + q_w) :=
  ⟨idx.1 % (1 + q_w), Nat.mod_lt _ (by omega)⟩

private def routerTreeTL {h_tree q_w : ℕ} (s : Fin h_tree) (idx : Fin (2 ^ s.1 * (1 + q_w))) :
    Fin (2 ^ h_tree) :=
  ⟨(routerTreeP idx).1 * 2 ^ (h_tree - 1 - s.1 + 1), routerTree_nodeL_lt s (routerTreeP idx)⟩

private def routerTreeTR {h_tree q_w : ℕ} (s : Fin h_tree) (idx : Fin (2 ^ s.1 * (1 + q_w))) :
    Fin (2 ^ h_tree) :=
  ⟨(routerTreeP idx).1 * 2 ^ (h_tree - 1 - s.1 + 1) + 2 ^ (h_tree - 1 - s.1),
    routerTree_node_lt s (routerTreeP idx)⟩

private def routerTreeCtrl (ℓ q_w h_tree anc_leaf : ℕ) (s : Fin h_tree)
    (idx : Fin (2 ^ s.1 * (1 + q_w))) : Fin (routerTotal ℓ q_w h_tree anc_leaf) :=
  wFanCopy ℓ q_w h_tree anc_leaf s (routerTreeP idx) (routerTreeK idx)

private def routerTreeLeft (ℓ q_w h_tree anc_leaf : ℕ) (s : Fin h_tree)
    (idx : Fin (2 ^ s.1 * (1 + q_w))) : Fin (routerTotal ℓ q_w h_tree anc_leaf) :=
  wSlotItem ℓ q_w h_tree anc_leaf (routerTreeTL s idx) (routerTreeK idx)

private def routerTreeRight (ℓ q_w h_tree anc_leaf : ℕ) (s : Fin h_tree)
    (idx : Fin (2 ^ s.1 * (1 + q_w))) : Fin (routerTotal ℓ q_w h_tree anc_leaf) :=
  wSlotItem ℓ q_w h_tree anc_leaf (routerTreeTR s idx) (routerTreeK idx)

private lemma routerTree_ca (ℓ q_w h_tree anc_leaf : ℕ) (s : Fin h_tree)
    (idx : Fin (2 ^ s.1 * (1 + q_w))) :
    routerTreeCtrl ℓ q_w h_tree anc_leaf s idx ≠ routerTreeLeft ℓ q_w h_tree anc_leaf s idx :=
  (wSlotItem_ne_wFanCopy _ _ _ _ _ _ _ _ _).symm

private lemma routerTree_cb (ℓ q_w h_tree anc_leaf : ℕ) (s : Fin h_tree)
    (idx : Fin (2 ^ s.1 * (1 + q_w))) :
    routerTreeCtrl ℓ q_w h_tree anc_leaf s idx ≠ routerTreeRight ℓ q_w h_tree anc_leaf s idx :=
  (wSlotItem_ne_wFanCopy _ _ _ _ _ _ _ _ _).symm

private lemma routerTree_ab (ℓ q_w h_tree anc_leaf : ℕ) (s : Fin h_tree)
    (idx : Fin (2 ^ s.1 * (1 + q_w))) :
    routerTreeLeft ℓ q_w h_tree anc_leaf s idx ≠ routerTreeRight ℓ q_w h_tree anc_leaf s idx := by
  intro h
  have ht := (wSlotItem_inj h).1
  have hval := @congrArg (Fin (2 ^ h_tree)) ℕ _ _ Fin.val ht
  have hpos : 0 < 2 ^ (h_tree - 1 - s.1) := Nat.two_pow_pos _
  dsimp [routerTreeTL, routerTreeTR] at hval
  omega

private noncomputable def routerTreeGate (ℓ q_w h_tree anc_leaf : ℕ) (s : Fin h_tree)
    (idx : Fin (2 ^ s.1 * (1 + q_w))) : LayeredCircuit (routerTotal ℓ q_w h_tree anc_leaf) :=
  cswapOn (routerTreeCtrl ℓ q_w h_tree anc_leaf s idx)
    (routerTreeLeft ℓ q_w h_tree anc_leaf s idx)
    (routerTreeRight ℓ q_w h_tree anc_leaf s idx)
    (routerTree_ca ℓ q_w h_tree anc_leaf s idx)
    (routerTree_cb ℓ q_w h_tree anc_leaf s idx)
    (routerTree_ab ℓ q_w h_tree anc_leaf s idx)

private def routerTreeSet (ℓ q_w h_tree anc_leaf : ℕ) (s : Fin h_tree)
    (idx : Fin (2 ^ s.1 * (1 + q_w))) : Finset (Fin (routerTotal ℓ q_w h_tree anc_leaf)) :=
  {routerTreeCtrl ℓ q_w h_tree anc_leaf s idx,
   routerTreeLeft ℓ q_w h_tree anc_leaf s idx,
   routerTreeRight ℓ q_w h_tree anc_leaf s idx}

private lemma routerTreeGate_usesOnly (ℓ q_w h_tree anc_leaf : ℕ) (s : Fin h_tree)
    (idx : Fin (2 ^ s.1 * (1 + q_w))) :
    (routerTreeGate ℓ q_w h_tree anc_leaf s idx).UsesOnly (routerTreeSet ℓ q_w h_tree anc_leaf s idx) :=
  cswapOn_usesOnly _ _ _ _ _ _

private lemma routerTreeSet_disjoint (ℓ q_w h_tree anc_leaf : ℕ) (s : Fin h_tree)
    (i₁ i₂ : Fin (2 ^ s.1 * (1 + q_w))) (hne : i₁ ≠ i₂) :
    Disjoint (routerTreeSet ℓ q_w h_tree anc_leaf s i₁)
      (routerTreeSet ℓ q_w h_tree anc_leaf s i₂) := by
  let j := h_tree - 1 - s.1
  let p₁ := routerTreeP i₁
  let k₁ := routerTreeK i₁
  let p₂ := routerTreeP i₂
  let k₂ := routerTreeK i₂
  have hp_or_k : p₁ ≠ p₂ ∨ k₁ ≠ k₂ := by
    by_contra h
    push Not at h
    apply hne
    have h1 := Nat.div_add_mod i₁.1 (1 + q_w)
    have h2 := Nat.div_add_mod i₂.1 (1 + q_w)
    have hpv : p₁.1 = p₂.1 := @congrArg (Fin (2 ^ s.1)) ℕ _ _ Fin.val h.1
    have hkv : k₁.1 = k₂.1 := @congrArg (Fin (1 + q_w)) ℕ _ _ Fin.val h.2
    dsimp [p₁, p₂, k₁, k₂, routerTreeP, routerTreeK] at hpv hkv
    rw [hpv, hkv] at h1
    exact Fin.ext (by omega)
  have h2j_lt : 2 ^ j < 2 ^ (j + 1) := by rw [pow_succ']; have := Nat.two_pow_pos j; omega
  have h0_lt : 0 < 2 ^ (j + 1) := Nat.two_pow_pos _
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  simp only [routerTreeSet, Finset.mem_insert, Finset.mem_singleton] at hw1 hw2
  rcases hw1 with rfl | rfl | rfl <;> rcases hw2 with heq | heq | heq
  · rcases wFanCopy_inj heq with ⟨_, hp, hk⟩
    rcases hp_or_k with h | h
    · exact h (Fin.ext hp)
    · exact h hk
  · exact (wSlotItem_ne_wFanCopy _ _ _ _ _ _ _ _ _).symm heq
  · exact (wSlotItem_ne_wFanCopy _ _ _ _ _ _ _ _ _).symm heq
  · exact wSlotItem_ne_wFanCopy _ _ _ _ _ _ _ _ _ heq
  · rcases wSlotItem_inj heq with ⟨ht, hk⟩
    have ht_val := @congrArg (Fin (2 ^ h_tree)) ℕ _ _ Fin.val ht
    have hpr := routerTree_slot_disjoint_pair s p₁ p₂ 0 0 h0_lt h0_lt (by simpa [j, routerTreeTL] using ht_val)
    rcases hp_or_k with h | h
    · exact h hpr.1
    · exact h hk
  · rcases wSlotItem_inj heq with ⟨ht, _⟩
    have ht_val := @congrArg (Fin (2 ^ h_tree)) ℕ _ _ Fin.val ht
    have hpr := routerTree_slot_disjoint_pair s p₁ p₂ 0 (2 ^ j) h0_lt h2j_lt
      (by simpa [j, routerTreeTL, routerTreeTR] using ht_val)
    exact Nat.ne_of_lt (Nat.two_pow_pos j) hpr.2
  · exact wSlotItem_ne_wFanCopy _ _ _ _ _ _ _ _ _ heq
  · rcases wSlotItem_inj heq with ⟨ht, _⟩
    have ht_val := @congrArg (Fin (2 ^ h_tree)) ℕ _ _ Fin.val ht
    have hpr := routerTree_slot_disjoint_pair s p₁ p₂ (2 ^ j) 0 h2j_lt h0_lt
      (by simpa [j, routerTreeTL, routerTreeTR] using ht_val)
    exact Nat.ne_of_gt (Nat.two_pow_pos j) hpr.2
  · rcases wSlotItem_inj heq with ⟨ht, hk⟩
    have ht_val := @congrArg (Fin (2 ^ h_tree)) ℕ _ _ Fin.val ht
    have hpr := routerTree_slot_disjoint_pair s p₁ p₂ (2 ^ j) (2 ^ j) h2j_lt h2j_lt
      (by simpa [j, routerTreeTR] using ht_val)
    rcases hp_or_k with h | h
    · exact h hpr.1
    · exact h hk

private noncomputable def routerTreeLevel (ℓ q_w h_tree anc_leaf : ℕ) (s : Fin h_tree) :
    LayeredCircuit (routerTotal ℓ q_w h_tree anc_leaf) :=
  (parMergeFin
    (routerTreeGate ℓ q_w h_tree anc_leaf s)
    (routerTreeSet ℓ q_w h_tree anc_leaf s)
    (routerTreeGate_usesOnly ℓ q_w h_tree anc_leaf s)
    (routerTreeSet_disjoint ℓ q_w h_tree anc_leaf s)).1

private lemma routerTreeLevel_size (ℓ q_w h_tree anc_leaf : ℕ) (s : Fin h_tree) :
    (routerTreeLevel ℓ q_w h_tree anc_leaf s).size = 7 * (2 ^ s.1 * (1 + q_w)) := by
  dsimp only [routerTreeLevel]
  rw [(parMergeFin _ _ _ _).2.2.1]
  have hterm : ∀ idx : Fin (2 ^ s.1 * (1 + q_w)),
      (routerTreeGate ℓ q_w h_tree anc_leaf s idx).size = 7 := fun _ => cswapOn_size _ _ _ _ _ _
  simp_rw [hterm]
  simp [Finset.sum_const, smul_eq_mul, mul_comm]

private lemma routerTreeLevel_depth (ℓ q_w h_tree anc_leaf : ℕ) (s : Fin h_tree) :
    (routerTreeLevel ℓ q_w h_tree anc_leaf s).depth ≤ 7 := by
  dsimp only [routerTreeLevel]
  exact (parMergeFin _ _ _ _).2.2.2 7 fun _ => le_of_eq (cswapOn_depth _ _ _ _ _ _)

private lemma act_routerTreeLevel_ket (ℓ q_w h_tree anc_leaf : ℕ) (s : Fin h_tree)
    (z : Qubits (routerTotal ℓ q_w h_tree anc_leaf))
    (bitVal : Bool) (p_cur : Fin (2 ^ s.1)) (data : Qubits (1 + q_w))
    (hfan : ∀ (p : Fin (2 ^ s.1)) (k : Fin (1 + q_w)),
      z (wFanCopy ℓ q_w h_tree anc_leaf s p k) = bitVal)
    (hslot : ∀ (t : Fin (2 ^ h_tree)) (k : Fin (1 + q_w)),
      z (wSlotItem ℓ q_w h_tree anc_leaf t k) =
        if t.1 = p_cur.1 * 2 ^ (h_tree - 1 - s.1 + 1) then data k else false) :
    let j := h_tree - 1 - s.1
    let t_next := p_cur.1 * 2 ^ (j + 1) + (if bitVal then 2 ^ j else 0)
    act (routerTreeLevel ℓ q_w h_tree anc_leaf s).unitary (ket z) =
      ket (fun wq =>
        if h : ∃ (t : Fin (2 ^ h_tree)) (k : Fin (1 + q_w)),
            wSlotItem ℓ q_w h_tree anc_leaf t k = wq then
          if (Classical.choose h).1 = t_next then
            data (Classical.choose (Classical.choose_spec h))
          else false
        else z wq) := by
  classical
  intro j t_next
  let z_next : Qubits (routerTotal ℓ q_w h_tree anc_leaf) := fun wq =>
    if h : ∃ (t : Fin (2 ^ h_tree)) (k : Fin (1 + q_w)),
        wSlotItem ℓ q_w h_tree anc_leaf t k = wq then
      if (Classical.choose h).1 = t_next then
        data (Classical.choose (Classical.choose_spec h))
      else false
    else z wq
  have hz_next_slot : ∀ (t : Fin (2 ^ h_tree)) (k : Fin (1 + q_w)),
      z_next (wSlotItem ℓ q_w h_tree anc_leaf t k) = if t.1 = t_next then data k else false := by
    intro t k
    have hex : ∃ (t' : Fin (2 ^ h_tree)) (k' : Fin (1 + q_w)),
        wSlotItem ℓ q_w h_tree anc_leaf t' k' = wSlotItem ℓ q_w h_tree anc_leaf t k := ⟨t, k, rfl⟩
    dsimp only [z_next]
    rw [dif_pos hex]
    have heq := wSlotItem_inj (Classical.choose_spec (Classical.choose_spec hex))
    have heq1 : (Classical.choose hex).1 = t.1 := @congrArg (Fin (2 ^ h_tree)) ℕ _ _ Fin.val heq.1
    rw [heq.2, heq1]
  have hact_each : ∀ idx : Fin (2 ^ s.1 * (1 + q_w)),
      ∃ x' : Qubits (routerTotal ℓ q_w h_tree anc_leaf),
        act (routerTreeGate ℓ q_w h_tree anc_leaf s idx).unitary (ket z) = ket x' ∧
        ∀ wq ∈ routerTreeSet ℓ q_w h_tree anc_leaf s idx, x' wq = z_next wq := by
    intro idx
    dsimp only [routerTreeGate]
    refine ⟨_, act_cswapOn_ket _ _ _ _ _ _ z, fun wq hwq => ?_⟩
    set p := routerTreeP idx
    set k := routerTreeK idx
    set tL := routerTreeTL s idx
    set tR := routerTreeTR s idx
    set c := routerTreeCtrl ℓ q_w h_tree anc_leaf s idx
    set a := routerTreeLeft ℓ q_w h_tree anc_leaf s idx
    set b := routerTreeRight ℓ q_w h_tree anc_leaf s idx
    have hzc : z c = bitVal := hfan p k
    have hza : z a = if tL.1 = p_cur.1 * 2 ^ (j + 1) then data k else false := hslot tL k
    have hzb : z b = if tR.1 = p_cur.1 * 2 ^ (j + 1) then data k else false := hslot tR k
    have h2j_lt : 2 ^ j < 2 ^ (j + 1) := by rw [pow_succ']; have := Nat.two_pow_pos j; omega
    have h0_lt : 0 < 2 ^ (j + 1) := Nat.two_pow_pos _
    have htb_ne : tR.1 ≠ p_cur.1 * 2 ^ (j + 1) := by
      intro heq
      have hpr := routerTree_slot_disjoint_pair s p p_cur (2 ^ j) 0 h2j_lt h0_lt (by simpa [tR, j, routerTreeTR] using heq)
      exact Nat.ne_of_gt (Nat.two_pow_pos j) hpr.2
    rw [if_neg htb_ne] at hzb
    have hca : c ≠ a := routerTree_ca ℓ q_w h_tree anc_leaf s idx
    have hcb : c ≠ b := routerTree_cb ℓ q_w h_tree anc_leaf s idx
    have hab : a ≠ b := routerTree_ab ℓ q_w h_tree anc_leaf s idx
    simp only [routerTreeSet, Finset.mem_insert, Finset.mem_singleton] at hwq
    rcases hwq with rfl | rfl | rfl
    · have hnot_c : ¬ ∃ (t' : Fin (2 ^ h_tree)) (k' : Fin (1 + q_w)),
          wSlotItem ℓ q_w h_tree anc_leaf t' k' = c := by
        rintro ⟨t', k', h⟩; exact wSlotItem_ne_wFanCopy _ _ _ _ t' k' s p k h
      dsimp only [z_next]
      rw [dif_neg hnot_c]
      cases hbv : bitVal
      · rw [if_neg (by rw [hzc, hbv]; decide)]
      · rw [if_pos (by rw [hzc, hbv]), if_neg hca, if_neg hcb]
    · change (if z c = true then (if a = a then z b else if a = b then z a else z a) else z a) = z_next a
      have hnsL : z_next a = if tL.1 = t_next then data k else false := hz_next_slot tL k
      rw [hnsL]
      by_cases hp : p = p_cur
      · have hpv : (routerTreeP idx).1 = p_cur.1 := congrArg Fin.val hp
        have htL_eq : tL.1 = p_cur.1 * 2 ^ (j + 1) := by dsimp [tL, routerTreeTL, j]; rw [hpv]
        rw [if_pos htL_eq] at hza
        cases hbv : bitVal
        · have ht_next_eq : t_next = p_cur.1 * 2 ^ (j + 1) := by simp [t_next, hbv]
          rw [if_neg (by rw [hzc, hbv]; decide), if_pos (by rw [htL_eq, ht_next_eq]), hza]
        · have ht_next_eq : t_next = p_cur.1 * 2 ^ (j + 1) + 2 ^ j := by simp [t_next, hbv]
          have hne_L : tL.1 ≠ t_next := by
            rw [htL_eq, ht_next_eq]; have := Nat.two_pow_pos j; omega
          rw [if_pos (by rw [hzc, hbv]), if_pos rfl, if_neg hne_L, hzb]
      · have htL_ne1 : tL.1 ≠ p_cur.1 * 2 ^ (j + 1) := by
          intro heq
          have hpr := routerTree_slot_disjoint_pair s p p_cur 0 0 h0_lt h0_lt (by simpa [tL, j, routerTreeTL] using heq)
          exact hp hpr.1
        have htL_ne2 : tL.1 ≠ t_next := by
          intro heq
          cases hbv : bitVal
          · simp [t_next, hbv] at heq; exact htL_ne1 heq
          · simp [t_next, hbv] at heq
            have hpr := routerTree_slot_disjoint_pair s p p_cur 0 (2 ^ j) h0_lt h2j_lt (by simpa [tL, j, routerTreeTL] using heq)
            exact Nat.ne_of_lt (Nat.two_pow_pos j) hpr.2
        rw [if_neg htL_ne1] at hza
        rw [if_neg htL_ne2]
        cases hbv : bitVal
        · rw [if_neg (by rw [hzc, hbv]; decide), hza]
        · rw [if_pos (by rw [hzc, hbv]), if_pos rfl, hzb]
    · change (if z c = true then (if b = a then z b else if b = b then z a else z b) else z b) = z_next b
      have hnsR : z_next b = if tR.1 = t_next then data k else false := hz_next_slot tR k
      rw [hnsR]
      by_cases hp : p = p_cur
      · have hpv : (routerTreeP idx).1 = p_cur.1 := congrArg Fin.val hp
        have htL_eq : tL.1 = p_cur.1 * 2 ^ (j + 1) := by dsimp [tL, routerTreeTL, j]; rw [hpv]
        have htR_eq : tR.1 = p_cur.1 * 2 ^ (j + 1) + 2 ^ j := by dsimp [tR, routerTreeTR, j]; rw [hpv]
        rw [if_pos htL_eq] at hza
        cases hbv : bitVal
        · have ht_next_eq : t_next = p_cur.1 * 2 ^ (j + 1) := by simp [t_next, hbv]
          have hne_R : tR.1 ≠ t_next := by
            rw [htR_eq, ht_next_eq]; have := Nat.two_pow_pos j; omega
          rw [if_neg (by rw [hzc, hbv]; decide), if_neg hne_R, hzb]
        · have ht_next_eq : t_next = p_cur.1 * 2 ^ (j + 1) + 2 ^ j := by simp [t_next, hbv]
          rw [if_pos (by rw [hzc, hbv]), if_neg hab.symm, if_pos rfl, if_pos (by rw [htR_eq, ht_next_eq]), hza]
      · have htL_ne1 : tL.1 ≠ p_cur.1 * 2 ^ (j + 1) := by
          intro heq
          have hpr := routerTree_slot_disjoint_pair s p p_cur 0 0 h0_lt h0_lt (by simpa [tL, j, routerTreeTL] using heq)
          exact hp hpr.1
        have htR_ne2 : tR.1 ≠ t_next := by
          intro heq
          cases hbv : bitVal
          · simp [t_next, hbv] at heq; exact htb_ne heq
          · simp [t_next, hbv] at heq
            have hpr := routerTree_slot_disjoint_pair s p p_cur (2 ^ j) (2 ^ j) h2j_lt h2j_lt
              (by simpa [tR, j, routerTreeTR] using heq)
            exact hp hpr.1
        rw [if_neg htL_ne1] at hza
        rw [if_neg htR_ne2]
        cases hbv : bitVal
        · rw [if_neg (by rw [hzc, hbv]; decide), hzb]
        · rw [if_pos (by rw [hzc, hbv]), if_neg hab.symm, if_pos rfl, hza]
  dsimp only [routerTreeLevel]
  rw [act_parMergeFin_ket _ _ _ _ z z_next hact_each]
  congr 1
  funext wq
  by_cases hmem : wq ∈ Finset.univ.biUnion (routerTreeSet ℓ q_w h_tree anc_leaf s)
  · rw [if_pos hmem]
  · rw [if_neg hmem]
    by_cases hslot_wq : ∃ (t : Fin (2 ^ h_tree)) (k : Fin (1 + q_w)),
        wSlotItem ℓ q_w h_tree anc_leaf t k = wq
    · rcases hslot_wq with ⟨t, k, rfl⟩
      have hns := hz_next_slot t k
      dsimp only [z_next] at hns
      rw [hns, hslot t k]
      have hne_cur : t.1 ≠ p_cur.1 * 2 ^ (j + 1) := by
        intro heq
        apply hmem
        rw [Finset.mem_biUnion]
        let idx : Fin (2 ^ s.1 * (1 + q_w)) :=
          ⟨p_cur.1 * (1 + q_w) + k.1, mul_add_lt_mul p_cur.isLt k.isLt⟩
        refine ⟨idx, Finset.mem_univ _, ?_⟩
        simp only [routerTreeSet, Finset.mem_insert, Finset.mem_singleton]
        right; left
        have hdiv : (routerTreeP idx).1 = p_cur.1 :=
          mul_add_div_right p_cur.1 k.1 (1 + q_w) (by omega) k.isLt
        have hmod : routerTreeK idx = k :=
          Fin.ext (mul_add_mod_right p_cur.1 k.1 (1 + q_w) k.isLt)
        change wSlotItem ℓ q_w h_tree anc_leaf t k =
          wSlotItem ℓ q_w h_tree anc_leaf (routerTreeTL s idx) (routerTreeK idx)
        rw [hmod]
        congr 1; exact Fin.ext (by dsimp [routerTreeTL, j]; rw [hdiv]; exact heq)
      have hne_next : t.1 ≠ t_next := by
        intro heq
        apply hmem
        rw [Finset.mem_biUnion]
        let idx : Fin (2 ^ s.1 * (1 + q_w)) :=
          ⟨p_cur.1 * (1 + q_w) + k.1, mul_add_lt_mul p_cur.isLt k.isLt⟩
        refine ⟨idx, Finset.mem_univ _, ?_⟩
        simp only [routerTreeSet, Finset.mem_insert, Finset.mem_singleton]
        have hdiv : (routerTreeP idx).1 = p_cur.1 :=
          mul_add_div_right p_cur.1 k.1 (1 + q_w) (by omega) k.isLt
        have hmod : routerTreeK idx = k :=
          Fin.ext (mul_add_mod_right p_cur.1 k.1 (1 + q_w) k.isLt)
        cases hbv : bitVal
        · right; left
          simp [t_next, hbv] at heq
          change wSlotItem ℓ q_w h_tree anc_leaf t k =
            wSlotItem ℓ q_w h_tree anc_leaf (routerTreeTL s idx) (routerTreeK idx)
          rw [hmod]
          congr 1; exact Fin.ext (by dsimp [routerTreeTL, j]; rw [hdiv]; exact heq)
        · right; right
          simp [t_next, hbv] at heq
          change wSlotItem ℓ q_w h_tree anc_leaf t k =
            wSlotItem ℓ q_w h_tree anc_leaf (routerTreeTR s idx) (routerTreeK idx)
          rw [hmod]
          congr 1; exact Fin.ext (by dsimp [routerTreeTR, j]; rw [hdiv]; exact heq)
      rw [if_neg hne_next, if_neg hne_cur]
    · rw [dif_neg hslot_wq]

private noncomputable def routerTreePrefix (ℓ q_w h_tree anc_leaf : ℕ) :
    (k : ℕ) → k ≤ h_tree → LayeredCircuit (routerTotal ℓ q_w h_tree anc_leaf)
  | 0, _ => LayeredCircuit.id _
  | k + 1, hk => (routerTreePrefix ℓ q_w h_tree anc_leaf k (by omega)).seq
      (routerTreeLevel ℓ q_w h_tree anc_leaf ⟨k, hk⟩)

private noncomputable def routerTree (ℓ q_w h_tree anc_leaf : ℕ) :
    LayeredCircuit (routerTotal ℓ q_w h_tree anc_leaf) :=
  routerTreePrefix ℓ q_w h_tree anc_leaf h_tree le_rfl

private lemma routerTreePrefix_size (ℓ q_w h_tree anc_leaf k : ℕ) (hk : k ≤ h_tree) :
    (routerTreePrefix ℓ q_w h_tree anc_leaf k hk).size = 7 * (2 ^ k - 1) * (1 + q_w) := by
  induction k with
  | zero => simp [routerTreePrefix]
  | succ k ih =>
    simp only [routerTreePrefix, LayeredCircuit.seq_size, ih (by omega), routerTreeLevel_size]
    have h1 : 1 ≤ 2 ^ k := Nat.two_pow_pos k
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ']; omega
    rw [hpow]
    calc 7 * (2 ^ k - 1) * (1 + q_w) + 7 * (2 ^ k * (1 + q_w))
        = 7 * ((2 ^ k - 1) + 2 ^ k) * (1 + q_w) := by ring
      _ = 7 * (2 ^ k + 2 ^ k - 1) * (1 + q_w) := by congr 2; omega

private lemma routerTree_size (ℓ q_w h_tree anc_leaf : ℕ) :
    (routerTree ℓ q_w h_tree anc_leaf).size = 7 * (2 ^ h_tree - 1) * (1 + q_w) :=
  routerTreePrefix_size ℓ q_w h_tree anc_leaf h_tree le_rfl

private lemma routerTreePrefix_depth (ℓ q_w h_tree anc_leaf k : ℕ) (hk : k ≤ h_tree) :
    (routerTreePrefix ℓ q_w h_tree anc_leaf k hk).depth ≤ 7 * k := by
  induction k with
  | zero => simp [routerTreePrefix]
  | succ k ih =>
    simp only [routerTreePrefix, LayeredCircuit.seq_depth]
    have h1 := ih (by omega)
    have h2 := routerTreeLevel_depth ℓ q_w h_tree anc_leaf ⟨k, hk⟩
    omega

private lemma routerTree_depth (ℓ q_w h_tree anc_leaf : ℕ) :
    (routerTree ℓ q_w h_tree anc_leaf).depth ≤ 7 * h_tree :=
  routerTreePrefix_depth ℓ q_w h_tree anc_leaf h_tree le_rfl

private lemma act_routerTreePrefix_ket (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ)
    (w : Qubits ℓ) (data : Qubits (1 + q_w))
    (z : Qubits (routerTotal ℓ q_w h_tree anc_leaf))
    (hfan : ∀ (s : Fin h_tree) (p : Fin (2 ^ s.1)) (k : Fin (1 + q_w)),
      z (wFanCopy ℓ q_w h_tree anc_leaf s p k) = w ⟨h_tree - 1 - s.1, by omega⟩)
    (hslot0 : ∀ (t : Fin (2 ^ h_tree)) (k : Fin (1 + q_w)),
      z (wSlotItem ℓ q_w h_tree anc_leaf t k) = if t.1 = 0 then data k else false)
    (m : ℕ) (hm : m ≤ h_tree) :
    act (routerTreePrefix ℓ q_w h_tree anc_leaf m hm).unitary (ket z) =
      ket (fun wq =>
        if h : ∃ (t : Fin (2 ^ h_tree)) (k : Fin (1 + q_w)),
            wSlotItem ℓ q_w h_tree anc_leaf t k = wq then
          if (Classical.choose h).1 = routePos ℓ h_tree h_le w m then
            data (Classical.choose (Classical.choose_spec h))
          else false
        else z wq) := by
  classical
  induction m with
  | zero =>
    simp only [routerTreePrefix, LayeredCircuit.id_unitary, act_one]
    congr 1
    funext wq
    by_cases h : ∃ (t : Fin (2 ^ h_tree)) (k : Fin (1 + q_w)),
        wSlotItem ℓ q_w h_tree anc_leaf t k = wq
    · rw [dif_pos h]
      rcases h with ⟨t, k, rfl⟩
      have hex : ∃ (t' : Fin (2 ^ h_tree)) (k' : Fin (1 + q_w)),
          wSlotItem ℓ q_w h_tree anc_leaf t' k' = wSlotItem ℓ q_w h_tree anc_leaf t k := ⟨t, k, rfl⟩
      have heq := wSlotItem_inj (Classical.choose_spec (Classical.choose_spec hex))
      have heq1 : (Classical.choose hex).1 = t.1 := @congrArg (Fin (2 ^ h_tree)) ℕ _ _ Fin.val heq.1
      rw [hslot0 t k, routePos_zero]
      by_cases ht : t.1 = 0
      · rw [if_pos ht, if_pos (heq1.trans ht), heq.2]
      · rw [if_neg ht, if_neg (by rw [heq1]; exact ht)]
    · rw [dif_neg h]
  | succ m ih =>
    simp only [routerTreePrefix, LayeredCircuit.seq_unitary, act_mul, ih (by omega)]
    let s : Fin h_tree := ⟨m, hm⟩
    let j := h_tree - 1 - m
    let curPos := routePos ℓ h_tree h_le w m
    have hdvd : 2 ^ (j + 1) ∣ curPos := by
      have hj1 : j + 1 = h_tree - m := by omega
      rw [hj1]
      exact routePos_dvd ℓ h_tree h_le w m (by omega)
    have hlt_cur : curPos < 2 ^ h_tree := routePos_lt ℓ h_tree h_le w m
    have hdiv_lt : curPos / 2 ^ (j + 1) < 2 ^ m := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
      have hexp : m + (j + 1) = h_tree := by omega
      rwa [hexp]
    let p_cur : Fin (2 ^ s.1) := ⟨curPos / 2 ^ (j + 1), hdiv_lt⟩
    have hp_mul : p_cur.1 * 2 ^ (j + 1) = curPos :=
      Nat.div_mul_cancel hdvd
    let z_m : Qubits (routerTotal ℓ q_w h_tree anc_leaf) := fun wq =>
      if h : ∃ (t : Fin (2 ^ h_tree)) (k : Fin (1 + q_w)),
          wSlotItem ℓ q_w h_tree anc_leaf t k = wq then
        if (Classical.choose h).1 = curPos then
          data (Classical.choose (Classical.choose_spec h))
        else false
      else z wq
    have hzm_fan : ∀ (p : Fin (2 ^ s.1)) (k : Fin (1 + q_w)),
        z_m (wFanCopy ℓ q_w h_tree anc_leaf s p k) = w ⟨j, by omega⟩ := by
      intro p k
      have hnot : ¬ ∃ (t : Fin (2 ^ h_tree)) (k' : Fin (1 + q_w)),
          wSlotItem ℓ q_w h_tree anc_leaf t k' = wFanCopy ℓ q_w h_tree anc_leaf s p k := by
        rintro ⟨t, k', h⟩; exact wSlotItem_ne_wFanCopy _ _ _ _ t k' s p k h
      dsimp only [z_m]
      rw [dif_neg hnot]
      exact hfan s p k
    have hzm_slot : ∀ (t : Fin (2 ^ h_tree)) (k : Fin (1 + q_w)),
        z_m (wSlotItem ℓ q_w h_tree anc_leaf t k) =
          if t.1 = p_cur.1 * 2 ^ (h_tree - 1 - s.1 + 1) then data k else false := by
      intro t k
      have hex : ∃ (t' : Fin (2 ^ h_tree)) (k' : Fin (1 + q_w)),
          wSlotItem ℓ q_w h_tree anc_leaf t' k' = wSlotItem ℓ q_w h_tree anc_leaf t k := ⟨t, k, rfl⟩
      dsimp only [z_m]
      rw [dif_pos hex]
      have heq := wSlotItem_inj (Classical.choose_spec (Classical.choose_spec hex))
      have heq1 : (Classical.choose hex).1 = t.1 := @congrArg (Fin (2 ^ h_tree)) ℕ _ _ Fin.val heq.1
      rw [heq.2, heq1]
      have hpm : p_cur.1 * 2 ^ (h_tree - 1 - s.1 + 1) = curPos := hp_mul
      rw [hpm]
    rw [act_routerTreeLevel_ket ℓ q_w h_tree anc_leaf s z_m (w ⟨j, by omega⟩) p_cur data
      hzm_fan hzm_slot]
    have hpos_succ : p_cur.1 * 2 ^ (j + 1) + (if w ⟨j, by omega⟩ then 2 ^ j else 0) =
        routePos ℓ h_tree h_le w (m + 1) := by
      rw [hp_mul]
      exact (routePos_succ ℓ h_tree h_le w m hm).symm
    congr 1
    funext wq
    by_cases hslot : ∃ (t : Fin (2 ^ h_tree)) (k : Fin (1 + q_w)),
        wSlotItem ℓ q_w h_tree anc_leaf t k = wq
    · rw [dif_pos hslot, dif_pos hslot, hpos_succ]
    · rw [dif_neg hslot, dif_neg hslot]
      dsimp only [z_m]
      rw [dif_neg hslot]

/-! #### Combined Forward Routing (`routeFwd`), Parallel Leaves, and `coherentRouter` -/

private noncomputable def fwdState (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ)
    (w : Qubits ℓ) (fc : Bool) (reg : Qubits q_w) :
    Qubits (routerTotal ℓ q_w h_tree anc_leaf) := fun wq =>
  let actRoot := decide ((∀ i : Fin (ℓ - h_tree), w ⟨h_tree + i.1, by omega⟩ = false) ∧ fc = true)
  let data : Qubits (1 + q_w) := boolCons actRoot reg
  if hslot : ∃ (t : Fin (2 ^ h_tree)) (k : Fin (1 + q_w)),
      wSlotItem ℓ q_w h_tree anc_leaf t k = wq then
    if (Classical.choose hslot).1 = routePos ℓ h_tree h_le w h_tree then
      data (Classical.choose (Classical.choose_spec hslot))
    else false
  else if hfan : ∃ (s : Fin h_tree) (p : Fin (2 ^ s.1)) (k : Fin (1 + q_w)),
      wFanCopy ℓ q_w h_tree anc_leaf s p k = wq then
    w ⟨h_tree - 1 - (Classical.choose hfan).1, by omega⟩
  else
    padZero (routerMain ℓ q_w) (routerAnc ℓ q_w h_tree anc_leaf) (packRouterMain w fc reg) wq

private lemma fwdState_slot (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ)
    (w : Qubits ℓ) (fc : Bool) (reg : Qubits q_w)
    (t : Fin (2 ^ h_tree)) (k : Fin (1 + q_w)) :
    fwdState ℓ q_w h_tree anc_leaf h_le w fc reg (wSlotItem ℓ q_w h_tree anc_leaf t k) =
      if t.1 = routePos ℓ h_tree h_le w h_tree then
        boolCons (decide ((∀ i : Fin (ℓ - h_tree), w ⟨h_tree + i.1, by omega⟩ = false) ∧ fc = true)) reg k
      else false := by
  classical
  have hex : ∃ (t' : Fin (2 ^ h_tree)) (k' : Fin (1 + q_w)),
      wSlotItem ℓ q_w h_tree anc_leaf t' k' = wSlotItem ℓ q_w h_tree anc_leaf t k := ⟨t, k, rfl⟩
  dsimp only [fwdState]
  rw [dif_pos hex]
  have heq := wSlotItem_inj (Classical.choose_spec (Classical.choose_spec hex))
  have heq1 : (Classical.choose hex).1 = t.1 := @congrArg (Fin (2 ^ h_tree)) ℕ _ _ Fin.val heq.1
  rw [heq.2, heq1]

private lemma fwdState_leafAnc (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ)
    (w : Qubits ℓ) (fc : Bool) (reg : Qubits q_w)
    (t : Fin (2 ^ h_tree)) (a : Fin anc_leaf) :
    fwdState ℓ q_w h_tree anc_leaf h_le w fc reg (wLeafAnc ℓ q_w h_tree anc_leaf t a) = false := by
  classical
  have h1 : ¬ ∃ (t' : Fin (2 ^ h_tree)) (k : Fin (1 + q_w)),
      wSlotItem ℓ q_w h_tree anc_leaf t' k = wLeafAnc ℓ q_w h_tree anc_leaf t a := by
    rintro ⟨t', k, h⟩; exact wSlotItem_ne_wLeafAnc _ _ _ _ t' t k a h
  have h2 : ¬ ∃ (s : Fin h_tree) (p : Fin (2 ^ s.1)) (k : Fin (1 + q_w)),
      wFanCopy ℓ q_w h_tree anc_leaf s p k = wLeafAnc ℓ q_w h_tree anc_leaf t a := by
    rintro ⟨s, p, k, h⟩
    have := congrArg Fin.val h
    have ha := wLeafAnc_bounds ℓ q_w h_tree anc_leaf t a
    have hf := wFanCopy_ge ℓ q_w h_tree anc_leaf s p k
    omega
  dsimp only [fwdState]
  rw [dif_neg h1, dif_neg h2]
  have hnat : wLeafAnc ℓ q_w h_tree anc_leaf t a =
      Fin.natAdd (routerMain ℓ q_w)
        ⟨((ℓ - h_tree) + 1) + 2 ^ h_tree + (2 ^ h_tree - 1) * q_w + (t.1 * anc_leaf + a.1), by
          have hlt := mul_add_lt_mul t.isLt a.isLt
          have := Nat.two_pow_pos h_tree
          dsimp [routerAnc]; omega⟩ := by
    ext; dsimp [wLeafAnc, rLeafAncOff, rSlotOff, rActOff, rEqOff]; omega
  rw [hnat, padZero_natAdd]

private noncomputable def routeFwd (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ) :
    LayeredCircuit (routerTotal ℓ q_w h_tree anc_leaf) :=
  (routerEqRoot ℓ q_w h_tree anc_leaf h_le).seq
    ((routerPreFanout ℓ q_w h_tree anc_leaf h_le).seq
      (routerTree ℓ q_w h_tree anc_leaf))

private lemma routeFwd_size (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ) :
    (routeFwd ℓ q_w h_tree anc_leaf h_le).size ≤
      12 * (ℓ + 2) + 8 * (2 ^ h_tree - 1) * (1 + q_w) := by
  dsimp only [routeFwd]
  simp only [LayeredCircuit.seq_size, routerPreFanout_size, routerTree_size]
  have h1 := routerEqRoot_size ℓ q_w h_tree anc_leaf h_le
  have hsum : (2 ^ h_tree - 1) * (1 + q_w) + 7 * (2 ^ h_tree - 1) * (1 + q_w) =
      8 * (2 ^ h_tree - 1) * (1 + q_w) := by ring
  omega

private lemma routeFwd_depth (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ) :
    (routeFwd ℓ q_w h_tree anc_leaf h_le).depth ≤
      10 * Nat.clog 2 (ℓ + 2) + 8 * h_tree + Nat.clog 2 (q_w + 1) + 3 := by
  dsimp only [routeFwd]
  simp only [LayeredCircuit.seq_depth]
  have h1 := routerEqRoot_depth ℓ q_w h_tree anc_leaf h_le
  have h2 := routerPreFanout_depth ℓ q_w h_tree anc_leaf h_le
  have h3 := routerTree_depth ℓ q_w h_tree anc_leaf
  omega

private lemma act_routeFwd_ket (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ)
    (w : Qubits ℓ) (fc : Bool) (reg : Qubits q_w) :
    act (routeFwd ℓ q_w h_tree anc_leaf h_le).unitary
        (ket (padZero (routerMain ℓ q_w) (routerAnc ℓ q_w h_tree anc_leaf) (packRouterMain w fc reg))) =
      ket (fwdState ℓ q_w h_tree anc_leaf h_le w fc reg) := by
  classical
  dsimp only [routeFwd]
  simp only [LayeredCircuit.seq_unitary, act_mul]
  let z0 := padZero (routerMain ℓ q_w) (routerAnc ℓ q_w h_tree anc_leaf) (packRouterMain w fc reg)
  let actRoot := decide ((∀ i : Fin (ℓ - h_tree), w ⟨h_tree + i.1, by omega⟩ = false) ∧ fc = true)
  let z1 := Function.update z0 (wAct ℓ q_w h_tree anc_leaf ⟨0, Nat.two_pow_pos h_tree⟩) actRoot
  change act (routerTree ℓ q_w h_tree anc_leaf).unitary
      (act (routerPreFanout ℓ q_w h_tree anc_leaf h_le).unitary
        (act (routerEqRoot ℓ q_w h_tree anc_leaf h_le).unitary (ket z0))) = _
  rw [act_routerEqRoot_ket ℓ q_w h_tree anc_leaf h_le w fc reg]
  change act (routerTree ℓ q_w h_tree anc_leaf).unitary
      (act (routerPreFanout ℓ q_w h_tree anc_leaf h_le).unitary (ket z1)) = _
  have hclean1 : ∀ (s : Fin h_tree) (p : Fin (2 ^ s.1)) (k : Fin (1 + q_w)),
      z1 (wFanCopy ℓ q_w h_tree anc_leaf s p k) = false := by
    intro s p k
    have hne : wFanCopy ℓ q_w h_tree anc_leaf s p k ≠
        wAct ℓ q_w h_tree anc_leaf ⟨0, Nat.two_pow_pos h_tree⟩ := by
      intro h; exact wSlotItem_ne_wFanCopy _ _ _ _ ⟨0, Nat.two_pow_pos h_tree⟩ 0 s p k h.symm
    dsimp only [z1]
    rw [Function.update_of_ne hne]
    have hnat : wFanCopy ℓ q_w h_tree anc_leaf s p k =
        Fin.natAdd (routerMain ℓ q_w)
          ⟨((ℓ - h_tree) + 1) + 2 ^ h_tree + (2 ^ h_tree - 1) * q_w + 2 ^ h_tree * anc_leaf +
              (((2 ^ s.1 - 1) + p.1) * (1 + q_w) + k.1), by
            have hs1 : s.1 + 1 ≤ h_tree := s.isLt
            have hpow : 2 ^ (s.1 + 1) ≤ 2 ^ h_tree := Nat.pow_le_pow_right (by norm_num) hs1
            have h2s : 1 ≤ 2 ^ s.1 := Nat.two_pow_pos s.1
            have hp : p.1 < 2 ^ s.1 := p.isLt
            have hpow' : 2 ^ (s.1 + 1) = 2 ^ s.1 + 2 ^ s.1 := by rw [pow_succ']; omega
            have hrow : (2 ^ s.1 - 1) + p.1 < 2 ^ h_tree - 1 := by omega
            have hlt := mul_add_lt_mul hrow k.isLt
            dsimp [routerAnc]; omega⟩ := by
      ext
      simp only [wFanCopy, rFanOff, rLeafAncOff, rSlotOff, rActOff, rEqOff, Fin.val_natAdd]
      omega
    rw [hnat]
    exact padZero_natAdd _ _ _ _
  rw [act_routerPreFanout_ket ℓ q_w h_tree anc_leaf h_le z1 hclean1]
  let z2 : Qubits (routerTotal ℓ q_w h_tree anc_leaf) := fun wq =>
    if h : ∃ (s : Fin h_tree) (p : Fin (2 ^ s.1)) (k : Fin (1 + q_w)),
        wFanCopy ℓ q_w h_tree anc_leaf s p k = wq then
      z1 (wRegW ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - (Classical.choose h).1, by omega⟩)
    else z1 wq
  have hz2_fan : ∀ (s : Fin h_tree) (p : Fin (2 ^ s.1)) (k : Fin (1 + q_w)),
      z2 (wFanCopy ℓ q_w h_tree anc_leaf s p k) = w ⟨h_tree - 1 - s.1, by omega⟩ := by
    intro s p k
    have hex : ∃ (s' : Fin h_tree) (p' : Fin (2 ^ s'.1)) (k' : Fin (1 + q_w)),
        wFanCopy ℓ q_w h_tree anc_leaf s' p' k' = wFanCopy ℓ q_w h_tree anc_leaf s p k := ⟨s, p, k, rfl⟩
    dsimp only [z2]
    rw [dif_pos hex]
    rcases Classical.choose_spec hex with ⟨p', k', hspec⟩
    have hs_eq := (wFanCopy_inj hspec).1
    have hreg_eq : wRegW ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - (Classical.choose hex).1, by omega⟩ =
        wRegW ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - s.1, by omega⟩ := by
      congr 1; exact Fin.ext (by simp [hs_eq])
    rw [hreg_eq]
    have hne : wRegW ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - s.1, by omega⟩ ≠
        wAct ℓ q_w h_tree anc_leaf ⟨0, Nat.two_pow_pos h_tree⟩ := by
      intro h; have := congrArg Fin.val h
      have hlt := wRegW_lt ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - s.1, by omega⟩
      have hge := wAct_bounds ℓ q_w h_tree anc_leaf ⟨0, Nat.two_pow_pos h_tree⟩
      have hc := chain_offsets ℓ q_w h_tree anc_leaf
      omega
    dsimp only [z1]
    rw [Function.update_of_ne hne]
    have hcast : wRegW ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - s.1, by omega⟩ =
        Fin.castAdd (routerAnc ℓ q_w h_tree anc_leaf)
          ⟨h_tree - 1 - s.1, by change h_tree - 1 - s.1 < ℓ + 1 + q_w; omega⟩ := rfl
    dsimp only [z0]
    rw [hcast, padZero_castAdd]
    change routerW (packRouterMain w fc reg) ⟨h_tree - 1 - s.1, by omega⟩ = _
    rw [routerW_packRouterMain]
  have hz2_slot0 : ∀ (t : Fin (2 ^ h_tree)) (k : Fin (1 + q_w)),
      z2 (wSlotItem ℓ q_w h_tree anc_leaf t k) = if t.1 = 0 then boolCons actRoot reg k else false := by
    intro t k
    have hnot_fan : ¬ ∃ (s : Fin h_tree) (p : Fin (2 ^ s.1)) (k' : Fin (1 + q_w)),
        wFanCopy ℓ q_w h_tree anc_leaf s p k' = wSlotItem ℓ q_w h_tree anc_leaf t k := by
      rintro ⟨s, p, k', h⟩; exact (wSlotItem_ne_wFanCopy _ _ _ _ t k s p k').symm h
    dsimp only [z2]
    rw [dif_neg hnot_fan]
    by_cases hk0 : k.1 = 0
    · have hk_eq : k = 0 := Fin.ext hk0
      subst hk_eq
      have hw_eq : wSlotItem ℓ q_w h_tree anc_leaf t 0 = wAct ℓ q_w h_tree anc_leaf t := rfl
      rw [hw_eq]
      by_cases ht0 : t.1 = 0
      · have ht_eq : t = ⟨0, Nat.two_pow_pos h_tree⟩ := Fin.ext ht0
        subst ht_eq
        dsimp only [z1]; rw [Function.update_self, if_pos rfl]; rfl
      · have hne : wAct ℓ q_w h_tree anc_leaf t ≠
            wAct ℓ q_w h_tree anc_leaf ⟨0, Nat.two_pow_pos h_tree⟩ := by
          intro h; apply ht0
          have := congrArg Fin.val h; dsimp [wAct] at this; omega
        dsimp only [z1]; rw [Function.update_of_ne hne, if_neg ht0]
        have hnat : wAct ℓ q_w h_tree anc_leaf t =
            Fin.natAdd (routerMain ℓ q_w) ⟨(ℓ - h_tree) + 1 + t.1, by
              have := t.isLt; have := Nat.two_pow_pos h_tree; dsimp [routerAnc]; omega⟩ := by
          ext; dsimp [wAct, rActOff, rEqOff]; omega
        dsimp only [z0]; rw [hnat, padZero_natAdd]
    · have hne_act : wSlotItem ℓ q_w h_tree anc_leaf t k ≠
          wAct ℓ q_w h_tree anc_leaf ⟨0, Nat.two_pow_pos h_tree⟩ := by
        intro h
        have h0_eq : wAct ℓ q_w h_tree anc_leaf ⟨0, Nat.two_pow_pos h_tree⟩ =
            wSlotItem ℓ q_w h_tree anc_leaf ⟨0, Nat.two_pow_pos h_tree⟩ 0 := rfl
        rw [h0_eq] at h
        have hk_inj := (wSlotItem_inj h).2
        exact hk0 (congrArg Fin.val hk_inj)
      dsimp only [z1]; rw [Function.update_of_ne hne_act]
      have hk_pos : 1 ≤ k.1 := Nat.pos_of_ne_zero hk0
      have hk_cons : boolCons actRoot reg k = reg ⟨k.1 - 1, by have := k.isLt; omega⟩ := by
        dsimp only [boolCons]; rw [dif_neg hk0]
      by_cases ht0 : t.1 = 0
      · have hw_eq : wSlotItem ℓ q_w h_tree anc_leaf t k =
            wReg ℓ q_w h_tree anc_leaf ⟨k.1 - 1, by have := k.isLt; omega⟩ := by
          dsimp only [wSlotItem]; rw [dif_neg hk0, dif_pos ht0]
        rw [hw_eq, if_pos ht0, hk_cons]
        have hcast : wReg ℓ q_w h_tree anc_leaf ⟨k.1 - 1, by have := k.isLt; omega⟩ =
            Fin.castAdd (routerAnc ℓ q_w h_tree anc_leaf)
              ⟨ℓ + 1 + (k.1 - 1), by change ℓ + 1 + (k.1 - 1) < ℓ + 1 + q_w; have := k.isLt; omega⟩ := rfl
        dsimp only [z0]; rw [hcast, padZero_castAdd]
        change routerReg (packRouterMain w fc reg) ⟨k.1 - 1, by have := k.isLt; omega⟩ = _
        rw [routerReg_packRouterMain]
      · have hw_eq : wSlotItem ℓ q_w h_tree anc_leaf t k =
            wSlot ℓ q_w h_tree anc_leaf t (by omega) ⟨k.1 - 1, by have := k.isLt; omega⟩ := by
          dsimp only [wSlotItem]; rw [dif_neg hk0, dif_neg ht0]
        rw [hw_eq, if_neg ht0]
        have hnat : wSlot ℓ q_w h_tree anc_leaf t (by omega) ⟨k.1 - 1, by have := k.isLt; omega⟩ =
            Fin.natAdd (routerMain ℓ q_w)
              ⟨((ℓ - h_tree) + 1) + 2 ^ h_tree + ((t.1 - 1) * q_w + (k.1 - 1)), by
                have hlt := mul_add_lt_mul (show t.1 - 1 < 2 ^ h_tree - 1 by have := t.isLt; omega)
                  (show k.1 - 1 < q_w by have := k.isLt; omega)
                have := Nat.two_pow_pos h_tree
                dsimp [routerAnc]; omega⟩ := Fin.ext (by dsimp [wSlot, rSlotOff, rActOff, rEqOff]; omega)
        dsimp only [z0]; rw [hnat, padZero_natAdd]
  dsimp only [routerTree]
  rw [act_routerTreePrefix_ket ℓ q_w h_tree anc_leaf h_le w (boolCons actRoot reg) z2 hz2_fan hz2_slot0]
  congr 1
  funext wq
  dsimp only [fwdState]
  by_cases hslot : ∃ (t : Fin (2 ^ h_tree)) (k : Fin (1 + q_w)),
      wSlotItem ℓ q_w h_tree anc_leaf t k = wq
  · rw [dif_pos hslot, dif_pos hslot]
  · rw [dif_neg hslot, dif_neg hslot]
    dsimp only [z2]
    by_cases hfan : ∃ (s : Fin h_tree) (p : Fin (2 ^ s.1)) (k : Fin (1 + q_w)),
        wFanCopy ℓ q_w h_tree anc_leaf s p k = wq
    · rcases hfan with ⟨s, p, k, rfl⟩
      have hex : ∃ s' p' k', wFanCopy ℓ q_w h_tree anc_leaf s' p' k' =
          wFanCopy ℓ q_w h_tree anc_leaf s p k := ⟨s, p, k, rfl⟩
      rw [dif_pos hex, dif_pos hex]
      rcases Classical.choose_spec hex with ⟨p', k', hspec'⟩
      have hs_eq := (wFanCopy_inj hspec').1
      have hreg_eq : wRegW ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - (Classical.choose hex).1, by omega⟩ =
          wRegW ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - s.1, by omega⟩ := by
        congr 1; exact Fin.ext (by simp [hs_eq])
      rw [hreg_eq]
      have hne : wRegW ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - s.1, by omega⟩ ≠
          wAct ℓ q_w h_tree anc_leaf ⟨0, Nat.two_pow_pos h_tree⟩ := by
        intro h; have := congrArg Fin.val h
        have hlt := wRegW_lt ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - s.1, by omega⟩
        have hge := wAct_bounds ℓ q_w h_tree anc_leaf ⟨0, Nat.two_pow_pos h_tree⟩
        have hc := chain_offsets ℓ q_w h_tree anc_leaf
        omega
      dsimp only [z1]; rw [Function.update_of_ne hne]
      have hcast : wRegW ℓ q_w h_tree anc_leaf ⟨h_tree - 1 - s.1, by omega⟩ =
          Fin.castAdd (routerAnc ℓ q_w h_tree anc_leaf)
            ⟨h_tree - 1 - s.1, by dsimp [routerMain]; omega⟩ := rfl
      dsimp only [z0]; rw [hcast, padZero_castAdd]
      change routerW (packRouterMain w fc reg) ⟨h_tree - 1 - s.1, by omega⟩ = _
      rw [routerW_packRouterMain]
      congr 2; rw [hs_eq]
    · rw [dif_neg hfan, dif_neg hfan]
      have hne_act : wq ≠ wAct ℓ q_w h_tree anc_leaf ⟨0, Nat.two_pow_pos h_tree⟩ := by
        intro h; apply hslot
        refine ⟨⟨0, Nat.two_pow_pos h_tree⟩, 0, ?_⟩
        change wAct ℓ q_w h_tree anc_leaf ⟨0, Nat.two_pow_pos h_tree⟩ = wq
        exact h.symm
      dsimp only [z1]; rw [Function.update_of_ne hne_act]

/-! #### Parallel Leaves and `coherentRouter` -/

private def routerLeafWire (ℓ q_w h_tree anc_leaf : ℕ) (t : Fin (2 ^ h_tree))
    (w : Fin (1 + q_w + anc_leaf)) : Fin (routerTotal ℓ q_w h_tree anc_leaf) :=
  if h : w.1 < 1 + q_w then wSlotItem ℓ q_w h_tree anc_leaf t ⟨w.1, h⟩
  else wLeafAnc ℓ q_w h_tree anc_leaf t ⟨w.1 - (1 + q_w), by have := w.isLt; omega⟩

private def routerLeafEmb (ℓ q_w h_tree anc_leaf : ℕ) (t : Fin (2 ^ h_tree)) :
    Fin (1 + q_w + anc_leaf) ↪ Fin (routerTotal ℓ q_w h_tree anc_leaf) where
  toFun := routerLeafWire ℓ q_w h_tree anc_leaf t
  inj' a b hab := by
    have ha := a.isLt; have hb := b.isLt
    dsimp only [routerLeafWire] at hab
    by_cases ha1 : a.1 < 1 + q_w <;> by_cases hb1 : b.1 < 1 + q_w
    · rw [dif_pos ha1, dif_pos hb1] at hab
      have hk := (wSlotItem_inj hab).2
      have hkv : (⟨a.1, ha1⟩ : Fin (1 + q_w)).1 = (⟨b.1, hb1⟩ : Fin (1 + q_w)).1 :=
        @congrArg (Fin (1 + q_w)) ℕ _ _ Fin.val hk
      exact Fin.ext hkv
    · exfalso
      rw [dif_pos ha1, dif_neg hb1] at hab
      exact wSlotItem_ne_wLeafAnc _ _ _ _ t t _ _ hab
    · exfalso
      rw [dif_neg ha1, dif_pos hb1] at hab
      exact wSlotItem_ne_wLeafAnc _ _ _ _ t t _ _ hab.symm
    · rw [dif_neg ha1, dif_neg hb1] at hab
      have ha_eq := (wLeafAnc_inj hab).2
      have hav : (⟨a.1 - (1 + q_w), by omega⟩ : Fin anc_leaf).1 =
          (⟨b.1 - (1 + q_w), by omega⟩ : Fin anc_leaf).1 :=
        @congrArg (Fin anc_leaf) ℕ _ _ Fin.val ha_eq
      exact Fin.ext (by dsimp at hav; omega)

private lemma routerLeafEmb_apply (ℓ q_w h_tree anc_leaf : ℕ) (t : Fin (2 ^ h_tree))
    (w : Fin (1 + q_w + anc_leaf)) :
    routerLeafEmb ℓ q_w h_tree anc_leaf t w =
      if h : w.1 < 1 + q_w then wSlotItem ℓ q_w h_tree anc_leaf t ⟨w.1, h⟩
      else wLeafAnc ℓ q_w h_tree anc_leaf t ⟨w.1 - (1 + q_w), by have := w.isLt; omega⟩ := rfl

private lemma routerLeafEmb_castAdd (ℓ q_w h_tree anc_leaf : ℕ) (t : Fin (2 ^ h_tree))
    (k : Fin (1 + q_w)) :
    routerLeafEmb ℓ q_w h_tree anc_leaf t (Fin.castAdd anc_leaf k) =
      wSlotItem ℓ q_w h_tree anc_leaf t k := by
  have hk : (Fin.castAdd anc_leaf k).1 < 1 + q_w := k.isLt
  rw [routerLeafEmb_apply, dif_pos hk]
  rfl

private lemma routerLeafEmb_natAdd (ℓ q_w h_tree anc_leaf : ℕ) (t : Fin (2 ^ h_tree))
    (a : Fin anc_leaf) :
    routerLeafEmb ℓ q_w h_tree anc_leaf t (Fin.natAdd (1 + q_w) a) =
      wLeafAnc ℓ q_w h_tree anc_leaf t a := by
  have hnot : ¬ (Fin.natAdd (1 + q_w) a).1 < 1 + q_w := by simp
  rw [routerLeafEmb_apply, dif_neg hnot]
  congr 1; exact Fin.ext (by simp)

private def routerLeafSet (ℓ q_w h_tree anc_leaf : ℕ) (t : Fin (2 ^ h_tree)) :
    Finset (Fin (routerTotal ℓ q_w h_tree anc_leaf)) :=
  Finset.univ.image (routerLeafEmb ℓ q_w h_tree anc_leaf t)

private lemma routerLeafSet_disjoint (ℓ q_w h_tree anc_leaf : ℕ) (t₁ t₂ : Fin (2 ^ h_tree))
    (ht : t₁ ≠ t₂) :
    Disjoint (routerLeafSet ℓ q_w h_tree anc_leaf t₁)
      (routerLeafSet ℓ q_w h_tree anc_leaf t₂) := by
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  simp only [routerLeafSet, Finset.mem_image, Finset.mem_univ, true_and] at hw1 hw2
  rcases hw1 with ⟨a, rfl⟩
  rcases hw2 with ⟨b, hb⟩
  have hval := congrArg Fin.val hb
  rw [routerLeafEmb_apply, routerLeafEmb_apply] at hval
  split_ifs at hval with ha1 hb1 hb1'
  · exact ht (wSlotItem_inj (Fin.ext hval)).1.symm
  · exact wSlotItem_ne_wLeafAnc _ _ _ _ t₂ t₁ _ _ (Fin.ext hval)
  · exact wSlotItem_ne_wLeafAnc _ _ _ _ t₁ t₂ _ _ (Fin.ext hval.symm)
  · exact ht (wLeafAnc_inj (Fin.ext hval)).1.symm

private lemma routerLeafSet_ne (ℓ q_w h_tree anc_leaf : ℕ) (t₁ t₂ : Fin (2 ^ h_tree))
    (ht : t₁ ≠ t₂) :
    routerLeafSet ℓ q_w h_tree anc_leaf t₁ ≠ routerLeafSet ℓ q_w h_tree anc_leaf t₂ := by
  intro heq
  have hmem : wAct ℓ q_w h_tree anc_leaf t₁ ∈ routerLeafSet ℓ q_w h_tree anc_leaf t₁ := by
    rw [routerLeafSet, Finset.mem_image]
    refine ⟨0, Finset.mem_univ _, ?_⟩
    have h0 : (0 : Fin (1 + q_w + anc_leaf)).1 < 1 + q_w := by show 0 < 1 + q_w; omega
    rw [routerLeafEmb_apply, dif_pos h0]
    rfl
  have hmem2 : wAct ℓ q_w h_tree anc_leaf t₁ ∈ routerLeafSet ℓ q_w h_tree anc_leaf t₂ := heq ▸ hmem
  exact Finset.disjoint_left.mp (routerLeafSet_disjoint ℓ q_w h_tree anc_leaf t₁ t₂ ht) hmem hmem2

private def routerLeaves (ℓ q_w h_tree anc_leaf : ℕ)
    (leaves : Fin (2 ^ h_tree) → LayeredCircuit (1 + q_w + anc_leaf)) :
    LayeredCircuit (routerTotal ℓ q_w h_tree anc_leaf) :=
  (parMergeFin
    (fun t : Fin (2 ^ h_tree) => (leaves t).mapWires (routerLeafEmb ℓ q_w h_tree anc_leaf t))
    (routerLeafSet ℓ q_w h_tree anc_leaf)
    (fun t => (LayeredCircuit.mapWires_usesOnly _ _ (fun _ _ _ _ _ => Finset.mem_univ _)).mono
      (by intro w hw; simpa [routerLeafSet] using hw))
    (routerLeafSet_disjoint ℓ q_w h_tree anc_leaf)).1

private lemma routerLeaves_size (ℓ q_w h_tree anc_leaf : ℕ)
    (leaves : Fin (2 ^ h_tree) → LayeredCircuit (1 + q_w + anc_leaf)) :
    (routerLeaves ℓ q_w h_tree anc_leaf leaves).size = ∑ t : Fin (2 ^ h_tree), (leaves t).size := by
  dsimp only [routerLeaves]
  rw [(parMergeFin _ _ _ _).2.2.1]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [LayeredCircuit.mapWires_size]

private lemma routerLeaves_depth (ℓ q_w h_tree anc_leaf : ℕ)
    (leaves : Fin (2 ^ h_tree) → LayeredCircuit (1 + q_w + anc_leaf))
    (d : ℕ) (hd : ∀ t, (leaves t).depth ≤ d) :
    (routerLeaves ℓ q_w h_tree anc_leaf leaves).depth ≤ d := by
  dsimp only [routerLeaves]
  exact (parMergeFin _ _ _ _).2.2.2 d fun t => by
    rw [LayeredCircuit.mapWires_depth]; exact hd t

noncomputable def coherentRouter (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ)
    (leaves : Fin (2 ^ h_tree) → LayeredCircuit (1 + q_w + anc_leaf)) :
    LayeredCircuit (routerMain ℓ q_w + routerAnc ℓ q_w h_tree anc_leaf) :=
  let fwd := routeFwd ℓ q_w h_tree anc_leaf h_le
  fwd.seq ((routerLeaves ℓ q_w h_tree anc_leaf leaves).seq fwd.adj)

theorem coherentRouter_size (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ)
    (leaves : Fin (2 ^ h_tree) → LayeredCircuit (1 + q_w + anc_leaf)) :
    (coherentRouter ℓ q_w h_tree anc_leaf h_le leaves).size ≤
      24 * (ℓ + 2) + 16 * (2 ^ h_tree - 1) * (1 + q_w) +
      ∑ t : Fin (2 ^ h_tree), (leaves t).size := by
  dsimp only [coherentRouter]
  simp only [LayeredCircuit.seq_size, LayeredCircuit.adj_size, routerLeaves_size]
  have h1 := routeFwd_size ℓ q_w h_tree anc_leaf h_le
  have h2 : 2 * (8 * (2 ^ h_tree - 1) * (1 + q_w)) = 16 * (2 ^ h_tree - 1) * (1 + q_w) := by ring
  omega

theorem coherentRouter_size_le (ℓ q_w h_tree anc_leaf g : ℕ) (h_le : h_tree ≤ ℓ)
    (leaves : Fin (2 ^ h_tree) → LayeredCircuit (1 + q_w + anc_leaf))
    (hg : ∀ t, (leaves t).size ≤ g) :
    (coherentRouter ℓ q_w h_tree anc_leaf h_le leaves).size ≤
      24 * (ℓ + 2) + 16 * (2 ^ h_tree - 1) * (q_w + 1) + 2 ^ h_tree * g := by
  have h1 := coherentRouter_size ℓ q_w h_tree anc_leaf h_le leaves
  have hsum : (∑ t : Fin (2 ^ h_tree), (leaves t).size) ≤ 2 ^ h_tree * g := by
    calc (∑ t : Fin (2 ^ h_tree), (leaves t).size)
        ≤ ∑ _t : Fin (2 ^ h_tree), g := Finset.sum_le_sum fun t _ => hg t
      _ = 2 ^ h_tree * g := by simp
  have hmul : 16 * (2 ^ h_tree - 1) * (1 + q_w) = 16 * (2 ^ h_tree - 1) * (q_w + 1) := by ring
  omega

theorem coherentRouter_depth (ℓ q_w h_tree anc_leaf d : ℕ) (h_le : h_tree ≤ ℓ)
    (leaves : Fin (2 ^ h_tree) → LayeredCircuit (1 + q_w + anc_leaf))
    (hd : ∀ t, (leaves t).depth ≤ d) :
    (coherentRouter ℓ q_w h_tree anc_leaf h_le leaves).depth ≤
      20 * Nat.clog 2 (ℓ + 2) + 16 * h_tree + 2 * Nat.clog 2 (q_w + 1) + d + 6 := by
  dsimp only [coherentRouter]
  simp only [LayeredCircuit.seq_depth, LayeredCircuit.adj_depth]
  have h1 := routeFwd_depth ℓ q_w h_tree anc_leaf h_le
  have h2 := routerLeaves_depth ℓ q_w h_tree anc_leaf leaves d hd
  omega

def routerMat (ℓ q_w h_tree : ℕ)
    (U_mat : Fin (2 ^ h_tree) → Matrix (Qubits q_w) (Qubits q_w) ℂ) :
    Matrix (Qubits (routerMain ℓ q_w)) (Qubits (routerMain ℓ q_w)) ℂ :=
  Matrix.of fun y z =>
    if routerW y = routerW z ∧ routerFC y = routerFC z then
      if h : routerFC z = true ∧ bitsToNatLSB (routerW z) < 2 ^ h_tree then
        U_mat ⟨bitsToNatLSB (routerW z), h.2⟩ (routerReg y) (routerReg z)
      else
        if routerReg y = routerReg z then 1 else 0
    else 0

private lemma fwdState_eq_outside_t0 (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ)
    (w : Qubits ℓ) (fc : Bool) (reg y_reg : Qubits q_w) (t₀ : Fin (2 ^ h_tree))
    (ht₀ : routePos ℓ h_tree h_le w h_tree = t₀.1)
    (wq : Fin (routerTotal ℓ q_w h_tree anc_leaf))
    (hnot_slot_t0 : ¬ ∃ k : Fin (1 + q_w), wSlotItem ℓ q_w h_tree anc_leaf t₀ k = wq) :
    fwdState ℓ q_w h_tree anc_leaf h_le w fc reg wq =
      fwdState ℓ q_w h_tree anc_leaf h_le w fc y_reg wq := by
  classical
  by_cases hslot : ∃ (t : Fin (2 ^ h_tree)) (k : Fin (1 + q_w)),
      wSlotItem ℓ q_w h_tree anc_leaf t k = wq
  · rcases hslot with ⟨t, k, rfl⟩
    have hne_t : t ≠ t₀ := fun h => hnot_slot_t0 ⟨k, by subst h; rfl⟩
    have hne_val : t.1 ≠ t₀.1 := fun h => hne_t (Fin.ext h)
    rw [fwdState_slot, fwdState_slot, ht₀, if_neg hne_val, if_neg hne_val]
  · by_cases hfan : ∃ (s : Fin h_tree) (p : Fin (2 ^ s.1)) (k : Fin (1 + q_w)),
        wFanCopy ℓ q_w h_tree anc_leaf s p k = wq
    · rcases hfan with ⟨s, p, k, rfl⟩
      dsimp only [fwdState]
      rw [dif_neg hslot, dif_neg hslot]
      have hex : ∃ s' p' k', wFanCopy ℓ q_w h_tree anc_leaf s' p' k' =
          wFanCopy ℓ q_w h_tree anc_leaf s p k := ⟨s, p, k, rfl⟩
      rw [dif_pos hex, dif_pos hex]
    · dsimp only [fwdState]
      rw [dif_neg hslot, dif_neg hslot, dif_neg hfan, dif_neg hfan]
      have hnot_reg : ∀ j : Fin q_w, wq ≠ wReg ℓ q_w h_tree anc_leaf j := by
        intro j h; apply hslot
        refine ⟨⟨0, Nat.two_pow_pos h_tree⟩, Fin.natAdd 1 j, ?_⟩
        dsimp only [wSlotItem]
        rw [dif_neg (by simp), dif_pos rfl, h]
        congr 1; exact Fin.ext (by simp)
      by_cases hmain : wq.1 < routerMain ℓ q_w
      · have hcast : wq = Fin.castAdd (routerAnc ℓ q_w h_tree anc_leaf) ⟨wq.1, hmain⟩ := rfl
        rw [hcast, padZero_castAdd, padZero_castAdd]
        dsimp only [packRouterMain]
        split_ifs with h1 h2
        · rfl
        · rfl
        · exfalso
          exact hnot_reg ⟨wq.1 - (ℓ + 1), by dsimp [routerMain] at hmain; omega⟩
            (Fin.ext (by dsimp [wReg]; omega))
      · have hlt_wq : wq.1 < routerMain ℓ q_w + routerAnc ℓ q_w h_tree anc_leaf := wq.isLt
        have hnat : wq = Fin.natAdd (routerMain ℓ q_w)
            ⟨wq.1 - routerMain ℓ q_w, by omega⟩ := Fin.ext (by simp; omega)
        rw [hnat, padZero_natAdd, padZero_natAdd]

private lemma act_leaf_inactive_ket (ℓ q_w h_tree anc_leaf : ℕ)
    (leaf : LayeredCircuit (1 + q_w + anc_leaf))
    (U_mat : Matrix (Qubits q_w) (Qubits q_w) ℂ)
    (hleaf : leaf.ImplementsOnClean (ctrlBlockMat U_mat))
    (t : Fin (2 ^ h_tree)) (st : Qubits (routerTotal ℓ q_w h_tree anc_leaf))
    (hclean : ∀ a : Fin anc_leaf,
      st (routerLeafEmb ℓ q_w h_tree anc_leaf t (Fin.natAdd (1 + q_w) a)) = false)
    (h0_false : st (wAct ℓ q_w h_tree anc_leaf t) = false) :
    act (leaf.mapWires (routerLeafEmb ℓ q_w h_tree anc_leaf t)).unitary (ket st) = ket st := by
  let emb := routerLeafEmb ℓ q_w h_tree anc_leaf t
  have hact := act_mapWires_implementsOnClean leaf (ctrlBlockMat U_mat) hleaf emb st hclean
  dsimp only at hact
  rw [hact]
  have h0' : (st ∘ ⇑((Fin.castAddEmb anc_leaf).trans emb)) 0 = false := by
    change st (emb (Fin.castAdd anc_leaf 0)) = false
    rw [routerLeafEmb_castAdd]
    change st (wAct ℓ q_w h_tree anc_leaf t) = false
    exact h0_false
  rw [Finset.sum_eq_single (st ∘ ⇑((Fin.castAddEmb anc_leaf).trans emb))]
  · simp only [ctrlBlockMat, Matrix.of_apply, h0', ↓reduceIte, Bool.false_eq_true, one_smul]
    congr 1; funext wq
    by_cases hmem : wq ∈ Set.range ((Fin.castAddEmb anc_leaf).trans emb)
    · rcases hmem with ⟨k, rfl⟩; rw [updateOn_apply_emb]; rfl
    · exact updateOn_apply_not_mem _ _ _ hmem
  · intro y _ hy
    simp only [ctrlBlockMat, Matrix.of_apply, h0']
    by_cases hy0 : y 0 = false
    · have hy_tail : (fun i => y (Fin.natAdd 1 i)) ≠
          (fun i => (st ∘ ⇑((Fin.castAddEmb anc_leaf).trans emb)) (Fin.natAdd 1 i)) := by
        intro h; apply hy; funext k
        by_cases hk0 : k.1 = 0
        · have hk : k = 0 := Fin.ext hk0; subst hk; rw [hy0, h0']
        · have hk_eq : k = Fin.natAdd 1 ⟨k.1 - 1, by have := k.isLt; omega⟩ :=
            Fin.ext (by simp; omega)
          rw [hk_eq]; exact congrFun h _
      rw [if_pos hy0, if_neg (by simp [hy0]), if_neg hy_tail, zero_smul]
    · rw [if_neg hy0, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem act_coherentRouter_ket (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ)
    (leaves : Fin (2 ^ h_tree) → LayeredCircuit (1 + q_w + anc_leaf))
    (U_mat : Fin (2 ^ h_tree) → Matrix (Qubits q_w) (Qubits q_w) ℂ)
    (hleaves : ∀ t, (leaves t).ImplementsOnClean (ctrlBlockMat (U_mat t)))
    (w : Qubits ℓ) (fc : Bool) (reg : Qubits q_w) :
    act (coherentRouter ℓ q_w h_tree anc_leaf h_le leaves).unitary
        (ket (padZero (routerMain ℓ q_w) (routerAnc ℓ q_w h_tree anc_leaf)
          (packRouterMain w fc reg))) =
      if h : fc = true ∧ bitsToNatLSB w < 2 ^ h_tree then
        ∑ y_reg : Qubits q_w, U_mat ⟨bitsToNatLSB w, h.2⟩ y_reg reg •
          ket (padZero (routerMain ℓ q_w) (routerAnc ℓ q_w h_tree anc_leaf)
            (packRouterMain w true y_reg))
      else
        ket (padZero (routerMain ℓ q_w) (routerAnc ℓ q_w h_tree anc_leaf)
          (packRouterMain w fc reg)) := by
  classical
  dsimp only [coherentRouter]
  simp only [LayeredCircuit.seq_unitary, act_mul]
  let fwd := routeFwd ℓ q_w h_tree anc_leaf h_le
  have hfwd_ket := act_routeFwd_ket ℓ q_w h_tree anc_leaf h_le w fc reg
  change act fwd.adj.unitary
      (act (routerLeaves ℓ q_w h_tree anc_leaf leaves).unitary
        (act fwd.unitary (ket (padZero _ _ (packRouterMain w fc reg))))) = _
  rw [hfwd_ket]
  have hclean_leaf : ∀ t : Fin (2 ^ h_tree), ∀ a : Fin anc_leaf,
      fwdState ℓ q_w h_tree anc_leaf h_le w fc reg
        (routerLeafEmb ℓ q_w h_tree anc_leaf t (Fin.natAdd (1 + q_w) a)) = false := by
    intro t a
    rw [routerLeafEmb_natAdd]
    exact fwdState_leafAnc ℓ q_w h_tree anc_leaf h_le w fc reg t a
  have htop_iff : (∀ i : Fin (ℓ - h_tree), w ⟨h_tree + i.1, by omega⟩ = false) ∧ fc = true ↔
      fc = true ∧ bitsToNatLSB w < 2 ^ h_tree := by
    rw [← bitsToNatLSB_lt_pow_iff h_le w, and_comm]
  by_cases hcond : fc = true ∧ bitsToNatLSB w < 2 ^ h_tree
  · rcases hcond with ⟨rfl, hlt⟩
    rw [dif_pos ⟨rfl, hlt⟩]
    let t₀ : Fin (2 ^ h_tree) := ⟨bitsToNatLSB w, hlt⟩
    have ht₀_pos : routePos ℓ h_tree h_le w h_tree = t₀.1 := by
      rw [routePos_h_tree]
      exact (bitsToNatLSB_eq_prefix_of_lt h_le w hlt).symm
    have hactRoot : decide ((∀ i : Fin (ℓ - h_tree), w ⟨h_tree + i.1, by omega⟩ = false) ∧ true = true) =
        true := decide_eq_true (htop_iff.mpr ⟨rfl, hlt⟩)
    have hid_other : ∀ t : Fin (2 ^ h_tree), t ≠ t₀ →
        act ((leaves t).mapWires (routerLeafEmb ℓ q_w h_tree anc_leaf t)).unitary
          (ket (fwdState ℓ q_w h_tree anc_leaf h_le w true reg)) =
          ket (fwdState ℓ q_w h_tree anc_leaf h_le w true reg) := by
      intro t hne
      refine act_leaf_inactive_ket ℓ q_w h_tree anc_leaf (leaves t) (U_mat t) (hleaves t) t _
        (hclean_leaf t) ?_
      change fwdState ℓ q_w h_tree anc_leaf h_le w true reg (wSlotItem ℓ q_w h_tree anc_leaf t 0) = false
      rw [fwdState_slot, ht₀_pos, if_neg (fun h => hne (Fin.ext h))]
    have hactive :
        act ((leaves t₀).mapWires (routerLeafEmb ℓ q_w h_tree anc_leaf t₀)).unitary
            (ket (fwdState ℓ q_w h_tree anc_leaf h_le w true reg)) =
          ∑ y_reg : Qubits q_w,
            U_mat t₀ y_reg reg • ket (fwdState ℓ q_w h_tree anc_leaf h_le w true y_reg) := by
      let st := fwdState ℓ q_w h_tree anc_leaf h_le w true reg
      let emb := routerLeafEmb ℓ q_w h_tree anc_leaf t₀
      let embMain := (Fin.castAddEmb anc_leaf).trans emb
      have hact_m := act_mapWires_implementsOnClean (leaves t₀) (ctrlBlockMat (U_mat t₀))
        (hleaves t₀) emb st (hclean_leaf t₀)
      change act ((leaves t₀).mapWires emb).unitary (ket st) =
        ∑ y : Qubits (1 + q_w), ctrlBlockMat (U_mat t₀) y (st ∘ embMain) • ket (updateOn embMain st y) at hact_m
      rw [hact_m]
      have hcomp_eq : st ∘ embMain = boolCons true reg := by
        funext k
        change st (emb (Fin.castAdd anc_leaf k)) = boolCons true reg k
        dsimp only [st, emb]
        rw [routerLeafEmb_castAdd, fwdState_slot, ht₀_pos, if_pos rfl, hactRoot]
      rw [hcomp_eq]
      let liftReg : Qubits q_w → Qubits (1 + q_w) := boolCons true
      have hsub : (∑ y : Qubits (1 + q_w),
            ctrlBlockMat (U_mat t₀) y (boolCons true reg) • ket (updateOn embMain st y)) =
          ∑ y ∈ Finset.univ.image liftReg,
            ctrlBlockMat (U_mat t₀) y (boolCons true reg) • ket (updateOn embMain st y) := by
        rw [← Finset.sum_subset (Finset.subset_univ _)]
        intro y _ hy
        by_cases hy0 : y 0 = true
        · exfalso; apply hy; rw [Finset.mem_image]
          refine ⟨fun i => y (Fin.natAdd 1 i), Finset.mem_univ _, ?_⟩
          funext k
          by_cases hk0 : k.1 = 0
          · have hk : k = 0 := Fin.ext hk0; subst hk; simp [liftReg, hy0]
          · have hk_eq : k = Fin.natAdd 1 ⟨k.1 - 1, by have := k.isLt; omega⟩ :=
              Fin.ext (by simp; omega)
            dsimp only [liftReg]
            rw [hk_eq, boolCons_natAdd]
        · have hyf : y 0 = false := by cases hy' : y 0 <;> simp_all
          simp only [ctrlBlockMat, Matrix.of_apply, hyf, boolCons_zero]
          simp
      rw [hsub, Finset.sum_image (fun a _ b _ h => boolCons_inj true h)]
      refine Finset.sum_congr rfl fun y_reg _ => ?_
      have hcb : ctrlBlockMat (U_mat t₀) (liftReg y_reg) (boolCons true reg) = U_mat t₀ y_reg reg := by
        simp only [ctrlBlockMat, Matrix.of_apply, liftReg, boolCons_zero, ↓reduceIte]
        have ht1 : (fun i : Fin q_w => boolCons true y_reg (Fin.natAdd 1 i)) = y_reg := by
          funext i; exact boolCons_natAdd true y_reg i
        have ht2 : (fun i : Fin q_w => boolCons true reg (Fin.natAdd 1 i)) = reg := by
          funext i; exact boolCons_natAdd true reg i
        rw [ht1, ht2]
      rw [hcb]
      refine congrArg (fun v => U_mat t₀ y_reg reg • ket v) (funext fun wq => ?_)
      by_cases hmem : wq ∈ Set.range embMain
      · rcases hmem with ⟨k, rfl⟩
        rw [updateOn_apply_emb]
        change liftReg y_reg k =
          fwdState ℓ q_w h_tree anc_leaf h_le w true y_reg
            (routerLeafEmb ℓ q_w h_tree anc_leaf t₀ (Fin.castAdd anc_leaf k))
        dsimp only [liftReg]
        rw [routerLeafEmb_castAdd, fwdState_slot, ht₀_pos, if_pos rfl, hactRoot]
      · rw [updateOn_apply_not_mem _ _ _ hmem]
        refine fwdState_eq_outside_t0 ℓ q_w h_tree anc_leaf h_le w true reg y_reg t₀ ht₀_pos wq ?_
        rintro ⟨k, rfl⟩
        apply hmem
        exact ⟨k, routerLeafEmb_castAdd ℓ q_w h_tree anc_leaf t₀ k⟩
    have hleaves_act :
        act (routerLeaves ℓ q_w h_tree anc_leaf leaves).unitary
            (ket (fwdState ℓ q_w h_tree anc_leaf h_le w true reg)) =
          ∑ y_reg : Qubits q_w,
            U_mat t₀ y_reg reg • ket (fwdState ℓ q_w h_tree anc_leaf h_le w true y_reg) := by
      dsimp only [routerLeaves]
      refine act_parMergeFin_singleActive _ _ _ _ t₀ (fun t₁ t₂ ht =>
        Or.inl (routerLeafSet_ne ℓ q_w h_tree anc_leaf t₁ t₂ ht)) _ _ _ hactive ?_ hid_other
      intro y_reg wq hwq
      refine fwdState_eq_outside_t0 ℓ q_w h_tree anc_leaf h_le w true y_reg reg t₀ ht₀_pos wq ?_
      rintro ⟨k, rfl⟩
      apply hwq
      rw [routerLeafSet, Finset.mem_image]
      exact ⟨Fin.castAdd anc_leaf k, Finset.mem_univ _, routerLeafEmb_castAdd _ _ _ _ t₀ k⟩
    rw [hleaves_act, act_sum]
    refine Finset.sum_congr rfl fun y_reg _ => ?_
    have h_unroute :
        act fwd.adj.unitary (ket (fwdState ℓ q_w h_tree anc_leaf h_le w true y_reg)) =
          ket (padZero (routerMain ℓ q_w) (routerAnc ℓ q_w h_tree anc_leaf)
            (packRouterMain w true y_reg)) := by
      have hfwd_y := act_routeFwd_ket ℓ q_w h_tree anc_leaf h_le w true y_reg
      change act fwd.unitary (ket (padZero (routerMain ℓ q_w) (routerAnc ℓ q_w h_tree anc_leaf)
          (packRouterMain w true y_reg))) =
        ket (fwdState ℓ q_w h_tree anc_leaf h_le w true y_reg) at hfwd_y
      rw [← hfwd_y, ← act_mul, LayeredCircuit.adj_unitary,
        Matrix.mem_unitaryGroup_iff'.mp fwd.unitary_mem_unitaryGroup, act_one]
    rw [act_smul, h_unroute]
  · rw [dif_neg hcond]
    have hactRoot : decide ((∀ i : Fin (ℓ - h_tree), w ⟨h_tree + i.1, by omega⟩ = false) ∧ fc = true) =
        false := decide_eq_false (mt htop_iff.mp hcond)
    have hid_all : ∀ t : Fin (2 ^ h_tree),
        act ((leaves t).mapWires (routerLeafEmb ℓ q_w h_tree anc_leaf t)).unitary
          (ket (fwdState ℓ q_w h_tree anc_leaf h_le w fc reg)) =
          ket (fwdState ℓ q_w h_tree anc_leaf h_le w fc reg) := by
      intro t
      refine act_leaf_inactive_ket ℓ q_w h_tree anc_leaf (leaves t) (U_mat t) (hleaves t) t _
        (hclean_leaf t) ?_
      change fwdState ℓ q_w h_tree anc_leaf h_le w fc reg (wSlotItem ℓ q_w h_tree anc_leaf t 0) = false
      rw [fwdState_slot]
      split_ifs
      · exact hactRoot
      · rfl
    have hleaves_id :
        act (routerLeaves ℓ q_w h_tree anc_leaf leaves).unitary
            (ket (fwdState ℓ q_w h_tree anc_leaf h_le w fc reg)) =
          ket (fwdState ℓ q_w h_tree anc_leaf h_le w fc reg) := by
      dsimp only [routerLeaves]
      exact act_parMergeFin_allId _ _ _ _ _ hid_all
    rw [hleaves_id, ← hfwd_ket, ← act_mul, LayeredCircuit.adj_unitary,
      Matrix.mem_unitaryGroup_iff'.mp fwd.unitary_mem_unitaryGroup, act_one]

theorem coherentRouter_implements (ℓ q_w h_tree anc_leaf : ℕ) (h_le : h_tree ≤ ℓ)
    (leaves : Fin (2 ^ h_tree) → LayeredCircuit (1 + q_w + anc_leaf))
    (U_mat : Fin (2 ^ h_tree) → Matrix (Qubits q_w) (Qubits q_w) ℂ)
    (hleaves : ∀ t, (leaves t).ImplementsOnClean (ctrlBlockMat (U_mat t))) :
    (coherentRouter ℓ q_w h_tree anc_leaf h_le leaves).ImplementsOnClean
      (routerMat ℓ q_w h_tree U_mat) := by
  apply implementsOnClean_of_act
  intro x
  rw [eq_packRouterMain x]
  have hact := act_coherentRouter_ket ℓ q_w h_tree anc_leaf h_le leaves U_mat hleaves
    (routerW x) (routerFC x) (routerReg x)
  change act (coherentRouter ℓ q_w h_tree anc_leaf h_le leaves).unitary
      (ket (padZero (routerMain ℓ q_w) (routerAnc ℓ q_w h_tree anc_leaf)
        (packRouterMain (routerW x) (routerFC x) (routerReg x)))) = _
  rw [hact]
  by_cases hcond : routerFC x = true ∧ bitsToNatLSB (routerW x) < 2 ^ h_tree
  · rw [dif_pos hcond]
    let liftReg : Qubits q_w → Qubits (routerMain ℓ q_w) :=
      packRouterMain (routerW x) true
    have hsum : (∑ y : Qubits (routerMain ℓ q_w),
          routerMat ℓ q_w h_tree U_mat y (packRouterMain (routerW x) (routerFC x) (routerReg x)) •
            ket (padZero (routerMain ℓ q_w) (routerAnc ℓ q_w h_tree anc_leaf) y)) =
        ∑ y ∈ Finset.univ.image liftReg,
          routerMat ℓ q_w h_tree U_mat y (packRouterMain (routerW x) (routerFC x) (routerReg x)) •
            ket (padZero (routerMain ℓ q_w) (routerAnc ℓ q_w h_tree anc_leaf) y) := by
      rw [← Finset.sum_subset (Finset.subset_univ _)]
      intro y _ hy
      simp only [routerMat, Matrix.of_apply, routerW_packRouterMain, routerFC_packRouterMain]
      by_cases hwf : routerW y = routerW x ∧ routerFC y = routerFC x
      · exfalso; apply hy; rw [Finset.mem_image]
        refine ⟨routerReg y, Finset.mem_univ _, ?_⟩
        dsimp only [liftReg]
        rw [← hwf.1, ← hcond.1, ← hwf.2]
        exact (eq_packRouterMain y).symm
      · rw [if_neg hwf, zero_smul]
    rw [hsum, Finset.sum_image (fun a _ b _ h => by
      have := congrArg routerReg h
      simpa [liftReg] using this)]
    refine Finset.sum_congr rfl fun y_reg _ => ?_
    simp only [routerMat, Matrix.of_apply, liftReg, routerW_packRouterMain,
      routerFC_packRouterMain, routerReg_packRouterMain, hcond.1, true_and, and_self,
      ↓reduceIte, dif_pos hcond.2]
  · rw [dif_neg hcond]
    symm
    rw [Finset.sum_eq_single (packRouterMain (routerW x) (routerFC x) (routerReg x))]
    · simp only [routerMat, Matrix.of_apply, routerW_packRouterMain,
        routerFC_packRouterMain, routerReg_packRouterMain, and_self, ↓reduceIte,
        dif_neg hcond, one_smul]
    · intro y _ hy
      simp only [routerMat, Matrix.of_apply, routerW_packRouterMain,
        routerFC_packRouterMain, routerReg_packRouterMain]
      by_cases hwf : routerW y = routerW x ∧ routerFC y = routerFC x
      · rw [if_pos hwf, dif_neg hcond]
        have hne : routerReg y ≠ routerReg x := by
          intro hr
          apply hy
          rw [eq_packRouterMain y, hwf.1, hwf.2, hr]
        rw [if_neg hne, zero_smul]
      · rw [if_neg hwf, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h

/-! ### 7. Two-Level Unitary & Controlled Two-Level Unitary (`twoLevelCtrlGate`, `ctrlTwoLevelGate`) -/

def twoLevelMat (q_w : ℕ) (u v : Qubits q_w) (M2 : Matrix Bool Bool ℂ) :
    Matrix (Qubits q_w) (Qubits q_w) ℂ :=
  Matrix.of fun y z =>
    if y = u ∧ z = u then M2 false false
    else if y = v ∧ z = u then M2 true false
    else if y = u ∧ z = v then M2 false true
    else if y = v ∧ z = v then M2 true true
    else if y = z ∧ z ≠ u ∧ z ≠ v then 1
    else 0

private lemma eq_boolCons_iff {q_w : ℕ} (b : Bool) (x : Qubits (1 + q_w)) (w : Qubits q_w) :
    x = boolCons b w ↔ (x 0 = b ∧ (fun i => x (Fin.natAdd 1 i)) = w) := by
  constructor
  · rintro rfl
    refine ⟨rfl, funext fun i => boolCons_natAdd b w i⟩
  · rintro ⟨h0, htail⟩
    funext k
    by_cases hk0 : k.1 = 0
    · have hk : k = 0 := Fin.ext hk0; subst hk; exact h0
    · have hk_eq : k = Fin.natAdd 1 ⟨k.1 - 1, by have := k.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [hk_eq, boolCons_natAdd]
      exact congrFun htail _

lemma twoLevelMat_boolCons_true (q_w : ℕ) (u v : Qubits q_w) (M2 : Matrix Bool Bool ℂ) :
    twoLevelMat (1 + q_w) (boolCons true u) (boolCons true v) M2 =
      ctrlBlockMat (twoLevelMat q_w u v M2) := by
  ext y z
  simp only [twoLevelMat, ctrlBlockMat, Matrix.of_apply]
  simp only [ne_eq, eq_boolCons_iff]
  cases hy0 : y 0 <;> cases hz0 : z 0
  · simp only [Bool.false_eq_true, false_and, not_false_eq_true, and_true, ↓reduceIte]
    have hyz_iff : y = z ↔ (fun i : Fin q_w => y (Fin.natAdd 1 i)) = fun i => z (Fin.natAdd 1 i) := by
      constructor
      · rintro rfl; rfl
      · intro htail
        funext k
        by_cases hk0 : k.1 = 0
        · have hk : k = 0 := Fin.ext hk0; subst hk; rw [hy0, hz0]
        · have hk_eq : k = Fin.natAdd 1 ⟨k.1 - 1, by have := k.isLt; omega⟩ :=
            Fin.ext (by simp; omega)
          rw [hk_eq]; exact congrFun htail _
    simp only [hyz_iff]
  · simp only [Bool.false_eq_true, false_and, ↓reduceIte]
    have hne : y ≠ z := fun h => by rw [h, hz0] at hy0; cases hy0
    simp [hne]
  · simp only [Bool.false_eq_true, false_and, ↓reduceIte]
    have hne : y ≠ z := fun h => by rw [h, hz0] at hy0; cases hy0
    simp [hne]
  · simp only [true_and, ↓reduceIte]
    have hyz_iff : y = z ↔ (fun i : Fin q_w => y (Fin.natAdd 1 i)) = fun i => z (Fin.natAdd 1 i) := by
      constructor
      · rintro rfl; rfl
      · intro htail
        funext k
        by_cases hk0 : k.1 = 0
        · have hk : k = 0 := Fin.ext hk0; subst hk; rw [hy0, hz0]
        · have hk_eq : k = Fin.natAdd 1 ⟨k.1 - 1, by have := k.isLt; omega⟩ :=
            Fin.ext (by simp; omega)
          rw [hk_eq]; exact congrFun htail _
    simp only [hyz_iff]

private lemma exists_coord_ne {q_w : ℕ} {u v : Qubits q_w} (huv : u ≠ v) :
    ∃ p : Fin q_w, u p ≠ v p := by
  by_contra h
  push Not at h
  exact huv (funext h)

private def skipWire (q_w : ℕ) (p : Fin q_w) : Fin (q_w - 1) ↪ Fin q_w where
  toFun i := if h : i.1 < p.1 then ⟨i.1, by omega⟩
    else ⟨i.1 + 1, by have := i.isLt; have := p.isLt; omega⟩
  inj' a b hab := by
    have ha := a.isLt; have hb := b.isLt; have hp := p.isLt
    have hval := congrArg Fin.val hab
    by_cases ha1 : a.1 < p.1 <;> by_cases hb1 : b.1 < p.1
    · simp only [ha1, hb1, ↓reduceDIte] at hval; exact Fin.ext hval
    · simp only [ha1, hb1, ↓reduceDIte] at hval; omega
    · simp only [ha1, hb1, ↓reduceDIte] at hval; omega
    · simp only [ha1, hb1, ↓reduceDIte] at hval; exact Fin.ext (by omega)

private lemma skipWire_apply (q_w : ℕ) (p : Fin q_w) (i : Fin (q_w - 1)) :
    skipWire q_w p i =
      if h : i.1 < p.1 then ⟨i.1, by omega⟩
      else ⟨i.1 + 1, by have := i.isLt; have := p.isLt; omega⟩ := rfl

private lemma skipWire_ne (q_w : ℕ) (p : Fin q_w) (i : Fin (q_w - 1)) :
    skipWire q_w p i ≠ p := by
  intro h
  have hval := congrArg Fin.val h
  by_cases hi : i.1 < p.1
  · simp only [skipWire_apply, hi, ↓reduceDIte] at hval; omega
  · simp only [skipWire_apply, hi, ↓reduceDIte] at hval; omega

private lemma exists_skipWire_eq {q_w : ℕ} (p w : Fin q_w) (hw : w ≠ p) :
    ∃ i : Fin (q_w - 1), skipWire q_w p i = w := by
  have hp := p.isLt; have hwl := w.isLt
  have hne : w.1 ≠ p.1 := fun h => hw (Fin.ext h)
  by_cases hlt : w.1 < p.1
  · refine ⟨⟨w.1, by omega⟩, Fin.ext ?_⟩
    rw [skipWire_apply, dif_pos hlt]
  · refine ⟨⟨w.1 - 1, by omega⟩, Fin.ext ?_⟩
    have hnot : ¬ w.1 - 1 < p.1 := by omega
    rw [skipWire_apply, dif_neg hnot]
    simp; omega

private noncomputable def cnotFanList (m : ℕ) (p : Fin m) :
    (L : List (Fin m)) → (∀ i ∈ L, i ≠ p) → LayeredCircuit m
  | [], _ => LayeredCircuit.id m
  | i :: rest, h =>
    (cnotGate p i (h i List.mem_cons_self).symm).seq
      (cnotFanList m p rest fun j hj => h j (List.mem_cons_of_mem _ hj))

private lemma cnotFanList_size (m : ℕ) (p : Fin m) (L : List (Fin m))
    (h : ∀ i ∈ L, i ≠ p) : (cnotFanList m p L h).size = L.length := by
  induction L with
  | nil => simp [cnotFanList]
  | cons i rest ih => simp [cnotFanList, ih, Nat.add_comm]

private lemma cnotFanList_depth (m : ℕ) (p : Fin m) (L : List (Fin m))
    (h : ∀ i ∈ L, i ≠ p) : (cnotFanList m p L h).depth = L.length := by
  induction L with
  | nil => simp [cnotFanList]
  | cons i rest ih => simp [cnotFanList, ih, Nat.add_comm]

private lemma act_cnotFanList_ket (m : ℕ) (p : Fin m) (L : List (Fin m))
    (h : ∀ i ∈ L, i ≠ p) (hnd : L.Nodup) (x : Qubits m) :
    act (cnotFanList m p L h).unitary (ket x) =
      ket (fun w => if w ∈ L then xor (x w) (x p) else x w) := by
  induction L generalizing x with
  | nil => simp [cnotFanList, LayeredCircuit.id_unitary, act_one]
  | cons i rest ih =>
    rw [List.nodup_cons] at hnd
    simp only [cnotFanList, LayeredCircuit.seq_unitary, act_mul, act_cnotGate_ket]
    let x1 := Function.update x i (xor (x i) (x p))
    have hi_ne : i ≠ p := h i List.mem_cons_self
    have hx1p : x1 p = x p := Function.update_of_ne hi_ne.symm _ _
    have hx1_rest : ∀ w ∈ rest, x1 w = x w := fun w hw =>
      Function.update_of_ne (fun heq => hnd.1 (by subst heq; exact hw)) _ _
    change act (cnotFanList m p rest _).unitary (ket x1) = _
    rw [ih _ hnd.2 x1]
    congr 1; funext w
    by_cases hwi : w = i
    · subst hwi
      simp only [List.mem_cons, true_or, ↓reduceIte, if_neg hnd.1]
      exact Function.update_self _ _ _
    · by_cases hwr : w ∈ rest
      · simp only [List.mem_cons, hwi, false_or, hwr, ↓reduceIte, hx1_rest w hwr, hx1p]
      · simp only [List.mem_cons, hwi, hwr, or_self, ↓reduceIte]
        exact Function.update_of_ne hwi _ _

private noncomputable def relabelCirc (q_w : ℕ) (p : Fin q_w) (u v : Qubits q_w) :
    LayeredCircuit q_w :=
  let L : List (Fin q_w) := (List.finRange q_w).filter fun i => decide (i ≠ p ∧ u i ≠ v i)
  have hL : ∀ i ∈ L, i ≠ p := fun i hi => by
    simp only [L, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hi
    exact hi.1
  let cStep := cnotFanList q_w p L hL
  let xStep := if u p then pauliXGate p else LayeredCircuit.id q_w
  cStep.seq xStep

private def relabelFn (q_w : ℕ) (p : Fin q_w) (u v x : Qubits q_w) : Qubits q_w :=
  fun w =>
    if w = p then xor (x p) (u p)
    else if u w ≠ v w then xor (x w) (x p)
    else x w

private lemma relabelFilter_length_le (q_w : ℕ) (p : Fin q_w) (u v : Qubits q_w) :
    ((List.finRange q_w).filter fun i => decide (i ≠ p ∧ u i ≠ v i)).length ≤ q_w - 1 := by
  let L : List (Fin q_w) := (List.finRange q_w).filter fun i => decide (i ≠ p ∧ u i ≠ v i)
  have hnd : L.Nodup := (List.nodup_finRange q_w).filter _
  have hp_not : p ∉ L := by
    intro h
    simp only [L, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at h
    exact h.1 rfl
  rw [← List.toFinset_card_of_nodup hnd]
  have hsub : L.toFinset ⊆ Finset.univ.erase p := fun i hi => by
    rw [List.mem_toFinset] at hi
    exact Finset.mem_erase.mpr ⟨fun h => hp_not (h ▸ hi), Finset.mem_univ _⟩
  have hle := Finset.card_le_card hsub
  rwa [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin] at hle

private lemma relabelCirc_size (q_w : ℕ) (p : Fin q_w) (u v : Qubits q_w) :
    (relabelCirc q_w p u v).size ≤ q_w := by
  dsimp only [relabelCirc]
  have hcard := relabelFilter_length_le q_w p u v
  have hp_pos := p.isLt
  simp only [LayeredCircuit.seq_size, cnotFanList_size]
  split_ifs <;> simp only [LayeredCircuit.id_size, pauliXGate_size] <;> omega

private lemma relabelCirc_depth (q_w : ℕ) (p : Fin q_w) (u v : Qubits q_w) :
    (relabelCirc q_w p u v).depth ≤ q_w := by
  dsimp only [relabelCirc]
  have hcard := relabelFilter_length_le q_w p u v
  have hp_pos := p.isLt
  simp only [LayeredCircuit.seq_depth, cnotFanList_depth]
  split_ifs <;> simp only [LayeredCircuit.id_depth, pauliXGate_depth] <;> omega

private lemma act_relabelCirc_ket (q_w : ℕ) (p : Fin q_w) (u v x : Qubits q_w) :
    act (relabelCirc q_w p u v).unitary (ket x) = ket (relabelFn q_w p u v x) := by
  dsimp only [relabelCirc]
  let L : List (Fin q_w) := (List.finRange q_w).filter fun i => decide (i ≠ p ∧ u i ≠ v i)
  have hnd : L.Nodup := (List.nodup_finRange q_w).filter _
  simp only [LayeredCircuit.seq_unitary, act_mul]
  rw [act_cnotFanList_ket q_w p L _ hnd x]
  let x1 : Qubits q_w := fun w => if w ∈ L then xor (x w) (x p) else x w
  have hx1_def : (fun w => if w ∈ L then xor (x w) (x p) else x w) = x1 := rfl
  rw [hx1_def]
  have hx1_p : x1 p = x p := by
    have hp : p ∉ L := by simp [L]
    dsimp only [x1]; rw [if_neg hp]
  have hx1_ne : ∀ w : Fin q_w, w ≠ p → x1 w = if u w ≠ v w then xor (x w) (x p) else x w := by
    intro w hwp
    have hmem : w ∈ L ↔ u w ≠ v w := by simp [L, hwp]
    dsimp only [x1]
    by_cases huv : u w ≠ v w
    · rw [if_pos (hmem.mpr huv), if_pos huv]
    · rw [if_neg (mt hmem.mp huv), if_neg huv]
  cases hup : u p
  · simp only [Bool.false_eq_true, ↓reduceIte, LayeredCircuit.id_unitary, act_one]
    congr 1; funext w
    dsimp only [relabelFn]
    by_cases hwp : w = p
    · rw [hwp, if_pos rfl, hx1_p, hup, Bool.xor_false]
    · rw [if_neg hwp, hx1_ne w hwp]
  · simp only [↓reduceIte]
    rw [act_pauliXGate_ket]
    congr 1; funext w
    dsimp only [relabelFn]
    by_cases hwp : w = p
    · rw [hwp, Function.update_self, if_pos rfl, hx1_p, hup]; simp
    · rw [Function.update_of_ne hwp, if_neg hwp, hx1_ne w hwp]

private lemma relabelFn_u_p (q_w : ℕ) (p : Fin q_w) (u v : Qubits q_w) :
    relabelFn q_w p u v u p = false := by
  dsimp only [relabelFn]; rw [if_pos rfl, Bool.xor_self]

private lemma relabelFn_v_p (q_w : ℕ) (p : Fin q_w) (u v : Qubits q_w) (hp : u p ≠ v p) :
    relabelFn q_w p u v v p = true := by
  dsimp only [relabelFn]; rw [if_pos rfl]
  cases hu : u p <;> cases hv : v p <;> simp_all

private lemma relabelFn_u_eq_v (q_w : ℕ) (p : Fin q_w) (u v : Qubits q_w) (hp : u p ≠ v p)
    (w : Fin q_w) (hw : w ≠ p) :
    relabelFn q_w p u v u w = relabelFn q_w p u v v w := by
  dsimp only [relabelFn]
  rw [if_neg hw, if_neg hw]
  by_cases huv : u w ≠ v w
  · rw [if_pos huv, if_pos huv]
    cases huw : u w <;> cases hvw : v w <;> cases hup : u p <;> cases hvp : v p <;> simp_all
  · rw [if_neg huv, if_neg huv]
    exact not_not.mp huv

private lemma relabelFn_inj (q_w : ℕ) (p : Fin q_w) (u v : Qubits q_w) :
    Function.Injective (relabelFn q_w p u v) := by
  intro x₁ x₂ h
  have hp_eq : xor (x₁ p) (u p) = xor (x₂ p) (u p) := by
    have := congrFun h p
    simpa [relabelFn] using this
  have hxp : x₁ p = x₂ p := by
    cases hx1 : x₁ p <;> cases hx2 : x₂ p <;> cases hup : u p <;> simp_all
  funext w
  by_cases hw : w = p
  · subst hw; exact hxp
  · have hwe := congrFun h w
    dsimp only [relabelFn] at hwe
    rw [if_neg hw, if_neg hw] at hwe
    by_cases huv : u w ≠ v w
    · rw [if_pos huv, if_pos huv, hxp] at hwe
      cases hx1 : x₁ w <;> cases hx2 : x₂ w <;> cases hxp2 : x₂ p <;> simp_all
    · rw [if_neg huv, if_neg huv] at hwe
      exact hwe

private lemma relabelFn_ne_pat {q_w : ℕ} (p : Fin q_w) (u v : Qubits q_w) (hp : u p ≠ v p)
    (x : Qubits q_w) (hxu : x ≠ u) (hxv : x ≠ v) :
    ¬ ∀ i : Fin (q_w - 1),
      relabelFn q_w p u v x (skipWire q_w p i) = relabelFn q_w p u v u (skipWire q_w p i) := by
  intro hall
  have hoff : ∀ w : Fin q_w, w ≠ p → relabelFn q_w p u v x w = relabelFn q_w p u v u w := by
    intro w hw
    rcases exists_skipWire_eq p w hw with ⟨i, rfl⟩
    exact hall i
  cases hx : relabelFn q_w p u v x p
  · apply hxu
    apply relabelFn_inj q_w p u v
    funext w
    by_cases hw : w = p
    · rw [hw, hx, relabelFn_u_p]
    · exact hoff w hw
  · apply hxv
    apply relabelFn_inj q_w p u v
    funext w
    by_cases hw : w = p
    · rw [hw, hx, relabelFn_v_p q_w p u v hp]
    · rw [hoff w hw, relabelFn_u_eq_v q_w p u v hp w hw]

private def twoLevelEqWire (q_w : ℕ) (p : Fin q_w)
    (w : Fin ((q_w - 1) + 1 + (q_w - 1))) : Fin (q_w + q_w) :=
  if h1 : w.1 < q_w - 1 then
    Fin.castAdd q_w (skipWire q_w p ⟨w.1, h1⟩)
  else if _ : w.1 = q_w - 1 then
    Fin.castAdd q_w p
  else
    Fin.natAdd q_w ⟨w.1 - ((q_w - 1) + 1), by have := w.isLt; have := p.isLt; omega⟩

private lemma twoLevelEqWire_lt (q_w : ℕ) (p : Fin q_w)
    (w : Fin ((q_w - 1) + 1 + (q_w - 1))) (h : w.1 < q_w - 1) :
    twoLevelEqWire q_w p w = Fin.castAdd q_w (skipWire q_w p ⟨w.1, h⟩) := by
  dsimp only [twoLevelEqWire]; rw [dif_pos h]

private lemma twoLevelEqWire_eq (q_w : ℕ) (p : Fin q_w)
    (w : Fin ((q_w - 1) + 1 + (q_w - 1))) (h : w.1 = q_w - 1) :
    twoLevelEqWire q_w p w = Fin.castAdd q_w p := by
  dsimp only [twoLevelEqWire]; rw [dif_neg (by omega), dif_pos h]

private lemma twoLevelEqWire_gt (q_w : ℕ) (p : Fin q_w)
    (w : Fin ((q_w - 1) + 1 + (q_w - 1))) (h1 : ¬ w.1 < q_w - 1) (h2 : w.1 ≠ q_w - 1) :
    twoLevelEqWire q_w p w =
      Fin.natAdd q_w ⟨w.1 - ((q_w - 1) + 1), by have := w.isLt; have := p.isLt; omega⟩ := by
  dsimp only [twoLevelEqWire]; rw [dif_neg h1, dif_neg h2]

private def twoLevelEqEmb (q_w : ℕ) (p : Fin q_w) :
    Fin ((q_w - 1) + 1 + (q_w - 1)) ↪ Fin (q_w + q_w) where
  toFun := twoLevelEqWire q_w p
  inj' a b hab := by
    have ha := a.isLt; have hb := b.isLt; have hp := p.isLt
    change twoLevelEqWire q_w p a = twoLevelEqWire q_w p b at hab
    by_cases ha1 : a.1 < q_w - 1 <;> by_cases hb1 : b.1 < q_w - 1
    · rw [twoLevelEqWire_lt q_w p a ha1, twoLevelEqWire_lt q_w p b hb1] at hab
      have hval := congrArg Fin.val hab
      simp only [Fin.val_castAdd] at hval
      have hsw := (skipWire q_w p).injective (Fin.ext hval)
      exact Fin.ext (by simpa using congrArg Fin.val hsw)
    · by_cases hb2 : b.1 = q_w - 1
      · rw [twoLevelEqWire_lt q_w p a ha1, twoLevelEqWire_eq q_w p b hb2] at hab
        have hval := congrArg Fin.val hab
        simp only [Fin.val_castAdd] at hval
        exact absurd (Fin.ext hval) (skipWire_ne q_w p ⟨a.1, ha1⟩)
      · rw [twoLevelEqWire_lt q_w p a ha1, twoLevelEqWire_gt q_w p b hb1 hb2] at hab
        have hval := congrArg Fin.val hab
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
        have hlt := (skipWire q_w p ⟨a.1, ha1⟩).isLt
        omega
    · by_cases ha2 : a.1 = q_w - 1
      · rw [twoLevelEqWire_eq q_w p a ha2, twoLevelEqWire_lt q_w p b hb1] at hab
        have hval := congrArg Fin.val hab
        simp only [Fin.val_castAdd] at hval
        exact absurd (Fin.ext hval.symm) (skipWire_ne q_w p ⟨b.1, hb1⟩)
      · rw [twoLevelEqWire_gt q_w p a ha1 ha2, twoLevelEqWire_lt q_w p b hb1] at hab
        have hval := congrArg Fin.val hab
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
        have hlt := (skipWire q_w p ⟨b.1, hb1⟩).isLt
        omega
    · by_cases ha2 : a.1 = q_w - 1 <;> by_cases hb2 : b.1 = q_w - 1
      · exact Fin.ext (by omega)
      · rw [twoLevelEqWire_eq q_w p a ha2, twoLevelEqWire_gt q_w p b hb1 hb2] at hab
        have hval := congrArg Fin.val hab
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
        omega
      · rw [twoLevelEqWire_gt q_w p a ha1 ha2, twoLevelEqWire_eq q_w p b hb2] at hab
        have hval := congrArg Fin.val hab
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
        omega
      · rw [twoLevelEqWire_gt q_w p a ha1 ha2, twoLevelEqWire_gt q_w p b hb1 hb2] at hab
        have hval := congrArg Fin.val hab
        simp only [Fin.val_natAdd] at hval
        exact Fin.ext (by omega)

private lemma twoLevelEqEmb_apply (q_w : ℕ) (p : Fin q_w)
    (w : Fin ((q_w - 1) + 1 + (q_w - 1))) :
    twoLevelEqEmb q_w p w =
      if h1 : w.1 < q_w - 1 then
        Fin.castAdd q_w (skipWire q_w p ⟨w.1, h1⟩)
      else if _ : w.1 = q_w - 1 then
        Fin.castAdd q_w p
      else
        Fin.natAdd q_w ⟨w.1 - ((q_w - 1) + 1), by have := w.isLt; have := p.isLt; omega⟩ := rfl

private lemma twoLevelEqEmb_skip (q_w : ℕ) (p : Fin q_w) (i : Fin (q_w - 1)) :
    twoLevelEqEmb q_w p (Fin.castAdd (q_w - 1) ⟨i.1, by have := i.isLt; omega⟩) =
      Fin.castAdd q_w (skipWire q_w p i) := by
  have hi : (Fin.castAdd (q_w - 1) (⟨i.1, by have := i.isLt; omega⟩ : Fin ((q_w - 1) + 1))).1 <
      q_w - 1 := i.isLt
  rw [twoLevelEqEmb_apply, dif_pos hi]; rfl

private lemma twoLevelEqEmb_tgt (q_w : ℕ) (p : Fin q_w) :
    twoLevelEqEmb q_w p (Fin.castAdd (q_w - 1) ⟨q_w - 1, Nat.lt_succ_self _⟩) =
      Fin.castAdd q_w p := by
  rw [twoLevelEqEmb_apply, dif_neg (by simp), dif_pos (by simp)]

private lemma twoLevelEqEmb_anc (q_w : ℕ) (p : Fin q_w) (j : Fin (q_w - 1)) :
    twoLevelEqEmb q_w p (Fin.natAdd ((q_w - 1) + 1) j) =
      Fin.natAdd q_w ⟨j.1, by have := j.isLt; omega⟩ := by
  rw [twoLevelEqEmb_apply, dif_neg (by simp; omega), dif_neg (by simp; omega)]
  congr 1; exact Fin.ext (by simp)

noncomputable def twoLevelCtrlGate (q_w : ℕ) (u v : Qubits q_w) (huv : u ≠ v)
    (M2 : Matrix Bool Bool ℂ) (hM2 : M2 ∈ Matrix.unitaryGroup Bool ℂ) :
    LayeredCircuit (q_w + q_w) :=
  let p := Classical.choose (exists_coord_ne huv)
  let pat : Qubits (q_w - 1) := fun i => relabelFn q_w p u v u (skipWire q_w p i)
  let rel := (relabelCirc q_w p u v).mapWires (Fin.castAddEmb q_w)
  let mid := (multiEqCtrl1 (q_w - 1) pat M2 hM2).mapWires (twoLevelEqEmb q_w p)
  rel.seq (mid.seq rel.adj)

theorem twoLevelCtrlGate_size (q_w : ℕ) (u v : Qubits q_w) (huv : u ≠ v)
    (M2 : Matrix Bool Bool ℂ) (hM2 : M2 ∈ Matrix.unitaryGroup Bool ℂ) :
    (twoLevelCtrlGate q_w u v huv M2 hM2).size ≤ 14 * q_w := by
  dsimp only [twoLevelCtrlGate]
  have hp_pos : 1 ≤ q_w := by have := (Classical.choose (exists_coord_ne huv)).isLt; omega
  have h1 := relabelCirc_size q_w (Classical.choose (exists_coord_ne huv)) u v
  have h2 := multiEqCtrl1_size (q_w - 1)
    (fun i => relabelFn q_w (Classical.choose (exists_coord_ne huv)) u v u
      (skipWire q_w (Classical.choose (exists_coord_ne huv)) i)) M2 hM2
  simp only [LayeredCircuit.seq_size, LayeredCircuit.adj_size, LayeredCircuit.mapWires_size]
  omega

theorem twoLevelCtrlGate_depth (q_w : ℕ) (u v : Qubits q_w) (huv : u ≠ v)
    (M2 : Matrix Bool Bool ℂ) (hM2 : M2 ∈ Matrix.unitaryGroup Bool ℂ) :
    (twoLevelCtrlGate q_w u v huv M2 hM2).depth ≤ 2 * q_w + 10 * Nat.clog 2 q_w + 3 := by
  dsimp only [twoLevelCtrlGate]
  have hp_pos : 1 ≤ q_w := by have := (Classical.choose (exists_coord_ne huv)).isLt; omega
  have h1 := relabelCirc_depth q_w (Classical.choose (exists_coord_ne huv)) u v
  have h2 := multiEqCtrl1_depth (q_w - 1)
    (fun i => relabelFn q_w (Classical.choose (exists_coord_ne huv)) u v u
      (skipWire q_w (Classical.choose (exists_coord_ne huv)) i)) M2 hM2
  have hclog : Nat.clog 2 (q_w - 1 + 1) = Nat.clog 2 q_w :=
    congrArg (Nat.clog 2) (by omega)
  rw [hclog] at h2
  simp only [LayeredCircuit.seq_depth, LayeredCircuit.adj_depth, LayeredCircuit.mapWires_depth]
  omega

theorem twoLevelCtrlGate_depth_linear (q_w : ℕ) (u v : Qubits q_w) (huv : u ≠ v)
    (M2 : Matrix Bool Bool ℂ) (hM2 : M2 ∈ Matrix.unitaryGroup Bool ℂ) :
    (twoLevelCtrlGate q_w u v huv M2 hM2).depth ≤ 12 * q_w + 3 := by
  have hd := twoLevelCtrlGate_depth q_w u v huv M2 hM2
  have hc : Nat.clog 2 q_w ≤ q_w :=
    Nat.clog_le_iff_le_pow (by norm_num : 1 < 2) |>.mpr Nat.lt_two_pow_self.le
  omega

theorem twoLevelCtrlGate_implements (q_w : ℕ) (u v : Qubits q_w) (huv : u ≠ v)
    (M2 : Matrix Bool Bool ℂ) (hM2 : M2 ∈ Matrix.unitaryGroup Bool ℂ) :
    (twoLevelCtrlGate q_w u v huv M2 hM2).ImplementsOnClean (twoLevelMat q_w u v M2) := by
  classical
  apply implementsOnClean_of_act
  intro x
  let p := Classical.choose (exists_coord_ne huv)
  have hp : u p ≠ v p := Classical.choose_spec (exists_coord_ne huv)
  let pat : Qubits (q_w - 1) := fun i => relabelFn q_w p u v u (skipWire q_w p i)
  let rel := (relabelCirc q_w p u v).mapWires (Fin.castAddEmb q_w)
  let emb := twoLevelEqEmb q_w p
  let embMain : Fin ((q_w - 1) + 1) ↪ Fin (q_w + q_w) := (Fin.castAddEmb (q_w - 1)).trans emb
  let mid := (multiEqCtrl1 (q_w - 1) pat M2 hM2).mapWires emb
  have hrel_ket : ∀ y : Qubits q_w,
      act rel.unitary (ket (padZero q_w q_w y)) =
        ket (padZero q_w q_w (relabelFn q_w p u v y)) := fun y => by
    refine act_mapWires_ket (relabelCirc q_w p u v) (Fin.castAddEmb q_w)
      (padZero q_w q_w y) (relabelFn q_w p u v y) ?_ (padZero q_w q_w (relabelFn q_w p u v y)) ?_ ?_
    · have hcomp : padZero q_w q_w y ∘ Fin.castAddEmb q_w = y := by
        funext i; exact padZero_castAdd q_w q_w y i
      rw [hcomp]
      exact act_relabelCirc_ket q_w p u v y
    · funext i; exact padZero_castAdd q_w q_w _ i
    · intro w hw
      have hge : q_w ≤ w.1 := by
        by_contra hlt; apply hw
        exact ⟨⟨w.1, by omega⟩, Fin.ext rfl⟩
      have hnat : w = Fin.natAdd q_w ⟨w.1 - q_w, by have := w.isLt; omega⟩ := by
        ext; simp; omega
      rw [hnat, padZero_natAdd, padZero_natAdd]
  have hrel_adj : ∀ y : Qubits q_w,
      act rel.adj.unitary (ket (padZero q_w q_w (relabelFn q_w p u v y))) =
        ket (padZero q_w q_w y) := fun y => by
    rw [← hrel_ket y, ← act_mul, LayeredCircuit.adj_unitary,
      Matrix.mem_unitaryGroup_iff'.mp rel.unitary_mem_unitaryGroup, act_one]
  change act (rel.seq (mid.seq rel.adj)).unitary (ket (padZero q_w q_w x)) = _
  simp only [LayeredCircuit.seq_unitary, act_mul]
  rw [hrel_ket x]
  have hclean : ∀ j : Fin (q_w - 1),
      padZero q_w q_w (relabelFn q_w p u v x) (emb (Fin.natAdd ((q_w - 1) + 1) j)) = false := fun j => by
    have heq : emb (Fin.natAdd ((q_w - 1) + 1) j) = Fin.natAdd q_w ⟨j.1, by have := j.isLt; omega⟩ :=
      twoLevelEqEmb_anc q_w p j
    rw [heq, padZero_natAdd]
  have hmid := act_mapWires_implementsOnClean (multiEqCtrl1 (q_w - 1) pat M2 hM2)
    (eqCtrlMat (q_w - 1) pat M2) (multiEqCtrl1_implements (q_w - 1) pat M2 hM2) emb
    (padZero q_w q_w (relabelFn q_w p u v x)) hclean
  dsimp only at hmid
  change act mid.unitary (ket (padZero q_w q_w (relabelFn q_w p u v x))) = _ at hmid
  rw [hmid]
  let fx := relabelFn q_w p u v x
  let liftB : Bool → Qubits ((q_w - 1) + 1) := fun b i =>
    if hi : i.1 < q_w - 1 then fx (skipWire q_w p ⟨i.1, hi⟩) else b
  have hcomp_skip : ∀ i : Fin (q_w - 1),
      (padZero q_w q_w fx ∘ embMain) ⟨i.1, by omega⟩ = pat i ↔
        relabelFn q_w p u v x (skipWire q_w p i) = pat i := fun i => by
    change padZero q_w q_w fx (emb (Fin.castAdd (q_w - 1) ⟨i.1, by omega⟩)) = pat i ↔ _
    dsimp only [emb]
    rw [twoLevelEqEmb_skip, padZero_castAdd]
  have hcomp_tgt : (padZero q_w q_w fx ∘ embMain) ⟨q_w - 1, Nat.lt_succ_self _⟩ = fx p := by
    change padZero q_w q_w fx (emb (Fin.castAdd (q_w - 1) ⟨q_w - 1, Nat.lt_succ_self _⟩)) = fx p
    dsimp only [emb]
    rw [twoLevelEqEmb_tgt, padZero_castAdd]
  have hsub : (∑ z' : Qubits ((q_w - 1) + 1),
        eqCtrlMat (q_w - 1) pat M2 z' (padZero q_w q_w fx ∘ embMain) •
          ket (updateOn embMain (padZero q_w q_w fx) z')) =
      ∑ z' ∈ Finset.univ.image liftB,
        eqCtrlMat (q_w - 1) pat M2 z' (padZero q_w q_w fx ∘ embMain) •
          ket (updateOn embMain (padZero q_w q_w fx) z') := by
    rw [← Finset.sum_subset (Finset.subset_univ _)]
    intro z' _ hz'
    simp only [eqCtrlMat, Matrix.of_apply]
    by_cases haddr : ∀ i : Fin (q_w - 1),
        z' ⟨i.1, by omega⟩ = (padZero q_w q_w fx ∘ embMain) ⟨i.1, by omega⟩
    · exfalso; apply hz'; rw [Finset.mem_image]
      refine ⟨z' ⟨q_w - 1, Nat.lt_succ_self _⟩, Finset.mem_univ _, ?_⟩
      funext k
      by_cases hk : k.1 < q_w - 1
      · dsimp only [liftB]; rw [dif_pos hk]
        have h1 := haddr ⟨k.1, hk⟩
        change z' k = padZero q_w q_w fx (emb (Fin.castAdd (q_w - 1) k)) at h1
        dsimp only [emb] at h1
        have heq : twoLevelEqEmb q_w p (Fin.castAdd (q_w - 1) k) =
            Fin.castAdd q_w (skipWire q_w p ⟨k.1, hk⟩) :=
          twoLevelEqEmb_skip q_w p ⟨k.1, hk⟩
        rw [heq, padZero_castAdd] at h1
        exact h1.symm
      · have hk_eq : k = ⟨q_w - 1, Nat.lt_succ_self _⟩ := by
          ext; change k.1 = q_w - 1; have := k.isLt; omega
        subst hk_eq
        dsimp only [liftB]; rw [dif_neg (lt_irrefl _)]
    · rw [if_neg haddr, zero_smul]
  rw [hsub, Finset.sum_image (fun b₁ _ b₂ _ h => by
    have := congrFun h ⟨q_w - 1, Nat.lt_succ_self _⟩
    simpa [liftB] using this)]
  have hsum_upd : ∀ b : Bool,
      updateOn embMain (padZero q_w q_w fx) (liftB b) =
        padZero q_w q_w (Function.update fx p b) := fun b => by
    funext w
    refine Fin.addCases (fun i => ?_) (fun j => ?_) w
    · rw [padZero_castAdd]
      by_cases hip : i = p
      · rw [hip]
        have heq : Fin.castAdd q_w p = embMain ⟨q_w - 1, Nat.lt_succ_self _⟩ := by
          change Fin.castAdd q_w p = emb (Fin.castAdd (q_w - 1) ⟨q_w - 1, Nat.lt_succ_self _⟩)
          exact (twoLevelEqEmb_tgt q_w p).symm
        rw [heq, updateOn_apply_emb, Function.update_self]
        dsimp only [liftB]; rw [dif_neg (lt_irrefl _)]
      · rcases exists_skipWire_eq p i hip with ⟨k, rfl⟩
        have heq : Fin.castAdd q_w (skipWire q_w p k) =
            embMain ⟨k.1, by have := k.isLt; omega⟩ := by
          change Fin.castAdd q_w (skipWire q_w p k) =
            emb (Fin.castAdd (q_w - 1) ⟨k.1, by have := k.isLt; omega⟩)
          exact (twoLevelEqEmb_skip q_w p k).symm
        rw [heq, updateOn_apply_emb, Function.update_of_ne hip]
        dsimp only [liftB]; rw [dif_pos k.isLt]
    · rw [padZero_natAdd]
      have hnot : Fin.natAdd q_w j ∉ Set.range embMain := by
        rintro ⟨k, hk⟩
        have hk_lt := k.isLt
        have hval := congrArg Fin.val hk
        change (twoLevelEqWire q_w p (Fin.castAdd (q_w - 1) k)).1 = q_w + j.1 at hval
        by_cases hk1 : k.1 < q_w - 1
        · rw [twoLevelEqWire_lt q_w p _ hk1] at hval
          simp only [Fin.val_castAdd] at hval
          have := (skipWire q_w p ⟨k.1, hk1⟩).isLt; omega
        · have hk2 : (Fin.castAdd (q_w - 1) k).1 = q_w - 1 := by
            simp only [Fin.val_castAdd]; omega
          rw [twoLevelEqWire_eq q_w p _ hk2] at hval
          simp only [Fin.val_castAdd] at hval
          have := p.isLt; omega
      rw [updateOn_apply_not_mem _ _ _ hnot, padZero_natAdd]
  have hsum_coef : ∀ b : Bool,
      eqCtrlMat (q_w - 1) pat M2 (liftB b) (padZero q_w q_w fx ∘ embMain) =
        if (∀ i : Fin (q_w - 1), fx (skipWire q_w p i) = pat i) then M2 b (fx p)
        else if b = fx p then 1 else 0 := fun b => by
    simp only [eqCtrlMat, Matrix.of_apply]
    have haddr : ∀ i : Fin (q_w - 1),
        liftB b ⟨i.1, by omega⟩ = (padZero q_w q_w fx ∘ embMain) ⟨i.1, by omega⟩ := fun i => by
      dsimp only [liftB]; rw [dif_pos i.isLt]
      change fx (skipWire q_w p i) =
        padZero q_w q_w fx (emb (Fin.castAdd (q_w - 1) ⟨i.1, by omega⟩))
      dsimp only [emb]
      rw [twoLevelEqEmb_skip, padZero_castAdd]
    rw [if_pos haddr]
    have hpat_eq : (∀ i : Fin (q_w - 1), (padZero q_w q_w fx ∘ embMain) ⟨i.1, by omega⟩ = pat i) ↔
        ∀ i : Fin (q_w - 1), fx (skipWire q_w p i) = pat i :=
      forall_congr' hcomp_skip
    have hb_eq : liftB b ⟨q_w - 1, Nat.lt_succ_self _⟩ = b := by
      dsimp only [liftB]; rw [dif_neg (lt_irrefl _)]
    rw [hb_eq, hcomp_tgt]
    by_cases hpat : ∀ i : Fin (q_w - 1), fx (skipWire q_w p i) = pat i
    · rw [if_pos (hpat_eq.mpr hpat), if_pos hpat]
    · rw [if_neg (mt hpat_eq.mp hpat), if_neg hpat]
  simp_rw [hsum_upd, hsum_coef, act_sum, act_smul]
  by_cases hxu : x = u
  · subst hxu
    have hpat : ∀ i : Fin (q_w - 1), fx (skipWire q_w p i) = pat i := fun _ => rfl
    have hfxp : fx p = false := relabelFn_u_p q_w p x v
    have hupd_f : Function.update fx p false = relabelFn q_w p x v x := by
      funext w
      by_cases hw : w = p
      · rw [hw, Function.update_self, relabelFn_u_p]
      · exact Function.update_of_ne hw _ _
    have hupd_t : Function.update fx p true = relabelFn q_w p x v v := by
      funext w
      by_cases hw : w = p
      · rw [hw, Function.update_self, relabelFn_v_p q_w p x v hp]
      · rw [Function.update_of_ne hw]; exact relabelFn_u_eq_v q_w p x v hp w hw
    simp_rw [if_pos hpat, hfxp]
    rw [Fintype.sum_bool, hupd_t, hupd_f, hrel_adj v, hrel_adj x]
    symm
    have hvu : v ≠ x := huv.symm
    have hsum_v : (∑ y ∈ Finset.univ.erase x,
          twoLevelMat q_w x v M2 y x • ket (padZero q_w q_w y)) =
        twoLevelMat q_w x v M2 v x • ket (padZero q_w q_w v) := by
      rw [Finset.sum_eq_single v]
      · intro y hy hne
        have hne' : y ≠ x := (Finset.mem_erase.mp hy).1
        simp only [twoLevelMat, Matrix.of_apply, hne', hne, false_and, ↓reduceIte, zero_smul]
      · intro h; exact absurd (Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ _⟩) h
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x), hsum_v]
    simp only [twoLevelMat, Matrix.of_apply, hvu, and_self, ↓reduceIte, false_and]
  · by_cases hxv : x = v
    · subst hxv
      have hpat : ∀ i : Fin (q_w - 1), fx (skipWire q_w p i) = pat i := fun i =>
        (relabelFn_u_eq_v q_w p u x hp (skipWire q_w p i) (skipWire_ne q_w p i)).symm
      have hfxp : fx p = true := relabelFn_v_p q_w p u x hp
      have hupd_f : Function.update fx p false = relabelFn q_w p u x u := by
        funext w
        by_cases hw : w = p
        · rw [hw, Function.update_self, relabelFn_u_p]
        · rw [Function.update_of_ne hw]
          exact (relabelFn_u_eq_v q_w p u x hp w hw).symm
      have hupd_t : Function.update fx p true = relabelFn q_w p u x x := by
        funext w
        by_cases hw : w = p
        · rw [hw, Function.update_self, relabelFn_v_p q_w p u x hp]
        · exact Function.update_of_ne hw _ _
      simp_rw [if_pos hpat, hfxp]
      rw [Fintype.sum_bool, hupd_t, hupd_f, hrel_adj x, hrel_adj u]
      symm
      have hsum_x : (∑ y ∈ Finset.univ.erase u,
            twoLevelMat q_w u x M2 y x • ket (padZero q_w q_w y)) =
          twoLevelMat q_w u x M2 x x • ket (padZero q_w q_w x) := by
        rw [Finset.sum_eq_single x]
        · intro y hy hne
          have hne' : y ≠ u := (Finset.mem_erase.mp hy).1
          simp only [twoLevelMat, Matrix.of_apply, hne', hne, false_and, ↓reduceIte, zero_smul]
        · intro h; exact absurd (Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ _⟩) h
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ u), hsum_x]
      simp only [twoLevelMat, Matrix.of_apply, huv, huv.symm, and_self, ↓reduceIte, false_and,
        and_false]
    · have hpat : ¬ ∀ i : Fin (q_w - 1), fx (skipWire q_w p i) = pat i :=
        relabelFn_ne_pat p u v hp x hxu hxv
      simp_rw [if_neg hpat]
      rw [Finset.sum_eq_single (fx p)]
      · rw [if_pos rfl, one_smul]
        have hupd : Function.update fx p (fx p) = fx := Function.update_eq_self _ _
        rw [hupd]
        change act rel.adj.unitary (ket (padZero q_w q_w (relabelFn q_w p u v x))) = _
        rw [hrel_adj x]
        symm
        rw [Finset.sum_eq_single x]
        · simp [twoLevelMat, hxu, hxv]
        · intro y _ hy
          simp [twoLevelMat, hy, hxu, hxv]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro b _ hb
        rw [if_neg hb, zero_smul]
      · intro h; exact absurd (Finset.mem_univ _) h

noncomputable def ctrlTwoLevelGate (q_w : ℕ) (u v : Qubits q_w) (huv : u ≠ v)
    (M2 : Matrix Bool Bool ℂ) (hM2 : M2 ∈ Matrix.unitaryGroup Bool ℂ) :
    LayeredCircuit ((1 + q_w) + (1 + q_w)) :=
  twoLevelCtrlGate (1 + q_w) (boolCons true u) (boolCons true v)
    (fun h => huv (boolCons_inj true h)) M2 hM2

theorem ctrlTwoLevelGate_size (q_w : ℕ) (u v : Qubits q_w) (huv : u ≠ v)
    (M2 : Matrix Bool Bool ℂ) (hM2 : M2 ∈ Matrix.unitaryGroup Bool ℂ) :
    (ctrlTwoLevelGate q_w u v huv M2 hM2).size ≤ 14 * (q_w + 1) := by
  have h := twoLevelCtrlGate_size (1 + q_w) (boolCons true u) (boolCons true v)
    (fun h => huv (boolCons_inj true h)) M2 hM2
  change (ctrlTwoLevelGate q_w u v huv M2 hM2).size ≤ 14 * (1 + q_w) at h
  omega

theorem ctrlTwoLevelGate_depth (q_w : ℕ) (u v : Qubits q_w) (huv : u ≠ v)
    (M2 : Matrix Bool Bool ℂ) (hM2 : M2 ∈ Matrix.unitaryGroup Bool ℂ) :
    (ctrlTwoLevelGate q_w u v huv M2 hM2).depth ≤ 2 * (q_w + 1) + 10 * Nat.clog 2 (q_w + 1) + 3 := by
  have h := twoLevelCtrlGate_depth (1 + q_w) (boolCons true u) (boolCons true v)
    (fun h => huv (boolCons_inj true h)) M2 hM2
  change (ctrlTwoLevelGate q_w u v huv M2 hM2).depth ≤
    2 * (1 + q_w) + 10 * Nat.clog 2 (1 + q_w) + 3 at h
  have hclog : Nat.clog 2 (1 + q_w) = Nat.clog 2 (q_w + 1) := congrArg (Nat.clog 2) (Nat.add_comm 1 q_w)
  omega

theorem ctrlTwoLevelGate_depth_linear (q_w : ℕ) (u v : Qubits q_w) (huv : u ≠ v)
    (M2 : Matrix Bool Bool ℂ) (hM2 : M2 ∈ Matrix.unitaryGroup Bool ℂ) :
    (ctrlTwoLevelGate q_w u v huv M2 hM2).depth ≤ 12 * (q_w + 1) + 3 := by
  have h := twoLevelCtrlGate_depth_linear (1 + q_w) (boolCons true u) (boolCons true v)
    (fun h => huv (boolCons_inj true h)) M2 hM2
  change (ctrlTwoLevelGate q_w u v huv M2 hM2).depth ≤ 12 * (1 + q_w) + 3 at h
  omega

theorem ctrlTwoLevelGate_implements (q_w : ℕ) (u v : Qubits q_w) (huv : u ≠ v)
    (M2 : Matrix Bool Bool ℂ) (hM2 : M2 ∈ Matrix.unitaryGroup Bool ℂ) :
    (ctrlTwoLevelGate q_w u v huv M2 hM2).ImplementsOnClean
      (ctrlBlockMat (twoLevelMat q_w u v M2)) := by
  rw [← twoLevelMat_boolCons_true]
  exact twoLevelCtrlGate_implements (1 + q_w) (boolCons true u) (boolCons true v)
    (fun h => huv (boolCons_inj true h)) M2 hM2

/-! ### 8. Ripple-Carry Comparison (`ltConstCircuit`) and Diagonal Sign Gates (`ltPhaseSignGate`, `u0DiagSignGate`) -/

private def ltPrefixSum {q_w : ℕ} (x : Qubits q_w) (m : ℕ) (hm : m ≤ q_w) : ℕ :=
  bitsToNatLSB (fun i : Fin m => x ⟨i.1, by omega⟩)

private lemma ltPrefixSum_zero {q_w : ℕ} (x : Qubits q_w) :
    ltPrefixSum x 0 (Nat.zero_le _) = 0 := by
  simp [ltPrefixSum, bitsToNatLSB]

private lemma ltPrefixSum_lt {q_w : ℕ} (x : Qubits q_w) (m : ℕ) (hm : m ≤ q_w) :
    ltPrefixSum x m hm < 2 ^ m :=
  bitsToNatLSB_lt m _

private lemma ltPrefixSum_succ {q_w : ℕ} (x : Qubits q_w) (m : ℕ) (hm : m + 1 ≤ q_w) :
    ltPrefixSum x (m + 1) hm =
      ltPrefixSum x m (by omega) + if x ⟨m, hm⟩ then 2 ^ m else 0 := by
  dsimp only [ltPrefixSum, bitsToNatLSB]
  rw [Fin.sum_univ_castSucc]
  rfl

private lemma mod_two_pow_succ (H m : ℕ) :
    H % 2 ^ (m + 1) = H % 2 ^ m + (if H.testBit m then 2 ^ m else 0) := by
  have h2m : 0 < 2 ^ m := Nat.two_pow_pos m
  have hpow : 2 ^ (m + 1) = 2 ^ m * 2 := pow_succ 2 m
  let q := H / 2 ^ m
  let r := H % 2 ^ m
  have hr : r < 2 ^ m := Nat.mod_lt H h2m
  have hH : H = q * 2 ^ m + r := by
    dsimp only [q, r]; rw [mul_comm, Nat.div_add_mod]
  have hq : q = (q / 2) * 2 + q % 2 := by rw [mul_comm, Nat.div_add_mod]
  have hH' : H = (q / 2) * 2 ^ (m + 1) + (2 ^ m * (q % 2) + r) := by
    calc H = q * 2 ^ m + r := hH
      _ = ((q / 2) * 2 + q % 2) * 2 ^ m + r := by rw [← hq]
      _ = (q / 2) * (2 ^ m * 2) + (2 ^ m * (q % 2) + r) := by ring
      _ = (q / 2) * 2 ^ (m + 1) + (2 ^ m * (q % 2) + r) := by rw [hpow]
  have hrem_lt : 2 ^ m * (q % 2) + r < 2 ^ (m + 1) := by
    have hq2 : q % 2 < 2 := Nat.mod_lt q (by norm_num)
    rw [hpow]; nlinarith
  have hmod : H % 2 ^ (m + 1) = 2 ^ m * (q % 2) + r := by
    conv_lhs => rw [hH']
    exact mul_add_mod_right (q / 2) (2 ^ m * (q % 2) + r) (2 ^ (m + 1)) hrem_lt
  rw [hmod, Nat.testBit_eq_decide_div_mod_eq]
  have hq2 : q % 2 < 2 := Nat.mod_lt q (by norm_num)
  change 2 ^ m * (q % 2) + r = r + (if decide (q % 2 = 1) = true then 2 ^ m else 0)
  rcases (by omega : q % 2 = 0 ∨ q % 2 = 1) with h0 | h1
  · simp [h0]
  · simp [h1, add_comm]

private lemma lt_step_zero_eval {q_w : ℕ} (H : ℕ) (x : Qubits q_w) (hq : 0 < q_w) :
    decide (ltPrefixSum x 1 hq < H % 2 ^ 1) = (H.testBit 0 && !x ⟨0, hq⟩) := by
  have hsum : ltPrefixSum x 1 hq = if x ⟨0, hq⟩ then 1 else 0 := by
    rw [ltPrefixSum_succ x 0 hq, ltPrefixSum_zero, zero_add, pow_zero]
  have hH : H % 2 ^ 1 = if H.testBit 0 then 1 else 0 := by
    rw [mod_two_pow_succ H 0, pow_zero, Nat.mod_one, zero_add]
  rw [hsum, hH]
  cases H.testBit 0 <;> cases x ⟨0, hq⟩ <;> decide

private lemma lt_step_succ_eval {q_w : ℕ} (H : ℕ) (x : Qubits q_w) (m : ℕ) (hm : m + 2 ≤ q_w) :
    decide (ltPrefixSum x (m + 2) hm < H % 2 ^ (m + 2)) =
      if H.testBit (m + 1) then
        !(x ⟨m + 1, hm⟩ && !decide (ltPrefixSum x (m + 1) (by omega) < H % 2 ^ (m + 1)))
      else
        (!x ⟨m + 1, hm⟩ && decide (ltPrefixSum x (m + 1) (by omega) < H % 2 ^ (m + 1))) := by
  have hx_lt := ltPrefixSum_lt x (m + 1) (by omega)
  have hH_lt : H % 2 ^ (m + 1) < 2 ^ (m + 1) := Nat.mod_lt H (Nat.two_pow_pos _)
  rw [ltPrefixSum_succ x (m + 1) hm, mod_two_pow_succ H (m + 1)]
  cases H.testBit (m + 1) <;> cases x ⟨m + 1, hm⟩ <;>
    by_cases hlt : ltPrefixSum x (m + 1) (by omega) < H % 2 ^ (m + 1) <;>
    simp [hlt] <;> omega

private def ltInWire (q_w : ℕ) (i : Fin q_w) : Fin (q_w + 1 + q_w) :=
  ⟨i.1, by omega⟩

private def ltOutWire (q_w : ℕ) : Fin (q_w + 1 + q_w) :=
  ⟨q_w, by omega⟩

private def ltBorrowWire (q_w : ℕ) (m : Fin q_w) : Fin (q_w + 1 + q_w) :=
  ⟨q_w + 1 + m.1, by have := m.isLt; omega⟩

private def ltSupport (q_w : ℕ) : Finset (Fin (q_w + 1 + q_w)) :=
  Finset.univ.filter fun w => w.1 ≠ q_w

private lemma mem_ltSupport_iff (q_w : ℕ) (w : Fin (q_w + 1 + q_w)) :
    w ∈ ltSupport q_w ↔ w.1 ≠ q_w := by
  simp [ltSupport]

private lemma ltOutWire_not_mem_ltSupport (q_w : ℕ) :
    ltOutWire q_w ∉ ltSupport q_w := by
  simp [ltSupport, ltOutWire]

private noncomputable def ltStep (q_w H : ℕ) (m : ℕ) (hm : m < q_w) :
    LayeredCircuit (q_w + 1 + q_w) :=
  match m with
  | 0 =>
    let x0 := ltInWire q_w ⟨0, hm⟩
    let b0 := ltBorrowWire q_w ⟨0, hm⟩
    have hxb : x0 ≠ b0 := by
      intro h; have := congrArg Fin.val h; dsimp [x0, b0, ltInWire, ltBorrowWire] at this; omega
    if H.testBit 0 then (pauliXGate b0).seq (cnotGate x0 b0 hxb)
    else LayeredCircuit.id (q_w + 1 + q_w)
  | m' + 1 =>
    let xm := ltInWire q_w ⟨m' + 1, hm⟩
    let bm := ltBorrowWire q_w ⟨m', by omega⟩
    let bm1 := ltBorrowWire q_w ⟨m' + 1, hm⟩
    have h12 : xm ≠ bm := by
      intro h; have := congrArg Fin.val h; dsimp [xm, bm, ltInWire, ltBorrowWire] at this; omega
    have h13 : xm ≠ bm1 := by
      intro h; have := congrArg Fin.val h; dsimp [xm, bm1, ltInWire, ltBorrowWire] at this; omega
    have h23 : bm ≠ bm1 := by
      intro h; have := congrArg Fin.val h; dsimp [bm, bm1, ltBorrowWire] at this; omega
    if H.testBit (m' + 1) then
      (pauliXGate bm).seq ((toffoliOn xm bm bm1 h12 h13 h23).seq
        ((pauliXGate bm).seq (pauliXGate bm1)))
    else
      (pauliXGate xm).seq ((toffoliOn xm bm bm1 h12 h13 h23).seq (pauliXGate xm))

private lemma ltStep_size (q_w H m : ℕ) (hm : m < q_w) :
    (ltStep q_w H m hm).size ≤ 8 := by
  cases m <;> dsimp only [ltStep] <;> split_ifs <;> simp

private lemma ltStep_depth (q_w H m : ℕ) (hm : m < q_w) :
    (ltStep q_w H m hm).depth ≤ 8 := by
  cases m <;> dsimp only [ltStep] <;> split_ifs <;> simp

private lemma ltStep_usesOnly (q_w H m : ℕ) (hm : m < q_w) :
    (ltStep q_w H m hm).UsesOnly (ltSupport q_w) := by
  cases m <;> dsimp only [ltStep]
  · split_ifs
    · refine LayeredCircuit.seq_usesOnly
        ((pauliXGate_usesOnly _).mono fun w hw => ?_)
        ((cnotGate_usesOnly _ _ _).mono fun w hw => ?_)
      · rw [Finset.mem_singleton] at hw; rw [hw, mem_ltSupport_iff]; dsimp [ltBorrowWire]; omega
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rw [mem_ltSupport_iff]
        rcases hw with rfl | rfl <;> [dsimp [ltInWire]; dsimp [ltBorrowWire]] <;> omega
    · exact LayeredCircuit.id_usesOnly _
  · split_ifs
    · refine LayeredCircuit.seq_usesOnly ((pauliXGate_usesOnly _).mono fun w hw => ?_)
        (LayeredCircuit.seq_usesOnly ((toffoliOn_usesOnly _ _ _ _ _ _).mono fun w hw => ?_)
          (LayeredCircuit.seq_usesOnly ((pauliXGate_usesOnly _).mono fun w hw => ?_)
            ((pauliXGate_usesOnly _).mono fun w hw => ?_)))
      · rw [Finset.mem_singleton] at hw; rw [hw, mem_ltSupport_iff]; dsimp [ltBorrowWire]; omega
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rw [mem_ltSupport_iff]
        rcases hw with rfl | rfl | rfl <;> [dsimp [ltInWire]; dsimp [ltBorrowWire]; dsimp [ltBorrowWire]] <;> omega
      · rw [Finset.mem_singleton] at hw; rw [hw, mem_ltSupport_iff]; dsimp [ltBorrowWire]; omega
      · rw [Finset.mem_singleton] at hw; rw [hw, mem_ltSupport_iff]; dsimp [ltBorrowWire]; omega
    · refine LayeredCircuit.seq_usesOnly ((pauliXGate_usesOnly _).mono fun w hw => ?_)
        (LayeredCircuit.seq_usesOnly ((toffoliOn_usesOnly _ _ _ _ _ _).mono fun w hw => ?_)
          ((pauliXGate_usesOnly _).mono fun w hw => ?_))
      · rw [Finset.mem_singleton] at hw; rw [hw, mem_ltSupport_iff]; dsimp [ltInWire]; omega
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rw [mem_ltSupport_iff]
        rcases hw with rfl | rfl | rfl <;> [dsimp [ltInWire]; dsimp [ltBorrowWire]; dsimp [ltBorrowWire]] <;> omega
      · rw [Finset.mem_singleton] at hw; rw [hw, mem_ltSupport_iff]; dsimp [ltInWire]; omega

private lemma act_ltStep_zero_ket (q_w H : ℕ) (hq : 0 < q_w) (z : Qubits (q_w + 1 + q_w))
    (hclean : z (ltBorrowWire q_w ⟨0, hq⟩) = false) :
    act (ltStep q_w H 0 hq).unitary (ket z) =
      ket (Function.update z (ltBorrowWire q_w ⟨0, hq⟩)
        (H.testBit 0 && !z (ltInWire q_w ⟨0, hq⟩))) := by
  dsimp only [ltStep]
  let x0 := ltInWire q_w ⟨0, hq⟩
  let b0 := ltBorrowWire q_w ⟨0, hq⟩
  have hxb : x0 ≠ b0 := by
    intro h; have := congrArg Fin.val h; dsimp [x0, b0, ltInWire, ltBorrowWire] at this; omega
  cases hb : H.testBit 0
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, LayeredCircuit.id_unitary, act_one]
    congr 1; funext w
    by_cases hw : w = b0
    · rw [hw, Function.update_self]; exact hclean
    · rw [Function.update_of_ne hw]
  · simp only [↓reduceIte, Bool.true_and, LayeredCircuit.seq_unitary, act_mul,
      act_pauliXGate_ket, act_cnotGate_ket]
    congr 1; funext w
    dsimp only [x0, b0] at hclean hxb ⊢
    by_cases hw : w = ltBorrowWire q_w ⟨0, hq⟩
    · subst hw
      simp only [Function.update_self, Function.update_of_ne hxb, hclean, Bool.not_false,
        Bool.true_xor]
    · rw [Function.update_of_ne hw, Function.update_of_ne hw, Function.update_of_ne hw]

private lemma act_ltStep_succ_ket (q_w H m' : ℕ) (hm : m' + 1 < q_w) (z : Qubits (q_w + 1 + q_w))
    (hclean : z (ltBorrowWire q_w ⟨m' + 1, hm⟩) = false) :
    let xm := ltInWire q_w ⟨m' + 1, hm⟩
    let bm := ltBorrowWire q_w ⟨m', by omega⟩
    let bm1 := ltBorrowWire q_w ⟨m' + 1, hm⟩
    act (ltStep q_w H (m' + 1) hm).unitary (ket z) =
      ket (Function.update z bm1
        (if H.testBit (m' + 1) then !(z xm && !z bm) else (!z xm && z bm))) := by
  dsimp only [ltStep]
  let xm := ltInWire q_w ⟨m' + 1, hm⟩
  let bm := ltBorrowWire q_w ⟨m', by omega⟩
  let bm1 := ltBorrowWire q_w ⟨m' + 1, hm⟩
  have h12 : xm ≠ bm := by
    intro h; have := congrArg Fin.val h; dsimp [xm, bm, ltInWire, ltBorrowWire] at this; omega
  have h13 : xm ≠ bm1 := by
    intro h; have := congrArg Fin.val h; dsimp [xm, bm1, ltInWire, ltBorrowWire] at this; omega
  have h23 : bm ≠ bm1 := by
    intro h; have := congrArg Fin.val h; dsimp [bm, bm1, ltBorrowWire] at this; omega
  cases hb : H.testBit (m' + 1)
  · simp only [Bool.false_eq_true, ↓reduceIte, LayeredCircuit.seq_unitary, act_mul,
      act_pauliXGate_ket, act_toffoliOn_ket]
    congr 1; funext w
    dsimp only [xm, bm, bm1] at hclean h12 h13 h23 ⊢
    by_cases hw1 : w = ltBorrowWire q_w ⟨m' + 1, hm⟩
    · subst hw1
      simp only [Function.update_self, Function.update_of_ne h13.symm,
        Function.update_of_ne h12.symm, hclean, Bool.false_xor]
    · by_cases hw2 : w = ltInWire q_w ⟨m' + 1, hm⟩
      · subst hw2
        simp only [Function.update_self, Function.update_of_ne h13, Bool.not_not]
      · simp only [Function.update_of_ne hw1, Function.update_of_ne hw2]
  · simp only [↓reduceIte, LayeredCircuit.seq_unitary, act_mul,
      act_pauliXGate_ket, act_toffoliOn_ket]
    congr 1; funext w
    dsimp only [xm, bm, bm1] at hclean h12 h13 h23 ⊢
    by_cases hw1 : w = ltBorrowWire q_w ⟨m' + 1, hm⟩
    · subst hw1
      simp only [Function.update_self, Function.update_of_ne h23.symm,
        Function.update_of_ne h12, hclean, Bool.false_xor]
    · by_cases hw2 : w = ltBorrowWire q_w ⟨m', by omega⟩
      · subst hw2
        simp only [Function.update_of_ne h23, Function.update_self, Bool.not_not]
      · simp only [Function.update_of_ne hw1, Function.update_of_ne hw2]

private noncomputable def ltRipplePrefix (q_w H : ℕ) :
    (k : ℕ) → k ≤ q_w → LayeredCircuit (q_w + 1 + q_w)
  | 0, _ => LayeredCircuit.id (q_w + 1 + q_w)
  | k + 1, hk => (ltRipplePrefix q_w H k (by omega)).seq (ltStep q_w H k hk)

private lemma ltRipplePrefix_size (q_w H k : ℕ) (hk : k ≤ q_w) :
    (ltRipplePrefix q_w H k hk).size ≤ 8 * k := by
  induction k with
  | zero => simp [ltRipplePrefix]
  | succ k ih =>
    simp only [ltRipplePrefix, LayeredCircuit.seq_size]
    have h1 := ih (by omega)
    have h2 := ltStep_size q_w H k hk
    omega

private lemma ltRipplePrefix_depth (q_w H k : ℕ) (hk : k ≤ q_w) :
    (ltRipplePrefix q_w H k hk).depth ≤ 8 * k := by
  induction k with
  | zero => simp [ltRipplePrefix]
  | succ k ih =>
    simp only [ltRipplePrefix, LayeredCircuit.seq_depth]
    have h1 := ih (by omega)
    have h2 := ltStep_depth q_w H k hk
    omega

private lemma ltRipplePrefix_usesOnly (q_w H k : ℕ) (hk : k ≤ q_w) :
    (ltRipplePrefix q_w H k hk).UsesOnly (ltSupport q_w) := by
  induction k with
  | zero => exact LayeredCircuit.id_usesOnly _
  | succ k ih =>
    exact LayeredCircuit.seq_usesOnly (ih (by omega)) (ltStep_usesOnly q_w H k hk)

private lemma act_ltRipplePrefix_ket (q_w H : ℕ) (z : Qubits (q_w + 1 + q_w))
    (hclean : ∀ m : Fin q_w, z (ltBorrowWire q_w m) = false)
    (k : ℕ) (hk : k ≤ q_w) :
    ∃ z' : Qubits (q_w + 1 + q_w),
      act (ltRipplePrefix q_w H k hk).unitary (ket z) = ket z' ∧
      (∀ w : Fin (q_w + 1 + q_w), w.1 ≤ q_w → z' w = z w) ∧
      (∀ m : Fin q_w, k ≤ m.1 → z' (ltBorrowWire q_w m) = false) ∧
      (∀ hk1 : 1 ≤ k, z' (ltBorrowWire q_w ⟨k - 1, by omega⟩) =
        decide (ltPrefixSum (fun i : Fin q_w => z ⟨i.1, by omega⟩) k hk < H % 2 ^ k)) := by
  induction k with
  | zero =>
    refine ⟨z, by simp [ltRipplePrefix, LayeredCircuit.id_unitary, act_one],
      fun _ _ => rfl, fun m _ => hclean m, fun h => by omega⟩
  | succ k ih =>
    rcases ih (by omega) with ⟨z1, hz1_act, hz1_low, hz1_clean, hz1_top⟩
    let bNext := ltBorrowWire q_w ⟨k, hk⟩
    have hclean_k : z1 bNext = false := hz1_clean ⟨k, hk⟩ le_rfl
    cases k with
    | zero =>
      refine ⟨Function.update z1 bNext (H.testBit 0 && !z1 (ltInWire q_w ⟨0, hk⟩)), ?_, ?_, ?_, ?_⟩
      · change act ((ltRipplePrefix q_w H 0 (by omega)).seq (ltStep q_w H 0 hk)).unitary (ket z) = _
        rw [LayeredCircuit.seq_unitary, act_mul, hz1_act]
        exact act_ltStep_zero_ket q_w H hk z1 hclean_k
      · intro w hw
        have hne : w ≠ bNext := fun h => by
          have := congrArg Fin.val h; dsimp [bNext, ltBorrowWire] at this; omega
        rw [Function.update_of_ne hne, hz1_low w hw]
      · intro m hm
        have hne : ltBorrowWire q_w m ≠ bNext := fun h => by
          have := congrArg Fin.val h; dsimp [bNext, ltBorrowWire] at this; omega
        rw [Function.update_of_ne hne]
        exact hz1_clean m (by omega)
      · intro _
        rw [Function.update_self]
        have hx0 : z1 (ltInWire q_w ⟨0, hk⟩) = z ⟨0, by omega⟩ :=
          hz1_low _ (by dsimp [ltInWire]; omega)
        rw [hx0, ← lt_step_zero_eval H (fun i : Fin q_w => z ⟨i.1, by omega⟩) hk]
    | succ k' =>
      let xm := ltInWire q_w ⟨k' + 1, hk⟩
      let bm := ltBorrowWire q_w ⟨k', by omega⟩
      refine ⟨Function.update z1 bNext
          (if H.testBit (k' + 1) then !(z1 xm && !z1 bm) else (!z1 xm && z1 bm)), ?_, ?_, ?_, ?_⟩
      · change act ((ltRipplePrefix q_w H (k' + 1) (by omega)).seq
          (ltStep q_w H (k' + 1) hk)).unitary (ket z) = _
        rw [LayeredCircuit.seq_unitary, act_mul, hz1_act]
        exact act_ltStep_succ_ket q_w H k' hk z1 hclean_k
      · intro w hw
        have hne : w ≠ bNext := fun h => by
          have := congrArg Fin.val h; dsimp [bNext, ltBorrowWire] at this; omega
        rw [Function.update_of_ne hne, hz1_low w hw]
      · intro m hm
        have hne : ltBorrowWire q_w m ≠ bNext := fun h => by
          have := congrArg Fin.val h; dsimp [bNext, ltBorrowWire] at this; omega
        rw [Function.update_of_ne hne]
        exact hz1_clean m (by omega)
      · intro _
        have hidx : ltBorrowWire q_w ⟨k' + 1 + 1 - 1, by omega⟩ = bNext :=
          Fin.ext (by simp [bNext, ltBorrowWire])
        rw [hidx, Function.update_self]
        have hxm : z1 xm = z ⟨k' + 1, by omega⟩ := hz1_low xm (by dsimp [xm, ltInWire]; omega)
        have hbm : z1 bm = decide (ltPrefixSum (fun i : Fin q_w => z ⟨i.1, by omega⟩) (k' + 1) (by omega) <
            H % 2 ^ (k' + 1)) := hz1_top (by omega)
        rw [hxm, hbm]
        exact (lt_step_succ_eval H (fun i : Fin q_w => z ⟨i.1, by omega⟩) k' hk).symm

def ltOutMat (q_w H : ℕ) : Matrix (Qubits (q_w + 1)) (Qubits (q_w + 1)) ℂ :=
  permMat fun x =>
    Function.update x ⟨q_w, Nat.lt_succ_self q_w⟩
      (xor (x ⟨q_w, Nat.lt_succ_self q_w⟩)
        (decide (bitsToNatLSB (fun i : Fin q_w => x ⟨i.1, by omega⟩) < H)))

noncomputable def ltConstCircuit (q_w H : ℕ) : LayeredCircuit (q_w + 1 + q_w) :=
  if _ : 2 ^ q_w ≤ H then
    pauliXGate (ltOutWire q_w)
  else if hq : 1 ≤ q_w then
    let fwd := ltRipplePrefix q_w H q_w le_rfl
    let bLast := ltBorrowWire q_w ⟨q_w - 1, by omega⟩
    let out := ltOutWire q_w
    have hbo : bLast ≠ out := by
      intro h; have := congrArg Fin.val h; dsimp [bLast, out, ltBorrowWire, ltOutWire] at this; omega
    fwd.seq ((cnotGate bLast out hbo).seq fwd.adj)
  else
    LayeredCircuit.id (q_w + 1 + q_w)

theorem ltConstCircuit_size (q_w H : ℕ) :
    (ltConstCircuit q_w H).size ≤ 16 * q_w + 1 := by
  unfold ltConstCircuit
  split_ifs with hH hq
  · simp
  · simp only [LayeredCircuit.seq_size, LayeredCircuit.adj_size, cnotGate_size]
    have h1 := ltRipplePrefix_size q_w H q_w le_rfl
    omega
  · simp

theorem ltConstCircuit_depth (q_w H : ℕ) :
    (ltConstCircuit q_w H).depth ≤ 16 * q_w + 1 := by
  unfold ltConstCircuit
  split_ifs with hH hq
  · simp
  · simp only [LayeredCircuit.seq_depth, LayeredCircuit.adj_depth, cnotGate_depth]
    have h1 := ltRipplePrefix_depth q_w H q_w le_rfl
    omega
  · simp

theorem ltConstCircuit_implements (q_w H : ℕ) :
    (ltConstCircuit q_w H).ImplementsOnClean (ltOutMat q_w H) := by
  apply implementsOnClean_of_act_perm
  intro x
  by_cases hH : 2 ^ q_w ≤ H
  · simp only [ltConstCircuit, dif_pos hH]
    rw [act_pauliXGate_ket]
    congr 1; funext w
    have hlt_H : bitsToNatLSB (fun i : Fin q_w => x ⟨i.1, by omega⟩) < H :=
      Nat.lt_of_lt_of_le (bitsToNatLSB_lt q_w _) hH
    refine Fin.addCases (fun i => ?_) (fun j => ?_) w
    · rw [padZero_castAdd]
      by_cases hi : i.1 = q_w
      · have hi_eq : i = ⟨q_w, Nat.lt_succ_self q_w⟩ := Fin.ext hi
        subst hi_eq
        have heq : (Fin.castAdd q_w ⟨q_w, Nat.lt_succ_self q_w⟩ : Fin (q_w + 1 + q_w)) =
            ltOutWire q_w := Fin.ext rfl
        rw [heq, Function.update_self, Function.update_self, ← heq, padZero_castAdd]
        simp [hlt_H]
      · have hne : (Fin.castAdd q_w i : Fin (q_w + 1 + q_w)) ≠ ltOutWire q_w := fun h =>
          hi (congrArg Fin.val h)
        have hne' : i ≠ ⟨q_w, Nat.lt_succ_self q_w⟩ := fun h => hi (congrArg Fin.val h)
        rw [Function.update_of_ne hne, padZero_castAdd, Function.update_of_ne hne']
    · have hne : (Fin.natAdd (q_w + 1) j : Fin (q_w + 1 + q_w)) ≠ ltOutWire q_w := fun h => by
        have := congrArg Fin.val h; dsimp [ltOutWire] at this; omega
      rw [Function.update_of_ne hne, padZero_natAdd, padZero_natAdd]
  · have hH_lt : H < 2 ^ q_w := Nat.lt_of_not_le hH
    by_cases hq : 1 ≤ q_w
    · simp only [ltConstCircuit, dif_neg hH, dif_pos hq]
      let fwd := ltRipplePrefix q_w H q_w le_rfl
      let bLast := ltBorrowWire q_w ⟨q_w - 1, by omega⟩
      let out := ltOutWire q_w
      have hbo : bLast ≠ out := by
        intro h; have := congrArg Fin.val h; dsimp [bLast, out, ltBorrowWire, ltOutWire] at this; omega
      let z0 := padZero (q_w + 1) q_w x
      have hclean : ∀ m : Fin q_w, z0 (ltBorrowWire q_w m) = false := fun m => by
        have hnat : ltBorrowWire q_w m = Fin.natAdd (q_w + 1) m := Fin.ext rfl
        rw [hnat]; exact padZero_natAdd _ _ _ _
      rcases act_ltRipplePrefix_ket q_w H z0 hclean q_w le_rfl with
        ⟨z', hfwd_act, hz'_low, _, hz'_top⟩
      have hmod : H % 2 ^ q_w = H := Nat.mod_eq_of_lt hH_lt
      have hx_in : (fun i : Fin q_w => z0 ⟨i.1, by omega⟩) =
          fun i : Fin q_w => x ⟨i.1, by omega⟩ := by
        funext i
        change z0 (Fin.castAdd q_w ⟨i.1, by omega⟩) = _
        exact padZero_castAdd (q_w + 1) q_w x ⟨i.1, by omega⟩
      have htop_val : z' bLast =
          decide (bitsToNatLSB (fun i : Fin q_w => x ⟨i.1, by omega⟩) < H) := by
        have h := hz'_top hq
        rw [hmod, hx_in] at h
        exact h
      have hfwd_adj : ∀ b : Bool,
          act fwd.adj.unitary (ket (Function.update z' out b)) =
            ket (Function.update z0 out b) := fun b => by
        have hupd := act_ket_update_of_not_mem fwd (ltRipplePrefix_usesOnly q_w H q_w le_rfl)
          out (ltOutWire_not_mem_ltSupport q_w) hfwd_act b
        rw [← hupd, ← act_mul, LayeredCircuit.adj_unitary,
          Matrix.mem_unitaryGroup_iff'.mp fwd.unitary_mem_unitaryGroup, act_one]
      have hz'_out : z' out = x ⟨q_w, Nat.lt_succ_self q_w⟩ := by
        rw [hz'_low out (by dsimp [out, ltOutWire]; omega)]
        change z0 (Fin.castAdd q_w ⟨q_w, Nat.lt_succ_self q_w⟩) = _
        exact padZero_castAdd (q_w + 1) q_w x _
      simp only [LayeredCircuit.seq_unitary, act_mul]
      change act fwd.adj.unitary (act (cnotGate bLast out hbo).unitary (act fwd.unitary (ket z0))) = _
      rw [hfwd_act, act_cnotGate_ket, hfwd_adj, hz'_out, htop_val]
      congr 1; funext w
      refine Fin.addCases (fun i => ?_) (fun j => ?_) w
      · rw [padZero_castAdd]
        by_cases hi : i.1 = q_w
        · have hi_eq : i = ⟨q_w, Nat.lt_succ_self q_w⟩ := Fin.ext hi
          subst hi_eq
          have heq : (Fin.castAdd q_w ⟨q_w, Nat.lt_succ_self q_w⟩ : Fin (q_w + 1 + q_w)) = out :=
            Fin.ext rfl
          rw [heq, Function.update_self, Function.update_self]
        · have hne : (Fin.castAdd q_w i : Fin (q_w + 1 + q_w)) ≠ out := fun h =>
            hi (congrArg Fin.val h)
          have hne' : i ≠ ⟨q_w, Nat.lt_succ_self q_w⟩ := fun h => hi (congrArg Fin.val h)
          rw [Function.update_of_ne hne, Function.update_of_ne hne']
          exact padZero_castAdd (q_w + 1) q_w x i
      · have hne : (Fin.natAdd (q_w + 1) j : Fin (q_w + 1 + q_w)) ≠ out := fun h => by
          have := congrArg Fin.val h; dsimp [out, ltOutWire] at this; omega
        rw [Function.update_of_ne hne]
        exact (padZero_natAdd (q_w + 1) q_w x j).trans
          (padZero_natAdd (q_w + 1) q_w _ j).symm
    · have hq0 : q_w = 0 := by omega
      subst hq0
      have hH0 : H = 0 := by simp at hH_lt; exact hH_lt
      subst hH0
      simp only [ltConstCircuit, dif_neg hH, dif_neg (by decide : ¬ 1 ≤ 0),
        LayeredCircuit.id_unitary, act_one]
      congr 1; funext w
      refine Fin.addCases (fun i => ?_) (fun j => Fin.elim0 j) w
      have hi0 : i = ⟨0, Nat.lt_succ_self 0⟩ := Fin.ext (by omega)
      subst hi0
      rw [padZero_castAdd, padZero_castAdd, Function.update_self]
      simp [bitsToNatLSB]

/-! #### Generic Phase-Kickback Combinator & Diagonal Sign Gates -/

def diagPhaseMat {q_w : ℕ} (P : Qubits q_w → Bool) : Matrix (Qubits q_w) (Qubits q_w) ℂ :=
  Matrix.diagonal fun x => if P x then (-1 : ℂ) else 1

noncomputable def phaseGateOfFlag {q_w anc : ℕ} (flagCompute : LayeredCircuit (q_w + (1 + anc))) :
    LayeredCircuit (q_w + (1 + anc)) :=
  flagCompute.seq ((pauliZGate ⟨q_w, by omega⟩).seq flagCompute.adj)

lemma phaseGateOfFlag_size {q_w anc : ℕ} (flagCompute : LayeredCircuit (q_w + (1 + anc))) :
    (phaseGateOfFlag flagCompute).size = 2 * flagCompute.size + 1 := by
  simp [phaseGateOfFlag]; omega

lemma phaseGateOfFlag_depth {q_w anc : ℕ} (flagCompute : LayeredCircuit (q_w + (1 + anc))) :
    (phaseGateOfFlag flagCompute).depth = 2 * flagCompute.depth + 1 := by
  simp [phaseGateOfFlag]; omega

lemma phaseGateOfFlag_implements {q_w anc : ℕ}
    (flagCompute : LayeredCircuit (q_w + (1 + anc))) (P : Qubits q_w → Bool)
    (hcomp : ∀ x : Qubits q_w, ∃ z' : Qubits (q_w + (1 + anc)),
      act flagCompute.unitary (ket (padZero q_w (1 + anc) x)) = ket z' ∧
      z' ⟨q_w, by omega⟩ = P x) :
    (phaseGateOfFlag flagCompute).ImplementsOnClean (diagPhaseMat P) := by
  apply implementsOnClean_of_act
  intro x
  rcases hcomp x with ⟨z', hact, hz'_flag⟩
  have hclean_z' : act flagCompute.adj.unitary (ket z') = ket (padZero q_w (1 + anc) x) := by
    rw [← hact, ← act_mul, LayeredCircuit.adj_unitary,
      Matrix.mem_unitaryGroup_iff'.mp flagCompute.unitary_mem_unitaryGroup, act_one]
  dsimp only [phaseGateOfFlag]
  simp only [LayeredCircuit.seq_unitary, act_mul]
  rw [hact, act_pauliZGate_ket, act_smul, hclean_z', hz'_flag]
  symm
  rw [Finset.sum_eq_single x]
  · simp [diagPhaseMat]
  · intro y _ hy
    simp [diagPhaseMat, hy]
  · intro h; exact absurd (Finset.mem_univ _) h

private def liftCtrlEmb (q_w anc : ℕ) : Fin (q_w + (1 + anc)) ↪ Fin ((1 + q_w) + (1 + anc)) where
  toFun w := ⟨w.1 + 1, by have := w.isLt; omega⟩
  inj' a b h := Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)

@[simp] private lemma liftCtrlEmb_val (q_w anc : ℕ) (w : Fin (q_w + (1 + anc))) :
    (liftCtrlEmb q_w anc w).1 = w.1 + 1 := rfl

noncomputable def ctrlPhaseGateOfFlag {q_w anc : ℕ}
    (flagCompute : LayeredCircuit (q_w + (1 + anc))) :
    LayeredCircuit ((1 + q_w) + (1 + anc)) :=
  let fc := flagCompute.mapWires (liftCtrlEmb q_w anc)
  let cZ := ctrlGate1 pauliZ pauliZ_mem_unitaryGroup 0 ⟨1 + q_w, by omega⟩ (by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_zero] at this; omega)
  fc.seq (cZ.seq fc.adj)

lemma ctrlPhaseGateOfFlag_size {q_w anc : ℕ}
    (flagCompute : LayeredCircuit (q_w + (1 + anc))) :
    (ctrlPhaseGateOfFlag flagCompute).size = 2 * flagCompute.size + 1 := by
  simp [ctrlPhaseGateOfFlag]; omega

lemma ctrlPhaseGateOfFlag_depth {q_w anc : ℕ}
    (flagCompute : LayeredCircuit (q_w + (1 + anc))) :
    (ctrlPhaseGateOfFlag flagCompute).depth = 2 * flagCompute.depth + 1 := by
  simp [ctrlPhaseGateOfFlag]; omega

lemma ctrlPhaseGateOfFlag_implements {q_w anc : ℕ}
    (flagCompute : LayeredCircuit (q_w + (1 + anc))) (P : Qubits q_w → Bool)
    (hcomp : ∀ x : Qubits q_w, ∃ z' : Qubits (q_w + (1 + anc)),
      act flagCompute.unitary (ket (padZero q_w (1 + anc) x)) = ket z' ∧
      z' ⟨q_w, by omega⟩ = P x) :
    (ctrlPhaseGateOfFlag flagCompute).ImplementsOnClean (ctrlBlockMat (diagPhaseMat P)) := by
  apply implementsOnClean_of_act
  intro x
  let emb := liftCtrlEmb q_w anc
  let fc := flagCompute.mapWires emb
  let flagW : Fin ((1 + q_w) + (1 + anc)) := ⟨1 + q_w, by omega⟩
  have hc_ne : (0 : Fin ((1 + q_w) + (1 + anc))) ≠ flagW := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_zero, flagW] at this; omega
  let c0 : Bool := x 0
  let xTail : Qubits q_w := fun i => x (Fin.natAdd 1 i)
  have hx_comp : padZero (1 + q_w) (1 + anc) x ∘ emb = padZero q_w (1 + anc) xTail := by
    funext w
    refine Fin.addCases (fun i => ?_) (fun j => ?_) w
    · have heq : emb (Fin.castAdd (1 + anc) i) = Fin.castAdd (1 + anc) (Fin.natAdd 1 i) :=
        Fin.ext (by dsimp only [emb]; simp; omega)
      change padZero (1 + q_w) (1 + anc) x (emb (Fin.castAdd (1 + anc) i)) = _
      rw [heq, padZero_castAdd, padZero_castAdd]
    · have heq : emb (Fin.natAdd q_w j) = Fin.natAdd (1 + q_w) j :=
        Fin.ext (by dsimp only [emb]; simp; omega)
      change padZero (1 + q_w) (1 + anc) x (emb (Fin.natAdd q_w j)) = _
      rw [heq, padZero_natAdd, padZero_natAdd]
  rcases hcomp xTail with ⟨z', hz'_act, hz'_flag⟩
  let zCtrl : Qubits ((1 + q_w) + (1 + anc)) := fun w =>
    if hw : w.1 = 0 then c0 else z' ⟨w.1 - 1, by have := w.isLt; omega⟩
  have hfc_ket : act fc.unitary (ket (padZero (1 + q_w) (1 + anc) x)) = ket zCtrl := by
    refine act_mapWires_ket flagCompute emb (padZero (1 + q_w) (1 + anc) x) z'
      (by rwa [hx_comp]) zCtrl ?_ ?_
    · funext w
      dsimp only [zCtrl]
      have hne0 : (emb w).1 ≠ 0 := by dsimp only [emb]; simp
      rw [Function.comp_apply, dif_neg hne0]
      exact congrArg z' (Fin.ext rfl)
    · intro w hw
      have hw0 : w.1 = 0 := by
        by_contra hne0; apply hw
        refine ⟨⟨w.1 - 1, by have := w.isLt; omega⟩, Fin.ext ?_⟩
        dsimp only [emb]; rw [liftCtrlEmb_val]; dsimp; omega
      have hw_fin0 : w = 0 := Fin.ext hw0
      subst hw_fin0
      have hpad0 : padZero (1 + q_w) (1 + anc) x 0 = c0 := padZero_castAdd (1 + q_w) (1 + anc) x 0
      have h0val : (0 : Fin ((1 + q_w) + (1 + anc))).1 = 0 := rfl
      dsimp only [zCtrl]; rw [dif_pos h0val, hpad0]
  have hfc_adj : act fc.adj.unitary (ket zCtrl) = ket (padZero (1 + q_w) (1 + anc) x) := by
    rw [← hfc_ket, ← act_mul, LayeredCircuit.adj_unitary,
      Matrix.mem_unitaryGroup_iff'.mp fc.unitary_mem_unitaryGroup, act_one]
  dsimp only [ctrlPhaseGateOfFlag]
  simp only [LayeredCircuit.seq_unitary, act_mul]
  change act fc.adj.unitary (act (ctrlGate1 pauliZ pauliZ_mem_unitaryGroup 0 flagW hc_ne).unitary
    (act fc.unitary (ket (padZero (1 + q_w) (1 + anc) x)))) = _
  rw [hfc_ket, act_ctrlGate1_ket]
  have hzCtrl_0 : zCtrl 0 = c0 := by rfl
  have hzCtrl_flag : zCtrl flagW = P xTail := by
    dsimp only [zCtrl, flagW]
    rw [dif_neg (by omega)]
    have heq : (⟨1 + q_w - 1, by omega⟩ : Fin (q_w + (1 + anc))) = ⟨q_w, by omega⟩ :=
      Fin.ext (by simp)
    rw [heq, hz'_flag]
  rw [Finset.sum_eq_single (P xTail)]
  · rw [hzCtrl_0, hzCtrl_flag]
    have hupd : Function.update zCtrl flagW (P xTail) = zCtrl := by
      rw [← hzCtrl_flag]; exact Function.update_eq_self _ _
    rw [hupd, act_smul, hfc_adj]
    symm
    rw [Finset.sum_eq_single x]
    · simp only [ctrlBlockMat, Matrix.of_apply, ↓reduceIte, diagPhaseMat, Matrix.diagonal_apply]
      cases hc0 : c0 <;> simp [c0, xTail, hc0, pauliZ]
    · intro y _ hy
      simp only [ctrlBlockMat, Matrix.of_apply]
      by_cases hy0 : y 0 = x 0
      · rw [if_pos hy0]
        have htail_ne : (fun i => y (Fin.natAdd 1 i)) ≠ xTail := by
          intro h; apply hy; funext k
          by_cases hk0 : k.1 = 0
          · have hk : k = 0 := Fin.ext hk0; subst hk; exact hy0
          · have hk_eq : k = Fin.natAdd 1 ⟨k.1 - 1, by have := k.isLt; omega⟩ :=
              Fin.ext (by simp; omega)
            rw [hk_eq]; exact congrFun h _
        cases y 0 <;> simp [diagPhaseMat, xTail, htail_ne]
      · rw [if_neg hy0, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    rw [hzCtrl_flag]
    have h0 : (if zCtrl 0 then pauliZ b (P xTail) else if b = P xTail then 1 else 0) = 0 := by
      cases zCtrl 0 <;> simp [pauliZ, hb]
    rw [h0, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

def dtSignBool (q_w h : ℕ) (x : Qubits q_w) : Bool :=
  let idx := bitsToNatLSB x
  if h % 2 = 0 then decide (idx ≠ 1 ∧ idx < h + 2 ∧ idx % 2 = 1)
  else decide (idx ≠ 0 ∧ (h + 2 ≤ idx ∨ idx % 2 = 1))

theorem dtSignBool_spec {q_w h : ℕ} (x : Qubits q_w) :
    dtSignBool q_w h x =
      if bitsToNatLSB x = 0 then false
      else if bitsToNatLSB x = 1 then decide (h % 2 = 1)
      else decide (min (bitsToNatLSB x - 2) h % 2 = 1) := by
  dsimp only [dtSignBool]
  generalize bitsToNatLSB x = idx
  have h2 : h % 2 = 0 ∨ h % 2 = 1 := by omega
  rcases h2 with h0 | h1
  · simp only [h0, ↓reduceIte]
    rcases (by omega : idx = 0 ∨ idx = 1 ∨ 2 ≤ idx) with rfl | rfl | hge
    · simp
    · simp
    · have hne0 : idx ≠ 0 := by omega
      have hne1 : idx ≠ 1 := by omega
      rw [if_neg hne0, if_neg hne1]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, hne1, ne_eq, not_false_eq_true, true_and]
      by_cases hlt : idx < h + 2
      · have hmin : min (idx - 2) h = idx - 2 := Nat.min_eq_left (by omega)
        rw [hmin]
        omega
      · have hmin : min (idx - 2) h = h := Nat.min_eq_right (by omega)
        rw [hmin, h0]
        simp [hlt]
  · simp only [h1, Nat.one_ne_zero, ↓reduceIte]
    rcases (by omega : idx = 0 ∨ idx = 1 ∨ 2 ≤ idx) with rfl | rfl | hge
    · simp
    · simp
    · have hne0 : idx ≠ 0 := by omega
      have hne1 : idx ≠ 1 := by omega
      rw [if_neg hne0, if_neg hne1]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, hne0, ne_eq, not_false_eq_true, true_and]
      by_cases hlt : idx < h + 2
      · have hmin : min (idx - 2) h = idx - 2 := Nat.min_eq_left (by omega)
        rw [hmin]
        omega
      · have hmin : min (idx - 2) h = h := Nat.min_eq_right (by omega)
        rw [hmin, h1]
        have hge2 : h + 2 ≤ idx := by omega
        simp [hge2]

private lemma bitsToNatLSB_mod_two {q_w : ℕ} (hq : 1 ≤ q_w) (x : Qubits q_w) :
    decide (bitsToNatLSB x % 2 = 1) = x ⟨0, hq⟩ := by
  have h1 := bitsToNatLSB_split hq x
  have hlo : bitsToNatLSB (fun i : Fin 1 => x ⟨i.1, by omega⟩) = if x ⟨0, hq⟩ then 1 else 0 := by
    rw [bitsToNatLSB, Fin.sum_univ_one]
    simp
  rw [hlo] at h1
  cases hx0 : x ⟨0, hq⟩
  · have hmod : bitsToNatLSB x % 2 = 0 := by rw [hx0] at h1; simp at h1; omega
    rw [hmod]; decide
  · have hmod : bitsToNatLSB x % 2 = 1 := by rw [hx0] at h1; simp at h1; omega
    rw [hmod]; decide

private def dtLtEmb (q_w : ℕ) : Fin (q_w + 1 + q_w) ↪ Fin (q_w + (1 + (1 + q_w))) where
  toFun w := if w.1 < q_w then ⟨w.1, by omega⟩ else ⟨w.1 + 1, by have := w.isLt; omega⟩
  inj' a b hab := by
    have ha := a.isLt; have hb := b.isLt
    have hval := congrArg Fin.val hab
    by_cases ha1 : a.1 < q_w <;> by_cases hb1 : b.1 < q_w
    · simp only [ha1, hb1, ↓reduceIte] at hval; exact Fin.ext hval
    · simp only [ha1, hb1, ↓reduceIte] at hval; omega
    · simp only [ha1, hb1, ↓reduceIte] at hval; omega
    · simp only [ha1, hb1, ↓reduceIte] at hval; exact Fin.ext (by omega)

@[simp] private lemma dtLtEmb_val (q_w : ℕ) (w : Fin (q_w + 1 + q_w)) :
    (dtLtEmb q_w w).1 = if w.1 < q_w then w.1 else w.1 + 1 := by
  change (if w.1 < q_w then (⟨w.1, by omega⟩ : Fin (q_w + (1 + (1 + q_w))))
    else ⟨w.1 + 1, by have := w.isLt; omega⟩).1 = _
  split_ifs <;> rfl

private def dtEqEmb (q_w : ℕ) : Fin (q_w + 1 + q_w) ↪ Fin (q_w + (1 + (1 + q_w))) where
  toFun w := if w.1 ≤ q_w then ⟨w.1, by omega⟩ else ⟨w.1 + 1, by have := w.isLt; omega⟩
  inj' a b hab := by
    have ha := a.isLt; have hb := b.isLt
    have hval := congrArg Fin.val hab
    by_cases ha1 : a.1 ≤ q_w <;> by_cases hb1 : b.1 ≤ q_w
    · simp only [ha1, hb1, ↓reduceIte] at hval; exact Fin.ext hval
    · simp only [ha1, hb1, ↓reduceIte] at hval; omega
    · simp only [ha1, hb1, ↓reduceIte] at hval; omega
    · simp only [ha1, hb1, ↓reduceIte] at hval; exact Fin.ext (by omega)

@[simp] private lemma dtEqEmb_val (q_w : ℕ) (w : Fin (q_w + 1 + q_w)) :
    (dtEqEmb q_w w).1 = if w.1 ≤ q_w then w.1 else w.1 + 1 := by
  change (if w.1 ≤ q_w then (⟨w.1, by omega⟩ : Fin (q_w + (1 + (1 + q_w))))
    else ⟨w.1 + 1, by have := w.isLt; omega⟩).1 = _
  split_ifs <;> rfl

private noncomputable def dtFlagCompute (q_w h : ℕ) : LayeredCircuit (q_w + (1 + (1 + q_w))) :=
  if hq : 1 ≤ q_w then
    let ltStep := (ltConstCircuit q_w (h + 2)).mapWires (dtLtEmb q_w)
    let x0 : Fin (q_w + (1 + (1 + q_w))) := ⟨0, by omega⟩
    let fOut : Fin (q_w + (1 + (1 + q_w))) := ⟨q_w, by omega⟩
    let fLt : Fin (q_w + (1 + (1 + q_w))) := ⟨q_w + 1, by omega⟩
    have hxo : x0 ≠ fOut := by intro e; have := congrArg Fin.val e; dsimp [x0, fOut] at this; omega
    have hlx : fLt ≠ x0 := by intro e; have := congrArg Fin.val e; dsimp [fLt, x0] at this; omega
    have hlo : fLt ≠ fOut := by intro e; have := congrArg Fin.val e; dsimp [fLt, fOut] at this; omega
    if h % 2 = 0 then
      let andStep := toffoliOn fLt x0 fOut hlx hlo hxo
      let eqStep := (multiEqCtrl1 q_w (natToBitsLSB q_w 1) pauliX pauliX_mem_unitaryGroup).mapWires
        (dtEqEmb q_w)
      ltStep.seq (andStep.seq eqStep)
    else
      let andEven := (pauliXGate x0).seq ((toffoliOn fLt x0 fOut hlx hlo hxo).seq
        ((pauliXGate x0).seq (pauliXGate fOut)))
      ltStep.seq andEven
  else
    LayeredCircuit.id (q_w + (1 + (1 + q_w)))

private lemma dtFlagCompute_size (q_w h : ℕ) :
    (dtFlagCompute q_w h).size ≤ 28 * q_w + 18 := by
  by_cases hq : 1 ≤ q_w
  · by_cases heven : h % 2 = 0
    · simp only [dtFlagCompute, dif_pos hq, if_pos heven,
        LayeredCircuit.seq_size, LayeredCircuit.mapWires_size, toffoliOn_size]
      have h1 := ltConstCircuit_size q_w (h + 2)
      have h2 := multiEqCtrl1_size q_w (natToBitsLSB q_w 1) pauliX pauliX_mem_unitaryGroup
      omega
    · simp only [dtFlagCompute, dif_pos hq, if_neg heven,
        LayeredCircuit.seq_size, LayeredCircuit.mapWires_size, pauliXGate_size, toffoliOn_size]
      have h1 := ltConstCircuit_size q_w (h + 2)
      omega
  · simp [dtFlagCompute, dif_neg hq]

private lemma dtFlagCompute_depth (q_w h : ℕ) :
    (dtFlagCompute q_w h).depth ≤ 16 * q_w + 10 * Nat.clog 2 (q_w + 1) + 9 := by
  by_cases hq : 1 ≤ q_w
  · by_cases heven : h % 2 = 0
    · simp only [dtFlagCompute, dif_pos hq, if_pos heven,
        LayeredCircuit.seq_depth, LayeredCircuit.mapWires_depth, toffoliOn_depth]
      have h1 := ltConstCircuit_depth q_w (h + 2)
      have h2 := multiEqCtrl1_depth q_w (natToBitsLSB q_w 1) pauliX pauliX_mem_unitaryGroup
      omega
    · simp only [dtFlagCompute, dif_pos hq, if_neg heven,
        LayeredCircuit.seq_depth, LayeredCircuit.mapWires_depth, pauliXGate_depth,
        toffoliOn_depth]
      have h1 := ltConstCircuit_depth q_w (h + 2)
      omega
  · simp [dtFlagCompute, dif_neg hq]

private lemma act_mapWires_multiEqCtrl1_pauliX_ket {L m : ℕ}
    (pat : Qubits L) (emb : Fin (L + 1 + L) ↪ Fin m) (z : Qubits m)
    (hclean : ∀ j : Fin L, z (emb (Fin.natAdd (L + 1) j)) = false) :
    let embMain : Fin (L + 1) ↪ Fin m := (Fin.castAddEmb L).trans emb
    let tgtW : Fin m := embMain ⟨L, Nat.lt_succ_self L⟩
    act ((multiEqCtrl1 L pat pauliX pauliX_mem_unitaryGroup).mapWires emb).unitary (ket z) =
      ket (Function.update z tgtW
        (xor (z tgtW) (decide (∀ i : Fin L, z (embMain ⟨i.1, by omega⟩) = pat i)))) := by
  intro embMain tgtW
  have hact := act_mapWires_implementsOnClean
    (multiEqCtrl1 L pat pauliX pauliX_mem_unitaryGroup) (eqCtrlMat L pat pauliX)
    (multiEqCtrl1_implements L pat pauliX pauliX_mem_unitaryGroup) emb z hclean
  dsimp only at hact
  rw [hact]
  let tgt : Qubits (L + 1) :=
    Function.update (z ∘ embMain) ⟨L, Nat.lt_succ_self L⟩
      (xor (z tgtW) (decide (∀ i : Fin L, z (embMain ⟨i.1, by omega⟩) = pat i)))
  have htgt_i : ∀ i : Fin L, tgt ⟨i.1, by omega⟩ = (z ∘ embMain) ⟨i.1, by omega⟩ := fun i => by
    have hne : (⟨i.1, by omega⟩ : Fin (L + 1)) ≠ ⟨L, Nat.lt_succ_self L⟩ := by
      intro e; have := congrArg Fin.val e; dsimp at this; omega
    exact Function.update_of_ne hne _ _
  have htgt_last : tgt ⟨L, Nat.lt_succ_self L⟩ =
      xor (z tgtW) (decide (∀ i : Fin L, z (embMain ⟨i.1, by omega⟩) = pat i)) :=
    Function.update_self _ _ _
  rw [Finset.sum_eq_single tgt]
  · have hent : eqCtrlMat L pat pauliX tgt (z ∘ embMain) = 1 := by
      simp only [eqCtrlMat, Matrix.of_apply, if_pos htgt_i]
      change (if ∀ i : Fin L, z (embMain ⟨i.1, by omega⟩) = pat i then
          pauliX (tgt ⟨L, Nat.lt_succ_self L⟩) (z tgtW)
        else if tgt ⟨L, Nat.lt_succ_self L⟩ = z tgtW then 1 else 0) = 1
      by_cases hpat : ∀ i : Fin L, z (embMain ⟨i.1, by omega⟩) = pat i
      · rw [if_pos hpat, htgt_last, decide_eq_true hpat]
        cases z tgtW <;> simp [pauliX]
      · rw [if_neg hpat, htgt_last, decide_eq_false hpat]
        simp
    rw [hent, one_smul]
    congr 1; funext w
    by_cases hw : w = tgtW
    · subst hw
      rw [Function.update_self]
      change updateOn embMain z tgt (embMain ⟨L, Nat.lt_succ_self L⟩) = _
      rw [updateOn_apply_emb, htgt_last]
    · rw [Function.update_of_ne hw]
      by_cases hmem : w ∈ Set.range embMain
      · rcases hmem with ⟨i, rfl⟩
        rw [updateOn_apply_emb]
        have hne : i ≠ ⟨L, Nat.lt_succ_self L⟩ := fun h => hw (congrArg embMain h)
        exact Function.update_of_ne hne _ _
      · exact updateOn_apply_not_mem _ _ _ hmem
  · intro y _ hy
    have hent0 : eqCtrlMat L pat pauliX y (z ∘ embMain) = 0 := by
      simp only [eqCtrlMat, Matrix.of_apply]
      by_cases hy_i : ∀ i : Fin L, y ⟨i.1, by omega⟩ = (z ∘ embMain) ⟨i.1, by omega⟩
      · rw [if_pos hy_i]
        have hy_ne : y ⟨L, Nat.lt_succ_self L⟩ ≠ tgt ⟨L, Nat.lt_succ_self L⟩ := by
          intro hlast; apply hy; funext k
          by_cases hk : k.1 < L
          · exact (hy_i ⟨k.1, hk⟩).trans (htgt_i ⟨k.1, hk⟩).symm
          · have hkL : k = ⟨L, Nat.lt_succ_self L⟩ := Fin.ext (by have := k.isLt; dsimp; omega)
            subst hkL; exact hlast
        change (if ∀ i : Fin L, z (embMain ⟨i.1, by omega⟩) = pat i then
            pauliX (y ⟨L, Nat.lt_succ_self L⟩) (z tgtW)
          else if y ⟨L, Nat.lt_succ_self L⟩ = z tgtW then 1 else 0) = 0
        by_cases hpat : ∀ i : Fin L, z (embMain ⟨i.1, by omega⟩) = pat i
        · rw [if_pos hpat]
          rw [htgt_last, decide_eq_true hpat] at hy_ne
          cases hyL : y ⟨L, Nat.lt_succ_self L⟩ <;> cases hz : z tgtW <;>
            simp [hyL, hz, pauliX] at hy_ne ⊢
        · rw [if_neg hpat]
          rw [htgt_last, decide_eq_false hpat, Bool.xor_false] at hy_ne
          rw [if_neg hy_ne]
      · rw [if_neg hy_i]
    rw [hent0, zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma dtFlagCompute_implements (q_w h : ℕ) (x : Qubits q_w) :
    ∃ z' : Qubits (q_w + (1 + (1 + q_w))),
      act (dtFlagCompute q_w h).unitary (ket (padZero q_w (1 + (1 + q_w)) x)) = ket z' ∧
      z' ⟨q_w, by omega⟩ = dtSignBool q_w h x := by
  by_cases hq : 1 ≤ q_w
  · let x0 : Fin (q_w + (1 + (1 + q_w))) := ⟨0, by omega⟩
    let fOut : Fin (q_w + (1 + (1 + q_w))) := ⟨q_w, by omega⟩
    let fLt : Fin (q_w + (1 + (1 + q_w))) := ⟨q_w + 1, by omega⟩
    have hxo : x0 ≠ fOut := by intro e; have := congrArg Fin.val e; dsimp [x0, fOut] at this; omega
    have hlx : fLt ≠ x0 := by intro e; have := congrArg Fin.val e; dsimp [fLt, x0] at this; omega
    have hlo : fLt ≠ fOut := by intro e; have := congrArg Fin.val e; dsimp [fLt, fOut] at this; omega
    let z0 := padZero q_w (1 + (1 + q_w)) x
    have hclean_lt : ∀ j : Fin q_w,
        z0 (dtLtEmb q_w (Fin.natAdd (q_w + 1) j)) = false := fun j => by
      have heq : dtLtEmb q_w (Fin.natAdd (q_w + 1) j) =
          Fin.natAdd q_w ⟨j.1 + 2, by have := j.isLt; omega⟩ := by
        apply Fin.ext; rw [dtLtEmb_val, if_neg (by simp; omega)]; simp; omega
      rw [heq]; exact padZero_natAdd _ _ _ _
    have hlt_main : ∀ i : Fin q_w,
        (z0 ∘ (Fin.castAddEmb q_w).trans (dtLtEmb q_w)) ⟨i.1, by omega⟩ = x i := fun i => by
      change z0 (dtLtEmb q_w (Fin.castAdd q_w ⟨i.1, by omega⟩)) = x i
      have heq : dtLtEmb q_w (Fin.castAdd q_w (⟨i.1, by omega⟩ : Fin (q_w + 1))) =
          Fin.castAdd (1 + (1 + q_w)) i := by
        apply Fin.ext; rw [dtLtEmb_val, if_pos (by simp)]; simp
      rw [heq]; exact padZero_castAdd _ _ _ _
    have hlt_out : (z0 ∘ (Fin.castAddEmb q_w).trans (dtLtEmb q_w)) ⟨q_w, Nat.lt_succ_self q_w⟩ =
        false := by
      change z0 (dtLtEmb q_w (Fin.castAdd q_w ⟨q_w, Nat.lt_succ_self q_w⟩)) = false
      have heq : dtLtEmb q_w (Fin.castAdd q_w ⟨q_w, Nat.lt_succ_self q_w⟩) =
          Fin.natAdd q_w ⟨1, by omega⟩ := by
        apply Fin.ext; rw [dtLtEmb_val, if_neg (by simp)]; simp
      rw [heq]; exact padZero_natAdd _ _ _ _
    have hlt_act :
        act ((ltConstCircuit q_w (h + 2)).mapWires (dtLtEmb q_w)).unitary (ket z0) =
          ket (Function.update z0 fLt (decide (bitsToNatLSB x < h + 2))) := by
      have hact := act_mapWires_implementsOnClean (ltConstCircuit q_w (h + 2))
        (ltOutMat q_w (h + 2)) (ltConstCircuit_implements q_w (h + 2)) (dtLtEmb q_w) z0 hclean_lt
      dsimp only at hact
      rw [hact]
      let tgt : Qubits (q_w + 1) :=
        Function.update (z0 ∘ (Fin.castAddEmb q_w).trans (dtLtEmb q_w)) ⟨q_w, Nat.lt_succ_self q_w⟩
          (decide (bitsToNatLSB x < h + 2))
      have heq_in :
          (fun i : Fin q_w => (z0 ∘ (Fin.castAddEmb q_w).trans (dtLtEmb q_w)) ⟨i.1, by omega⟩) = x :=
        funext hlt_main
      rw [Finset.sum_eq_single tgt]
      · have hent : ltOutMat q_w (h + 2) tgt (z0 ∘ (Fin.castAddEmb q_w).trans (dtLtEmb q_w)) = 1 := by
          simp only [ltOutMat, permMat, Matrix.of_apply, heq_in, hlt_out, Bool.false_xor]
          exact if_pos rfl
        rw [hent, one_smul]
        congr 1; funext w
        by_cases hwf : w = fLt
        · rw [hwf, Function.update_self]
          have heq : fLt = ((Fin.castAddEmb q_w).trans (dtLtEmb q_w)) ⟨q_w, Nat.lt_succ_self q_w⟩ := by
            apply Fin.ext; simp [fLt]
          rw [heq, updateOn_apply_emb]
          dsimp only [tgt]; rw [Function.update_self]
        · rw [Function.update_of_ne hwf]
          by_cases hmem : w ∈ Set.range ((Fin.castAddEmb q_w).trans (dtLtEmb q_w))
          · rcases hmem with ⟨i, rfl⟩
            rw [updateOn_apply_emb]
            have hne_q : i ≠ ⟨q_w, Nat.lt_succ_self q_w⟩ := fun h => by
              apply hwf; rw [h]; apply Fin.ext; simp [fLt]
            dsimp only [tgt]; rw [Function.update_of_ne hne_q]; rfl
          · rw [updateOn_apply_not_mem _ _ _ hmem]
      · intro y _ hy
        simp only [ltOutMat, permMat, Matrix.of_apply, heq_in, hlt_out, Bool.false_xor]
        have hne : y ≠ tgt := hy
        rw [if_neg hne, zero_smul]
      · intro h; exact absurd (Finset.mem_univ _) h
    let z1 := Function.update z0 fLt (decide (bitsToNatLSB x < h + 2))
    have hz1_x0 : z1 x0 = x ⟨0, hq⟩ := by
      have hne : x0 ≠ fLt := hlx.symm
      dsimp only [z1]; rw [Function.update_of_ne hne]
      exact padZero_castAdd _ _ x ⟨0, hq⟩
    have hz1_fOut : z1 fOut = false := by
      have hne : fOut ≠ fLt := hlo.symm
      dsimp only [z1]; rw [Function.update_of_ne hne]
      have hnat : fOut = Fin.natAdd q_w ⟨0, by omega⟩ := Fin.ext rfl
      rw [hnat]; exact padZero_natAdd _ _ _ _
    have hz1_fLt : z1 fLt = decide (bitsToNatLSB x < h + 2) := Function.update_self _ _ _
    have hmod_x0 : decide (bitsToNatLSB x % 2 = 1) = x ⟨0, hq⟩ := bitsToNatLSB_mod_two hq x
    by_cases heven : h % 2 = 0
    · let z2 := Function.update z1 fOut (z1 fLt && z1 x0)
      have hand_act :
          act (toffoliOn fLt x0 fOut hlx hlo hxo).unitary (ket z1) = ket z2 := by
        rw [act_toffoliOn_ket]
        dsimp only [z2]; rw [hz1_fOut, Bool.false_xor]
      have hclean_eq : ∀ j : Fin q_w,
          z2 (dtEqEmb q_w (Fin.natAdd (q_w + 1) j)) = false := fun j => by
        have heq : dtEqEmb q_w (Fin.natAdd (q_w + 1) j) =
            Fin.natAdd q_w ⟨j.1 + 2, by have := j.isLt; omega⟩ := by
          apply Fin.ext; rw [dtEqEmb_val, if_neg (by simp; omega)]; simp; omega
        have hne_out : dtEqEmb q_w (Fin.natAdd (q_w + 1) j) ≠ fOut := by
          intro e; have := congrArg Fin.val e; rw [heq] at this; dsimp [fOut] at this; simp at this
        have hne_lt : dtEqEmb q_w (Fin.natAdd (q_w + 1) j) ≠ fLt := by
          intro e; have := congrArg Fin.val e; rw [heq] at this; dsimp [fLt] at this; simp at this
        dsimp only [z2, z1]
        rw [Function.update_of_ne hne_out, Function.update_of_ne hne_lt, heq]
        exact padZero_natAdd _ _ _ _
      have heq_act := act_mapWires_multiEqCtrl1_pauliX_ket (natToBitsLSB q_w 1) (dtEqEmb q_w) z2 hclean_eq
      have htot : act (dtFlagCompute q_w h).unitary (ket z0) =
          ket (Function.update z2 (((Fin.castAddEmb q_w).trans (dtEqEmb q_w)) ⟨q_w, Nat.lt_succ_self q_w⟩)
            (xor (z2 (((Fin.castAddEmb q_w).trans (dtEqEmb q_w)) ⟨q_w, Nat.lt_succ_self q_w⟩))
              (decide (∀ i : Fin q_w,
                z2 (((Fin.castAddEmb q_w).trans (dtEqEmb q_w)) ⟨i.1, by omega⟩) =
                  natToBitsLSB q_w 1 i)))) := by
        dsimp only [dtFlagCompute]
        rw [dif_pos hq, if_pos heven, LayeredCircuit.seq_unitary, act_mul,
          LayeredCircuit.seq_unitary, act_mul, hlt_act, hand_act]
        exact heq_act
      refine ⟨_, htot, ?_⟩
      have htgtW : ((Fin.castAddEmb q_w).trans (dtEqEmb q_w)) ⟨q_w, Nat.lt_succ_self q_w⟩ = fOut := by
        apply Fin.ext; simp [fOut]
      rw [htgtW, Function.update_self]
      have hz2_fOut : z2 fOut = (decide (bitsToNatLSB x < h + 2) && x ⟨0, hq⟩) := by
        dsimp only [z2]; rw [Function.update_self, hz1_fLt, hz1_x0]
      have heq_in : ∀ i : Fin q_w,
          z2 (((Fin.castAddEmb q_w).trans (dtEqEmb q_w)) ⟨i.1, by omega⟩) = x i := fun i => by
        have hwire : ((Fin.castAddEmb q_w).trans (dtEqEmb q_w)) ⟨i.1, by omega⟩ =
            Fin.castAdd (1 + (1 + q_w)) i := by
          apply Fin.ext; simp [show i.1 ≤ q_w by omega]
        have hne_out : Fin.castAdd (1 + (1 + q_w)) i ≠ fOut := by
          intro e; have := congrArg Fin.val e; dsimp [fOut] at this; have := i.isLt; simp at this; omega
        have hne_lt : Fin.castAdd (1 + (1 + q_w)) i ≠ fLt := by
          intro e; have := congrArg Fin.val e; dsimp [fLt] at this; have := i.isLt; simp at this; omega
        rw [hwire]
        dsimp only [z2, z1]
        rw [Function.update_of_ne hne_out, Function.update_of_ne hne_lt]
        exact padZero_castAdd _ _ _ _
      have hall_iff :
          (∀ i : Fin q_w,
            z2 (((Fin.castAddEmb q_w).trans (dtEqEmb q_w)) ⟨i.1, by omega⟩) =
              natToBitsLSB q_w 1 i) ↔
          bitsToNatLSB x = 1 := by
        simp_rw [heq_in]
        have hpow : 1 < 2 ^ q_w := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hq)
        constructor
        · intro hall
          have hx_eq : x = natToBitsLSB q_w 1 := funext hall
          rw [hx_eq]
          exact bitsToNatLSB_natToBitsLSB hpow
        · intro h1 i
          rw [← natToBitsLSB_bitsToNatLSB x, h1]
      rw [hz2_fOut]
      simp only [hall_iff, ← hmod_x0]
      by_cases hx1 : bitsToNatLSB x = 1
      · simp [dtSignBool, heven, hx1]
      · simp only [hx1, decide_false, Bool.xor_false]
        dsimp only [dtSignBool]
        rw [if_pos heven]
        apply Bool.eq_iff_iff.mpr
        simp [hx1]
    · let z2 := Function.update z1 x0 (!z1 x0)
      let z3 := Function.update z2 fOut (xor (z2 fOut) (z2 fLt && z2 x0))
      let z4 := Function.update z3 x0 (!z3 x0)
      let z5 := Function.update z4 fOut (!z4 fOut)
      have htot : act (dtFlagCompute q_w h).unitary (ket z0) = ket z5 := by
        dsimp only [dtFlagCompute]
        rw [dif_pos hq, if_neg heven]
        simp only [LayeredCircuit.seq_unitary, act_mul, hlt_act, act_pauliXGate_ket,
          act_toffoliOn_ket]
        rfl
      refine ⟨z5, htot, ?_⟩
      change z5 fOut = dtSignBool q_w h x
      dsimp only [z5, z4, z3, z2]
      simp only [Function.update_self, Function.update_of_ne hxo.symm,
        Function.update_of_ne hlx, hz1_fOut, hz1_fLt, hz1_x0, Bool.false_xor]
      rw [← hmod_x0]
      dsimp only [dtSignBool]
      rw [if_neg heven]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.not_and, Bool.not_not, Bool.or_eq_true, decide_eq_true_eq,
        Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
      omega
  · have hq0 : q_w = 0 := by omega
    subst hq0
    simp only [dtFlagCompute, dif_neg hq, LayeredCircuit.id_unitary, act_one]
    refine ⟨padZero 0 (1 + (1 + 0)) x, rfl, ?_⟩
    have hnat : (⟨0, by omega⟩ : Fin (0 + (1 + (1 + 0)))) = Fin.natAdd 0 ⟨0, by omega⟩ := Fin.ext rfl
    rw [hnat, padZero_natAdd]
    dsimp only [dtSignBool]
    split_ifs <;> simp [bitsToNatLSB]

noncomputable def ltPhaseSignGate (q_w h : ℕ) : LayeredCircuit (q_w + (1 + (1 + q_w))) :=
  phaseGateOfFlag (dtFlagCompute q_w h)

theorem ltPhaseSignGate_size (q_w h : ℕ) :
    (ltPhaseSignGate q_w h).size ≤ 56 * q_w + 37 := by
  rw [ltPhaseSignGate, phaseGateOfFlag_size]
  have h1 := dtFlagCompute_size q_w h
  omega

theorem ltPhaseSignGate_depth (q_w h : ℕ) :
    (ltPhaseSignGate q_w h).depth ≤ 32 * q_w + 20 * Nat.clog 2 (q_w + 1) + 19 := by
  rw [ltPhaseSignGate, phaseGateOfFlag_depth]
  have h1 := dtFlagCompute_depth q_w h
  omega

private lemma clog2_add_one_le (q_w : ℕ) : Nat.clog 2 (q_w + 1) ≤ q_w + 1 := by
  rw [clog2_le_iff_le_pow]
  induction q_w with
  | zero => simp
  | succ k ih => rw [pow_succ']; omega

theorem ltPhaseSignGate_depth_linear (q_w h : ℕ) :
    (ltPhaseSignGate q_w h).depth ≤ 52 * q_w + 39 := by
  have hd := ltPhaseSignGate_depth q_w h
  have hc := clog2_add_one_le q_w
  omega

theorem ltPhaseSignGate_implements (q_w h : ℕ) :
    (ltPhaseSignGate q_w h).ImplementsOnClean (diagPhaseMat (dtSignBool q_w h)) :=
  phaseGateOfFlag_implements (dtFlagCompute q_w h) (dtSignBool q_w h) (dtFlagCompute_implements q_w h)

noncomputable def ctrlLtPhaseSignGate (q_w h : ℕ) :
    LayeredCircuit ((1 + q_w) + (1 + (1 + q_w))) :=
  ctrlPhaseGateOfFlag (dtFlagCompute q_w h)

theorem ctrlLtPhaseSignGate_size (q_w h : ℕ) :
    (ctrlLtPhaseSignGate q_w h).size ≤ 56 * q_w + 37 := by
  rw [ctrlLtPhaseSignGate, ctrlPhaseGateOfFlag_size]
  have h1 := dtFlagCompute_size q_w h
  omega

theorem ctrlLtPhaseSignGate_depth (q_w h : ℕ) :
    (ctrlLtPhaseSignGate q_w h).depth ≤ 32 * q_w + 20 * Nat.clog 2 (q_w + 1) + 19 := by
  rw [ctrlLtPhaseSignGate, ctrlPhaseGateOfFlag_depth]
  have h1 := dtFlagCompute_depth q_w h
  omega

theorem ctrlLtPhaseSignGate_depth_linear (q_w h : ℕ) :
    (ctrlLtPhaseSignGate q_w h).depth ≤ 52 * q_w + 39 := by
  have hd := ctrlLtPhaseSignGate_depth q_w h
  have hc := clog2_add_one_le q_w
  omega

theorem ctrlLtPhaseSignGate_implements (q_w h : ℕ) :
    (ctrlLtPhaseSignGate q_w h).ImplementsOnClean
      (ctrlBlockMat (diagPhaseMat (dtSignBool q_w h))) :=
  ctrlPhaseGateOfFlag_implements (dtFlagCompute q_w h) (dtSignBool q_w h)
    (dtFlagCompute_implements q_w h)

/-! #### `U_0` Diagonal Sign Gate (`(-1)^(i+1)` for `e_i`, index `2 + i`) -/

def u0DiagSignBool (q_w : ℕ) (x : Qubits q_w) : Bool :=
  decide (2 ≤ bitsToNatLSB x ∧ bitsToNatLSB x % 2 = 0)

private def u0EqEmb (q_w : ℕ) : Fin (q_w + 1 + q_w) ↪ Fin (q_w + (1 + q_w)) where
  toFun w := ⟨w.1, by omega⟩
  inj' a b h := Fin.ext (by have := congrArg Fin.val h; exact this)

@[simp] private lemma u0EqEmb_val (q_w : ℕ) (w : Fin (q_w + 1 + q_w)) :
    (u0EqEmb q_w w).1 = w.1 := rfl

private noncomputable def u0FlagCompute (q_w : ℕ) : LayeredCircuit (q_w + (1 + q_w)) :=
  if hq : 2 ≤ q_w then
    let x0 : Fin (q_w + (1 + q_w)) := ⟨0, by omega⟩
    let fOut : Fin (q_w + (1 + q_w)) := ⟨q_w, by omega⟩
    have hxo : x0 ≠ fOut := by intro e; have := congrArg Fin.val e; dsimp [x0, fOut] at this; omega
    let parityStep := (pauliXGate x0).seq ((cnotGate x0 fOut hxo).seq (pauliXGate x0))
    let eqStep := (multiEqCtrl1 q_w (fun _ => false) pauliX pauliX_mem_unitaryGroup).mapWires
      (u0EqEmb q_w)
    parityStep.seq eqStep
  else
    LayeredCircuit.id (q_w + (1 + q_w))

private lemma u0FlagCompute_size (q_w : ℕ) :
    (u0FlagCompute q_w).size ≤ 12 * q_w + 15 := by
  by_cases hq : 2 ≤ q_w
  · simp only [u0FlagCompute, dif_pos hq, LayeredCircuit.seq_size, pauliXGate_size, cnotGate_size,
      LayeredCircuit.mapWires_size]
    have h2 := multiEqCtrl1_size q_w (fun _ => false) pauliX pauliX_mem_unitaryGroup
    omega
  · simp [u0FlagCompute, dif_neg hq]

private lemma u0FlagCompute_depth (q_w : ℕ) :
    (u0FlagCompute q_w).depth ≤ 10 * Nat.clog 2 (q_w + 1) + 6 := by
  by_cases hq : 2 ≤ q_w
  · simp only [u0FlagCompute, dif_pos hq, LayeredCircuit.seq_depth, pauliXGate_depth, cnotGate_depth,
      LayeredCircuit.mapWires_depth]
    have h2 := multiEqCtrl1_depth q_w (fun _ => false) pauliX pauliX_mem_unitaryGroup
    omega
  · simp [u0FlagCompute, dif_neg hq]

private lemma u0FlagCompute_implements (q_w : ℕ) (x : Qubits q_w) :
    ∃ z' : Qubits (q_w + (1 + q_w)),
      act (u0FlagCompute q_w).unitary (ket (padZero q_w (1 + q_w) x)) = ket z' ∧
      z' ⟨q_w, by omega⟩ = u0DiagSignBool q_w x := by
  by_cases hq : 2 ≤ q_w
  · let x0 : Fin (q_w + (1 + q_w)) := ⟨0, by omega⟩
    let fOut : Fin (q_w + (1 + q_w)) := ⟨q_w, by omega⟩
    have hxo : x0 ≠ fOut := by intro e; have := congrArg Fin.val e; dsimp [x0, fOut] at this; omega
    let z0 := padZero q_w (1 + q_w) x
    have hz0_x0 : z0 x0 = x ⟨0, by omega⟩ := padZero_castAdd q_w (1 + q_w) x ⟨0, by omega⟩
    have hz0_fOut : z0 fOut = false := by
      have hnat : fOut = Fin.natAdd q_w ⟨0, by omega⟩ := Fin.ext rfl
      rw [hnat]; exact padZero_natAdd _ _ _ _
    let z1 := Function.update z0 fOut (!x ⟨0, by omega⟩)
    have hpar_act :
        act ((pauliXGate x0).seq ((cnotGate x0 fOut hxo).seq (pauliXGate x0))).unitary (ket z0) =
          ket z1 := by
      simp only [LayeredCircuit.seq_unitary, act_mul, act_pauliXGate_ket, act_cnotGate_ket]
      congr 1; funext w
      dsimp only [z1]
      by_cases hw_out : w = fOut
      · subst hw_out
        simp only [Function.update_self, Function.update_of_ne hxo.symm, hz0_fOut, hz0_x0,
          Bool.false_xor]
      · rw [Function.update_of_ne hw_out]
        by_cases hw_x0 : w = x0
        · subst hw_x0
          simp only [Function.update_self, Function.update_of_ne hxo, Bool.not_not]
        · simp only [Function.update_of_ne hw_x0, Function.update_of_ne hw_out]
    have hclean_eq : ∀ j : Fin q_w,
        z1 (u0EqEmb q_w (Fin.natAdd (q_w + 1) j)) = false := fun j => by
      have heq : u0EqEmb q_w (Fin.natAdd (q_w + 1) j) =
          Fin.natAdd q_w ⟨j.1 + 1, by have := j.isLt; omega⟩ := by
        apply Fin.ext; simp; omega
      have hne_out : u0EqEmb q_w (Fin.natAdd (q_w + 1) j) ≠ fOut := by
        intro e; have := congrArg Fin.val e; rw [heq] at this; dsimp [fOut] at this; simp at this
      dsimp only [z1]
      rw [Function.update_of_ne hne_out, heq]
      exact padZero_natAdd _ _ _ _
    have heq_act := act_mapWires_multiEqCtrl1_pauliX_ket (fun _ => false) (u0EqEmb q_w) z1 hclean_eq
    have htot : act (u0FlagCompute q_w).unitary (ket z0) =
        ket (Function.update z1 (((Fin.castAddEmb q_w).trans (u0EqEmb q_w)) ⟨q_w, Nat.lt_succ_self q_w⟩)
          (xor (z1 (((Fin.castAddEmb q_w).trans (u0EqEmb q_w)) ⟨q_w, Nat.lt_succ_self q_w⟩))
            (decide (∀ i : Fin q_w,
              z1 (((Fin.castAddEmb q_w).trans (u0EqEmb q_w)) ⟨i.1, by omega⟩) = false)))) := by
      dsimp only [u0FlagCompute]
      rw [dif_pos hq, LayeredCircuit.seq_unitary, act_mul, hpar_act]
      exact heq_act
    refine ⟨_, htot, ?_⟩
    have htgtW : ((Fin.castAddEmb q_w).trans (u0EqEmb q_w)) ⟨q_w, Nat.lt_succ_self q_w⟩ = fOut := by
      apply Fin.ext; simp [fOut]
    rw [htgtW, Function.update_self]
    have hz1_fOut : z1 fOut = !x ⟨0, by omega⟩ := Function.update_self _ _ _
    have heq_in : ∀ i : Fin q_w,
        z1 (((Fin.castAddEmb q_w).trans (u0EqEmb q_w)) ⟨i.1, by omega⟩) = x i := fun i => by
      have hwire : ((Fin.castAddEmb q_w).trans (u0EqEmb q_w)) ⟨i.1, by omega⟩ =
          Fin.castAdd (1 + q_w) i := by
        apply Fin.ext; simp
      have hne_out : Fin.castAdd (1 + q_w) i ≠ fOut := by
        intro e; have := congrArg Fin.val e; dsimp [fOut] at this; have := i.isLt; simp at this; omega
      rw [hwire]
      dsimp only [z1]
      rw [Function.update_of_ne hne_out]
      exact padZero_castAdd _ _ _ _
    have hzero_iff :
        (∀ i : Fin q_w,
          z1 (((Fin.castAddEmb q_w).trans (u0EqEmb q_w)) ⟨i.1, by omega⟩) = false) ↔
        bitsToNatLSB x = 0 := by
      simp_rw [heq_in]
      constructor
      · intro hall
        have hx_eq : x = natToBitsLSB q_w 0 := by rw [natToBitsLSB_zero]; funext i; exact hall i
        rw [hx_eq]
        exact bitsToNatLSB_natToBitsLSB (Nat.two_pow_pos q_w)
      · intro h0 i
        rw [← natToBitsLSB_bitsToNatLSB x, h0, natToBitsLSB_zero]
    have hmod_x0 : decide (bitsToNatLSB x % 2 = 1) = x ⟨0, by omega⟩ :=
      bitsToNatLSB_mod_two (by omega) x
    rw [hz1_fOut]
    simp only [hzero_iff, ← hmod_x0]
    dsimp only [u0DiagSignBool]
    by_cases hx0 : bitsToNatLSB x = 0
    · simp [hx0]
    · simp only [hx0, decide_false, Bool.xor_false]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
      omega
  · simp only [u0FlagCompute, dif_neg hq, LayeredCircuit.id_unitary, act_one]
    refine ⟨padZero q_w (1 + q_w) x, rfl, ?_⟩
    have hnat : (⟨q_w, by omega⟩ : Fin (q_w + (1 + q_w))) = Fin.natAdd q_w ⟨0, by omega⟩ := Fin.ext rfl
    rw [hnat, padZero_natAdd]
    have hlt_pow : bitsToNatLSB x < 2 ^ q_w := bitsToNatLSB_lt q_w x
    have hpow_le : 2 ^ q_w ≤ 2 := by
      rcases (by omega : q_w = 0 ∨ q_w = 1) with rfl | rfl <;> norm_num
    dsimp only [u0DiagSignBool]
    simp [show ¬ 2 ≤ bitsToNatLSB x by omega]

noncomputable def u0DiagSignGate (q_w : ℕ) : LayeredCircuit (q_w + (1 + q_w)) :=
  phaseGateOfFlag (u0FlagCompute q_w)

theorem u0DiagSignGate_size (q_w : ℕ) :
    (u0DiagSignGate q_w).size ≤ 24 * q_w + 31 := by
  rw [u0DiagSignGate, phaseGateOfFlag_size]
  have h1 := u0FlagCompute_size q_w
  omega

theorem u0DiagSignGate_depth (q_w : ℕ) :
    (u0DiagSignGate q_w).depth ≤ 20 * Nat.clog 2 (q_w + 1) + 13 := by
  rw [u0DiagSignGate, phaseGateOfFlag_depth]
  have h1 := u0FlagCompute_depth q_w
  omega

theorem u0DiagSignGate_implements (q_w : ℕ) :
    (u0DiagSignGate q_w).ImplementsOnClean (diagPhaseMat (u0DiagSignBool q_w)) :=
  phaseGateOfFlag_implements (u0FlagCompute q_w) (u0DiagSignBool q_w) (u0FlagCompute_implements q_w)

noncomputable def ctrlU0DiagSignGate (q_w : ℕ) : LayeredCircuit ((1 + q_w) + (1 + q_w)) :=
  ctrlPhaseGateOfFlag (u0FlagCompute q_w)

theorem ctrlU0DiagSignGate_size (q_w : ℕ) :
    (ctrlU0DiagSignGate q_w).size ≤ 24 * q_w + 31 := by
  rw [ctrlU0DiagSignGate, ctrlPhaseGateOfFlag_size]
  have h1 := u0FlagCompute_size q_w
  omega

theorem ctrlU0DiagSignGate_depth (q_w : ℕ) :
    (ctrlU0DiagSignGate q_w).depth ≤ 20 * Nat.clog 2 (q_w + 1) + 13 := by
  rw [ctrlU0DiagSignGate, ctrlPhaseGateOfFlag_depth]
  have h1 := u0FlagCompute_depth q_w
  omega

theorem ctrlU0DiagSignGate_implements (q_w : ℕ) :
    (ctrlU0DiagSignGate q_w).ImplementsOnClean
      (ctrlBlockMat (diagPhaseMat (u0DiagSignBool q_w))) :=
  ctrlPhaseGateOfFlag_implements (u0FlagCompute q_w) (u0DiagSignBool q_w)
    (u0FlagCompute_implements q_w)

end Thm410Router


