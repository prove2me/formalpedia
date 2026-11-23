-- Prove2me | Definitions.Def_MegiddoLP_ApproachI
-- name    : MegiddoLP_ApproachI
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-23T06:39:50.742722+00:00
-- url     : https://prove2.me/theorems/54231ace-41db-42a3-9208-f9b5a709ecc6
-- title:
--   The one-dimensional base case of Megiddo’s Approach I
-- statement:
--   A structured real pointer machine locates a point relative to a family of one-dimensional hyperplanes using the supplied comparison oracle. The specification covers the returned information and the cost of the base case.
-- source:
--   Nimrod Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, JACM 31(1), 1984, §2 and §5. https://theory.stanford.edu/~megiddo/pdf/lplin.pdf

import Definitions.Def_MegiddoLP_MachineFrame
import Definitions.Def_MegiddoLP_Infeasibility
import Definitions.Def_MegiddoLP_VectorGadgets
import Definitions.Def_MegiddoLP_ConstructiveApproachI
import Definitions.Def_MegiddoLP_Selection
import Definitions.Def_MegiddoLP_Oracle
import Mathlib.Tactic

/-!
# Megiddo's Approach I Multi-Hyperplane Pruning on `SmaleNinth.RAMProgram`

Constructs `buildApproachISolver {D : ℕ} (ora : OracleSolver D) (e : ℕ) : ApproachISolver D (e + 1)`
by structural recursion on `e`:
- `e = 0` (`dim = 1`): computes ratios `γ_u / h_{u,0}`, selects median `c` via `selectMedianStmt`,
  calls `ora.mkStmt` once on `(M_adj 0, c)`, updates `(xCand, vCand)` monotonically, and settles
  at least `M / 2` hyperplanes via `settle1D`.
- `e' + 1` (`dim = e' + 2`): sequential `O(M)` streaming slope-median split into `Z` (`a_0 = 0`),
  `E` (`ρ = c`), `L` (`ρ < c`), and `G` (`c < ρ`), two recursive passes at dimension `e' + 1`
  (`M_adj1` on `Z + Pairs`, `M_adj2` on `E + Pass-1-settled Pairs`), planar pair decoding via
  `decodePair`, and sequential FIFO merge settling at least `M / 2 ^ (2 ^ (e' + 2) - 1)` hyperplanes.
-/

namespace MegiddoLP.ApproachI

open SmaleNinth Matrix
open MegiddoLP.MachineDSL MegiddoLP.Infeasibility MegiddoLP.VectorGadgets
open MegiddoLP.ConstructiveApproachI MegiddoLP.Selection MegiddoLP.Oracle

/-! ## Subspace Pullback, Row Independence, and Solver Interface -/

/-- Coordinate vector `y_j = M_adj j ⬝ᵥ w` induced by `e` ambient normals `M_adj : Fin e → Fin D → ℝ`. -/
def pullVec {e D : ℕ} (M_adj : Fin e → Fin D → ℝ) (w : Fin D → ℝ) : Fin e → ℝ :=
  fun j => M_adj j ⬝ᵥ w

/-- Linear independence of the `e` rows `M_adj : Fin e → Fin D → ℝ`. -/
def MatIndep {e D : ℕ} (M_adj : Fin e → Fin D → ℝ) : Prop :=
  ∀ μ : Fin e → ℝ, (∑ j : Fin e, μ j • M_adj j) = 0 → μ = 0

/-- `s.regs` stores `M_adj : Fin e → Fin D → ℝ` row-major at `rMat .. rMat + e * D - 1`. -/
def MatRegs {e D : ℕ} (s : MState) (rMat : ℕ) (M_adj : Fin e → Fin D → ℝ) : Prop :=
  ∀ j : Fin e, VecRegs s (rMat + j.1 * D) (M_adj j)

theorem MatRegs.of_pres {e D : ℕ} {s₁ s₂ : MState} {rMat : ℕ} {M_adj : Fin e → Fin D → ℝ}
    (h : MatRegs s₁ rMat M_adj)
    (hp : ∀ r, rMat ≤ r → r < rMat + e * D → s₂.regs r = s₁.regs r) :
    MatRegs s₂ rMat M_adj := by
  intro j k
  have hj := j.2
  have hk := k.2
  have hlt : j.1 * D + k.1 < e * D := by
    calc j.1 * D + k.1 < j.1 * D + D := by omega
      _ = (j.1 + 1) * D := by ring
      _ ≤ e * D := Nat.mul_le_mul_right D (by omega)
  exact (hp (rMat + j.1 * D + k.1) (by omega) (by omega)).trans (h j k)

theorem MatRegs.tail {e' D : ℕ} {s : MState} {rMat : ℕ} {M_adj : Fin (e' + 2) → Fin D → ℝ}
    (h : MatRegs s rMat M_adj) :
    MatRegs s (rMat + D) (fun j : Fin (e' + 1) => M_adj j.succ) := by
  intro j k
  have eqr : (rMat + D) + j.1 * D + k.1 = rMat + (j.1 + 1) * D + k.1 := by ring
  rw [eqr]
  exact h j.succ k

theorem pullVec_id {D : ℕ} (w : Fin D → ℝ) :
    pullVec (fun j : Fin D => Pi.single j (1 : ℝ)) w = w := by
  ext j
  simp [pullVec, dotProduct, Pi.single_apply, ite_mul, Finset.sum_ite_eq']

theorem matIndep_id (D : ℕ) : MatIndep (fun j : Fin D => Pi.single j (1 : ℝ)) := by
  intro μ hsum
  ext k
  have hk := congr_fun hsum k
  simpa [Pi.single_apply] using hk

theorem matIndep_one_ne_zero {D : ℕ} {M_adj : Fin 1 → Fin D → ℝ} (h : MatIndep M_adj) :
    M_adj 0 ≠ 0 := by
  intro h0
  have hzero := h (fun _ => 1) (by simp [h0])
  have h10 : (1 : ℝ) = 0 := congr_fun hzero 0
  norm_num at h10

theorem matIndep_tail {e' D : ℕ} {M_adj : Fin (e' + 2) → Fin D → ℝ} (h : MatIndep M_adj) :
    MatIndep (fun j : Fin (e' + 1) => M_adj j.succ) := by
  intro μ hsum
  have hc := h (Fin.cons 0 μ) (by simp [Fin.sum_univ_succ, hsum])
  ext j
  simpa using congr_fun hc j.succ

theorem matIndep_shear {e' D : ℕ} {M_adj : Fin (e' + 2) → Fin D → ℝ} (h : MatIndep M_adj) (c : ℝ) :
    MatIndep (Fin.cons (M_adj 0 + c • M_adj 1) (fun k : Fin e' => M_adj k.succ.succ)) := by
  intro μ hsum
  have hexp : μ 0 • M_adj 0 + (μ 0 * c) • M_adj 1 +
      ∑ k : Fin e', μ k.succ • M_adj k.succ.succ = 0 := by
    rw [Fin.sum_univ_succ] at hsum
    simp only [Fin.cons_zero, Fin.cons_succ, smul_add, smul_smul] at hsum
    exact hsum
  let ν : Fin (e' + 2) → ℝ := Fin.cons (μ 0) (Fin.cons (μ 0 * c) (fun k => μ k.succ))
  have hν : (∑ i : Fin (e' + 2), ν i • M_adj i) = 0 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simpa [ν, add_assoc] using hexp
  have hν0 := h ν hν
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simpa [ν] using congr_fun hν0 0
  · simpa [ν] using congr_fun hν0 k.succ.succ

/-- Unrolled initialization of the `D × D` identity matrix at `rMat .. rMat + D * D - 1`. -/
noncomputable def initIdMatAux (D rMat : ℕ) : (j : ℕ) → j ≤ D → Stmt
  | 0, _ => .skip
  | j + 1, hj =>
    .seq (initIdMatAux D rMat j (Nat.le_of_succ_le hj))
      (.seq (zeroRegs D (rMat + j * D))
        (.prim (.const (rMat + j * D + j) 1)))

noncomputable def initIdMatStmt (D rMat : ℕ) : Stmt :=
  initIdMatAux D rMat D le_rfl

theorem initIdMatStmt_spec {rMin pMin : ℕ} {memBound : ℤ} (D : ℕ) {rMat : ℕ}
    (hMat : rMin ≤ rMat) (s : MState) :
    ∃ s', SpecRun rMin pMin memBound (initIdMatStmt D rMat) s s' (D * (D + 1)) ∧
      MatRegs s' rMat (fun j : Fin D => Pi.single j (1 : ℝ)) ∧
      (∀ i, i < rMat ∨ rMat + D * D ≤ i → s'.regs i = s.regs i) ∧
      s'.ptrs = s.ptrs ∧ s'.mem = s.mem := by
  have hAux : ∀ (j : ℕ) (hj : j ≤ D),
      ∃ s₁, SpecRun rMin pMin memBound (initIdMatAux D rMat j hj) s s₁ (j * (D + 1)) ∧
        (∀ (r : Fin D), r.1 < j → VecRegs s₁ (rMat + r.1 * D) (Pi.single r (1 : ℝ))) ∧
        (∀ i, i < rMat ∨ rMat + j * D ≤ i → s₁.regs i = s.regs i) ∧
        s₁.ptrs = s.ptrs ∧ s₁.mem = s.mem := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨s, by rw [zero_mul]; exact SpecRun.skip rMin pMin memBound s,
        fun _ hr => absurd hr (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨s₁, p1, hrows1, hoth1, hp1, hm1⟩ := ih (Nat.le_of_succ_le hj)
      obtain ⟨s₂, p2, hvZ, hothZ, hp2, hm2⟩ :=
        zeroRegs_spec (rMin := rMin) (pMin := pMin) (memBound := memBound) D
          (rDst := rMat + j * D) (by omega) s₁
      have p3 : SpecRun rMin pMin memBound (.prim (.const (rMat + j * D + j) 1)) s₂ _ 1 :=
        sprim
      set s₃ := (Prim.const (rMat + j * D + j) 1).step s₂
      have hstep : j * (D + 1) + (D + 1) = (j + 1) * (D + 1) := by ring
      refine ⟨s₃, (p1.seq (p2.seq p3)).mono (by omega), ?_, ?_, hp2.trans hp1, hm2.trans hm1⟩
      · intro r hr
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hr) with hlt | heq
        · have hr_end : r.1 * D + D ≤ j * D := by
            calc r.1 * D + D = (r.1 + 1) * D := by ring
              _ ≤ j * D := Nat.mul_le_mul_right D (by omega)
          exact (hrows1 r hlt).of_pres fun k hk => by
            simp only [s₃, Prim.step]
            rw [Function.update_of_ne (by omega), hothZ _ (by omega)]
        · subst heq
          intro k
          simp only [s₃, Prim.step]
          by_cases hkr : k = r
          · subst hkr
            simp
          · have hkr' : k.1 ≠ r.1 := fun e => hkr (Fin.ext e)
            rw [Function.update_of_ne (by omega), hvZ k, Pi.single_eq_of_ne hkr]; rfl
      · intro i hi
        have hjd : (j + 1) * D = j * D + D := by ring
        rw [hjd] at hi
        simp only [s₃, Prim.step]
        rw [Function.update_of_ne (by omega), hothZ i (by omega), hoth1 i (by omega)]
  obtain ⟨s', hrun, hrows, hoth, hp, hm⟩ := hAux D le_rfl
  exact ⟨s', hrun, fun j => hrows j j.2, hoth, hp, hm⟩

/-- Unrolled row-0 shear `rDst[k] := rRow0[k] + rC * rRow1[k]` (`k < D`), followed by copying `e' * D` regs. -/
noncomputable def shearRow0Aux (rDst rRow0 rRow1 rC rProd : ℕ) : ℕ → Stmt
  | 0 => .skip
  | k + 1 =>
    .seq (shearRow0Aux rDst rRow0 rRow1 rC rProd k)
      (.seq (.prim (.mul rProd rC (rRow1 + k)))
        (.prim (.add (rDst + k) (rRow0 + k) rProd)))

noncomputable def shearMatStmt (e' D rDst rMat rC rProd rZero : ℕ) : Stmt :=
  .seq (shearRow0Aux rDst rMat (rMat + D) rC rProd D)
    (copyRegs (e' * D) (rDst + D) (rMat + 2 * D) rZero)

theorem shearMatStmt_spec {rMin pMin e' D : ℕ} {memBound : ℤ}
    {rDst rMat rC rProd rZero : ℕ}
    {M_adj : Fin (e' + 2) → Fin D → ℝ} {c : ℝ} {s : MState}
    (hMat : MatRegs s rMat M_adj) (hc : s.regs rC = c)
    (hDst : rMin ≤ rDst) (hProd : rMin ≤ rProd) (hZero : rMin ≤ rZero)
    (hMatDst : rMat + (e' + 2) * D ≤ rDst)
    (hCDst : rC < rDst)
    (hDstProd : rDst + (e' + 1) * D ≤ rProd)
    (hProdZero : rProd < rZero) :
    ∃ s', SpecRun rMin pMin memBound (shearMatStmt e' D rDst rMat rC rProd rZero) s s'
        (2 * (e' + 1) * D + 2) ∧
      MatRegs s' rDst (Fin.cons (M_adj 0 + c • M_adj 1) (fun k : Fin e' => M_adj k.succ.succ)) ∧
      (∀ i, i < rDst → s'.regs i = s.regs i) ∧
      s'.ptrs = s.ptrs ∧ s'.mem = s.mem := by
  have hRow0 : ∀ (k : ℕ) (hkD : k ≤ D),
      ∃ s₁, SpecRun rMin pMin memBound (shearRow0Aux rDst rMat (rMat + D) rC rProd k) s s₁ (2 * k) ∧
        (∀ j (hj : j < k), s₁.regs (rDst + j) = M_adj 0 ⟨j, lt_of_lt_of_le hj hkD⟩ +
          c * M_adj 1 ⟨j, lt_of_lt_of_le hj hkD⟩) ∧
        (∀ i, (i < rDst ∨ rDst + k ≤ i) → i ≠ rProd → s₁.regs i = s.regs i) ∧
        s₁.ptrs = s.ptrs ∧ s₁.mem = s.mem := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨s, SpecRun.skip rMin pMin memBound s, fun _ hj => absurd hj (Nat.not_lt_zero _),
        fun _ _ _ => rfl, rfl, rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨s₁, p1, hv1, hoth1, hp1, hm1⟩ := ih (Nat.le_of_succ_le hk)
      have hMD : 2 * D ≤ (e' + 2) * D := by rw [add_mul]; omega
      have hDD : D ≤ (e' + 1) * D := by rw [add_mul, one_mul]; omega
      have q1 : SpecRun rMin pMin memBound (.prim (.mul rProd rC (rMat + D + k))) s₁ _ 1 := sprim
      set s₂ := (Prim.mul rProd rC (rMat + D + k)).step s₁
      have q2 : SpecRun rMin pMin memBound (.prim (.add (rDst + k) (rMat + k) rProd)) s₂ _ 1 := sprim
      set s₃ := (Prim.add (rDst + k) (rMat + k) rProd).step s₂
      refine ⟨s₃, (p1.seq (q1.seq q2)).mono (by omega), ?_, ?_, hp1, hm1⟩
      · intro j hj
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | rfl
        · simp only [s₃, s₂, Prim.step, Function.update_of_ne (show rDst + j ≠ rDst + k by omega),
            Function.update_of_ne (show rDst + j ≠ rProd by omega)]
          exact hv1 j hlt
        · simp only [s₃, s₂, Prim.step, Function.update_self,
            Function.update_of_ne (show rMat + j ≠ rProd by omega)]
          have hm0 := hMat 0 ⟨j, hk⟩
          have hm1_v := hMat 1 ⟨j, hk⟩
          simp only [Fin.val_zero, zero_mul, add_zero, Fin.val_one, one_mul] at hm0 hm1_v
          rw [hoth1 (rMat + j) (by omega) (by omega), hoth1 rC (by omega) (by omega),
              hoth1 (rMat + D + j) (by omega) (by omega), hm0, hc, hm1_v]
      · intro i hi hiP
        simp only [s₃, s₂, Prim.step, Function.update_of_ne (show i ≠ rDst + k by omega),
          Function.update_of_ne hiP]
        exact hoth1 i (by omega) hiP
  obtain ⟨s₁, pRow0, hv0, hoth0, hp0, hm0⟩ := hRow0 D le_rfl
  let flatRest : Fin (e' * D) → ℝ := fun idx => s.regs (rMat + 2 * D + idx.1)
  have hMD2 : 2 * D + e' * D = (e' + 2) * D := by ring
  have hED1 : D + e' * D = (e' + 1) * D := by ring
  have hvFlat1 : VecRegs s₁ (rMat + 2 * D) flatRest := by
    intro idx
    have := idx.2
    exact hoth0 (rMat + 2 * D + idx.1) (by omega) (by omega)
  obtain ⟨s₂, pCopy, hvCp, hothCp, hpCp, hmCp⟩ :=
    copyRegs_spec (rMin := rMin) (pMin := pMin) (memBound := memBound) (e' * D)
      (rDst := rDst + D) (rSrc := rMat + 2 * D) (rZero := rZero) (s := s₁)
      hvFlat1 (by omega) hZero (by omega) (by omega) (by omega)
  refine ⟨s₂, (pRow0.seq pCopy).mono (by ring_nf; omega), ?_, ?_, hpCp.trans hp0, hmCp.trans hm0⟩
  · intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · intro d_idx
      simp only [Fin.val_zero, zero_mul, add_zero, Fin.cons_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hothCp (rDst + d_idx.1) (by have := d_idx.2; omega) (by have := d_idx.2; omega)]
      exact hv0 d_idx.1 d_idx.2
    · intro d_idx
      simp only [Fin.val_succ, Fin.cons_succ]
      have hlt_ed : k.1 * D + d_idx.1 < e' * D := by
        have := k.2; have := d_idx.2
        calc k.1 * D + d_idx.1 < k.1 * D + D := by omega
          _ = (k.1 + 1) * D := by ring
          _ ≤ e' * D := Nat.mul_le_mul_right D (by omega)
      have eqDst : rDst + (k.1 + 1) * D + d_idx.1 = (rDst + D) + (k.1 * D + d_idx.1) := by ring
      have eqSrc : rMat + 2 * D + (k.1 * D + d_idx.1) = rMat + (k.1 + 2) * D + d_idx.1 := by ring
      rw [eqDst, hvCp ⟨k.1 * D + d_idx.1, hlt_ed⟩]
      dsimp only [flatRest]
      rw [eqSrc]
      exact hMat k.succ.succ d_idx
  · intro i hi
    rw [hothCp i (by omega) (by omega), hoth0 i (by omega) (by omega)]

/-- Linear-time Approach I hyperplane batch solver in dimension `D` on an `e`-dimensional subspace. -/
structure ApproachISolver (D e : ℕ) where
  C : ℕ
  mkStmt : (rCand rMat pTabStart pTabEnd pHypStart pHypEnd pArena pBase : ℕ) → Stmt
  spec : ∀ {m M : ℕ} (hm : 0 < m)
    {rCand rMat pTabStart pTabEnd pHypStart pHypEnd pArena pBase : ℕ}
    {A : Fin m → Fin D → ℝ} {b : Fin m → ℝ}
    {M_adj : Fin e → Fin D → ℝ}
    {H_q : Fin M → Fin e → ℝ} {γ_q : Fin M → ℝ}
    {xCand : Fin D → ℝ} {s : MState},
    RowTableAt s.mem (s.ptrs pTabStart) A b →
    A ⟨0, hm⟩ = 0 → b ⟨0, hm⟩ = 0 →
    s.ptrs pTabEnd = s.ptrs pTabStart + (m : ℤ) * ((D : ℤ) + 1) →
    s.ptrs pTabStart + (m : ℤ) * ((D : ℤ) + 1) ≤ s.ptrs pArena →
    RowTableAt s.mem (s.ptrs pHypStart) H_q γ_q →
    (∀ u : Fin M, H_q u ≠ 0) →
    s.ptrs pHypEnd = s.ptrs pHypStart + (M : ℤ) * ((e : ℤ) + 1) →
    s.ptrs pHypStart + (M : ℤ) * ((e : ℤ) + 1) ≤ s.ptrs pArena →
    MatRegs s rMat M_adj → MatIndep M_adj →
    VecRegs s rCand xCand → s.regs (rCand + D) = rInfeas hm A b xCand →
    rMat + e * D ≤ rCand →
    pTabStart < pBase → pTabEnd < pBase →
    pHypStart < pBase → pHypEnd < pBase → pArena < pBase →
    ∃ (s' : MState) (xCand' : Fin D → ℝ) (ans : Fin M → Option Ordering),
      SpecRun rCand pBase (s.ptrs pArena)
        (mkStmt rCand rMat pTabStart pTabEnd pHypStart pHypEnd pArena pBase)
        s s' (C * (m + M + 1)) ∧
      VecRegs s' rCand xCand' ∧
      s'.regs (rCand + D) = rInfeas hm A b xCand' ∧
      rInfeas hm A b xCand' ≤ rInfeas hm A b xCand ∧
      VecAt s'.mem (s.ptrs pArena) (fun u : Fin M => encodeOptOrd (ans u)) ∧
      (∀ (u : Fin M) (o : Ordering), ans u = some o →
        ∀ w : Fin D → ℝ, rInfeas hm A b w < rInfeas hm A b xCand' →
          compare (H_q u ⬝ᵥ pullVec M_adj w) (γ_q u) = o) ∧
      M / 2 ^ (2 ^ e - 1) ≤ (Finset.univ.filter fun u : Fin M => (ans u).isSome).card

/-! ## Base Case `e = 1`: 1D Ratio Median + Single Oracle Query -/

/-- Update `(rCand .. rCand + D)` to `(rOraOut .. rOraOut + D)` whenever `v' ≤ vCand`. -/
noncomputable def updateCandStmt (D rCand rOraOut rDiff rZero : ℕ) : Stmt :=
  .seq (.prim (.sub rDiff (rOraOut + D) (rCand + D)))
    (.ifLeZero rDiff (copyRegs (D + 1) rCand rOraOut rZero) .skip)

theorem updateCandStmt_spec {rMin pMin m D : ℕ} {memBound : ℤ} (hm : 0 < m)
    {rCand rOraOut rDiff rZero : ℕ}
    {A : Fin m → Fin D → ℝ} {b : Fin m → ℝ}
    {xCand x' : Fin D → ℝ} {s : MState}
    (hxC : VecRegs s rCand xCand) (hvC : s.regs (rCand + D) = rInfeas hm A b xCand)
    (hx' : VecRegs s rOraOut x') (hv' : s.regs (rOraOut + D) = rInfeas hm A b x')
    (hCand : rMin ≤ rCand) (hCO : rCand + D + 1 ≤ rOraOut)
    (hOD : rOraOut + D + 1 ≤ rDiff) (hDZ : rDiff < rZero) :
    ∃ (s' : MState) (xCand' : Fin D → ℝ),
      SpecRun rMin pMin memBound (updateCandStmt D rCand rOraOut rDiff rZero) s s' (2 * D + 6) ∧
      VecRegs s' rCand xCand' ∧
      s'.regs (rCand + D) = rInfeas hm A b xCand' ∧
      rInfeas hm A b xCand' ≤ rInfeas hm A b xCand ∧
      rInfeas hm A b xCand' ≤ rInfeas hm A b x' ∧
      (∀ i, (i < rCand ∨ rCand + D + 1 ≤ i) → i ≠ rDiff → i ≠ rZero → s'.regs i = s.regs i) ∧
      s'.ptrs = s.ptrs ∧ s'.mem = s.mem := by
  have p1 : SpecRun rMin pMin memBound (.prim (.sub rDiff (rOraOut + D) (rCand + D))) s _ 1 := sprim
  set s₁ := (Prim.sub rDiff (rOraOut + D) (rCand + D)).step s
  by_cases hle : rInfeas hm A b x' ≤ rInfeas hm A b xCand
  · have hcond : s₁.regs rDiff ≤ 0 := by
      simp only [s₁, Prim.step, Function.update_self, hv', hvC]; linarith
    let fullX' : Fin (D + 1) → ℝ := Fin.snoc x' (rInfeas hm A b x')
    have hvFull : VecRegs s₁ rOraOut fullX' := by
      intro j
      simp only [s₁, Prim.step, Function.update_of_ne (show rOraOut + j.1 ≠ rDiff by have := j.2; omega)]
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa [fullX'] using hv'
      · simpa [fullX'] using hx' k
    obtain ⟨s₂, p2, hvCp, hothCp, hpCp, hmCp⟩ :=
      copyRegs_spec (rMin := rMin) (pMin := pMin) (memBound := memBound) (D + 1)
        (rDst := rCand) (rSrc := rOraOut) (rZero := rZero) (s := s₁)
        hvFull hCand (by omega) (by omega) (by omega) (by omega)
    refine ⟨s₂, x',
      (p1.seq (SpecRun.ifLeZero_true (e := .skip) hcond p2)).mono (by omega),
      fun k => by simpa [fullX'] using hvCp k.castSucc,
      by simpa [fullX'] using hvCp (Fin.last D),
      hle, le_rfl, ?_, hpCp, hmCp⟩
    intro i hi hiD hiZ
    rw [hothCp i (by omega) hiZ]
    simp [s₁, Prim.step, Function.update_of_ne hiD]
  · have hcond : ¬ s₁.regs rDiff ≤ 0 := by
      simp only [s₁, Prim.step, Function.update_self, hv', hvC]; linarith
    refine ⟨s₁, xCand,
      (p1.seq (SpecRun.ifLeZero_false (t := copyRegs (D + 1) rCand rOraOut rZero) hcond
        (SpecRun.skip rMin pMin memBound s₁))).mono (by omega),
      hxC.of_pres fun k hk => Function.update_of_ne (by omega) _ _,
      by simp [s₁, Prim.step, Function.update_of_ne (show rCand + D ≠ rDiff by omega), hvC],
      le_rfl, le_of_not_ge hle,
      fun i _ hiD _ => Function.update_of_ne hiD _ _, rfl, rfl⟩

/-- Compute `encodeOptOrd (settle1D c σ h0 γ)` into `rAns` given `rC = c`, `rSig = encodeOrd σ`,
`rH0 = h0` (`h0 ≠ 0`), `rGam = γ`, using scratch `rScr .. rScr + 3` (`rT, rDiff, rZero, rNeg`). -/
noncomputable def settle1DRegsStmt (rAns rC rSig rH0 rGam rScr : ℕ) : Stmt :=
  let rT := rScr
  let rDiff := rScr + 1
  let rZero := rScr + 2
  let rNeg := rScr + 3
  let eqBranch : Stmt :=
    .seq (.prim (.mul rT rH0 rC))
      (.seq (.prim (.sub rDiff rT rGam))
        (ifEqZero rDiff rZero rNeg
          (.prim (.const rAns 2))
          (.ifLeZero rDiff (.prim (.const rAns 1)) (.prim (.const rAns 3)))))
  let ltBranch : Stmt :=
    .seq (.prim (.div rT rGam rH0))
      (.seq (.prim (.sub rDiff rC rT))
        (.ifLeZero rDiff
          (.ifLeZero rH0 (.prim (.const rAns 3)) (.prim (.const rAns 1)))
          (.prim (.const rAns 0))))
  let gtBranch : Stmt :=
    .seq (.prim (.div rT rGam rH0))
      (.seq (.prim (.sub rDiff rT rC))
        (.ifLeZero rDiff
          (.ifLeZero rH0 (.prim (.const rAns 1)) (.prim (.const rAns 3)))
          (.prim (.const rAns 0))))
  ifEqZero rSig rZero rNeg eqBranch (.ifLeZero rSig ltBranch gtBranch)

theorem settle1DRegsStmt_spec {rMin pMin : ℕ} {memBound : ℤ}
    {rAns rC rSig rH0 rGam rScr : ℕ}
    {c h0 γ : ℝ} {σ : Ordering} {s : MState}
    (hc : s.regs rC = c) (hSig : s.regs rSig = encodeOrd σ)
    (hh0 : s.regs rH0 = h0) (hγ : s.regs rGam = γ) (hh_ne : h0 ≠ 0)
    (hAns : rMin ≤ rAns) (hScr : rMin ≤ rScr)
    (hDisjIn : ∀ r ∈ [rC, rSig, rH0, rGam], r < rAns)
    (hAnsScr : rAns + 1 ≤ rScr) :
    ∃ s', SpecRun rMin pMin memBound (settle1DRegsStmt rAns rC rSig rH0 rGam rScr) s s' 20 ∧
      s'.regs rAns = encodeOptOrd (settle1D c σ h0 γ) ∧
      (∀ i, i < rAns → s'.regs i = s.regs i) ∧
      s'.ptrs = s.ptrs ∧ s'.mem = s.mem := by
  have hCA := hDisjIn rC (by simp)
  have hSA := hDisjIn rSig (by simp)
  have hHA := hDisjIn rH0 (by simp)
  have hGA := hDisjIn rGam (by simp)
  let rT := rScr
  let rDiff := rScr + 1
  let rZero := rScr + 2
  let rNeg := rScr + 3
  set s₀ := eqZeroPre rSig rZero rNeg s
  have hs₀_pres : ∀ i, i < rScr → s₀.regs i = s.regs i := fun i hi =>
    eqZeroPre_regs_other s (by omega) (by omega)
  cases σ with
  | eq =>
    have hsig0 : s.regs rSig = 0 := by simp [hSig, encodeOrd]
    have e1 : SpecRun rAns pMin memBound (.prim (.mul rT rH0 rC)) s₀ _ 1 := sprim
    have e2 : SpecRun rAns pMin memBound (.prim (.sub rDiff rT rGam))
        ((Prim.mul rT rH0 rC).step s₀) _ 1 := sprim
    set s₂ := (Prim.sub rDiff rT rGam).step ((Prim.mul rT rH0 rC).step s₀)
    have hdiff2 : s₂.regs rDiff = h0 * c - γ := by
      simp [s₂, Prim.step, Function.update_of_ne (show rGam ≠ rT by omega),
        hs₀_pres rH0 (by omega), hs₀_pres rC (by omega), hs₀_pres rGam (by omega), hh0, hc, hγ]
    set s₃ := eqZeroPre rDiff rZero rNeg s₂
    by_cases hd0 : h0 * c - γ = 0
    · have p4 : SpecRun rAns pMin memBound (.prim (.const rAns 2)) s₃ _ 1 := sprim
      have hInner := ifEqZero_true_spec (rMin := rAns) (pMin := pMin) (memBound := memBound)
        (e := .ifLeZero rDiff (.prim (.const rAns 1)) (.prim (.const rAns 3)))
        (by omega) (by omega) (by omega) (by omega) (by omega) (hdiff2.trans hd0) p4
      have hOuter : SpecRun rAns pMin memBound (settle1DRegsStmt rAns rC rSig rH0 rGam rScr) s _ _ :=
        ifEqZero_true_spec (rMin := rAns) (pMin := pMin) (memBound := memBound)
        (e := _) (by omega) (by omega) (by omega) (by omega) (by omega) hsig0 (e1.seq (e2.seq hInner))
      have hcmp : compare (h0 * c) γ = .eq := compare_eq_iff_eq.mpr (by linarith)
      exact ⟨_, (hOuter.weakenFrame hAns le_rfl le_rfl).mono (by omega),
        by simp [Prim.step, settle1D, hcmp, encodeOptOrd, encodeOrd],
        hOuter.regs_pres, rfl, rfl⟩
    · by_cases hdle : h0 * c - γ ≤ 0
      · have hdlt : h0 * c < γ := lt_of_sub_neg (lt_of_le_of_ne hdle hd0)
        have hle3 : s₃.regs rDiff ≤ 0 := by
          rw [eqZeroPre_regs_other s₂ (by omega) (by omega), hdiff2]; exact hdle
        have p4 : SpecRun rAns pMin memBound (.prim (.const rAns 1)) s₃ _ 1 := sprim
        have hInner := ifEqZero_false_spec (rMin := rAns) (pMin := pMin) (memBound := memBound)
          (t := .prim (.const rAns 2)) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by rw [hdiff2]; exact hd0)
          (SpecRun.ifLeZero_true (e := .prim (.const rAns 3)) hle3 p4)
        have hOuter : SpecRun rAns pMin memBound (settle1DRegsStmt rAns rC rSig rH0 rGam rScr) s _ _ :=
          ifEqZero_true_spec (rMin := rAns) (pMin := pMin) (memBound := memBound)
          (e := _) (by omega) (by omega) (by omega) (by omega) (by omega) hsig0 (e1.seq (e2.seq hInner))
        have hcmp : compare (h0 * c) γ = .lt := compare_lt_iff_lt.mpr hdlt
        exact ⟨_, (hOuter.weakenFrame hAns le_rfl le_rfl).mono (by omega),
          by simp [Prim.step, settle1D, hcmp, encodeOptOrd, encodeOrd]; norm_num,
          hOuter.regs_pres, rfl, rfl⟩
      · have hdgt : γ < h0 * c := by linarith
        have hnle3 : ¬ s₃.regs rDiff ≤ 0 := by
          rw [eqZeroPre_regs_other s₂ (by omega) (by omega), hdiff2]; exact hdle
        have p4 : SpecRun rAns pMin memBound (.prim (.const rAns 3)) s₃ _ 1 := sprim
        have hInner := ifEqZero_false_spec (rMin := rAns) (pMin := pMin) (memBound := memBound)
          (t := .prim (.const rAns 2)) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by rw [hdiff2]; exact hd0)
          (SpecRun.ifLeZero_false (t := .prim (.const rAns 1)) hnle3 p4)
        have hOuter : SpecRun rAns pMin memBound (settle1DRegsStmt rAns rC rSig rH0 rGam rScr) s _ _ :=
          ifEqZero_true_spec (rMin := rAns) (pMin := pMin) (memBound := memBound)
          (e := _) (by omega) (by omega) (by omega) (by omega) (by omega) hsig0 (e1.seq (e2.seq hInner))
        have hcmp : compare (h0 * c) γ = .gt := compare_gt_iff_gt.mpr hdgt
        exact ⟨_, (hOuter.weakenFrame hAns le_rfl le_rfl).mono (by omega),
          by simp [Prim.step, settle1D, hcmp, encodeOptOrd, encodeOrd]; norm_num,
          hOuter.regs_pres, rfl, rfl⟩
  | lt =>
    have hsig_ne : s.regs rSig ≠ 0 := by simp [hSig, encodeOrd]
    have hsig_le : s₀.regs rSig ≤ 0 := by rw [hs₀_pres rSig (by omega), hSig]; norm_num [encodeOrd]
    have l1 : SpecRun rAns pMin memBound (.prim (.div rT rGam rH0)) s₀ _ 1 := sprim
    have l2 : SpecRun rAns pMin memBound (.prim (.sub rDiff rC rT))
        ((Prim.div rT rGam rH0).step s₀) _ 1 := sprim
    set s₂ := (Prim.sub rDiff rC rT).step ((Prim.div rT rGam rH0).step s₀)
    have hdiff2 : s₂.regs rDiff = c - γ / h0 := by
      simp [s₂, Prim.step, Function.update_of_ne (show rC ≠ rT by omega),
        hs₀_pres rC (by omega), hs₀_pres rGam (by omega), hs₀_pres rH0 (by omega), hc, hγ, hh0]
    have hh2 : s₂.regs rH0 = h0 := by
      simp [s₂, Prim.step, Function.update_of_ne (show rH0 ≠ rDiff by omega),
        Function.update_of_ne (show rH0 ≠ rT by omega), hs₀_pres rH0 (by omega), hh0]
    by_cases hcle : c ≤ γ / h0
    · have hdle : s₂.regs rDiff ≤ 0 := by rw [hdiff2]; linarith
      by_cases hhle : h0 ≤ 0
      · have hhnotpos : ¬ 0 < h0 := not_lt.mpr hhle
        have p3 : SpecRun rAns pMin memBound (.prim (.const rAns 3)) s₂ _ 1 := sprim
        have hBr := l1.seq (l2.seq (SpecRun.ifLeZero_true (e := .prim (.const rAns 0)) hdle
          (SpecRun.ifLeZero_true (e := .prim (.const rAns 1)) (by rw [hh2]; exact hhle) p3)))
        have hOuter : SpecRun rAns pMin memBound (settle1DRegsStmt rAns rC rSig rH0 rGam rScr) s _ _ :=
          ifEqZero_false_spec (rMin := rAns) (pMin := pMin) (memBound := memBound)
          (t := _) (by omega) (by omega) (by omega) (by omega) (by omega) hsig_ne
          (SpecRun.ifLeZero_true (e := _) hsig_le hBr)
        exact ⟨_, (hOuter.weakenFrame hAns le_rfl le_rfl).mono (by omega),
          by simp [Prim.step, settle1D, hcle, scaleOrd, hhnotpos, Ordering.swap, encodeOptOrd, encodeOrd]; norm_num,
          hOuter.regs_pres, rfl, rfl⟩
      · have hhpos : 0 < h0 := lt_of_not_ge hhle
        have p3 : SpecRun rAns pMin memBound (.prim (.const rAns 1)) s₂ _ 1 := sprim
        have hBr := l1.seq (l2.seq (SpecRun.ifLeZero_true (e := .prim (.const rAns 0)) hdle
          (SpecRun.ifLeZero_false (t := .prim (.const rAns 3)) (by rw [hh2]; exact hhle) p3)))
        have hOuter : SpecRun rAns pMin memBound (settle1DRegsStmt rAns rC rSig rH0 rGam rScr) s _ _ :=
          ifEqZero_false_spec (rMin := rAns) (pMin := pMin) (memBound := memBound)
          (t := _) (by omega) (by omega) (by omega) (by omega) (by omega) hsig_ne
          (SpecRun.ifLeZero_true (e := _) hsig_le hBr)
        exact ⟨_, (hOuter.weakenFrame hAns le_rfl le_rfl).mono (by omega),
          by simp [Prim.step, settle1D, hcle, scaleOrd, hhpos, encodeOptOrd, encodeOrd]; norm_num,
          hOuter.regs_pres, rfl, rfl⟩
    · have hdnle : ¬ s₂.regs rDiff ≤ 0 := by rw [hdiff2]; linarith
      have p3 : SpecRun rAns pMin memBound (.prim (.const rAns 0)) s₂ _ 1 := sprim
      have hBr := l1.seq (l2.seq (SpecRun.ifLeZero_false
        (t := .ifLeZero rH0 (.prim (.const rAns 3)) (.prim (.const rAns 1))) hdnle p3))
      have hOuter : SpecRun rAns pMin memBound (settle1DRegsStmt rAns rC rSig rH0 rGam rScr) s _ _ :=
        ifEqZero_false_spec (rMin := rAns) (pMin := pMin) (memBound := memBound)
        (t := _) (by omega) (by omega) (by omega) (by omega) (by omega) hsig_ne
        (SpecRun.ifLeZero_true (e := _) hsig_le hBr)
      exact ⟨_, (hOuter.weakenFrame hAns le_rfl le_rfl).mono (by omega),
        by simp [Prim.step, settle1D, hcle, encodeOptOrd],
        hOuter.regs_pres, rfl, rfl⟩
  | gt =>
    have hsig_ne : s.regs rSig ≠ 0 := by simp [hSig, encodeOrd]
    have hsig_nle : ¬ s₀.regs rSig ≤ 0 := by rw [hs₀_pres rSig (by omega), hSig]; norm_num [encodeOrd]
    have g1 : SpecRun rAns pMin memBound (.prim (.div rT rGam rH0)) s₀ _ 1 := sprim
    have g2 : SpecRun rAns pMin memBound (.prim (.sub rDiff rT rC))
        ((Prim.div rT rGam rH0).step s₀) _ 1 := sprim
    set s₂ := (Prim.sub rDiff rT rC).step ((Prim.div rT rGam rH0).step s₀)
    have hdiff2 : s₂.regs rDiff = γ / h0 - c := by
      simp [s₂, Prim.step, Function.update_of_ne (show rC ≠ rT by omega),
        hs₀_pres rC (by omega), hs₀_pres rGam (by omega), hs₀_pres rH0 (by omega), hc, hγ, hh0]
    have hh2 : s₂.regs rH0 = h0 := by
      simp [s₂, Prim.step, Function.update_of_ne (show rH0 ≠ rDiff by omega),
        Function.update_of_ne (show rH0 ≠ rT by omega), hs₀_pres rH0 (by omega), hh0]
    by_cases hcle : γ / h0 ≤ c
    · have hdle : s₂.regs rDiff ≤ 0 := by rw [hdiff2]; linarith
      by_cases hhle : h0 ≤ 0
      · have hhnotpos : ¬ 0 < h0 := not_lt.mpr hhle
        have p3 : SpecRun rAns pMin memBound (.prim (.const rAns 1)) s₂ _ 1 := sprim
        have hBr := g1.seq (g2.seq (SpecRun.ifLeZero_true (e := .prim (.const rAns 0)) hdle
          (SpecRun.ifLeZero_true (e := .prim (.const rAns 3)) (by rw [hh2]; exact hhle) p3)))
        have hOuter : SpecRun rAns pMin memBound (settle1DRegsStmt rAns rC rSig rH0 rGam rScr) s _ _ :=
          ifEqZero_false_spec (rMin := rAns) (pMin := pMin) (memBound := memBound)
          (t := _) (by omega) (by omega) (by omega) (by omega) (by omega) hsig_ne
          (SpecRun.ifLeZero_false (t := _) hsig_nle hBr)
        exact ⟨_, (hOuter.weakenFrame hAns le_rfl le_rfl).mono (by omega),
          by simp [Prim.step, settle1D, hcle, scaleOrd, hhnotpos, Ordering.swap, encodeOptOrd, encodeOrd]; norm_num,
          hOuter.regs_pres, rfl, rfl⟩
      · have hhpos : 0 < h0 := lt_of_not_ge hhle
        have p3 : SpecRun rAns pMin memBound (.prim (.const rAns 3)) s₂ _ 1 := sprim
        have hBr := g1.seq (g2.seq (SpecRun.ifLeZero_true (e := .prim (.const rAns 0)) hdle
          (SpecRun.ifLeZero_false (t := .prim (.const rAns 1)) (by rw [hh2]; exact hhle) p3)))
        have hOuter : SpecRun rAns pMin memBound (settle1DRegsStmt rAns rC rSig rH0 rGam rScr) s _ _ :=
          ifEqZero_false_spec (rMin := rAns) (pMin := pMin) (memBound := memBound)
          (t := _) (by omega) (by omega) (by omega) (by omega) (by omega) hsig_ne
          (SpecRun.ifLeZero_false (t := _) hsig_nle hBr)
        exact ⟨_, (hOuter.weakenFrame hAns le_rfl le_rfl).mono (by omega),
          by simp [Prim.step, settle1D, hcle, scaleOrd, hhpos, encodeOptOrd, encodeOrd]; norm_num,
          hOuter.regs_pres, rfl, rfl⟩
    · have hdnle : ¬ s₂.regs rDiff ≤ 0 := by rw [hdiff2]; linarith
      have p3 : SpecRun rAns pMin memBound (.prim (.const rAns 0)) s₂ _ 1 := sprim
      have hBr := g1.seq (g2.seq (SpecRun.ifLeZero_false
        (t := .ifLeZero rH0 (.prim (.const rAns 1)) (.prim (.const rAns 3))) hdnle p3))
      have hOuter : SpecRun rAns pMin memBound (settle1DRegsStmt rAns rC rSig rH0 rGam rScr) s _ _ :=
        ifEqZero_false_spec (rMin := rAns) (pMin := pMin) (memBound := memBound)
        (t := _) (by omega) (by omega) (by omega) (by omega) (by omega) hsig_ne
        (SpecRun.ifLeZero_false (t := _) hsig_nle hBr)
      exact ⟨_, (hOuter.weakenFrame hAns le_rfl le_rfl).mono (by omega),
        by simp [Prim.step, settle1D, hcle, encodeOptOrd],
        hOuter.regs_pres, rfl, rfl⟩

/-- Construct `ApproachISolver D 1` from `ora : OracleSolver D`. -/
noncomputable def approachIOneStmt {D : ℕ} (ora : OracleSolver D)
    (rCand rMat pTabStart pTabEnd pHypStart pHypEnd pArena pBase : ℕ) : Stmt :=
  let rC      := rCand + D + 1
  let rOraOut := rCand + D + 2            -- D + 2 regs: x', v', encodeOrd σ
  let rSig    := rOraOut + D + 1
  let rH0     := rOraOut + D + 2
  let rGam    := rOraOut + D + 3
  let rAns    := rOraOut + D + 4
  let rScr    := rOraOut + D + 5          -- 16 regs for selectMedianStmt / settle1DRegsStmt
  let pScan   := pBase
  let pWrite  := pBase + 1
  let pSub    := pBase + 2
  let buildRatios : Stmt :=
    Stmt.block [
      .prim (.pcopy pScan pHypStart),
      .prim (.pcopy pWrite pArena),
      .whilePtrLt pScan pHypEnd
        (Stmt.block [
          loadRow 1 rH0 rGam pScan,
          .prim (.div rAns rGam rH0),
          .prim (.store pWrite rAns),
          .prim (.pinc pWrite)])]
  let settleLoop : Stmt :=
    Stmt.block [
      .prim (.pcopy pScan pHypStart),
      .prim (.pcopy pWrite pArena),
      .whilePtrLt pScan pHypEnd
        (Stmt.block [
          loadRow 1 rH0 rGam pScan,
          settle1DRegsStmt rAns rC rSig rH0 rGam rScr,
          .prim (.store pWrite rAns),
          .prim (.pinc pWrite)])]
  .ifPtrLe pHypEnd pHypStart .skip
    (Stmt.block [
      buildRatios,
      selectMedianStmt rC pArena pWrite pWrite rScr pSub,
      ora.mkStmt rOraOut rMat rC pTabStart pTabEnd pArena pSub,
      updateCandStmt D rCand rOraOut rScr (rScr + 1),
      settleLoop])

set_option maxHeartbeats 400000 in
noncomputable def buildApproachIOne {D : ℕ} (ora : OracleSolver D) : ApproachISolver D 1 where
  C := ora.C + C_select + 2 * D + 60
  mkStmt := approachIOneStmt ora
  spec := by
    intro m M hm rCand rMat pTabStart pTabEnd pHypStart pHypEnd pArena pBase
      A b M_adj H_q γ_q xCand s
      hTab hA0 hb0 hTabEnd hTabAr hHyp hHypNe hHypEnd hHypAr
      hMat hIndep hxCand hvCand hMC hpTS hpTE hpHS hpHE hpAr
    set arena := s.ptrs pArena
    rcases Nat.eq_zero_or_pos M with rfl | hMpos
    · have hle : s.ptrs pHypEnd ≤ s.ptrs pHypStart := by rw [hHypEnd]; omega
      exact ⟨s, xCand, Fin.elim0,
        (SpecRun.ifPtrLe_true (e := _) hle (SpecRun.skip rCand pBase arena s)).mono
          (le_trans (by norm_num) (Nat.mul_le_mul (Nat.le_add_left 60 (ora.C + C_select + 2 * D))
            (Nat.le_add_left 1 (m + 0)))),
        hxCand, hvCand, le_rfl, fun u => Fin.elim0 u, fun u => Fin.elim0 u, by simp⟩
    · have hgt : ¬ s.ptrs pHypEnd ≤ s.ptrs pHypStart := by rw [hHypEnd]; omega
      let rC      := rCand + D + 1
      let rOraOut := rCand + D + 2
      let rSig    := rOraOut + D + 1
      let rH0     := rOraOut + D + 2
      let rGam    := rOraOut + D + 3
      let rAns    := rOraOut + D + 4
      let rScr    := rOraOut + D + 5
      let pScan   := pBase
      let pWrite  := pBase + 1
      let pSub    := pBase + 2
      -- Step 1: `buildRatios` into `[arena .. arena + M)`
      let ratios : Fin M → ℝ := fun u => γ_q u / H_q u 0
      have r1 : SpecRun rC pBase arena (.prim (.pcopy pScan pHypStart)) s _ 1 := sprim
      have r2 : SpecRun rC pBase arena (.prim (.pcopy pWrite pArena))
          ((Prim.pcopy pScan pHypStart).step s) _ 1 := sprim
      set sr₀ := (Prim.pcopy pWrite pArena).step ((Prim.pcopy pScan pHypStart).step s)
      let ratioBody : Stmt :=
        Stmt.block [loadRow 1 rH0 rGam pScan, .prim (.div rAns rGam rH0),
          .prim (.store pWrite rAns), .prim (.pinc pWrite)]
      let InvR : ℕ → MState → Prop := fun t st =>
        MemPreservedBelow arena s.mem st.mem ∧
        (∀ (u : Fin M), u.1 < t → st.mem (arena + (u.1 : ℤ)) = ratios u) ∧
        st.ptrs pScan = s.ptrs pHypStart + (t : ℤ) * 2 ∧
        st.ptrs pWrite = arena + (t : ℤ) ∧
        (∀ q < pBase, st.ptrs q = s.ptrs q) ∧
        (∀ r < rC, st.regs r = s.regs r)
      have hLoopR := SpecRun.forLoop (rMin := rC) (pMin := pBase) (memBound := arena)
        (q₁ := pScan) (q₂ := pHypEnd) (body := ratioBody) M 7 InvR
        (fun t ht st hInv => by
          obtain ⟨hmP, hRat, hpS, hpW, hpo, hro⟩ := hInv
          let u_t : Fin M := ⟨t, ht⟩
          refine ⟨by rw [hpS, hpo pHypEnd hpHE, hHypEnd]; omega, ?_⟩
          have hHyp_st := hHyp.of_mem_pres hmP (by simpa using hHypAr)
          obtain ⟨hHu, hγu⟩ := hHyp_st u_t
          have hpS_eq : st.ptrs pScan = s.ptrs pHypStart + (u_t.1 : ℤ) * (((1 : ℕ) : ℤ) + 1) := by
            show st.ptrs pScan = s.ptrs pHypStart + (t : ℤ) * (((1 : ℕ) : ℤ) + 1)
            rw [hpS]; push_cast; ring
          rw [← hpS_eq] at hHu hγu
          obtain ⟨st₁, q1, hvH1, hγ1, hoth1, hp1, hm1⟩ :=
            loadRow_spec (rMin := rC) (pMin := pBase) (memBound := arena) 1
              (rA := rH0) (rB := rGam) (q := pScan) hHu hγu (by omega) (by omega) (by omega) le_rfl
          have q2 : SpecRun rC pBase arena (.prim (.div rAns rGam rH0)) st₁ _ 1 := sprim
          set st₂ := (Prim.div rAns rGam rH0).step st₁
          have hpW2 : st₂.ptrs pWrite = arena + (t : ℤ) := by
            simp [st₂, Prim.step, hp1, Function.update_of_ne (show pWrite ≠ pScan by omega), hpW]
          have q3 : SpecRun rC pBase arena (.prim (.store pWrite rAns)) st₂ _ 1 :=
            SpecRun.prim trivial (by intro _ _ h; cases h; rw [hpW2]; omega)
          have q4 : SpecRun rC pBase arena (.prim (.pinc pWrite))
              ((Prim.store pWrite rAns).step st₂) _ 1 := sprim
          set st₄ := (Prim.pinc pWrite).step ((Prim.store pWrite rAns).step st₂)
          have hBody : SpecRun rC pBase arena ratioBody st st₄ 7 :=
            (q1.seq (q2.seq (q3.seq q4))).mono (by omega)
          have hans2 : st₂.regs rAns = ratios u_t := by
            have hh0_1 := hvH1 0
            simp only [Fin.val_zero, add_zero] at hh0_1
            simp [st₂, Prim.step, hγ1, hh0_1, ratios]
          refine ⟨st₄, hBody, hmP.trans hBody.mem_pres, ?_,
            by simp [st₄, st₂, Prim.step, hp1, Function.update_of_ne (show pScan ≠ pWrite by omega), hpS]; ring,
            by simp [st₄, Prim.step, hpW2]; ring,
            fun q hq => (hBody.ptrs_pres q hq).trans (hpo q hq),
            fun r hr => (hBody.regs_pres r hr).trans (hro r hr)⟩
          intro u hu
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hu) with hlt | heq
          · simp only [st₄, Prim.step, hpW2]
            rw [Function.update_of_ne (by omega)]
            simpa [st₂, Prim.step, hm1] using hRat u hlt
          · have hueq : u = u_t := Fin.ext heq
            subst hueq
            simp [st₄, Prim.step, hpW2, hans2, heq])
        (fun st hInv => by
          obtain ⟨_, _, hpS, _, hpo, _⟩ := hInv
          rw [hpS, hpo pHypEnd hpHE, hHypEnd]; simp)
        M le_rfl sr₀
        ⟨MemPreservedBelow.refl _ _, fun _ h => by simp at h,
         by simp [sr₀, Prim.step, Function.update_of_ne (show pScan ≠ pWrite by omega)],
         by simp [sr₀, Prim.step, Function.update_of_ne (show pArena ≠ pScan by omega), arena],
         fun q hq => by simp [sr₀, Prim.step, Function.update_of_ne (show q ≠ pWrite by omega),
           Function.update_of_ne (show q ≠ pScan by omega)],
         fun _ _ => rfl⟩
      obtain ⟨s₁, hrLoop, hmP1, hRat1, _, hpW1, hpo1, hro1⟩ := hLoopR
      have hBuildR : SpecRun rC pBase arena _ s s₁ (9 * M + 3) :=
        (r1.seq (r2.seq hrLoop)).mono (by omega)
      -- Step 2: `selectMedianStmt` on `[pArena .. pWrite)`
      have hVecRat : VecAt s₁.mem (s₁.ptrs pArena) ratios := by
        rw [hpo1 pArena hpAr]; exact fun u => hRat1 u u.2
      obtain ⟨s₂, hSel, hcL, hcG, hregs2, hptrs2, hmP2⟩ :=
        selectMedianStmt_spec (rMin := rC) (pMin := pBase) (memBound := arena)
          (rOut := rC) (pArrStart := pArena) (pArrEnd := pWrite) (pArena := pWrite)
          (rBase := rScr) (pBase := pSub) (arr := ratios) (s := s₁)
          hVecRat (by rw [hpW1, hpo1 pArena hpAr]) (by rw [hpW1, hpo1 pArena hpAr])
          (by rw [hpW1]; omega) le_rfl (by omega) (by omega) (by omega) (by omega) (by omega)
      set c := s₂.regs rC
      -- Step 3: `ora.mkStmt` on `(h := M_adj 0, β := c)`
      have hPre2 := hBuildR.seq hSel
      have hpAr2 : s₂.ptrs pArena = arena := hPre2.ptrs_pres pArena hpAr
      have hTab2 : RowTableAt s₂.mem (s₂.ptrs pTabStart) A b := by
        rw [hPre2.ptrs_pres pTabStart hpTS]
        exact hTab.of_mem_pres hPre2.mem_pres hTabAr
      have hMat0_2 : VecRegs s₂ rMat (M_adj 0) := by
        have h0 : VecRegs s rMat (M_adj 0) := by simpa using hMat 0
        exact h0.of_pres fun k hk => hPre2.regs_pres (rMat + k) (by omega)
      obtain ⟨s₃, x', σ, hOra_raw, hx'3, hv'3, hSig3, hOraSound⟩ :=
        ora.spec hm (rOut := rOraOut) (rH := rMat) (rBeta := rC)
          (pTabStart := pTabStart) (pTabEnd := pTabEnd) (pArena := pArena) (pBase := pSub)
          (s := s₂) hTab2 hA0 hb0
          (by rw [hPre2.ptrs_pres pTabEnd hpTE, hPre2.ptrs_pres pTabStart hpTS, hTabEnd])
          (by rw [hPre2.ptrs_pres pTabStart hpTS, hpAr2]; exact hTabAr)
          (by simpa using hMat0_2) rfl (matIndep_one_ne_zero hIndep)
          (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [hpAr2] at hOra_raw
      have hOra : SpecRun rC pBase arena _ s₂ s₃ (ora.C * (m + 1)) :=
        hOra_raw.weakenFrame (by omega) (by omega) le_rfl
      -- Step 4: `updateCandStmt`
      have hPre3 := hPre2.seq hOra
      have hxCand3 : VecRegs s₃ rCand xCand :=
        hxCand.of_pres fun k hk => hPre3.regs_pres (rCand + k) (by omega)
      have hvCand3 : s₃.regs (rCand + D) = rInfeas hm A b xCand :=
        (hPre3.regs_pres (rCand + D) (by omega)).trans hvCand
      obtain ⟨s₄, xCand', hUpd, hxCand4, hvCand4, hleCand, hleOra, hothUpd, hpUpd, hmUpd⟩ :=
        updateCandStmt_spec (rMin := rCand) (pMin := pBase) (memBound := arena) hm
          (rCand := rCand) (rOraOut := rOraOut) (rDiff := rScr) (rZero := rScr + 1)
          hxCand3 hvCand3 hx'3 hv'3 le_rfl (by omega) (by omega) (by omega)
      -- Step 5: `settleLoop` into `[arena .. arena + M)`
      let ans : Fin M → Option Ordering := fun u => settle1D c σ (H_q u 0) (γ_q u)
      have hc4 : s₄.regs rC = c := by
        rw [hothUpd rC (by omega) (by omega) (by omega), hOra_raw.regs_pres rC (by omega)]
      have hSig4 : s₄.regs rSig = encodeOrd σ := by
        rw [hothUpd rSig (by omega) (by omega) (by omega), hSig3]
      have hPre4 := (hPre3.weakenFrame (by omega) le_rfl le_rfl).seq hUpd
      have sl1 : SpecRun rC pBase arena (.prim (.pcopy pScan pHypStart)) s₄ _ 1 := sprim
      have sl2 : SpecRun rC pBase arena (.prim (.pcopy pWrite pArena))
          ((Prim.pcopy pScan pHypStart).step s₄) _ 1 := sprim
      set ss₀ := (Prim.pcopy pWrite pArena).step ((Prim.pcopy pScan pHypStart).step s₄)
      let settleBody : Stmt :=
        Stmt.block [loadRow 1 rH0 rGam pScan, settle1DRegsStmt rAns rC rSig rH0 rGam rScr,
          .prim (.store pWrite rAns), .prim (.pinc pWrite)]
      let InvSet : ℕ → MState → Prop := fun t st =>
        MemPreservedBelow arena s.mem st.mem ∧
        (∀ (u : Fin M), u.1 < t → st.mem (arena + (u.1 : ℤ)) = encodeOptOrd (ans u)) ∧
        st.ptrs pScan = s.ptrs pHypStart + (t : ℤ) * 2 ∧
        st.ptrs pWrite = arena + (t : ℤ) ∧
        (∀ q < pBase, st.ptrs q = s.ptrs q) ∧
        (∀ r < rH0, st.regs r = s₄.regs r)
      have hLoopSet := SpecRun.forLoop (rMin := rC) (pMin := pBase) (memBound := arena)
        (q₁ := pScan) (q₂ := pHypEnd) (body := settleBody) M 26 InvSet
        (fun t ht st hInv => by
          obtain ⟨hmP, hAnsM, hpS, hpW, hpo, hro⟩ := hInv
          let u_t : Fin M := ⟨t, ht⟩
          refine ⟨by rw [hpS, hpo pHypEnd hpHE, hHypEnd]; omega, ?_⟩
          have hHyp_st := hHyp.of_mem_pres hmP (by simpa using hHypAr)
          obtain ⟨hHu, hγu⟩ := hHyp_st u_t
          have hpS_eq : st.ptrs pScan = s.ptrs pHypStart + (u_t.1 : ℤ) * (((1 : ℕ) : ℤ) + 1) := by
            show st.ptrs pScan = s.ptrs pHypStart + (t : ℤ) * (((1 : ℕ) : ℤ) + 1)
            rw [hpS]; push_cast; ring
          rw [← hpS_eq] at hHu hγu
          obtain ⟨st₁, q1, hvH1, hγ1, hoth1, hp1, hm1⟩ :=
            loadRow_spec (rMin := rH0) (pMin := pBase) (memBound := arena) 1
              (rA := rH0) (rB := rGam) (q := pScan) hHu hγu le_rfl (by omega) (by omega) le_rfl
          have hh0_ne : H_q u_t 0 ≠ 0 := by
            intro h0
            apply hHypNe u_t
            ext j; fin_cases j; exact h0
          have hh0_1 : st₁.regs rH0 = H_q u_t 0 := by simpa using hvH1 0
          obtain ⟨st₂, q2, hans2, hoth2, hp2, hm2⟩ :=
            settle1DRegsStmt_spec (rMin := rH0) (pMin := pBase) (memBound := arena)
              (rAns := rAns) (rC := rC) (rSig := rSig) (rH0 := rH0) (rGam := rGam) (rScr := rScr)
              (s := st₁)
              (by rw [hoth1 rC (by omega) (by omega), hro rC (by omega), hc4])
              (by rw [hoth1 rSig (by omega) (by omega), hro rSig (by omega), hSig4])
              hh0_1 hγ1 hh0_ne (by omega) (by omega)
              (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                  rcases hr with rfl | rfl | rfl | rfl <;> omega)
              (by omega)
          have hpW2 : st₂.ptrs pWrite = arena + (t : ℤ) := by
            rw [hp2, hp1, Function.update_of_ne (show pWrite ≠ pScan by omega), hpW]
          have q3 : SpecRun rH0 pBase arena (.prim (.store pWrite rAns)) st₂ _ 1 :=
            SpecRun.prim trivial (by intro _ _ h; cases h; rw [hpW2]; omega)
          have q4 : SpecRun rH0 pBase arena (.prim (.pinc pWrite))
              ((Prim.store pWrite rAns).step st₂) _ 1 := sprim
          set st₄ := (Prim.pinc pWrite).step ((Prim.store pWrite rAns).step st₂)
          have hBodyH : SpecRun rH0 pBase arena settleBody st st₄ 26 :=
            (q1.seq (q2.seq (q3.seq q4))).mono (by omega)
          have hBody : SpecRun rC pBase arena settleBody st st₄ 26 :=
            hBodyH.weakenFrame (by omega) le_rfl le_rfl
          refine ⟨st₄, hBody, hmP.trans hBody.mem_pres, ?_,
            by simp [st₄, Prim.step, hp2, hp1, Function.update_of_ne (show pScan ≠ pWrite by omega), hpS]; ring,
            by simp [st₄, Prim.step, hpW2]; ring,
            fun q hq => (hBody.ptrs_pres q hq).trans (hpo q hq),
            fun r hr => (hBodyH.regs_pres r hr).trans (hro r hr)⟩
          intro u hu
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hu) with hlt | heq
          · simp only [st₄, Prim.step, hpW2]
            rw [Function.update_of_ne (by omega), hm2, hm1]
            exact hAnsM u hlt
          · have hueq : u = u_t := Fin.ext heq
            subst hueq
            simp [st₄, Prim.step, hpW2, hans2, ans, heq])
        (fun st hInv => by
          obtain ⟨_, _, hpS, _, hpo, _⟩ := hInv
          rw [hpS, hpo pHypEnd hpHE, hHypEnd]; simp)
        M le_rfl ss₀
        ⟨hPre4.mem_pres, fun _ h => by simp at h,
         by simp [ss₀, Prim.step, Function.update_of_ne (show pScan ≠ pWrite by omega),
             hPre4.ptrs_pres pHypStart hpHS],
         by simp [ss₀, Prim.step, Function.update_of_ne (show pArena ≠ pScan by omega),
             hPre4.ptrs_pres pArena hpAr, arena],
         fun q hq => by simp [ss₀, Prim.step, Function.update_of_ne (show q ≠ pWrite by omega),
             Function.update_of_ne (show q ≠ pScan by omega), hPre4.ptrs_pres q hq],
         fun _ _ => rfl⟩
      obtain ⟨s₅, hSetRun, _, hAns5, _, _, _, hro5⟩ := hLoopSet
      have hSettle : SpecRun rCand pBase arena _ s₄ s₅ (28 * M + 3) :=
        ((sl1.seq (sl2.seq hSetRun)).weakenFrame (by omega) le_rfl le_rfl).mono (by omega)
      have hAll := SpecRun.ifPtrLe_false (t := .skip) hgt
        ((hBuildR.weakenFrame (by omega) le_rfl le_rfl).seq
          ((hSel.weakenFrame (by omega) le_rfl le_rfl).seq
            ((hOra.weakenFrame (by omega) le_rfl le_rfl).seq
              (hUpd.seq hSettle))))
      have hTimeBnd : (9 * M + 3) + (C_select * (M + 1) +
          (ora.C * (m + 1) + ((2 * D + 6) + (28 * M + 3)))) + 2 ≤
          (ora.C + C_select + 2 * D + 60) * (m + M + 1) := by
        clear * -
        have h1 : ora.C * (m + 1) ≤ ora.C * (m + M + 1) := Nat.mul_le_mul_left _ (by omega)
        have h2 : C_select * (M + 1) ≤ C_select * (m + M + 1) := Nat.mul_le_mul_left _ (by omega)
        have h3 : (2 * D + 60) * 1 + 37 * M ≤ (2 * D + 60) * (m + M + 1) := by
          have : (2 * D + 60) * (m + M + 1) = (2 * D + 60) * m + (2 * D + 60) * M + (2 * D + 60) := by ring
          have h5 : 60 * M ≤ (2 * D + 60) * M := Nat.mul_le_mul_right M (by omega)
          omega
        have h4 : (ora.C + C_select + 2 * D + 60) * (m + M + 1) =
            ora.C * (m + M + 1) + C_select * (m + M + 1) + (2 * D + 60) * (m + M + 1) := by ring
        omega
      refine ⟨s₅, xCand', ans, hAll.mono hTimeBnd,
        hxCand4.of_pres fun k hk => hro5 (rCand + k) (by omega),
        (hro5 (rCand + D) (by omega)).trans hvCand4,
        hleCand,
        fun u => hAns5 u u.2,
        ?_, ?_⟩
      · intro u o hset w hw
        have hh0_ne : H_q u 0 ≠ 0 := by
          intro h0; apply hHypNe u; ext j; fin_cases j; exact h0
        have hcmp0 := hOraSound w (lt_of_lt_of_le hw hleOra)
        have hdot : H_q u ⬝ᵥ pullVec M_adj w = H_q u 0 * (M_adj 0 ⬝ᵥ w) := by
          simp [dotProduct, pullVec]
        rw [hdot]
        exact settle1D_sound hh0_ne hcmp0 hset
      · simpa using settle1D_count (fun u => H_q u 0) γ_q c σ hcL hcG

end MegiddoLP.ApproachI


