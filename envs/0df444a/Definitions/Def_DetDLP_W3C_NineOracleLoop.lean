-- Prove2me | Definitions.Def_DetDLP_W3C_NineOracleLoop
-- name    : DetDLP_W3C_NineOracleLoop
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:15:47.455802+00:00
-- url     : https://prove2.me/theorems/fca5e7dc-79e9-4be0-ade1-60640a4100ca
-- title:
--   Nine-way oracle multiplexer and PolyT loop wrapper for Stage II
-- statement:
--   For $j=3i+k$, `tag9` prefixes a query with the ternary dispatch codes for $i$ and $k$. The theorem `nine_oracle_mux` realizes all nine machines on a common output tape with time $K(t+|x|+1)$ and space $K(s+|x|+1)$. For a polynomial-time controller, `nine_oracle_polyT_loop` compiles the resulting interaction into one primitive machine. With at most $r$ rounds, encoded intermediate words of length at most $n$, and subroutine budgets $(\tau,\sigma)$, its time is bounded by $r(P_C(n)+C(\tau+\sigma+1))$ and its space by $P_C(n)+C(\sigma+1)$, where $P_C(n)=C(n+1)^C$. The constant $C$ is independent of the trace.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Theorems.Thm_DetDLP_d4b_three_oracle_mux
import Theorems.Thm_DetDLP_m89_polyT_oracle_loop
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_P2M_Groundwork_PolyT_cons__3a60f43a3b86
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f

set_option autoImplicit false
namespace DetDLP.W3C.NineOracleLoop
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace DetDLP.MachineComposition

abbrev Word := List Bool
private def tag3 (i : Fin 3) (x : Word) := if i = 0 then false :: x else true :: decide (i = 2) :: x
private def row (j : Fin 9) : Fin 3 := ⟨j.val / 3, by omega⟩
private def col (j : Fin 9) : Fin 3 := ⟨j.val % 3, by omega⟩
private def idx (i k : Fin 3) : Fin 9 := ⟨3*i.val + k.val, by omega⟩
/-- The first ternary digit selects the group; the second selects its member. -/
def tag9 (j : Fin 9) (x : Word) := tag3 (row j) (tag3 (col j) x)

attribute [local fun_prop] Groundwork.PolyT.const P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_id__1c5d0f44cc8f
theorem tag9_poly (j : Fin 9) : Groundwork.PolyT (tag9 j) := by
  unfold tag9 tag3; split <;> split <;> fun_prop

theorem nine_oracle_mux (A : Fin 9 → PrimitiveMachine) (o : ∀ j, Fin (A j).tapeCount) :
    ∃ (O : PrimitiveMachine) (K : ℕ), 1 ≤ K ∧ ∀ j (x y : Word) (t s : ℝ), 0 ≤ t → 0 ≤ s →
      RunsWithin (A j) (o j) x y t s → RunsWithin O O.inputTape (tag9 j x) y
        (K * (t + x.length + 1)) (K * (s + x.length + 1)) := by
  choose B k hB using fun i => d4b_three_oracle_mux (fun l => A (idx i l)) (fun l => o (idx i l))
  obtain ⟨O,b,hO⟩ := d4b_three_oracle_mux B (fun i => (B i).inputTape)
  let d := ∑ i, k i
  refine ⟨O,b*(d+3)+1,by omega,?_⟩
  intro j x y t s ht hs hr
  have hij : idx (row j) (col j) = j := Fin.ext (by dsimp [idx,row,col]; omega)
  have inner := hB (row j) (col j) x y t s (by rw [hij]; exact hr)
  have outer := hO (row j) (tag3 (col j) x) y _ _ inner
  have hk : (k (row j) : ℝ) ≤ d := by exact_mod_cast Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (row j))
  have hl : (tag3 (col j) x).length ≤ x.length + 2 := by unfold tag3; split <;> simp
  have bound (u : ℝ) (hu : 0 ≤ u) :
      b * (k (row j) * (u + x.length + 1) + (tag3 (col j) x).length + 1) ≤
      ((b*(d+3)+1 : ℕ) : ℝ) * (u + x.length + 1) := by
    push_cast
    calc
      _ ≤ (b : ℝ) * ((d+3) * (u + x.length + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hl' : ((tag3 (col j) x).length : ℝ) ≤ x.length + 2 := by exact_mod_cast hl
        nlinarith [mul_le_mul_of_nonneg_right hk (show 0 ≤ u + x.length + 1 by positivity), Nat.cast_nonneg (α := ℝ) x.length]
      _ ≤ _ := by nlinarith [Nat.cast_nonneg (α := ℝ) x.length]
  exact runsWithin_mono outer (bound t ht) (bound s hs)

def pairWord (x y : Word) := x.flatMap (fun b => [true,b]) ++ [false] ++ y
/-- A halting round returns its output; a calling round passes the answer to the next state. -/
def LoopRuns (step : Word → Word) (call : Word → Word → Prop) : ℕ → Word → Word → Word → ℕ → Prop :=
  Nat.rec (fun _ _ _ _ => False) (fun _ prev st ans out n =>
    (step (pairWord st ans) = true :: out ∧ (pairWord st ans).length ≤ n ∧ out.length ≤ n) ∨
    ∃ st' q ans', step (pairWord st ans) = false :: pairWord st' q ∧ (pairWord st ans).length ≤ n ∧
      (pairWord st' q).length ≤ n ∧ ans'.length ≤ n ∧ call q ans' ∧ prev st' ans' out n)

def NineCall (A : Fin 9 → PrimitiveMachine) (o : ∀ j, Fin (A j).tapeCount) (τ σ : ℝ) (w y : Word) :=
  ∃ j q, w = tag9 j q ∧ RunsWithin (A j) (o j) q y τ σ

private def coeff (b d : ℕ) := b + 2*b*d + 1
private theorem absorb (b d n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    polyBound b n + b * (d*u + 2*d*(n+1) + 1) ≤ polyBound (coeff b d) n + (coeff b d : ℝ)*(u+1) := by
  let C := coeff b d
  have hn : 1 ≤ (n : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hp := pow_le_pow_right₀ hn (show b ≤ C by dsimp [C,coeff]; omega)
  have hl := pow_le_pow_right₀ hn (show 1 ≤ C by dsimp [C,coeff]; omega)
  rw [pow_one] at hl
  have hcoef : (b : ℝ)*d ≤ C := by dsimp [C,coeff]; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) b, Nat.cast_nonneg (α := ℝ) (b*d), mul_nonneg (Nat.cast_nonneg (α := ℝ) b) (Nat.cast_nonneg (α := ℝ) d)]
  have h₁ := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α := ℝ) b)
  have h₂ := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*(b:ℝ)*d by positivity)
  have h₃ := mul_le_mul_of_nonneg_right hcoef hu
  change _ ≤ (C:ℝ)*((n:ℝ)+1)^C + C*(u+1)
  have hc : (C:ℝ) = b + 2*(b:ℝ)*d + 1 := by simp [C,coeff]
  unfold polyBound; rw [hc]; nlinarith [pow_nonneg (by positivity : 0 ≤ (n:ℝ)+1) C, mul_nonneg (Nat.cast_nonneg (α := ℝ) b) (Nat.cast_nonneg (α := ℝ) d)]

/-- Uniform compilation of tagged calls, charging for temporary query words but reusing oracle space. -/
theorem nine_oracle_polyT_loop (step : Word → Word) (hstep : Groundwork.PolyT step)
    (A : Fin 9 → PrimitiveMachine) (o : ∀ j, Fin (A j).tapeCount) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (C : ℕ), 1 ≤ C ∧
      ∀ (τ σ : ℝ), 0 ≤ τ → 0 ≤ σ → ∀ (rounds maxLen : ℕ) (input output : Word), 1 ≤ rounds →
      LoopRuns step (NineCall A o τ σ) rounds input [] output maxLen → RunsWithin M out input output
        ((rounds : ℝ) * (polyBound C maxLen + (C : ℝ)*(τ+σ+1))) (polyBound C maxLen + (C : ℝ)*(σ+1)) := by
  obtain ⟨O,d,_,mux⟩ := nine_oracle_mux A o
  obtain ⟨M,out,b,_,loop⟩ := m89_polyT_oracle_loop step hstep O O.inputTape
  refine ⟨M,out,coeff b d,by unfold coeff; omega,?_⟩
  intro τ σ ht hs r n input output hr trace
  let cost (u : ℝ) := (d:ℝ)*(u+n+1)
  have liftTrace (k : ℕ) (st ans : Word) (h : LoopRuns step (NineCall A o τ σ) k st ans output n) :
      LoopRuns step (fun w y => RunsWithin O O.inputTape w y (cost τ) (cost σ)) k st ans output n := by
    induction k generalizing st ans with
    | zero => exact False.elim h
    | succ k ih =>
      rcases h with done | ⟨st',w,y,he,hi,hw,hy,⟨j,q,rfl,run⟩,next⟩
      · exact Or.inl done
      · have hq : q.length ≤ n := by
          simp only [pairWord,List.length_append,List.length_cons,List.length_nil,tag9,tag3] at hw
          split at hw <;> split at hw <;> simp at hw <;> omega
        have hcost (u : ℝ) : (d:ℝ)*(u+q.length+1) ≤ cost u := by dsimp [cost]; gcongr
        exact Or.inr ⟨st',_,y,he,hi,hw,hy,runsWithin_mono (mux j q y τ σ ht hs run) (hcost τ) (hcost σ),ih _ _ next⟩
  have run := loop (cost τ) (cost σ) (by dsimp [cost]; positivity) (by dsimp [cost]; positivity) r n input output hr (liftTrace r input [] trace)
  apply runsWithin_mono run
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [show cost τ + cost σ + 1 = (d:ℝ)*(τ+σ) + 2*d*(n+1) + 1 by dsimp [cost]; ring]
    exact absorb b d n (τ+σ) (add_nonneg ht hs)
  · refine le_trans ?_ (absorb b d n σ hs)
    dsimp [cost]; gcongr; nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (Nat.cast_nonneg (α := ℝ) n),Nat.cast_nonneg (α := ℝ) d]

end DetDLP.W3C.NineOracleLoop


