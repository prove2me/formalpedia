-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_BaselineBins
-- name    : ConsistentSubmodular_Deterministic_Reduction_BaselineBins
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:06:32.051758+00:00
-- url     : https://prove2.me/theorems/1f09053b-7304-43ba-a120-56e26c2f937e
-- title:
--   Baseline compression into $3N+2$ threshold bins: first crossing times and retained times
-- statement:
--   Fix a baseline $b : \mathbb{N} \to \mathbb{R}$ (intended monotone), a terminal time $T \in \mathbb{N}$ and a bin width $w \in \mathbb{R}$. The definitions compress the baseline on $\{0,\dots,T\}$ to finitely many retained times.
--
--   - `ConsistentSubmodular.BaselineBins.candidates` $(j)$: the finite set $\{T\} \cup \{t \in \{0,\dots,T\} : j\,w \le b(t)\}$ of times at which the baseline has reached the threshold $j w$, together with the terminal time $T$ (so it is never empty).
--   - `ConsistentSubmodular.BaselineBins.first` $(j)$: the least element of `candidates` $(j)$, the first time the baseline reaches $jw$, or $T$ if there is none.
--   - `ConsistentSubmodular.BaselineBins.retained` $(N, j)$: equal to `first` $(j)$ if $j < 3N+1$, and equal to $T$ otherwise. The last slot $j=3N+1$ is thus reserved for the terminal time.
--
--   The file also proves the basic facts: `first` lies in $[0,T]$, is the minimum over all valid times, and is monotone in $j$ when $w \ge 0$; `retained` is monotone, starts at $0$ when $b(0) \ge 0$, ends at $T$ in slot $3N+1$, and is bounded by $T$. Its main property is the approximation statement: if $b \ge 0$, $V>0$, $N>0$, width $V/N$, then every time $t \le T$ with $b(t) < 3V$ is preceded by some retained time $r_j \le t$ ($j \le 3N+1$) with $b(t) < b(r_j) + V/N$.
--
--   Repeated retained times are allowed, so the compressed description has the fixed size $3N+2$. It is used in the reduction of the deterministic upper-level argument to bound the information carried by a monotone baseline.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/BaselineBins.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib

noncomputable section

namespace ConsistentSubmodular

namespace BaselineBins

variable (b : ℕ → ℝ) (T : ℕ) (width : ℝ)

def candidates (j : ℕ) : Finset ℕ :=
  insert T ((Finset.range (T + 1)).filter fun t => (j : ℝ) * width ≤ b t)

def first (j : ℕ) : ℕ := (candidates b T width j).min'
  (Finset.insert_nonempty _ _)

theorem first_mem (j : ℕ) : first b T width j ∈ candidates b T width j :=
  Finset.min'_mem _ _

theorem first_le_terminal (j : ℕ) : first b T width j ≤ T :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem first_le (j t : ℕ) (ht : t ≤ T) (hc : (j : ℝ) * width ≤ b t) :
    first b T width j ≤ t := by
  apply Finset.min'_le
  exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hc⟩)

theorem first_mono (hw : 0 ≤ width) : Monotone (first b T width) := by
  intro i j hij
  apply Finset.min'_le
  have hm := first_mem b T width j
  rcases Finset.mem_insert.mp hm with he | hm
  · exact Finset.mem_insert.mpr (Or.inl he)
  · apply Finset.mem_insert_of_mem
    have hh := (Finset.mem_filter.mp hm)
    refine Finset.mem_filter.mpr ⟨hh.1, ?_⟩
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hw).trans hh.2

theorem first_zero (hb : 0 ≤ b 0) : first b T width 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact first_le b T width 0 0 (Nat.zero_le _) (by simpa using hb)

theorem threshold_at_first (j t : ℕ) (ht : t ≤ T) (hc : (j : ℝ) * width ≤ b t) :
    (j : ℝ) * width ≤ b (first b T width j) := by
  have hm := first_mem b T width j
  rcases Finset.mem_insert.mp hm with he | hm
  · have hle := first_le b T width j t ht hc
    have : t = T := by omega
    simpa [he, this] using hc
  · exact (Finset.mem_filter.mp hm).2

/-- The last slot is reserved for the terminal endpoint. -/
def retained (N j : ℕ) : ℕ := if j < 3 * N + 1 then first b T width j else T

theorem retained_mono (N : ℕ) (hw : 0 ≤ width) : Monotone (retained b T width N) := by
  intro i j hij
  unfold retained
  split_ifs with hi hj
  · exact first_mono b T width hw hij
  · exact first_le_terminal b T width i
  · omega
  · rfl

@[simp] theorem retained_initial (N : ℕ) (hb : 0 ≤ b 0) : retained b T width N 0 = 0 := by
  simp [retained, first_zero b T width hb]

@[simp] theorem retained_terminal (N : ℕ) : retained b T width N (3 * N + 1) = T := by
  simp [retained]

theorem retained_le_terminal (N j : ℕ) : retained b T width N j ≤ T := by
  unfold retained
  split_ifs
  · exact first_le_terminal b T width j
  · rfl

/-- Every low-baseline time follows a retained time within one bin width. -/
theorem approximates (N : ℕ) (hN : 0 < N) (V : ℝ) (hV : 0 < V)
    (hb : ∀ t, 0 ≤ b t) (t : ℕ) (ht : t ≤ T) (hlow : b t < 3 * V) :
    ∃ j : Fin (3 * N + 2), retained b T (V / N) N j.val ≤ t ∧
      b t < b (retained b T (V / N) N j.val) + V / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < V / N := div_pos hV hNr
  let j := ⌊b t / (V / N)⌋₊
  have hratio : 0 ≤ b t / (V / N) := div_nonneg (hb t) hw.le
  have hj : j < 3 * N := by
    apply (Nat.floor_lt hratio).2
    apply (div_lt_iff₀ hw).2
    have hmul : ((3 * N : ℕ) : ℝ) * (V / N) = 3 * V := by push_cast; field_simp
    rwa [hmul]
  have hfloor := Nat.floor_le hratio
  have hceil := Nat.lt_floor_add_one (b t / (V / N))
  have hc : (j : ℝ) * (V / N) ≤ b t := (le_div_iff₀ hw).mp hfloor
  have hu : b t < ((j : ℝ) + 1) * (V / N) := (div_lt_iff₀ hw).mp hceil
  refine ⟨⟨j, by omega⟩, ?_, ?_⟩
  · simpa [retained, show j < 3 * N + 1 by omega] using first_le b T (V / N) j t ht hc
  · have hh := threshold_at_first b T (V / N) j t ht hc
    simp only [retained, show j < 3 * N + 1 by omega, if_pos]
    nlinarith only [hu, hh]

end BaselineBins

end ConsistentSubmodular

end


