-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_ProtectedClock
-- name    : ConsistentSubmodular_Deterministic_Reduction_ProtectedClock
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:08:52.995257+00:00
-- url     : https://prove2.me/theorems/cc5f7bf5-ceed-4ed6-a29e-e95bb958a5b8
-- title:
--   Protected clock: choice of stable start times, and prefix optimum $F_k(t)$
-- statement:
--   Let $F : \mathbb{N}\to\mathbb{R}$ be a nonnegative nondecreasing sequence (a disclosed optimum sequence), $\eta \ge 0$, and $b, \ell, J \in \mathbb{N}$.
--
--   - `ConsistentSubmodular.ProtectedClock` $F\,\eta\,b\,\ell$: a structure consisting of start times $s_i \in \mathbb{N}$ ($i \in \mathbb{N}$) such that, for every $i$,
--     - $(i+1)\,b \le s_i$ and $s_i + \ell \le (i+2)\,b$, so the window $[s_i, s_i+\ell]$ lies in block $i+1$;
--     - protection: either the interval is stable, $F(s_i+\ell) \le (1+\eta)\,F(s_i)$, or the optimum has already grown fourfold, $4\,F((i+1)b) \le F(s_i)$.
--   - `ConsistentSubmodular.protectedClock`: given $J \ge 1$ with $J\ell \le b$ and $(J-1)\eta \ge 3$, a clock built from the fixed choices $s_i = (i+1)b + j_i \ell$, where $j_i < J$ is chosen (using the lemma below) for block $i$. The choices depend only on the fully disclosed sequence $F$.
--   - `ConsistentSubmodular.Objective.prefixOptimum` $(f, k, t)$: the optimum $F_k(t)$ over sets of at most $k$ elements of the arrived prefix, i.e. $\max\{f(A) : A\subseteq X_t,\ |A|\le k\}$ (the buffered optimum with empty buffer).
--
--   The file also proves the existence statement behind the construction: among $J$ consecutive intervals of length $\ell$ starting at $a$, either one is stable or the last start already has $F \ge 4F(a)$, by linear growth only. It also proves that $F_k$ is nondecreasing and nonnegative.
--
--   These objects give the time points of the reduction in Section 3.2 at which a candidate set can be switched without loss.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/ProtectedClock.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SchedulingBasics

noncomputable section

namespace ConsistentSubmodular

/-- A block contains a stable interval or its last candidate already has a
fourfold increase. The proof uses only linear growth, not concentration. -/
theorem exists_protected_interval (F : ℕ → ℝ) (hF : Monotone F)
    (hF0 : ∀ t, 0 ≤ F t) (a J ell : ℕ) (hJ : 1 ≤ J)
    (η : ℝ) (hη : 0 ≤ η) (hgrowth : 3 ≤ ((J - 1 : ℕ) : ℝ) * η) :
    ∃ j : ℕ, j < J ∧
      (F (a + (j + 1) * ell) ≤ (1 + η) * F (a + j * ell) ∨
        4 * F a ≤ F (a + j * ell)) := by
  classical
  by_cases hstable : ∃ j : ℕ, j < J ∧
      F (a + (j + 1) * ell) ≤ (1 + η) * F (a + j * ell)
  · obtain ⟨j, hj, h⟩ := hstable
    exact ⟨j, hj, Or.inl h⟩
  have hinc : ∀ j : ℕ, j < J →
      (1 + η) * F (a + j * ell) ≤ F (a + (j + 1) * ell) := by
    intro j hj
    exact (lt_of_not_ge (fun h => hstable ⟨j, hj, h⟩)).le
  have hlinear : ∀ j : ℕ, j ≤ J →
      (1 + (j : ℝ) * η) * F a ≤ F (a + j * ell) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hi := ih (by omega)
      have hc := hinc j (by omega)
      have hm := hF (show a ≤ a + j * ell by omega)
      have hp := mul_le_mul_of_nonneg_left hm hη
      push_cast
      nlinarith only [hi, hc, hp]
  refine ⟨J - 1, by omega, Or.inr ?_⟩
  have hh := hlinear (J - 1) (by omega)
  have hp := mul_nonneg (sub_nonneg.mpr hgrowth) (hF0 a)
  nlinarith only [hh, hp]

structure ProtectedClock (F : ℕ → ℝ) (η : ℝ) (b ell : ℕ) where
  start : ℕ → ℕ
  lower : ∀ i, (i + 1) * b ≤ start i
  upper : ∀ i, start i + ell ≤ (i + 2) * b
  protection : ∀ i,
    F (start i + ell) ≤ (1 + η) * F (start i) ∨
      4 * F ((i + 1) * b) ≤ F (start i)

/-- Fixed choices depend only on the fully disclosed optimum sequence. -/
def protectedClock (F : ℕ → ℝ) (hF : Monotone F) (hF0 : ∀ t, 0 ≤ F t)
    (b J ell : ℕ) (hJ : 1 ≤ J) (hfit : J * ell ≤ b)
    (η : ℝ) (hη : 0 ≤ η) (hgrowth : 3 ≤ ((J - 1 : ℕ) : ℝ) * η) :
    ProtectedClock F η b ell := by
  have he (i : ℕ) := exists_protected_interval F hF hF0 ((i + 1) * b) J ell hJ η hη hgrowth
  let j := fun i => Classical.choose (he i)
  have hj (i : ℕ) : j i < J := (Classical.choose_spec (he i)).1
  refine {
    start := fun i => (i + 1) * b + j i * ell
    lower := fun i => Nat.le_add_right _ _
    upper := ?_
    protection := ?_ }
  · intro i
    have hh := Nat.mul_le_mul_right ell (show j i + 1 ≤ J by have := hj i; omega)
    nlinarith
  · intro i
    have hh := (Classical.choose_spec (he i)).2
    simpa only [j, Nat.add_mul, one_mul, Nat.add_assoc] using hh

namespace Objective

variable {n : ℕ} (f : Objective n)

def prefixOptimum (k t : ℕ) : ℝ := f.bufferedOptimum (arrivedPrefix n t) ∅ k

theorem prefixOptimum_monotone (k : ℕ) : Monotone (f.prefixOptimum k) := by
  intro s t hst
  exact f.bufferedOptimum_mono_ground (arrivedPrefix_mono hst)

theorem prefixOptimum_nonnegative (k t : ℕ) : 0 ≤ f.prefixOptimum k t :=
  f.bufferedOptimum_nonnegative _ _ _

end Objective

end ConsistentSubmodular

end


