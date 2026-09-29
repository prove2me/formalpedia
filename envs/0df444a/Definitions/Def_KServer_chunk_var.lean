-- Prove2me | Definitions.Def_KServer_chunk_var
-- name    : KServer_chunk_var
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T12:03:51.38011+00:00
-- url     : https://prove2.me/theorems/2f098ff0-8417-43e6-a6f7-88f92cad0493
-- title:
--   Doob energy and Chebyshev counting for chunk systems
-- statement:
--   The second-moment layer over a chunk system: the **Doob increments** $\Delta_h = \mathbb E[f \mid \mathcal F_{h+1}] - \mathbb E[f \mid \mathcal F_h]$ of a random variable $f$, their **Doob energy** $\mathcal E_N(f) = \sum_{h < N} \mathbb E[\Delta_h^2]$, the orthogonality identity
--
--   $$\mathcal E_N(f) = \mathbb E\big[\mathbb E[f \mid \mathcal F_N]^2\big] - \mathbb E\big[\mathbb E[f \mid \mathcal F_0]^2\big],$$
--
--   and the **Chebyshev counting bound**: the expected number of times $h < N$ with $|\Delta_h| \ge \lambda$ is at most $\mathcal E_N(f)/\lambda^2$. In the repaired BCR induction this replaces any pointwise bound on conditional-expectation jumps: the number of combining windows whose boundary crossing suffers a large Doob increment — and whose conditional size therefore leaves the tight window — is a small fraction of the window count, controlled by the variance invariant carried through the levels.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Lemma 15 machinery, repaired form.

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace KServer

namespace ChunkSystemB

variable {X : Type*} [MetricSpace X] {s t : X} {cLo cHi total price : ℝ} {mLo : ℕ}
variable (C : ChunkSystemB X s t cLo cHi total price mLo)

/-- The expectation of a random variable under the outcome weights. -/
noncomputable def expVal (f : C.Ω → ℝ) : ℝ := ∑ ω, C.P ω * f ω

/-- The `h`-th **Doob increment** of `f`: the change of the conditional
expectation when the time-`h` history is refined to time `h + 1`. -/
noncomputable def dinc (f : C.Ω → ℝ) (h : ℕ) (ω : C.Ω) : ℝ :=
  C.condExp f (h + 1) ω - C.condExp f h ω

/-- The **Doob energy** of `f` up to time `N`: the summed second moments of
the Doob increments. By orthogonality this telescopes to the variance gain
of the conditional expectations, and it controls the number of large
increments by Chebyshev counting. -/
noncomputable def doobEnergy (f : C.Ω → ℝ) (N : ℕ) : ℝ :=
  ∑ h ∈ Finset.range N, C.expVal (fun ω => (C.dinc f h ω) ^ 2)

theorem doobEnergy_nonneg (f : C.Ω → ℝ) (N : ℕ) : 0 ≤ C.doobEnergy f N :=
  Finset.sum_nonneg fun h _ => Finset.sum_nonneg fun ω _ =>
    mul_nonneg (le_of_lt (C.hP ω)) (sq_nonneg _)

theorem condExp_mul_const (g : C.Ω → ℝ) (c : ℝ) (h : ℕ) (ω : C.Ω) :
    C.condExp (fun ω' => g ω' * c) h ω = C.condExp g h ω * c := by
  unfold condExp
  have h1 : ∑ ω' ∈ C.atom h ω, C.P ω' * (g ω' * c)
      = (∑ ω' ∈ C.atom h ω, C.P ω' * g ω') * c := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun ω' _ => by ring
  rw [h1, mul_div_right_comm]

/-- A Doob increment is orthogonal to the current conditional expectation. -/
theorem expVal_dinc_mul_condExp (f : C.Ω → ℝ) (h : ℕ) :
    C.expVal (fun ω => C.dinc f h ω * C.condExp f h ω) = 0 := by
  unfold expVal dinc
  have h1 : ∑ ω, C.P ω * (C.condExp f (h + 1) ω * C.condExp f h ω)
      = ∑ ω, C.P ω * (C.condExp f h ω * C.condExp f h ω) := by
    have h2 := C.sum_mul_condExp
      (fun ω => C.condExp f (h + 1) ω * C.condExp f h ω) h
    have h3 : ∀ ω : C.Ω,
        C.condExp (fun ω' => C.condExp f (h + 1) ω' * C.condExp f h ω') h ω
          = C.condExp f h ω * C.condExp f h ω := by
      intro ω
      have h4 : C.condExp (fun ω' => C.condExp f (h + 1) ω' * C.condExp f h ω') h ω
          = C.condExp (fun ω' => C.condExp f (h + 1) ω' * C.condExp f h ω) h ω := by
        refine C.condExp_congr_fun fun ω' hm => ?_
        rw [C.condExp_congr f (C.mem_atom.mp hm)]
      rw [h4, C.condExp_mul_const (C.condExp f (h + 1)) (C.condExp f h ω) h ω,
        C.condExp_condExp (Nat.le_succ h)]
    rw [← h2]
    exact Finset.sum_congr rfl fun ω _ => by rw [h3 ω]
  calc ∑ ω, C.P ω * ((C.condExp f (h + 1) ω - C.condExp f h ω) * C.condExp f h ω)
      = ∑ ω, C.P ω * (C.condExp f (h + 1) ω * C.condExp f h ω)
        - ∑ ω, C.P ω * (C.condExp f h ω * C.condExp f h ω) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun ω _ => by ring
    _ = 0 := by rw [h1, sub_self]

/-- Orthogonality: the Doob energy telescopes to the second-moment gain. -/
theorem doobEnergy_eq (f : C.Ω → ℝ) (N : ℕ) :
    C.doobEnergy f N
      = C.expVal (fun ω => (C.condExp f N ω) ^ 2)
        - C.expVal (fun ω => (C.condExp f 0 ω) ^ 2) := by
  induction N with
  | zero =>
    unfold doobEnergy
    rw [Finset.range_zero, Finset.sum_empty, sub_self]
  | succ N ih =>
    unfold doobEnergy at ih ⊢
    rw [Finset.sum_range_succ, ih]
    have h1 : C.expVal (fun ω => (C.condExp f (N + 1) ω) ^ 2)
        = C.expVal (fun ω => (C.condExp f N ω) ^ 2)
          + C.expVal (fun ω => (C.dinc f N ω) ^ 2)
          + 2 * C.expVal (fun ω => C.dinc f N ω * C.condExp f N ω) := by
      unfold expVal
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ω _ => ?_
      unfold dinc
      ring
    rw [expVal_dinc_mul_condExp] at h1
    rw [h1]
    ring

/-- **Chebyshev counting**: the expected number of large Doob increments is
controlled by the Doob energy. -/
theorem expVal_card_large_dinc (f : C.Ω → ℝ) (N : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    C.expVal (fun ω =>
        (((Finset.range N).filter (fun h => lam ≤ |C.dinc f h ω|)).card : ℝ))
      ≤ C.doobEnergy f N / lam ^ 2 := by
  classical
  have key : ∀ ω : C.Ω,
      ((((Finset.range N).filter (fun h => lam ≤ |C.dinc f h ω|)).card : ℝ))
        ≤ (∑ h ∈ Finset.range N, (C.dinc f h ω) ^ 2) / lam ^ 2 := by
    intro ω
    rw [le_div_iff₀ (pow_pos hlam 2)]
    calc (((Finset.range N).filter (fun h => lam ≤ |C.dinc f h ω|)).card : ℝ) * lam ^ 2
        = ∑ _h ∈ (Finset.range N).filter (fun h => lam ≤ |C.dinc f h ω|), lam ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ h ∈ (Finset.range N).filter (fun h => lam ≤ |C.dinc f h ω|),
            (C.dinc f h ω) ^ 2 := by
          refine Finset.sum_le_sum fun h hm => ?_
          have h1 := (Finset.mem_filter.mp hm).2
          calc lam ^ 2 ≤ |C.dinc f h ω| ^ 2 := by
                have h0 := le_of_lt hlam
                nlinarith
            _ = (C.dinc f h ω) ^ 2 := sq_abs _
      _ ≤ ∑ h ∈ Finset.range N, (C.dinc f h ω) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun h _ _ => sq_nonneg _)
  unfold expVal
  calc ∑ ω, C.P ω * (((Finset.range N).filter (fun h => lam ≤ |C.dinc f h ω|)).card : ℝ)
      ≤ ∑ ω, C.P ω * ((∑ h ∈ Finset.range N, (C.dinc f h ω) ^ 2) / lam ^ 2) :=
        Finset.sum_le_sum fun ω _ =>
          mul_le_mul_of_nonneg_left (key ω) (le_of_lt (C.hP ω))
    _ = (∑ ω, ∑ h ∈ Finset.range N, C.P ω * (C.dinc f h ω) ^ 2) / lam ^ 2 := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [mul_div_assoc']
        congr 1
        rw [Finset.mul_sum]
    _ = C.doobEnergy f N / lam ^ 2 := by
        unfold doobEnergy expVal
        rw [Finset.sum_comm]

end ChunkSystemB

end KServer


