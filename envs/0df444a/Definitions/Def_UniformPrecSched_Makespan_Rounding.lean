-- Prove2me | Definitions.Def_UniformPrecSched_Makespan_Rounding
-- name    : UniformPrecSched_Makespan_Rounding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T20:12:22.239645+00:00
-- url     : https://prove2.me/theorems/9da0a026-e1c7-4bb9-a4f0-898dcde0fabc
-- title:
--   Speed rounding of §3: dropping speeds below s̄₁/(αm) and rounding the rest down to powers of β
-- statement:
--   Fix an instance of $Q|prec|C_{\max}$ with fastest speed $\bar s_1$, and parameters $\alpha \ge 1$, $\beta > 1$.
--
--   1. **Kept machines.** Machine $i$ is kept when $s_i \ge \bar s_1/(\alpha m)$; the speeds less than $\bar s_1/(\alpha m)$ are rounded down to $0$, i.e. those machines are dropped. The fastest machine is always kept.
--   2. **Rounded speeds.** A kept speed $v$ lies in an interval $(\bar s_1 \beta^{-k}, \bar s_1\beta^{-k+1}]$ for exactly one integer $k \ge 1$, namely $k = \lfloor \log_\beta(\bar s_1/v)\rfloor + 1$, and is rounded down to $\bar s_1\beta^{-k}$.
--   3. **Rounded instance.** The rounded instance has the same jobs, processing requirements and precedence order; its machines are the kept machines, listed in increasing order of their original index, each running at its rounded speed.
--   4. **Theorem 3.7's choice.** For $m \ge 2$, the rounded instance used in Theorem 3.7 takes $\alpha = \log_2 m$ and $\beta = e$.
--
--   Every machine of the rounded instance runs no faster than its true speed, so a schedule for the rounded instance can be read as a schedule of the original instance.
--
--   **Formalization Note** The paper normalizes $\bar s_1 = 1$ (p. 9); here the rounding is relative to $\bar s_1$, so no normalization is assumed. The construction takes the proofs $1 \le \alpha$ and $1 < \beta$ as arguments (they are used to show that the rounded instance has a machine and positive speeds). The file contains two short auxiliary facts, $1 \le \log_2 m$ for $m \ge 2$ and $1 < e$, used to build the instance of Theorem 3.7.
-- source:
--   Chudak & Shmoys, Approximation algorithms for precedence-constrained scheduling problems on parallel machines that run at different speeds, authors' manuscript (preprint of J. Algorithms, 1999, DOI 10.1006/jagm.1998.0987), p. 9 (elimination of slow machines, rounding to powers of 1/2) and p. 10 (general rounding with α ≥ 1, β > 1; α = log m, β = e)

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Model

namespace UniformPrecSched.Makespan

variable {n m : ℕ}

theorem machines_nonempty (I : Instance n m) : (Finset.univ : Finset (Fin m)).Nonempty :=
  ⟨⟨0, I.m_pos⟩, Finset.mem_univ _⟩

/-- The speed `s̄_1` of the fastest machine. -/
noncomputable def maxSpeed (I : Instance n m) : ℝ :=
  Finset.univ.sup' (machines_nonempty I) I.s

theorem maxSpeed_pos (I : Instance n m) : 0 < maxSpeed I :=
  lt_of_lt_of_le (I.s_pos ⟨0, I.m_pos⟩)
    (Finset.le_sup' I.s (Finset.mem_univ _))

/-- The machines kept by the speed rounding of p. 10 with parameter `α`: those whose speed is
at least `s̄_1/(αm)`; the speeds less than `s̄_1/(αm)` are rounded down to `0`, i.e. their
machines are dropped. (The paper has normalized `s̄_1 = 1`, p. 9.) -/
noncomputable def keptSet (I : Instance n m) (α : ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i => maxSpeed I / (α * m) ≤ I.s i

/-- The number of kept machines. -/
noncomputable def keptCount (I : Instance n m) (α : ℝ) : ℕ :=
  (keptSet I α).card

/-- The kept machines, enumerated in increasing order of machine index: kept machine `i'` of the
rounded instance is machine `keptEmb I α i'` of the original instance. -/
noncomputable def keptEmb (I : Instance n m) (α : ℝ) : Fin (keptCount I α) ↪o Fin m :=
  (keptSet I α).orderEmbOfFin rfl

/-- Rounding of a speed `v ∈ (s̄_1 β^{-k}, s̄_1 β^{-k+1}]` (with `k ≥ 1` an integer) down to
`s̄_1 β^{-k}` (p. 10): since `k = ⌊log_β(s̄_1/v)⌋ + 1`, the rounded speed is
`s̄_1 β^{-(⌊log_β(s̄_1/v)⌋ + 1)}`. -/
noncomputable def roundedSpeed (I : Instance n m) (β v : ℝ) : ℝ :=
  maxSpeed I * β ^ (-(⌊Real.logb β (maxSpeed I / v)⌋ + 1))

theorem keptCount_pos (I : Instance n m) {α : ℝ} (hα : 1 ≤ α) : 0 < keptCount I α := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (machines_nonempty I) I.s
  refine Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast I.m_pos
  have h1 : (1 : ℝ) ≤ α * m := by nlinarith
  rw [← show maxSpeed I = I.s i from hi]
  exact div_le_self (maxSpeed_pos I).le h1

/-- The rounded instance of p. 10, for parameters `α ≥ 1` and `β > 1`: same jobs, processing
requirements and precedence order; its machines are the kept machines (`keptEmb`), and kept
machine `i'` has speed `roundedSpeed I β (s (keptEmb I α i'))`. -/
noncomputable def roundInstance (I : Instance n m) (α β : ℝ) (hα : 1 ≤ α) (hβ : 1 < β) :
    Instance n (keptCount I α) where
  p := I.p
  s := fun i => roundedSpeed I β (I.s (keptEmb I α i))
  prec := I.prec
  m_pos := keptCount_pos I hα
  p_pos := I.p_pos
  s_pos := fun _ => mul_pos (maxSpeed_pos I) (zpow_pos (by linarith) _)
  prec_irrefl := I.prec_irrefl
  prec_trans := I.prec_trans

theorem one_le_logb_two {m : ℕ} (hm : 2 ≤ m) : (1 : ℝ) ≤ Real.logb 2 m := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
  simpa using (show ((2 : ℕ) : ℝ) ≤ m by exact_mod_cast hm)

theorem one_lt_exp_one : (1 : ℝ) < Real.exp 1 := by
  simp

/-- The rounded instance used in Theorem 3.7 (p. 10): `α = log₂ m` and `β = e`, for `m ≥ 2`. -/
noncomputable def logRoundInstance (I : Instance n m) (hm : 2 ≤ m) :
    Instance n (keptCount I (Real.logb 2 m)) :=
  roundInstance I (Real.logb 2 m) (Real.exp 1) (one_le_logb_two hm) one_lt_exp_one

end UniformPrecSched.Makespan


