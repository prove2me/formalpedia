-- Prove2me | Definitions.Def_LearnManip_History
-- name    : LearnManip_History
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:43.368552+00:00
-- url     : https://prove2.me/theorems/eb00e103-1b1c-4a77-be9f-cb9ffaeba073
-- title:
--   Histories $(\mu_0,\dots,\mu_n)$ of posterior means
-- statement:
--   A history is the vector $(\mu_0,\dots,\mu_n)$ of the public's posterior means up to period $n$. The posterior variances are a function of it, given a quantity rule, so it generates the filtration of the belief process, to which an admissible policy is adapted.
--
--   The module also provides the last entry $\mu_n$, the prefix $(\mu_0,\dots,\mu_{n-1})$, and the history of an infinite path.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), §2, p.11

import Mathlib

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- A history `(μ₀, …, μ_n)` of the public's posterior means: the observations of the belief process
of §2, p.11, of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04), on which an admissible policy may depend.
The variances are a function of it (`varPath`), so it generates the filtration `F^M`. -/
abbrev History (n : ℕ) : Type := (i : Finset.Iic n) → (fun _ : ℕ => ℝ) i

/-- The last entry `μ_n` of a history. -/
def History.last {n : ℕ} (h : History n) : ℝ := h ⟨n, Finset.mem_Iic.mpr le_rfl⟩

/-- The history `(μ₀, …, μ_n)` as a prefix of `(μ₀, …, μ_{n+1})`. -/
def History.prefix {n : ℕ} (h : History (n + 1)) : History n :=
  Preorder.frestrictLe₂ (π := fun _ : ℕ => ℝ) (Nat.le_succ n) h

/-- The history `(ω 0, …, ω n)` of a path `ω`. -/
def History.ofPath (n : ℕ) (ω : ℕ → ℝ) : History n :=
  Preorder.frestrictLe (π := fun _ : ℕ => ℝ) n ω

end LearnManip


