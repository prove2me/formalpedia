-- Prove2me | Definitions.Def_MinSumFPT_Supplement_OVH
-- name    : MinSumFPT_Supplement_OVH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:16:42.279585+00:00
-- url     : https://prove2.me/theorems/66201c32-f60d-4e53-b9c7-283dcbb8e508
-- title:
--   The Orthogonal Vectors Hypothesis (OVH)
-- statement:
--   The **Orthogonal Vectors problem** takes two lists $A=(a_1,\dots,a_n)$ and $B=(b_1,\dots,b_n)$ of vectors in $\{0,1\}^d$ and asks whether some $a\in A$, $b\in B$ satisfy $\langle a,b\rangle=0$ over the reals. The naive algorithm takes $O(n^2d)$ time.
--
--   The **Orthogonal Vectors Hypothesis** asserts that for every constant $\epsilon>0$ there is an integer $C=C(\epsilon)>1$ such that no algorithm decides the Orthogonal Vectors problem with $n=|A|=|B|$ and
--   $$
--   d=\lceil C\log_2 n\rceil
--   $$
--   in time $O(n^{2-\epsilon})$: there is no admissible program and constant $K$ that, on every instance with $n\ge1$, answers correctly on every random tape within $K\,n^{2-\epsilon}$ steps.
--
--   OVH is the hypothesis of Theorems 38 and 39; it is a hypothesis of those theorems, not an assumption of the mission.
--
--   **Formalization Note** The problem is the published `ErrAmpOV.OV`; its input is given as the integer list $[n,d]$ followed by the $2nd$ bits. Lists may repeat vectors and the dimension is rounded up with base-2 logarithm; both make the hypothesis weaker than with sets and $C\ln n$, since a program for lists solves sets and a program for a larger dimension solves a smaller one by padding with zeros. With finitely many instances of each size, a threshold $n\ge n_0$ in the $O(\cdot)$ would change nothing.
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), §3.1, p.43, Orthogonal Vectors problem and Hypothesis 2 (OVH)

import Mathlib
import Definitions.Def_ErrAmpOV_OV
import Definitions.Def_MinSumFPT_Machine
import Definitions.Def_MinSumFPT_Supplement_InputMachine
set_option autoImplicit false

namespace MinSumFPT.Supplement

/-!
# The Orthogonal Vectors Hypothesis (OVH)

Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation
Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256
12e81235…), §3.1, p.43: the Orthogonal Vectors problem and Hypothesis 2 (OVH): "for every constant
ϵ > 0, there exists an integer C := C(ϵ) > 1 such that there is no algorithm that decides the
Orthogonal Vectors problem in O(n^{2−ϵ}) time where n = |A| = |B| and d = C log n."

This module bundles `encodeOV`, `ovDim` and `OVH`.

**Formalization Note.** The Orthogonal Vectors function is the published `ErrAmpOV.OV n d x`
(the input bits `x : Fin 2 × Fin n × Fin d → Bool`, row `0` the vectors of `A`, row `1` those of
`B`; true iff some `a ∈ A`, `b ∈ B` have `⟨a, b⟩ = 0`). The lists may repeat vectors (the page's
sets are the case of distinct entries; allowing repeats makes OVH weaker). The input is given as
the integer list `[n, d, x(0,0,0), …]` (bits `0/1`, row-major in `(a, i, k)`) to the input-reading
runs of `MinSumFPT.Supplement.inputState`. The dimension is `d = ⌈C · log₂ n⌉` (the weakest of the
usual readings of `C log n`: hardness at a larger dimension is a weaker claim). "No algorithm in
`O(n^{2−ϵ})` time" is: no admissible program and constant `K` such that on every OV instance with
`n ≥ 1` the program answers correctly on every tape within `K · n^{2−ϵ}` steps (there are finitely
many instances of each size, so a threshold `n ≥ n₀` would change nothing). -/

/-- The integer encoding `[n, d, bits…]` of an OV instance. -/
def encodeOV (n d : ℕ) (x : Fin 2 × Fin n × Fin d → Bool) : List ℤ :=
  (n : ℤ) :: (d : ℤ) :: (List.finRange 2).flatMap fun a => (List.finRange n).flatMap fun i =>
    (List.finRange d).map fun k => if x (a, i, k) then 1 else 0

/-- The dimension `d = ⌈C · log₂ n⌉` of OVH. -/
noncomputable def ovDim (C n : ℕ) : ℕ := ⌈(C : ℝ) * Real.logb 2 n⌉₊

/-- **OVH** (Hypothesis 2): for every `ϵ > 0` there is an integer `C > 1` such that no admissible
program decides `OV` at dimension `d = ⌈C log₂ n⌉` within `K · n^{2−ϵ}` steps. -/
def OVH : Prop :=
  ∀ ϵ : ℝ, 0 < ϵ → ∃ C : ℕ, 1 < C ∧
    ¬ ∃ P : Program, Admissible P ∧ ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n →
      ∀ x : Fin 2 × Fin n × Fin (ovDim C n) → Bool,
        AnswersWithin P (encodeOV n (ovDim C n) x) [] (ErrAmpOV.OV n (ovDim C n) x)
          (K * (n : ℝ) ^ (2 - ϵ))

end MinSumFPT.Supplement


