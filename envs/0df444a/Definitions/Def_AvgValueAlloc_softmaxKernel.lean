-- Prove2me | Definitions.Def_AvgValueAlloc_softmaxKernel
-- name    : AvgValueAlloc_softmaxKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:40:47.142931+00:00
-- url     : https://prove2.me/theorems/a76d4cfd-53ef-4729-9ec4-18fe3f2d4b29
-- title:
--   Local smoothed funding rule (ideal softmax)
-- statement:
--   Under shift $s$, a funding item $v$ that is not retained is not funded. A retained item with $m=|J(v)|$ and $c_v=2\max_{j\in J(v)}\rho_j$ chooses $j\in J(v)$ with probability
--   $$
--   \frac1{2m}+\frac12\,\frac{e^{\lambda_m s_j/c_v}}{\sum_{k\in J(v)}e^{\lambda_m s_k/c_v}},\qquad \lambda_m=\tfrac14\log\bigl(2+\log(2+m)\bigr),
--   $$
--   where $s_j$ is the score (6) with $\hat V$ the information LP $F^{J_{\ell,s}}_Y$ of $j$'s group at the bank earned so far; only the chosen surplus enters its bank.
--
--   **Formalization Note** Exact real exponentials (the ideal rule analyzed in Lemma 3.4).
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §3.3, p.9

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_posSet
import Definitions.Def_AvgValueAlloc_routBank
import Definitions.Def_AvgValueAlloc_edgeLP
import Definitions.Def_AvgValueAlloc_groupSum
import Definitions.Def_AvgValueAlloc_HsL

namespace AvgValueAlloc

/-- The temperature `λ_m = (1/4) log(2 + log(2 + m))`. -/
noncomputable def lamM (m : ℕ) : ℝ := (1 / 4) * Real.log (2 + Real.log (2 + (m : ℝ)))

open scoped Classical in
/-- **The local smoothed funding rule (exact softmax).**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §3.3, p.9: "Within its group use (6) with that
group's information LP. For m = |J(v)| and c_v = 2 max_{j∈J(v)} ρ_j, set λ_m = (1/4) log(2 + log(2 +
m)). Choose uniformly with probability 1/2 and otherwise proportional to exp(λ_m s_j/c_v); only the
chosen original surplus enters its bank. … The next lemma analyzes the ideal softmax probabilities."

`softmaxKernel ρ s Y M t X o`: a funding item `v = M t` that is not retained under shift `s` is not
funded (`o = none` with probability one). A retained item picks `j ∈ J(v)` with probability
`1/(2m) + (1/2) e^{λ_m s_j/c_v} / Σ_{k ∈ J(v)} e^{λ_m s_k/c_v}`, where `B` is the bank earned by
the earlier decisions and `s_j = v_j + F^{J_g}_Y(B + (v_j − ρ_j)e_j) − F^{J_g}_Y(B)` with `J_g`
the shifted group of `j` and `Y` the information records.

**Formalization Note.** Exact real exponentials (the ideal rule of Lemma 3.4); the finite-precision
implementation of Appendix A.2 belongs to the goal theorem. -/
noncomputable def softmaxKernel {n m : ℕ} {ι : Type} [Fintype ι] (ρ : Fin n → ℚ) (s : ℕ)
    (Y : ι → Vec n) (M : Fin m → Vec n) :
    Fin m → (Fin m → Option (Fin n)) → Option (Fin n) → ℝ :=
  fun t X o =>
    if h : IsRetained ρ s (M t) then
      match o with
      | none => 0
      | some j =>
        if j ∈ posSet ρ (M t) then
          let B := prefBank ρ M X t.val
          let grpSet : Fin n → Finset (Fin n) := fun k =>
            Finset.univ.filter fun i => shBand ρ s i = shBand ρ s k
          let sc : Fin n → ℝ := fun k =>
            ((M t k : ℚ≥0) : ℝ) +
              Flp ρ (grpSet k) Y (B + (((M t k : ℚ≥0) : ℝ) - ρ k) • Pi.single k 1) -
              Flp ρ (grpSet k) Y B
          let mm := (posSet ρ (M t)).card
          let c : ℝ := 2 * (((posSet ρ (M t)).sup' h.1 fun k => ρ k : ℚ) : ℝ)
          let wgt : Fin n → ℝ := fun k => Real.exp (lamM mm * sc k / c)
          1 / (2 * (mm : ℝ)) + (1 / 2) * (wgt j / ∑ k ∈ posSet ρ (M t), wgt k)
        else 0
    else if o = none then 1 else 0

end AvgValueAlloc


