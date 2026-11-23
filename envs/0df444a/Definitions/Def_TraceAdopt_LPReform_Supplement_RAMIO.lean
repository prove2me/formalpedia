-- Prove2me | Definitions.Def_TraceAdopt_LPReform_Supplement_RAMIO
-- name    : TraceAdopt_LPReform_Supplement_RAMIO
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:51:19.590588+00:00
-- url     : https://prove2.me/theorems/7621780e-3729-43a3-ab3c-3179c799376b
-- title:
--   MIN-SCTM on the unit-cost RAM — input layout, output seed set and the time bound of Theorem 3
-- statement:
--   These definitions fix how an instance of MIN-SCTM (problem (1), p. 6) is handed to a program of the **unit-cost real RAM** and how its answer is read back, so that the running time of Theorem 3 is a count of executed instructions.
--
--   An instance has firms $N_F=\{1,\dots,n\}$, supply chains $j=1,\dots,m$ with hyperedges $e_j\subseteq N_F$, benefits $r_{ji}$ for $i\in e_j$, adoption costs $c_i$ and thresholds $\theta_j$ (natural numbers), and real seeding costs $w_i$.
--
--   1. **Integer input.** The natural-number cells hold, in order: $n$, $m$; for each chain $j$, its threshold $\theta_j$, its size $|e_j|$ and, for each firm $i\in e_j$ in increasing order, the pair $(i,r_{ji})$; then $c_1,\dots,c_n$. Each number occupies one cell, so the input has $O(n+m+\sum_j|e_j|)$ cells.
--   2. **Real input.** The real cells $R[0],\dots,R[n-1]$ hold $w_1,\dots,w_n$.
--   3. **Output.** After the run halts, the output seed set is $\{i : I[i]=1\}$, read from the first $n$ integer cells.
--   4. **Time bound.** For an absolute constant $C$, tree-width parameter $\omega$ and $\vartheta_{\max}=\max\{\max_i c_i,\max_j\theta_j-1\}$,
--
--   $$T_C(G,\omega)=C\,\big((\vartheta_{\max}+1)(\omega+2)\big)^{C(\omega+1)}\,(n+m+1),$$
--
--   the form $[\vartheta_{\max}\cdot\omega]^{O(\omega)}(n+m)$ of Theorem 3 with shifts that keep the base positive.
--
--   **Formalization Note** The machine is the published unit-cost real RAM `MeanCertificates1424.Hardness.Supplement` (`Program`, `Cfg`, `RunsWithin`): integer cells with constants, addition, truncated subtraction and indirect addressing; real cells with $+,-,\times,\div$; comparisons and jumps; every executed instruction costs one step, and reals cannot be converted to integers. $\vartheta_{\max}$ is the published `varthetaMax`.
-- source:
--   Blaettchen, Calmon & Hall, Traceability Technology Adoption in Supply Chain Networks, arXiv:2104.14818v4, p. 6, problem (1) (MIN-SCTM); p. 18, Proposition 9 (ϑmax); p. 47, Theorem 3 (time bound); pp. 44–47, Algorithm 2 and Lemma 3 (operation counts)

import Mathlib
import Definitions.Def_TraceAdopt_LPReform_Model
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_RAM

set_option autoImplicit false

namespace TraceAdopt.LPReform.Supplement

/-- The natural-number part of an MIN-SCTM instance as read by the unit-cost RAM: `n`, `m`;
then for each supply chain `j` (in index order) its threshold `θ_j`, its size `k_j = |e_j|` and,
for each firm `i ∈ e_j` in increasing order, the pair `i, r_ji`; then the adoption costs
`c_1, …, c_n`. Each number occupies one integer cell. Only the benefits `r_ji` with `i ∈ e_j`
are part of the input, as in §3.1. -/
def ramInts (I : Instance) : List ℕ :=
  [I.n, I.m] ++
    (List.finRange I.m).flatMap (fun j =>
      [I.θ j, (I.e j).card] ++ ((I.e j).sort (· ≤ ·)).flatMap (fun i => [i.val, I.r j i])) ++
    List.ofFn I.c

/-- The real part of the input: the seeding costs `w_1, …, w_n` in real cells `R[0], …, R[n-1]`. -/
def ramReals (I : Instance) (w : Fin I.n → ℝ) : List ℝ := List.ofFn w

/-- The seed set written by a halted run: firm `i` is in the output set exactly when the
integer cell `I[i]` holds `1`. -/
def outSeeds (n : ℕ) (c : MeanCertificates1424.Hardness.Supplement.Cfg) : Finset (Fin n) :=
  Finset.univ.filter (fun i => c.imem i.val = 1)

/-- The running-time bound of Theorem 3 with an absolute constant `C`:
`C · ((ϑ_max + 1)(ω + 2))^{C(ω + 1)} · (n + m + 1)`, the form `[ϑ_max ⋅ ω]^{O(ω)} (n + m)`
with the shifts `+1`, `+2` that keep the base positive at `ϑ_max = 0` or `ω = 0`. -/
def dpTimeBound (C : ℕ) (I : Instance) (ω : ℕ) : ℕ :=
  C * ((varthetaMax I + 1) * (ω + 2)) ^ (C * (ω + 1)) * (I.n + I.m + 1)

end TraceAdopt.LPReform.Supplement


