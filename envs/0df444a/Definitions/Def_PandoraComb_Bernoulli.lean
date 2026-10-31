-- Prove2me | Definitions.Def_PandoraComb_Bernoulli
-- name    : PandoraComb_Bernoulli
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:09:34.052402+00:00
-- url     : https://prove2.me/theorems/b5ea03d1-43ff-41ac-8007-495ee88e69ac
-- title:
--   Weighted Bernoulli laws, impulsive strategies $(i_1,\dots,i_k)$ and the two-branch strategy of Lemma 3.1
-- statement:
--   1. The **weighted Bernoulli law** with weight $v$ and probability $p\in[0,1]$ is $(1-p)\,\delta_0+p\,\delta_v$: the value is $v$ with probability $p$ and $0$ otherwise. A **Bernoulli instance** has laws $D_i=(1-p_i)\delta_0+p_i\delta_{v_i}$ with $v_i\ge0$.
--   2. The **impulsive strategy** given by a tuple $\pi=(i_1,\dots,i_k)$ of distinct boxes inspects $i_1,i_2,\dots$ in this order and halts as soon as an inspected box has a non-zero value, or after $i_k$. The empty tuple is the empty strategy, which halts at once.
--   3. For a box $r$ and tuples $\pi^Y,\pi^N$ not containing $r$, the **two-branch strategy** inspects $r$ first; if $V_r\neq0$ it then runs the impulsive strategy $\pi^Y$ on the following boxes, halting at the first non-zero value among them, and if $V_r=0$ it runs $\pi^N$ in the same way.
--
--   Impulsive strategies are the optimal strategies of Theorem 3.1 on Bernoulli instances; the two-branch strategy is the hypothesis of Lemma 3.1 and Lemma 3.2.
--
--   **Formalization Note** Impulsive and two-branch strategies are deterministic and ignore the seed. Halting early at a zero value is the impulsive strategy of a shorter tuple, so the impulsive strategies are exactly the `impulsive l` for lists `l` without repetition. In the two-branch strategy the sub-strategies follow the convention of §3.1, p.9 ("halts if $V_1=v_1$").
-- source:
--   Berger, Ezra, Feldman & Fusco, Pandora’s Problem with Combinatorial Cost, arXiv:2303.01078v1, §2, pp.7–8 (Bernoulli instance, impulsive strategy, empty strategy); §3, p.8 (Lemma 3.1's strategy form); §3.1, p.9 (tuple notation)

import Definitions.Def_PandoraComb_Model

open MeasureTheory

noncomputable section

namespace PandoraComb

/-- **The weighted Bernoulli distribution** with weight `v` and probability `p`
(arXiv:2303.01078v1, §2, p.7: "e.g., with probability 0.7 Vi = 18 and otherwise Vi = 0"):
`(1 − p) δ_0 + p δ_v`. It is a probability measure when `0 ≤ p ≤ 1`. -/
def bernoulliLaw (v p : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - p) • Measure.dirac 0 + ENNReal.ofReal p • Measure.dirac v

/-- **A Bernoulli instance's laws** (§2, p.7: "A Bernoulli instance is an instance where all
distributions Di are weighted Bernoulli distributions"): box `i` has value `v i` with probability
`p i` and `0` otherwise. -/
def bernoulliInstance {ι : Type*} (v p : ι → ℝ) : ι → Measure ℝ :=
  fun i => bernoulliLaw (v i) (p i)

open Classical in
/-- **The impulsive strategy** given by the tuple `l` (§2, pp.7–8 and §3.1, p.9): it inspects the
boxes of `l` in order and halts as soon as an inspected box has a non-zero value, or when `l` is
exhausted. "(1,2,7) stands for the impulsive strategy that first inspects box 1 and halts if
V1 = v1, otherwise it proceeds to inspect box 2 and halts if V2 = v2, and otherwise it proceeds to
inspect box 7 and halts" (p.9). The empty tuple is the empty strategy (p.8).

**Formalization Note.** Halting early at a zero value is the impulsive strategy of a shorter
tuple, so impulsive strategies are exactly the `impulsive l` for tuples `l` without repetition. -/
def impulsive {ι : Type*} (l : List ι) : Strategy ι where
  next h _ := if ∃ x ∈ h, x.2 ≠ 0 then none else l[h.length]?

/-- **The two-branch strategy of Lemma 3.1** (§3, p.8): "Inspect some first box, denoted r, …
If Vr = vr, execute an impulsive sub-strategy π^Y. If Vr = 0, execute an impulsive sub-strategy
π^N."

**Formalization Note.** After box `r`, the sub-strategy runs as `impulsive πY` (if the value of
`r` is non-zero) or `impulsive πN` (if it is zero) on the boxes opened after `r`, halting at the
first non-zero value among them (§3.1, p.9, where impulsive sub-strategies halt when `V_i = v_i`). -/
def branch {ι : Type*} (r : ι) (πY πN : List ι) : Strategy ι where
  next h s :=
    match h with
    | [] => some r
    | (_, vr) :: rest => (impulsive (if vr ≠ 0 then πY else πN)).next rest s

end PandoraComb


