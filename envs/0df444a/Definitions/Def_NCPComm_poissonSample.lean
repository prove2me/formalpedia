-- Prove2me | Definitions.Def_NCPComm_poissonSample
-- name    : NCPComm_poissonSample
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:00:48.845899+00:00
-- url     : https://prove2.me/theorems/9d7a8dd8-e56c-419d-aa4d-cfbcd0244bcd
-- title:
--   The Poissonized sample $s^\prime\sim\mathrm{Poi}(s)$, its occurrence counts, pool totals and uniform reordering
-- statement:
--   Let $D$ be a distribution and $s\ge0$. The **Poissonized sample** of mean $s$ from $D$ draws $s'\sim\mathrm{Poi}(s)$ and then an ordered list of $s'$ independent draws from $D$. The **occurrence counts** $(X_x)_{x\in[N]}$ of a list give the number of occurrences of each label; the multiplicity indicators $v_i$ of the paper are recovered by $v_i(x)=1\iff X_x=i$.
--
--   Two further operations appear in the paper's claims. The **pool total** is the law of the sum of $t$ independent $\mathrm{Poi}(s)$ variables. The **uniform reordering** of a count function $c$ takes each label $x$ exactly $c(x)$ times and orders the resulting multiset uniformly at random.
--
--   **Formalization Note** The i.i.d. list is the published `OAI.ThreeState.iidList`. The Poisson law is Mathlib's `poissonMeasure`, read as a `PMF`. The uniform reordering is a uniform permutation of the positions of a fixed listing of the multiset, which gives the uniform law on arrangements.
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), §4, p.21 ("Poissonized protocols"); Claims 3.7, 3.9, 3.10, pp.15–16

import Mathlib
import Definitions.Def_OAI_Probability_ThreeState_Basic

open scoped NNReal ENNReal

namespace NCPComm

/-- The Poisson law `Poi(s)` on `ℕ`, as a `PMF`: Mathlib's `ProbabilityTheory.poissonMeasure`. -/
noncomputable def poissonLaw (s : ℝ≥0) : PMF ℕ := (ProbabilityTheory.poissonMeasure s).toPMF

/-- The Poissonized sample of §4, p.21 ("the verifier draws `s′ ∼ Poi(s)` samples"): draw
`s′ ∼ Poi(s)`, then an ordered list of `s′` independent draws from `D` (Herman, The Communication
Complexity of Verifying Distribution Properties, STOC 2027 submission, manuscript sha256 714c0353…).

**Formalization Note** `OAI.ThreeState.iidList D m` is the published law of `m` i.i.d. draws. The
mean `s` is a nonnegative real. -/
noncomputable def poissonSample {α : Type*} (D : PMF α) (s : ℝ≥0) : PMF (List α) :=
  (poissonLaw s).bind (OAI.ThreeState.iidList D)

/-- The occurrence counts of a sample: `countVec l x` is the number of occurrences of `x` in `l`
(`X_x` in Claim 3.7, p.15). The multiplicity indicators `v_i` of Definition 4.5, p.20, are
`v_i(x) = 1 ↔ countVec l x = i`, so the count function and the family `(v_i)_i` determine each
other. -/
def countVec {N : ℕ} (l : List (Fin N)) : Fin N → ℕ := fun x => l.count x

/-- The law of the total size of `t` independent Poisson sample pools of mean `s` (Claim 3.10,
p.16). -/
noncomputable def poolTotal (s : ℝ≥0) : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | t + 1 => (poolTotal s t).bind fun a => (poissonLaw s).map fun b => a + b

/-- The sample reconstruction of Claim 3.9, p.16: take each label `x` exactly `c x` times and order
the resulting multiset by a uniformly random permutation of the positions. -/
noncomputable def uniformOrder {N : ℕ} (c : Fin N → ℕ) : PMF (List (Fin N)) :=
  let L : List (Fin N) := (List.finRange N).flatMap fun x => List.replicate (c x) x
  (PMF.uniformOfFintype (Equiv.Perm (Fin L.length))).map fun σ => List.ofFn fun i => L.get (σ i)

end NCPComm


