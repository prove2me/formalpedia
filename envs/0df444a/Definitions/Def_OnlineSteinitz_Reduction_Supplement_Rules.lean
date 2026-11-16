-- Prove2me | Definitions.Def_OnlineSteinitz_Reduction_Supplement_Rules
-- name    : OnlineSteinitz_Reduction_Supplement_Rules
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:14:22.85791+00:00
-- url     : https://prove2.me/theorems/7929c055-471e-48a7-838c-b1aab9c8b2b9
-- title:
--   Scalar ratio routing and greedy augmented signing
-- statement:
--   The scalar local rule reconstructs actual left and right placements by quota replay of its proposed-sign history. Let $L,R$ be the two child sums and $r_L,r_R$ the remaining capacities. A full child forces the other destination. Otherwise put $H=L+R+(r_L+r_R)v$. For $H\ge0$, choose left exactly when $(L+1)/r_L\le(R+1)/r_R$; for $H<0$, choose left exactly when $(L-1)/r_L\ge(R-1)/r_R$. Ties go left. The comparison branch has positive remaining capacities.
--
--   The greedy signer returns $+1$ when the inner product of the previous proposed signed sum with the arriving vector is nonpositive, and $-1$ otherwise. The published augmentation supplies $(v,1)/\sqrt2$. Proposed state continues to update after quota overrides. Algorithm 1 uses the scalar rule in dimension one and greedy signing in higher dimensions. A generic causal interface replays the known vector prefix to recover the current router state, then performs the next descent; it never uses future inputs or their total. The exact constant from (3.2) is $(\sqrt2+1)/(1-\sqrt{2/3})$.
-- source:
--   Russo–Wei, The Online Steinitz Problem, STOC 2027 submission #22 (2026 preprint), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/22.pdf; SHA-256 32ff14f15a94c95630765c77f4fa5a429fb294bcf03a9055ed67c60658769366; Algorithm 1, p.5; §3.1, pp.13–14; §3.2 and (3.2), pp.14–15

import Definitions.Def_OnlineSteinitz_Reduction_Supplement_Algorithms

open scoped BigOperators

namespace OnlineSteinitz.Reduction.Supplement

/-! The scalar rule of §3.1 pp.13–14, with quota statistics replayed
from proposed history. The forced branches precede divisions. Ties go left. -/
noncomputable def scalarLocal (m : ℕ) : Signer ℝ Unit := fun _ h x =>
  let visits := repair m h
  let L := ((visits.filter Visit.actual).map Visit.vector).sum
  let R := ((visits.filter (fun e => !e.actual)).map Visit.vector).sum
  let rL := leftSize m - leftCount visits
  let rR := rightSize m - (visits.length - leftCount visits)
  if rL = 0 then false else if rR = 0 then true else
    if 0 ≤ L + R + ((rL + rR : ℕ) : ℝ) * x then
      decide ((L + 1) / rL ≤ (R + 1) / rR)
    else decide ((L - 1) / rL ≥ (R - 1) / rR)

noncomputable def scalarCoordinate {d : ℕ} (x : Vec d) : ℝ := ∑ i, x i

noncomputable def scalarVectorLocal (d m : ℕ) : Signer (Vec d) Unit :=
  fun ω h x => scalarLocal m ω
    (h.map (fun e => (scalarCoordinate e.1, e.2))) (scalarCoordinate x)

/-! Greedy proposed-sign state, §3.2 pp.14–15: equality chooses +1.
The published augmentedRule supplies (v,1)/sqrt(2). -/
noncomputable def greedyLocal (D : ℕ) : Signer (Vec D) Unit :=
  fun _ h z => decide (inner ℝ (signedVector h) z ≤ 0)

noncomputable def greedyRules (T d : ℕ) : Node T → Signer (Vec d) Unit :=
  fun _ => augmentedRule (greedyLocal (d + 1))

noncomputable def upperRules (T d : ℕ) : Node T → Signer (Vec d) Unit :=
  if d = 1 then fun u => scalarVectorLocal d u.2.val else greedyRules T d

/-! Causal interface for Algorithm 1: replay just the known vector prefix,
then perform the next placement. On histories it can reach this is its exact state.
No total sum, correctness property or discrepancy bound is an input. -/
noncomputable def routerOrdering {T d : ℕ}
    (rules : Node T → Signer (Vec d) Unit) : OrderingRule d Unit :=
  fun _ h x =>
    let old := execute rules (fun _ => ()) (h.map Prod.snd)
    let next := descend rules (fun _ => ()) T 0 T old.localHistory x
    next.1

noncomputable def upperOrdering (T d : ℕ) : OrderingRule d Unit :=
  routerOrdering (upperRules T d)

noncomputable def greedyConstant : ℝ :=
  (Real.sqrt 2 + 1) / (1 - Real.sqrt (2 / 3 : ℝ))

end OnlineSteinitz.Reduction.Supplement


