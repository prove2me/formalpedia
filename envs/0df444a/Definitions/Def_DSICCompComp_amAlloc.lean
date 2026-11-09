-- Prove2me | Definitions.Def_DSICCompComp_amAlloc
-- name    : DSICCompComp_amAlloc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:30:02.131844+00:00
-- url     : https://prove2.me/theorems/defcb0b4-1eb8-42a9-85ff-b80f612330b6
-- title:
--   Affine-maximizer allocation $S(v)$
-- statement:
--   Given a reported value profile $v$, the affine maximizer chooses a feasible allocation $S(v) = (S_1(v),\dots,S_n(v))$ that maximizes the affine-maximizer objective; $S_i(v)$ is the set of items allocated to bidder $i$.
--
--   **Formalization Note** Ties are broken by taking, among the maximizers, the first one in a fixed enumeration of all allocations. Any deterministic selection gives the same Clarke payments up to ties; this one is a measurable function of the profile.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), §3.3, pp.11–12 (pdf pp.12–13)

import Mathlib
import Definitions.Def_DSICCompComp_IsFeasibleAlloc
import Definitions.Def_DSICCompComp_amObj

open scoped NNReal

namespace DSICCompComp

open Classical in
/-- The allocation `S(v) = (S_1(v), …, S_n(v))` chosen by the affine maximizer of §3.3
(Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*,
STOC 2027 submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…, §3.3, pp.11–12
(pdf pp.12–13)): a feasible allocation (`IsFeasibleAlloc ℓ r`) maximizing the objective `amObj`
at the reported profile `v`.

**Formalization Note** Tie-break: among the maximizers, the one with the least index in the fixed
enumeration `Fintype.equivFin` of all allocations. This is one fixed deterministic selection
(not `Classical.choose`), so `v ↦ S(v)` is a measurable function of the profile (finitely many
comparisons of continuous functions). The set of maximizers is always nonempty (a finite
nonempty feasible set, containing `S ≡ ∅`); the `else` branch is never taken. -/
noncomputable def amAlloc {n m : ℕ} (ℓ r : ℕ) (a ε t T : ℝ) (v : Fin n → Fin m → ℝ≥0) :
    Fin n → Finset (Fin m) :=
  let feas := Finset.univ.filter (IsFeasibleAlloc (n := n) (m := m) ℓ r)
  if hne : feas.Nonempty then
    let best := feas.sup' hne (amObj r a ε t T v)
    let cands := feas.filter (fun S => amObj r a ε t T v S = best)
    let e := Fintype.equivFin (Fin n → Finset (Fin m))
    if hc : cands.Nonempty then e.symm ((cands.image e).min' (hc.image e)) else fun _ => ∅
  else fun _ => ∅

end DSICCompComp


