-- Prove2me | Definitions.Def_DSICCompComp_optMinus
-- name    : DSICCompComp_optMinus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:30:39.883613+00:00
-- url     : https://prove2.me/theorems/80ce748a-b47a-444a-bcf0-c98fcfb22154
-- title:
--   $\mathrm{OPT}_{-i,-U}(v)$: optimal objective without bidder $i$ and items $U$
-- statement:
--   For a bidder $i$ and a set of items $U \subseteq [\ell]$, $\mathrm{OPT}_{-i,-U}(v)$ is the optimal affine-maximizer objective without bidder $i$ and without the items in $U$: the maximum of the objective over feasible allocations with $S_i = \varnothing$ and $S_h \cap U = \varnothing$ for every bidder $h$. It does not depend on bidder $i$'s values $v_i$, and it is at least $0$ (the empty allocation is allowed).
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), §3.3, p.12 (pdf p.13)

import Mathlib
import Definitions.Def_DSICCompComp_IsFeasibleAlloc
import Definitions.Def_DSICCompComp_amObj

open scoped NNReal

namespace DSICCompComp

/-- `OPT_{−i,−U}(v)` of §3.3 (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive
Buyers over Independent Items*, STOC 2027 submission, manuscript of Nov. 3, 2026,
sha256 bf61bfdb…, §3.3, p.12 (pdf p.13)): the optimal affine-maximizer objective without bidder
`i` and without the items in `U ⊆ [ℓ]`, i.e. the maximum of `amObj` over feasible allocations
with `S_i = ∅` and `S_h ∩ U = ∅` for every bidder `h`. It does not depend on `v_i`.

**Formalization Note** The maximum is a `Finset.sup'` over a finite set that contains the empty
allocation `S ≡ ∅` (objective `0`), so it is a genuine maximum, never a junk value. -/
noncomputable def optMinus {n m : ℕ} (ℓ r : ℕ) (a ε t T : ℝ) (i : Fin n) (U : Finset (Fin m))
    (v : Fin n → Fin m → ℝ≥0) : ℝ :=
  (Finset.univ.filter (fun S : Fin n → Finset (Fin m) =>
      IsFeasibleAlloc ℓ r S ∧ S i = ∅ ∧ ∀ h, Disjoint (S h) U)).sup'
    ⟨fun _ => ∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp [IsFeasibleAlloc]⟩⟩
    (amObj r a ε t T v)

end DSICCompComp


