-- Prove2me | Definitions.Def_DworczakDACC_neverAfter
-- name    : DworczakDACC_neverAfter
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:17.093733+00:00
-- url     : https://prove2.me/theorems/d7a735d2-f5a4-4aa6-b454-9ab1a865b1fc
-- title:
--   $X^k$: pairs that never interact after round $k$
-- statement:
--   $$X^k=\bigl\{\{i,j\}:\ i\in N,\ j\in N_i,\ i\text{ and }j\text{ never interact after round }k\bigr\},$$
--
--   the set of man–woman pairs that do not interact at any time from the end of round $k$ on.
--
--   **Formalization Note** The paper defines $X^k$ for $k\ge k^\star$; the set makes sense for every $k$. It is a finite set of pairs in $D\times H$, defined classically.
-- source:
--   Dworczak, Deferred Acceptance with Compensation Chains (working paper, Nov 9, 2017), Appendix A, p. 23

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Definitions.Def_DworczakDACC_roundEnd
import Definitions.Def_DworczakDACC_Interacts

namespace DworczakDACC

open RuralHospitals

variable {D H : Type*} [Fintype D] [Fintype H] [DecidableEq D] [DecidableEq H]

open Classical in
/-- **`Xᵏ`: the man–woman pairs that never interact after round `k`.**
Dworczak, *Deferred Acceptance with Compensation Chains* (working paper, Nov 9, 2017), Appendix A,
p. 23: "Xᵏ = {{i, j} : i ∈ N, j ∈ Nᵢ, i and j never interact after round k}".

`neverAfter Mk Φ ord k` is the finite set of pairs `(d, h)` such that `Interacts Mk Φ ord t d h`
fails at every time `t ≥ roundEnd Mk Φ ord k`, i.e. in every pass of the loop after the end of
round `k`.

**Formalization Note.** The paper defines `Xᵏ` for `k ≥ k⋆`; the set itself makes sense for every
`k`, and the milestone `claim_5` uses it only for `k − 1 ≥ k⋆`. -/
noncomputable def neverAfter (Mk : Market D H) (Φ : ℕ → D ⊕ H) (ord : ℕ → Bool) (k : ℕ) :
    Finset (D × H) :=
  Finset.univ.filter
    (fun p => ∀ t, roundEnd Mk Φ ord k ≤ t → ¬ Interacts Mk Φ ord t p.1 p.2)

end DworczakDACC


