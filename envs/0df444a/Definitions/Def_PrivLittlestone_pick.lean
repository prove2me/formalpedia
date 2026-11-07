-- Prove2me | Definitions.Def_PrivLittlestone_pick
-- name    : PrivLittlestone_pick
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:35:09.984633+00:00
-- url     : https://prove2.me/theorems/45fbeedd-7173-4872-beb3-526249cd1506
-- title:
--   Inverse-CDF sampling from $Q_S$
-- statement:
--   Along a fixed public enumeration $h_1, \dots, h_n$ of $C(S)$, a number $u \in [0,1)$ is mapped to the first $h_k$ with $u < Q_S(h_1) + \dots + Q_S(h_k)$. For $u$ uniform on $[0,1]$ the output has law $Q_S$. This realizes the draws "independently from $Q_S$" of Algorithm 1, line 6, as functions of uniform coins.
--
--   **Formalization Note** The enumeration is `Finset.toList` (a fixed public encoding, as allowed in §2); $u = 1$ and $u \notin [0,1]$, which have probability zero, map to the last element or a fixed member of $C(S)$.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Algorithm 1, line 6, p.7; §2, p.4

import Mathlib
import Definitions.Def_PrivLittlestone_gibbs

namespace PrivLittlestone

/-- **Inverse-CDF sampling from `Q_S`** (He–He, *Private Online Learning of Littlestone Classes
and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), Algorithm 1, line 6,
p.7; §2, p.4: "All representative choices, … tie-breaking rules, and encodings are public and
fixed"): along the fixed enumeration `h_1, …, h_n` of `C(S)` (`Finset.toList`), a uniform
`u ∈ [0,1)` is mapped to the first `h_k` with `u < Q_S(h_1) + ⋯ + Q_S(h_k)`.

**Formalization Note** For `u` uniform on `[0,1]` the output has law `Q_S` (the event `u = 1` and
values outside `[0,1]` have probability zero; they map to the last element or a fixed member of
`C(S)`). -/
noncomputable def pick {Z U : Type*} {D : ℕ} {B : ℝ} (sys : RankedCandidateSystem Z U D B)
    (η a : ℝ) (S : List Z) (u : ℝ) : U :=
  let l := (sys.C S).toList
  match (List.range l.length).find?
      (fun k => decide (u < ((l.take (k + 1)).map (gibbs sys η a S)).sum)) with
  | some k => l.getD k (sys.C_nonempty S).choose
  | none => l.getLastD (sys.C_nonempty S).choose

end PrivLittlestone


