-- Prove2me | Definitions.Def_KarpLiptonOM_BPP
-- name    : KarpLiptonOM_BPP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:31.33489+00:00
-- url     : https://prove2.me/theorems/9cac2e63-9890-4001-a77c-9e2cea5fb779
-- title:
--   $L \in \mathrm{BPP}^A$ (bounded error $1/3$)
-- statement:
--   A language $L$ is in $\mathrm{BPP}^A$ if there are a deterministic polynomial-time oracle machine $M$ and a polynomial $q$ such that for every input $x$,
--   $$
--   \Pr_{r \in \{0,1\}^{q(|x|)}}\bigl[M^A(x, r) \text{ accepts} \iff x \in L\bigr] \ge \tfrac23 .
--   $$
--
--   **Formalization Note** The paper uses $\mathrm{BPP}^{\mathrm{ONP}}$ without defining BPP; this is the standard definition with error $1/3$.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Lemma A.4.1, p.29 (standard class)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_IsPolyTime
import Definitions.Def_KarpLiptonOM_OracleTM_Accepts
import Definitions.Def_KarpLiptonOM_countStr
import Definitions.Def_KarpLiptonOM_tupleEnc

namespace KarpLiptonOM

/-- `L ∈ BPP^A` (bounded-error probabilistic polynomial time with oracle `A`; standard, used
without definition in Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), Lemma A.4.1, p.29): a polynomial-time oracle machine `M` and a
polynomial `q` with `Pr_{r ∈ {0,1}^{q(|x|)}}[M^A(x, r) = L(x)] ≥ 2/3` for every `x`. -/
def BPP (A L : Set (List Bool)) : Prop :=
  ∃ (M : OracleTM) (k : ℕ) (q : Polynomial ℕ), M.IsPolyTime k ∧ ∀ x : List Bool,
    2 * 2 ^ q.eval x.length ≤
      3 * countStr (q.eval x.length) (fun r => M.Accepts A (tupleEnc [x, r]) ↔ x ∈ L)

end KarpLiptonOM


