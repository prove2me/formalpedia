-- Prove2me | Definitions.Def_PPADSIS_SubexpSIS_KarpReduction
-- name    : PPADSIS_SubexpSIS_KarpReduction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:50:00.25373+00:00
-- url     : https://prove2.me/theorems/f155ea12-c47f-40c8-b36c-52fb125b27a0
-- title:
--   Randomized Karp reductions from RSVL to EOML with a deterministic instance map (Theorem 3.3)
-- statement:
--   A **randomized Karp reduction from RSVL to EOML with success probability $|I|^{-O(1)}$** and a deterministic instance map is a pair $(R_1,R_2)$ such that
--
--   - $R_1$ maps RSVL instances to EOML instances and is computed in deterministic polynomial time on descriptions;
--   - $R_2$ is a probabilistic polynomial-time decoder on input $(I,z)$;
--   - there is a constant $c$ such that for every RSVL instance $I$ satisfying the promise, $R_1(I)$ satisfies the EOML guarantee, and for every solution $z$ of $R_1(I)$,
--   $$\Pr\bigl[R_2(I,z)\text{ is an RSVL solution of }I\bigr]\ \ge\ (|I|+2)^{-c},$$
--   where $|I|$ is the length of the description of $I$.
--
--   The paper does not define the notion; this reading follows the paragraph after Theorem 3.3 (p. 21): "In this reduction, the instance map $R_1$ is deterministic ... Given a solution of $R_1(I)$, the decoder $R_2$ picks one of these pairs uniformly at random ... This is an RSVL solution with probability at least $1/(\lceil\log L\rceil+1)$", and "if $D$ is a hard distribution over RSVL instances, then $R_1(D)$ is a hard distribution over EOML instances".
--
--   **Formalization Note** $|I|^{-O(1)}$ is written $(|I|+2)^{-c}$ to avoid the degenerate values $|I|\in\{0,1\}$; for $|I|\ge2$ the two classes of bounds coincide.
-- source:
--   Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript sha256 17abad73…), p. 21, Theorem 3.3 and the paragraph after it

import Mathlib
import Definitions.Def_PPSLattice_PolyTimeOn
import Definitions.Def_PPADSIS_SubexpSIS_EOML
import Definitions.Def_PPADSIS_SubexpSIS_RSVL

set_option autoImplicit false

namespace PPADSIS.SubexpSIS

/-- The input of the decoder `R2`: an RSVL instance `I` and an output string `z` (a claimed
solution of `R1(I)`), written `encPair (desc I) z`. -/
def decoderCode (Iz : RSVLInstance × List Bool) : List Bool := encPair Iz.1.enc Iz.2

/-- A **randomized Karp reduction from RSVL to EOML with success probability `|I|^{−O(1)}` and a
deterministic instance map** (Choudhuri, *PPAD Hardness from SIS*, STOC 2027 submission
(manuscript sha256 17abad73…), Theorem 3.3 and the paragraph after it, p. 21; the notion is not
defined in the paper). A pair `(R1, R2)`:
- `R1` maps RSVL instances to EOML instances and is deterministic polynomial time on
  descriptions;
- `R2` is a probabilistic polynomial-time decoder on input `(I, z)`;
- there is a constant `c` such that for every RSVL instance `I` satisfying the promise, `R1(I)`
  satisfies the EOML guarantee, and for every solution `z` of `R1(I)`, `R2(I, z)` is a solution of
  `I` with probability at least `(|I| + 2)^{−c}`, where `|I|` is the length of the description
  of `I`. -/
def IsRandKarpRSVLtoEOML (R1 : RSVLInstance → EOMLInstance) (R2 : CoinAlg decoderCode) :
    Prop :=
  PPSLattice.PolyTimeOn RSVLInstance.enc (fun I => (R1 I).enc) ∧
  R2.IsPPT ∧
  ∃ c : ℕ, ∀ I : RSVLInstance, I.Promise →
    (R1 I).Guarantee ∧
    ∀ z : List Bool, (R1 I).IsSolution z →
      R2.prob (I, z) I.IsSolution ≥ 1 / ((I.enc.length : ℝ) + 2) ^ c

end PPADSIS.SubexpSIS


