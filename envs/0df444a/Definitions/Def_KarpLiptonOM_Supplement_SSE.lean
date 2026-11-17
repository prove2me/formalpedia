-- Prove2me | Definitions.Def_KarpLiptonOM_Supplement_SSE
-- name    : KarpLiptonOM_Supplement_SSE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:39:37.799205+00:00
-- url     : https://prove2.me/theorems/70a5e0a1-5a42-4e9e-99d2-5405a934c187
-- title:
--   $\mathrm{SSE}$: set size estimation (the $\mathrm{prSBP}$-complete promise problem)
-- statement:
--   For a circuit $C$ with $n$ inputs let $\#C$ be the number of $x\in\{0,1\}^n$ with $C(x)=1$. The promise problem **SSE** (set size estimation) has
--
--   $$
--   \mathrm{SSE}_{\mathrm{YES}}=\{(C,m) : \#C\ge m\},\qquad \mathrm{SSE}_{\mathrm{NO}}=\{(C,m) : \#C\le m/2\},
--   $$
--
--   where $C$ is a circuit and $m\ge1$ is an integer given in binary. Strings that encode no instance lie in neither set.
--
--   SSE is complete for the promise class $\mathrm{prSBP}$ of Böhler, Glaßer and Meister, and an oracle for it is an oracle for approximate counting. The paper writes $\mathrm P^{\mathrm{prSBP}}=\mathrm P^{\mathrm{SSE}}$, $\mathrm{FP}^{\mathrm{prSBP}}=\mathrm{FP}^{\mathrm{SSE}}$ and $\mathrm{OGTD}[\mathrm{prSBP}]=\mathrm{OGTD}[\mathrm{SSE}]$, and every statement of this supplement about prSBP is a statement about SSE.
--
--   **Formalization Note** Instances are the strings `sseInst n s C m`, $\#C$ is `countStr n (fun x => C.eval x = true)`, and $\#C\le m/2$ is written $2\#C\le m$. The no-set requires $2\#C\le m$ for every instance the string encodes; as the encoding is injective, this is exactly the set above, and it lets the definition prove the two sets disjoint without decoding.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.3 ("Approximate counting"), p.22; #C, §A.2.1, p.21

import Mathlib
import Definitions.Def_KarpLiptonOM_PromiseProblem
import Definitions.Def_KarpLiptonOM_Circuit_eval
import Definitions.Def_KarpLiptonOM_countStr
import Definitions.Def_KarpLiptonOM_Supplement_sseInst

namespace KarpLiptonOM.Supplement

/-- The promise problem **SSE** (set size estimation; Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.3, "Approximate counting", p.22):
yes-instances are the pairs `(C, m)` with `#C ≥ m`, no-instances the pairs with `#C ≤ m/2`,
where `C` is a circuit, `#C` the number of its satisfying assignments (§A.2.1, p.21) and
`m ≥ 1` an integer given in binary. SSE is complete for prSBP, and the paper writes
`P^prSBP = P^SSE`, `FP^prSBP = FP^SSE` (p.22) and `OGTD[prSBP] = OGTD[SSE]` (p.25).

**Formalization Note** Instances are the strings `sseInst n s C m` (circuit `C` with `n` inputs and
at most `s` gates, `m ≥ 1`); a string that encodes no instance lies in neither set. `#C` is
`countStr n (fun x => C.eval x = true)` and `#C ≤ m/2` is written `2·#C ≤ m`. The no-set requires
`2·#C ≤ m` for every instance encoded by the string; since `sseInst` is injective on instances
this is the paper's no-set, and it makes disjointness provable without decoding. -/
def SSE : PromiseProblem where
  yes := {w | ∃ (n s : ℕ) (C : Circuit n) (m : ℕ), C.gates.length ≤ s ∧ 1 ≤ m ∧
    w = sseInst n s C m ∧ m ≤ countStr n (fun x => C.eval x = true)}
  no := {w | (∃ (n s : ℕ) (C : Circuit n) (m : ℕ), C.gates.length ≤ s ∧ 1 ≤ m ∧
      w = sseInst n s C m) ∧
    ∀ (n s : ℕ) (C : Circuit n) (m : ℕ), C.gates.length ≤ s → 1 ≤ m → w = sseInst n s C m →
      2 * countStr n (fun x => C.eval x = true) ≤ m}
  disjoint := by
    rw [Set.disjoint_left]
    rintro w ⟨n, s, C, m, hs, hm, hw, hc⟩ ⟨-, hall⟩
    have h2 := hall n s C m hs hm hw
    omega

end KarpLiptonOM.Supplement


