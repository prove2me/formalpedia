-- Prove2me | Definitions.Def_StretchDepth_Supplement_IsAvoidReduction
-- name    : StretchDepth_Supplement_IsAvoidReduction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:09:41.741101+00:00
-- url     : https://prove2.me/theorems/28c1b88b-5e47-4b9e-8994-587e233d217d
-- title:
--   $(q,d)$ amplification reductions for Avoid (Definition 6)
-- statement:
--   Let $N>n$ and $M>m$. A **$(q,d)$ amplification reduction for Avoid** from $n\mapsto N$ stretch to $m\mapsto M$ stretch is a pair $(H,\mathrm{Solve})$ where
--   1. $H:\{0,1\}^m\to\{0,1\}^M$ is a $(q,d)$-construction from an oracle $G:\{0,1\}^n\to\{0,1\}^N$ (at most $q$ queries in at most $d$ adaptive rounds, on every input and every $G$);
--   2. $\mathrm{Solve}:\{0,1\}^M\to\{0,1\}^N$ is an $\mathbf{FP^{NP}}$ query procedure of complexity $q$ querying $G$;
--   3. for every $G$ and every $y\in\{0,1\}^M$,
--   $$
--   y\notin\mathrm{range}(H^G)\ \Longrightarrow\ \mathrm{Solve}^G(y)\notin\mathrm{range}(G).
--   $$
--
--   No adaptivity-depth restriction is placed on $\mathrm{Solve}$. The definition formalizes a black-box reduction that turns a solution of Avoid for the stretched generator $H^G$ into a solution of Avoid for $G$.
--
--   **Formalization Note** $H$ uses the base mission's round trees and `IsConstruction`; the conditions $N>n$, $M>m$ are hypotheses of the theorems that use this predicate.
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), Definition 6, p.15 (PDF p.15)

import Definitions.Def_StretchDepth_IsConstruction
import Definitions.Def_StretchDepth_Supplement_FPNPProc

set_option autoImplicit false

namespace StretchDepth.Supplement

/-- **`(q, d)` amplification reduction for Avoid.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), Definition 6, p.15: "A (q, d) amplification reduction for Avoid from n ↦ N
stretch to m ↦ M stretch is a pair (H, Solve), where H(·) : {0,1}^m → {0,1}^M is a
(q, d)-construction from an oracle G : {0,1}^n → {0,1}^N, Solve(·) : {0,1}^M → {0,1}^N is an FP^NP
query procedure of complexity q, and jointly they satisfy the following for every
G : {0,1}^n → {0,1}^N, y ∈ {0,1}^M: y ∉ range(H^G) ⟹ Solve^G(y) ∉ range(G)."

**Formalization Note.** `H` is the base mission's round-tree construction (`IsConstruction`, with
multiplicity, on real oracles); `Solve` satisfies `IsFPNPProc` (at most `q` DNFs of width at most
`q` on every real run). No depth restriction is placed on `Solve` (p.15). The conditions `N > n`,
`M > m` are hypotheses of the theorems using this predicate. -/
def IsAvoidReduction {n N m M : ℕ} (H : Bits m → RoundTree n N M) (Solve : Bits M → FPNPProc n N)
    (q d : ℕ) : Prop :=
  IsConstruction H q d ∧ IsFPNPProc Solve q ∧
    ∀ (G : Bits n → Bits N) (y : Bits M),
      y ∉ Set.range (fun x => run G (H x)) → (Solve y).out G ∉ Set.range G

end StretchDepth.Supplement


