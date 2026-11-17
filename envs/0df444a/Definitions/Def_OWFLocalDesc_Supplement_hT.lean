-- Prove2me | Definitions.Def_OWFLocalDesc_Supplement_hT
-- name    : OWFLocalDesc_Supplement_hT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:40:48.268982+00:00
-- url     : https://prove2.me/theorems/0872a5a7-d7d7-4747-b0b2-384ea59e8725
-- title:
--   Minimum global program length $h^T_W(x,y)$ (Definition B.1)
-- statement:
--   Fix a global decoder $V$, a value $T$ of the global clock and a public tape $W$. For an ordered vector $x$ of $m$ points and a label vector $y\in\{0,1\}^m$,
--   $$h^T_W(x,y)=\min\{|\beta| : V(\beta, E(x), W)\text{ halts within }T\text{ steps with output exactly }y\},$$
--   and $h^T_W(x,y)=\infty$ if no program qualifies.
--
--   Only the program length is charged. The complete ordered point vector is the conditioning input, and the program may depend on the tape $W$.
--
--   **Formalization Note** The value lies in $\mathbb N\cup\{\infty\}$ (`ℕ∞`), and the infimum of the empty family is $\infty$. "Halts within $T$ steps" is the $T$-step run being halted, since runs are monotone.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Definition B.1, p.37

import Mathlib
import Definitions.Def_OWFLocalDesc_Supplement_GlobalDecoder
import Definitions.Def_OWFLocalDesc_Supplement_globalEnc
set_option autoImplicit false

namespace OWFLocalDesc.Supplement

/-- **Minimum global program length `h^T_W(x,y)` (Definition B.1).** Myrisiotis, *One-Way
Functions and Local Descriptions of Random Data*, STOC 2027 submission (held manuscript, sha256
d818fa43…4c4e), Definition B.1, p.37: "Write h^T_W(x,y) for the minimum length of a program that
makes V halt with output exactly y within that clock. The program receives conditioning input
E(x). Set this minimum to ∞ if no such program exists."

`hT V T x y W` is the least `|β|` such that `V` on program `β`, conditioning input `E(x)` and
public tape `W` has halted with output exactly the label string `y₁ ⋯ y_m` after `T` steps.

**Formalization Note.** The value is in `ℕ∞` (the infimum of the empty family is `⊤ = ∞`).
"Within the clock" is `run … T = some _` (runs are monotone, `GlobalDecoder.run_mono`). Only the
program length is charged. -/
noncomputable def hT (V : GlobalDecoder) (T : ℕ) {m n : ℕ} (x : Fin m → Fin n → Bool)
    (y : Fin m → Bool) (W : List Bool) : ℕ∞ :=
  ⨅ (β : List Bool) (_ : V.run β (globalEnc x) W T = some (List.ofFn y)), (β.length : ℕ∞)

end OWFLocalDesc.Supplement


