-- Prove2me | Definitions.Def_RvsCert_C0
-- name    : RvsCert_C0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:40:56.26131+00:00
-- url     : https://prove2.me/theorems/3caedfeb-5627-42cd-b11f-4c3d07934d19
-- title:
--   0-certificate complexity $C_0(f)$
-- statement:
--   For a Boolean function $f$ on a finite set of bit positions,
--   $$
--   C_0(f)=\max_{x\,:\,f(x)=0} C_x(f),
--   $$
--   the largest certificate complexity of a 0-input ($0$ when $f$ has no 0-input). Lemma 4 of the paper shows $C_0(f)=\Omega(n^2)$ for its function.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Lemma 4, p.3 (standard notion)

import Mathlib
import Definitions.Def_RvsCert_certAt

namespace RvsCert

/-- **0-certificate complexity** `C0(f)` (standard, [BdW02]; used in Lemma 4, p.3 of
Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1): the maximum, over inputs `x` with `f x = false`, of the least size of a
certificate for `x`.

**Formalization Note.** A `Finset.sup` over all inputs of `if f x = false then certAt f x else 0`;
it is `0` when `f` has no 0-input. -/
noncomputable def C0 {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → Bool) : ℕ :=
  Finset.univ.sup fun x => if f x = false then certAt f x else 0

end RvsCert


