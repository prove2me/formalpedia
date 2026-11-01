-- Prove2me | Definitions.Def_NoSignalPA_eveMarg
-- name    : NoSignalPA_eveMarg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:03:31.012819+00:00
-- url     : https://prove2.me/theorems/6eb5856e-c2f1-4bff-bbbe-0e78b9d1f7c8
-- title:
--   Eve's marginal $P_{e|z}$
-- statement:
--   For a box $P$ and inputs $\mathbf x,\mathbf y,z$,
--
--   $$
--   P_{e|z}=\sum_{\mathbf a}\sum_{\mathbf b}P_{\mathbf a,\mathbf b,e|\mathbf x,\mathbf y,z},
--   $$
--
--   the distribution of Eve's outcome when she measures with $z$. Under no signaling it does not depend on $\mathbf x,\mathbf y$. The ideal key is distributed as $2^{-N_s}P_{e|z}$.
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, p.2 ('If P_{e|z} is the distribution for the outcomes when this system is measured with the observable z')

import Mathlib
import Definitions.Def_NoSignalPA_Box

namespace NoSignalPA

open scoped ENNReal

/-- **Eve's marginal `P_{e|z}`.**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, p. 2 (PDF p. 2): "If `P_{e|z}` is the distribution for the outcomes when this system is measured
with the observable z".

`eveMarg P x y z e = Σ_a Σ_b P_{a,b,e|x,y,z}`, in `ℝ≥0∞`.

**Formalization Note.** Alice's and Bob's inputs `x, y` are parameters; under no signaling the
value does not depend on them. The security predicate uses `x = 0` and the same `y` as for the
key. -/
noncomputable def eveMarg.{u} {Nr : ℕ} {Z E : Type u} (P : Box Nr Z E) (x y : Str Nr) (z : Z)
    (e : E) : ℝ≥0∞ :=
  ∑ a : Str Nr, ∑ b : Str Nr, P x y z (a, b, e)

end NoSignalPA


