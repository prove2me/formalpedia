-- Prove2me | Definitions.Def_NoSignalPA_abMarg
-- name    : NoSignalPA_abMarg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:03:31.544698+00:00
-- url     : https://prove2.me/theorems/27e632c0-2abf-4356-bfd8-983cbe1b63f6
-- title:
--   Alice and Bob's marginal $P_{\mathbf a,\mathbf b|\mathbf x,\mathbf y}$
-- statement:
--   For a box $P$ and an input $z_0$ of Eve, the vector of $\mathbb R^{16^{N_r}}$
--
--   $$
--   P_{\mathbf a,\mathbf b|\mathbf x,\mathbf y}=\sum_e P_{\mathbf a,\mathbf b,e|\mathbf x,\mathbf y,z_0}.
--   $$
--
--   It is the vector paired with $|\mathrm{CHSH}\rangle^{\otimes N_r}$ on the right side of (5). Under no signaling it does not depend on $z_0$.
--
--   **Formalization Note** The sum over $e$ is an extended-real `tsum` with value at most 1, converted to a real number.
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, eq. (5), p.2

import Mathlib
import Definitions.Def_NoSignalPA_Box

namespace NoSignalPA

open scoped ENNReal

/-- **Alice and Bob's marginal `P_{a,b|x,y}`, as a vector of `ℝ^{16^{Nr}}`.**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, eq. (5), p. 2 (PDF p. 2): the right side of (5) pairs `|CHSH⟩^{⊗Nr}` with `|P_{a,b|x,y}⟩`.

`abMarg P z₀ a b x y = Σ_e P_{a,b,e|x,y,z₀}`, a real number in `[0, 1]`.

**Formalization Note.** The marginal is taken at Eve's input `z₀`; under no signaling it does not
depend on `z₀`, and the security predicate quantifies over every `z₀`. The sum over `e` is a
`tsum` in `ℝ≥0∞`, at most 1, converted to a real number. -/
noncomputable def abMarg.{u} {Nr : ℕ} {Z E : Type u} (P : Box Nr Z E) (z₀ : Z) :
    Str Nr → Str Nr → Str Nr → Str Nr → ℝ :=
  fun a b x y => (∑' e : E, P x y z₀ (a, b, e)).toReal

end NoSignalPA


