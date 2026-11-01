-- Prove2me | Definitions.Def_NoSignalPA_keyEveMarg
-- name    : NoSignalPA_keyEveMarg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:03:29.132066+00:00
-- url     : https://prove2.me/theorems/a2630d6a-532c-4569-90d1-d54fe58a1bbb
-- title:
--   Joint distribution $P_{\mathbf k,e|\mathbf x,z}$ of the key $\mathbf k=h(\mathbf a)$ and Eve's output
-- statement:
--   For a hash function $h:\{0,1\}^{N_r}\to\{0,1\}^{N_s}$, a box $P$, inputs $\mathbf x,\mathbf y,z$, a key value $\mathbf k$ and an output $e$ of Eve,
--
--   $$
--   P_{\mathbf k,e|\mathbf x,\mathbf y,z}=\sum_{\mathbf a:\,h(\mathbf a)=\mathbf k}\ \sum_{\mathbf b}P_{\mathbf a,\mathbf b,e|\mathbf x,\mathbf y,z}.
--   $$
--
--   The paper writes $P_{\mathbf k,e|\mathbf x=\mathbf 0,z}$; under no signaling the value does not depend on Bob's input $\mathbf y$.
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, Main result, eq. (5), p.2

import Mathlib
import Definitions.Def_NoSignalPA_Box

namespace NoSignalPA

open scoped ENNReal

/-- **The joint distribution `P_{k,e|x,z}` of the key `k = h(a)` and Eve's output.**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, Main result, eq. (5), p. 2 (PDF p. 2): "the random variable k = h(a)", with `P_{k,e|x=0,z}`.

`keyEveMarg h P x y z k e = Σ_{a : h(a) = k} Σ_b P_{a,b,e|x,y,z}`, in `ℝ≥0∞`.

**Formalization Note.** Bob's input `y` is a parameter: under no signaling the value does not
depend on it, and the security predicate quantifies over every `y`. -/
noncomputable def keyEveMarg.{u} {Nr Ns : ℕ} {Z E : Type u} (h : Str Nr → Str Ns)
    (P : Box Nr Z E) (x y : Str Nr) (z : Z) (k : Str Ns) (e : E) : ℝ≥0∞ :=
  ∑ a ∈ Finset.univ.filter (fun a => h a = k), ∑ b : Str Nr, P x y z (a, b, e)

end NoSignalPA


