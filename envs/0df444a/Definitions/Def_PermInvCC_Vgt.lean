-- Prove2me | Definitions.Def_PermInvCC_Vgt
-- name    : PermInvCC_Vgt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:26:08.231985+00:00
-- url     : https://prove2.me/theorems/0a33bf40-002d-43fd-b8c9-0f1a0e830728
-- title:
--   Juntas and degree spaces $V_{X,\le d}$, $V_{X,>d}$ on a multislice
-- statement:
--   A function on $X$ **depending on at most $d$ coordinates** is a $d$-junta: there is a set $I$ of at most $d$ positions such that the function agrees on any two strings of $X$ that agree on $I$. $V_{X,\le d}$ is the span of the $d$-juntas, and
--   $$V_{X,>d}:=V_{X,\le d}^{\perp}$$
--   is its orthogonal complement for the uniform-measure inner product.
--
--   Lemma B.2 shows that the averaging operators contract $V_{X,>d}$ exponentially in $d$.
--
--   **Formalization Note** Functions on $X$ are represented by functions on all of $[q]^N$; only their values on $X$ enter.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), App. B.1, p.40

import Mathlib
import Definitions.Def_PermInvCC_multislice

namespace PermInvCC

/-- A **`d`-junta** on a set `X` of strings: a function that depends on at most `d` coordinates,
i.e. there is a set `I` of at most `d` positions such that `u` agrees on any two strings of `X`
that agree on `I` (Y. Huang and Z. Ye, arXiv:2609.40116, held version sha256 fe1797dd…,
App. B.1, p.40). -/
def IsJunta {N q : ℕ} (X : Finset (Fin N → Fin q)) (d : ℕ) (u : (Fin N → Fin q) → ℝ) : Prop :=
  ∃ I : Finset (Fin N), I.card ≤ d ∧
    ∀ x ∈ X, ∀ x' ∈ X, (∀ i ∈ I, x i = x' i) → u x = u x'

/-- `V_{X,≤d}`: the span of the `d`-juntas (App. B.1, p.40).

**Formalization Note.** Functions on `X` are represented by functions on all of `[q]^N`; only
their values on `X` enter the inner product. -/
def Vle {N q : ℕ} (X : Finset (Fin N → Fin q)) (d : ℕ) : Submodule ℝ ((Fin N → Fin q) → ℝ) :=
  Submodule.span ℝ {u | IsJunta X d u}

/-- `V_{X,>d} := V_{X,≤d}^⊥`, the orthogonal complement for the uniform-measure inner product of
`L²(X)` (App. B.1, p.40). -/
def Vgt {N q : ℕ} (X : Finset (Fin N → Fin q)) (d : ℕ) : Set ((Fin N → Fin q) → ℝ) :=
  {h | ∀ u ∈ Vle X d, msInner X h u = 0}

end PermInvCC


