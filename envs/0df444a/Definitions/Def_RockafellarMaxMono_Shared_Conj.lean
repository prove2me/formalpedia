-- Prove2me | Definitions.Def_RockafellarMaxMono_Shared_Conj
-- name    : RockafellarMaxMono_Shared_Conj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:00:33.544751+00:00
-- url     : https://prove2.me/theorems/1a3ba5ef-ccfe-40b3-b471-81d6051ec3f8
-- title:
--   Conjugate function $f^*$ on the dual space
-- statement:
--   Let $V$ be a real normed space with dual $V^*$. The **conjugate** of a function $f : V \to [-\infty,+\infty]$ is the function $f^*$ on $V^*$ defined by
--
--   $$
--   f^*(x^*) = \sup \{\, \langle x, x^* \rangle - f(x) \mid x \in V \,\},
--   $$
--
--   with values in $[-\infty, +\infty]$. Applying the construction twice gives the biconjugate $f^{**} = (f^*)^*$, a function on the bidual $V^{**}$.
--
--   The conjugate is the bridge between $\partial f$ and $\partial f^*$ in Rockafellar's argument: the Fenchel–Young inequality (2.2) characterizes subgradients through equality in $f(x) + f^*(x^*) \ge \langle x, x^* \rangle$.
--
--   It serves chunk 01-maximal-monotone ((2.1) p. 210, (2.3) p. 211; the Fenchel–Young relation (2.2), Proposition 1, and the finiteness of $(f+j)^*$ in §3, p. 213) and chunk 02-cyclic-characterization ((2.1) p. 210, (2.3) p. 211; the finiteness of $(f+j)^*$ and $(g+j)^*$ on $E^*$ and the return to $E$ through the biconjugate in the proof of Theorem B).
--
--   **Formalization Note** The supremum is taken in `EReal`, over all of $V$ (points where $f = +\infty$ contribute $-\infty$). The Lean name is `conj f`; the biconjugate is `conj (conj f)`, a function on `StrongDual ℝ (StrongDual ℝ V)`.
-- source:
--   Rockafellar, On the maximal monotonicity of subdifferential mappings, Pacific J. Math. 33 (1970), p. 210, (2.1); p. 211, (2.3)

import Mathlib

namespace RockafellarMaxMono.Shared

/-- Rockafellar (1970), (2.1), p. 210: the *conjugate* of `f : V → (−∞, +∞]` is the function
on the dual `V* = StrongDual ℝ V` given by `f*(x*) = sup {⟨x, x*⟩ − f(x) | x ∈ V}`,
computed in `EReal` (so `f*` may take the value `+∞`). The biconjugate `f**` is
`conj (conj f)`, a function on the bidual `StrongDual ℝ (StrongDual ℝ V)`. -/
noncomputable def conj {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : V → EReal) :
    StrongDual ℝ V → EReal :=
  fun x' => ⨆ x : V, ((x' x : ℝ) : EReal) - f x

end RockafellarMaxMono.Shared


