-- Prove2me | Definitions.Def_VapnikChervonenkis_Shared_Phi
-- name    : VapnikChervonenkis_Shared_Phi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:32:47.233745+00:00
-- url     : https://prove2.me/theorems/e0f230b9-f972-463c-b212-4541f04d02cd
-- title:
--   The function Φ(n, r) of recurrence (1)
-- statement:
--   For natural numbers $n$ and $r$, the function $\Phi(n, r)$ of Vapnik and Chervonenkis is defined by the recurrence relation (1):
--
--   $$
--   \Phi(n, r) = \Phi(n, r-1) + \Phi(n-1, r-1), \qquad \Phi(0, r) = 1, \qquad \Phi(n, 0) = 1 .
--   $$
--
--   The first equation applies for $n \ge 1$ and $r \ge 1$; the two boundary conditions agree at $\Phi(0,0) = 1$. For example $\Phi(1, r) = r + 1$, and $\Phi(n, r) = 2^r$ whenever $r \le n$.
--
--   In the paper, $\Phi(n, r)$ is introduced (Example 3) as the maximal number of components into which $r$ hyperplanes partition $n$-dimensional space, which is the growth function of the class of half-spaces. Every later use of $\Phi$, beginning with Lemma 1 ("$\Phi(n, i)$ is defined by the recurrence relation (1)"), relies on the recurrence alone. $\Phi(n, r)$ is the Sauer–Shelah bound: it bounds the number of subsamples a class can induce on $r$ points once it induces all $2^n$ subsamples on no $n$ of them.
--
--   **Shared definition.** This one definition serves two missions of the paper: *01-growth-function* (the closed form and polynomial bound of $\Phi$, p. 266; Lemma 1, p. 266; the index bound behind Theorem 1, p. 268) and *03-entropy-criterion* (Lemma 1, p. 266, and inequality (26) in the necessity proof of Theorem 4, p. 277).
--
--   **Formalization Note.** $\Phi$ is a function $\mathbb{N} \times \mathbb{N} \to \mathbb{N}$ defined by structural recursion with exactly the three equations of (1). The geometric description (components of a hyperplane arrangement) is not formalized.
-- source:
--   Vapnik and Chervonenkis, On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities, Theory Probab. Appl. 16 (1971), p. 266, Subsection 1, Eq. (1)

import Mathlib

namespace VapnikChervonenkis.Shared

/-- The function `Φ(n, r)` of Vapnik and Chervonenkis (1971), p. 266, defined by the
recurrence relation (1):
`Φ(n, r) = Φ(n, r - 1) + Φ(n - 1, r - 1)`, `Φ(0, r) = 1`, `Φ(n, 0) = 1`.
(The paper introduces `Φ(n, r)` as the maximal number of regions into which `r` hyperplanes cut
`n`-dimensional space, but every later use, e.g. Lemma 1, takes it "defined by the recurrence
relation (1)"; that recurrence is the definition here.) -/
def Phi : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 1
  | n + 1, r + 1 => Phi (n + 1) r + Phi n r

end VapnikChervonenkis.Shared


