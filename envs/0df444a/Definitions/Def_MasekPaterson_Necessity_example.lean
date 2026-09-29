-- Prove2me | Definitions.Def_MasekPaterson_Necessity_example
-- name    : MasekPaterson_Necessity_example
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:19:30.055232+00:00
-- url     : https://prove2.me/theorems/75f82f39-9e10-4ed9-b0b1-ccb8f41a4e14
-- title:
--   The §4.1 example: alphabet {a, b, c}, costs 0, 1, π, 5, the strings A, B, and P*(i, j, k)
-- statement:
--   Let $\Sigma = \{a, b, c\}$ and define the cost function $\gamma$ by, for all $\sigma \in \Sigma$,
--
--   $$R_{\sigma,\sigma} = 0,\quad R_{a,b} = R_{b,a} = 1,\quad R_{c,b} = R_{c,a} = R_{a,c} = R_{b,c} = \pi,\quad I_\sigma = D_\sigma = 5.$$
--
--   Let $\mu_{2k} = \mu_{2k+1} = \lfloor 2k/(2\pi + 1) \rfloor$ for $k \ge 0$. The infinite strings $A$ and $B$ start from $A' = baba\ldots$ and $B' = abab\ldots$; some characters in even positions are replaced by $c$ so that the number of $c$'s in $A^i$ (and in $B^i$) equals $\mu_i$. Concretely, $A_i = b$ and $B_i = a$ for odd $i$; for even $i$, $A_i = B_i = c$ if $\mu_i > \mu_{i-1}$, and otherwise $A_i = a$, $B_i = b$. Since $2/(2\pi + 1) < 1$, $\mu$ grows by at most one between consecutive even indices, so this is the unique placement with the stated count. The first fifty characters are
--
--   $$A^{50} = bababab\,c\,bababab\,c\,babab\,c\,bababab\,c\,bababab\,c\,babab\,c\,bababa,$$
--
--   and $B^{50}$ is the same with $a$ and $b$ exchanged outside the $c$'s.
--
--   For this example $\delta_{i,j} = \delta(\gamma, A^i, B^j)$. $P(i, j, k)$ is the minimum cost of an edit path from $(i, j)$ to $(i + k, j + k)$, and $P^*(i, j, k)$ is the minimum cost of any path from $(i, j)$ to $(i + k, j + k)$ through points all of eccentricity at least $|i - j|$.
--
--   The costs make optimal paths use many replacements; the irrational cost $\pi$ keeps the even and the odd diagonals of the edit matrix from ever falling into a periodic pattern.
--
--   **Formalization Note** $\mu_i$ is written $\lfloor 2\lfloor i/2 \rfloor / (2\pi + 1) \rfloor$, which is the paper's $\mu_{2k} = \mu_{2k+1}$. The strings are 1-based functions $\mathbb{N} \to \Sigma$ and $A^n$ is the list $A_1, \dots, A_n$. The constraint on $P^*$ applies to every point of the path, both endpoints included. $P$ and $P^*$ are infima of nonempty sets (the diagonal of $k$ replacements qualifies) of nonnegative reals.
-- source:
--   Masek, Paterson, A Faster Algorithm Computing String Edit Distances, J. Comput. System Sci. 20, 1980, pp. 26–27, Section 4.1 (The Example) and Fig. 3

import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
import Definitions.Def_MasekPaterson_Necessity_editPaths
open MasekPaterson.Shared

namespace MasekPaterson.Necessity

/-- The alphabet `Σ = {a, b, c}` of the example of §4.1. -/
inductive Sym
  | a
  | b
  | c
  deriving DecidableEq, Repr

/-- The alphabet `Σ = {a, b, c}` is finite. -/
instance : Fintype Sym :=
  ⟨{Sym.a, Sym.b, Sym.c}, fun x => by cases x <;> simp⟩

/-- The replacement costs of the example: `R_{σ,σ} = 0`, `R_{a,b} = R_{b,a} = 1`,
`R_{c,b} = R_{c,a} = R_{a,c} = R_{b,c} = π`. -/
noncomputable def exRepl : Sym → Sym → ℝ
  | .a, .a => 0
  | .b, .b => 0
  | .c, .c => 0
  | .a, .b => 1
  | .b, .a => 1
  | .c, .b => Real.pi
  | .c, .a => Real.pi
  | .a, .c => Real.pi
  | .b, .c => Real.pi

/-- The cost function `γ` of the example: a replacement `x → y` costs `R_{x,y}` (`exRepl`),
and every insertion and every deletion costs `I_σ = D_σ = 5`. (The pair `(λ, λ)` is not an
edit operation; the last branch covers exactly the deletions and insertions.) -/
noncomputable def exCost (o : EditOp Sym) : ℝ :=
  match o.src, o.tgt with
  | some x, some y => exRepl x y
  | _, _ => 5

/-- `μ_i = ⌊2⌊i/2⌋ / (2π + 1)⌋`, i.e. `μ_{2k} = μ_{2k+1} = ⌊2k / (2π + 1)⌋`. -/
noncomputable def mu (i : ℕ) : ℕ :=
  ⌊((2 * (i / 2) : ℕ) : ℝ) / (2 * Real.pi + 1)⌋₊

/-- The infinite string `A` of the example, 1-based (`exA i` is `A_i` for `i ≥ 1`; the
value at `0` is never used): `A' = baba…` with `c` put in the even positions `i` where
`μ_i > μ_{i-1}`, so that `A^i` contains exactly `μ_i` letters `c`. -/
noncomputable def exA (i : ℕ) : Sym :=
  if i % 2 = 1 then .b else if mu (i - 1) < mu i then .c else .a

/-- The infinite string `B` of the example, 1-based: `B' = abab…` with `c` put in the same
even positions as in `A`. -/
noncomputable def exB (i : ℕ) : Sym :=
  if i % 2 = 1 then .a else if mu (i - 1) < mu i then .c else .b

/-- The prefix `A^n = A_1 ⋯ A_n` of length `n`. -/
noncomputable def exAPre (n : ℕ) : List Sym := List.ofFn fun t : Fin n => exA (t.val + 1)

/-- The prefix `B^n = B_1 ⋯ B_n` of length `n`. -/
noncomputable def exBPre (n : ℕ) : List Sym := List.ofFn fun t : Fin n => exB (t.val + 1)

/-- The edit matrix entry `δ_{i,j} = δ(γ, A^i, B^j)` of the example. -/
noncomputable def exDelta (i j : ℕ) : ℝ := editDist exCost (exAPre i) (exBPre j)

/-- `P(i, j, k)`: the minimum cost of an edit path from `(i, j)` to `(i + k, j + k)`. -/
noncomputable def exP (i j k : ℕ) : ℝ := pathMin exCost exA exB (i, j) (i + k, j + k)

/-- `P*(i, j, k)`: the minimum cost of an edit path from `(i, j)` to `(i + k, j + k)` all of
whose points (endpoints included) have eccentricity at least `|i - j|`. -/
noncomputable def exPstar (i j k : ℕ) : ℝ :=
  sInf {c : ℝ | ∃ ms : List Move, pathEnd (i, j) ms = (i + k, j + k) ∧
    (∀ x ∈ pathPoints (i, j) ms, ecc (i, j) ≤ ecc x) ∧
    c = pathCost exCost exA exB (i, j) ms}

end MasekPaterson.Necessity


