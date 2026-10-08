-- Prove2me | Definitions.Def_VeinottNoDiscount_Improve_Sets
-- name    : VeinottNoDiscount_Improve_Sets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:47:39.879559+00:00
-- url     : https://prove2.me/theorems/083c71fc-2cc1-4de3-bf1f-9705b58bbf85
-- title:
--   F′, F″ (p. 1286), the sets G(f), E(f) of decision rules (p. 1287), w(g) of (10), z(f) of (12) and the set H(f) (p. 1290)
-- statement:
--   This file defines the objects of Veinott's extended policy improvement method on top of Blackwell's finite decision model: a finite set of states $s$, a finite set of actions, incomes $i(s,a)$ and transition probabilities $q(s'\mid s,a)$. A decision rule $f\in F$ picks an action in every state; $r(f)$ is its income vector, $Q(f)$ its transition matrix, $Q^*(f)$ the Cesàro limit of the powers of $Q(f)$, and
--   $$x(f)=Q^*(f)\,r(f),\qquad y(f)=H(f)\,r(f)$$
--   are the **gain** and **bias** of the stationary policy $f^\infty$, with $H(f)=(I-Q(f)+Q^*(f))^{-1}-Q^*(f)$. Vectors are compared coordinatewise, and $[u]_s$ is the $s$th component of $u$.
--
--   1. $F'=\{f\in F : x(f)\ge x(g)\text{ for all } g\in F\}$ and $F''=\{f\in F' : y(f)\ge y(g)\text{ for all } g\in F'\}$.
--   2. For $f,g\in F$ consider
--   $$\text{(i)}\ \ [Q(g)x(f)]_s\ge [x(f)]_s,\qquad \text{(ii)}\ \ [r(g)+Q(g)y(f)]_s\ge [x(f)+y(f)]_s .$$
--   $G(f)$ is the set of $g\in F$ such that (i) holds for all $s$; (ii) holds for each $s$ for which (i) holds with equality; at least one of the inequalities (i), (ii) is strict for some $s$; and $g(s)=f(s)$ for each $s$ for which (i) and (ii) both hold with equality.
--   3. $E(f)$ is the set of $g\in F$ for which (i) and (ii) hold with equality at every state $s$.
--   4. For $g\in E(f)$, $w(g)=Q^*(g)\,(-y(f))$, the unique solution of $[I-Q(g)]w=0,\ Q^*(g)w=Q^*(g)(-y(f))$ (Veinott's (10)).
--   5. $z(f)=H(f)\,(-y(f))$, the unique solution of $[I-Q(f)]z=-y(f),\ Q^*(f)z=0$ (Veinott's (12)).
--   6. For $g\in E(f)$ consider
--   $$\text{(iii)}\ \ [-y(f)+Q(g)z(f)]_s\ge [z(f)]_s .$$
--   $H(f)$ is the set of $g\in E(f)$ such that (iii) holds for all $s$ and strictly for some $s$, and $g(s)=f(s)$ for each $s$ for which (iii) holds with equality.
--
--   $F'$ is the set of decision rules with maximal average return per unit time and $F''$ those that in addition have maximal bias; $G(f)$ and $H(f)$ are the two improvement sets of the algorithm whose stopping rule ($G(f)\cup H(f)$ empty) certifies $f\in F''$.
--
--   **Formalization Note** Every action is available in every state ($A_s=A$ for all $s$), as in the published Blackwell model this file builds on. The vectors $w$ and $z$ are defined by their closed forms; that they are the unique solutions of (10) and (12) is stated as separate theorems. $w(g)$ depends on the fixed $f$ as well and is written $w(f,g)$ in Lean. $H(f)$ is named `HSet` to keep it apart from Blackwell's deviation matrix $H(f)$ (`Hf`). The third clause of $G(f)$ is read as "for some $s$, (i) or (ii) is strict", which, given the first clause, coincides with "(i) is strict, or (i) holds with equality and (ii) is strict".
-- source:
--   Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting, Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, pp. 1286–1290: F′, F″ (p. 1286), (i), (ii) (p. 1286), G(f), E(f) (p. 1287), (10) (p. 1289), (12), (iii), H(f) (p. 1290)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottNoDiscount.Improve

variable {St Act : Type*} [Fintype St] [DecidableEq St]

/-- `F′ = {f | f ε F, x(f) ≧ x(g) all g ε F}`: the decision rules of maximal gain (average return
per unit time), compared coordinatewise against every decision rule.

Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting,
Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1286, §2
(unnumbered definition after (7)).

**Formalization Note.** `F = St → Act` (every action available in every state, `A_s = Act`);
`x(f)` is Blackwell's closed form `Q*(f) r(f)` (published `Model.x`), and `≧` is the pointwise
order on `St → ℝ`. -/
def Fprime (M : Model St Act) : Set (St → Act) :=
  {f | ∀ g : St → Act, M.x g ≤ M.x f}

/-- `F″ = {f | f ε F′, y(f) ≧ y(g) all g ε F′}`: among the gain-maximizing decision rules, those of
maximal bias.

Veinott (1966), DOI 10.1214/aoms/1177699272, p. 1286, §2 (unnumbered definition after (7)).

**Formalization Note.** `y(f)` is Blackwell's closed form `H(f) r(f)` (published `Model.y`);
`≧` is pointwise. -/
def Fdprime (M : Model St Act) : Set (St → Act) :=
  {f | f ∈ Fprime M ∧ ∀ g ∈ Fprime M, M.y g ≤ M.y f}

/-- Veinott's set `G(f)` of decision rules improving on `f` (p. 1287), built from the inequalities
(p. 1286)

* (i)  `[Q(g)x(f)]_s ≧ [x(f)]_s`,
* (ii) `[r(g) + Q(g)y(f)]_s ≧ [x(f) + y(f)]_s`:

`G(f)` is the set of `g ε F` such that (i) holds for all `s`; (ii) holds for each `s` for which (i)
holds with equality; at least one of the inequalities in (i), (ii) is strict; and for each `s` for
which (i) and (ii) hold with equality, `g(s) = f(s)`.

Veinott (1966), DOI 10.1214/aoms/1177699272, pp. 1286–1287, §2.

**Formalization Note.** `[Q(g)v]_s = M.pDot s (g s) v` and `[r(g)]_s = M.r g s`. The four
clauses are stated literally (this is not Blackwell's per-state `gainBiasImprovementSet`). The
third clause is read as "for some `s`, (i)_s is strict or (ii)_s is strict"; given the first
clause this coincides with the reading "(i)_s is strict, or (i)_s holds with equality and (ii)_s
is strict". -/
def GSet (M : Model St Act) (f : St → Act) : Set (St → Act) :=
  {g | (∀ s, M.x f s ≤ M.pDot s (g s) (M.x f)) ∧
      (∀ s, M.pDot s (g s) (M.x f) = M.x f s →
        M.x f s + M.y f s ≤ M.r g s + M.pDot s (g s) (M.y f)) ∧
      (∃ s, M.x f s < M.pDot s (g s) (M.x f) ∨
        M.x f s + M.y f s < M.r g s + M.pDot s (g s) (M.y f)) ∧
      (∀ s, M.pDot s (g s) (M.x f) = M.x f s →
        M.r g s + M.pDot s (g s) (M.y f) = M.x f s + M.y f s → g s = f s)}

/-- Veinott's set `E(f)`: the `g ε F` such that (i) and (ii) hold with equality for all `s`, i.e.
`[Q(g)x(f)]_s = [x(f)]_s` and `[r(g) + Q(g)y(f)]_s = [x(f) + y(f)]_s` for every state `s`.

Veinott (1966), DOI 10.1214/aoms/1177699272, p. 1287, §2, definition before (8).

**Formalization Note.** Written through Blackwell's per-state set `E(s, f)`
(`gainBiasEqualSet f s`), which is exactly the product form (8), `E(f) = ×_s E(s, f)`;
membership `g s ∈ M.gainBiasEqualSet f s` unfolds to `M.pDot s (g s) (M.x f) = M.x f s` and
`M.i s (g s) + M.pDot s (g s) (M.y f) = M.x f s + M.y f s`, i.e. (i) and (ii) with equality at
`s` (note `M.i s (g s) = M.r g s` by definition). -/
def ESet (M : Model St Act) (f : St → Act) : Set (St → Act) :=
  {g | ∀ s, g s ∈ M.gainBiasEqualSet f s}

/-- `w(g)` of Lemma 4 (p. 1289), for `f` fixed and `g ε E(f)`: the unique solution of
(10) `[I − Q(g)]w = 0, Q*(g)w = Q*(g)(−y(f))`.

Veinott (1966), DOI 10.1214/aoms/1177699272, p. 1289, Lemma 4, (10).

**Formalization Note.** Closed form `w = Q*(g)(−y(f))` (it solves (10) because
`Q(g)Q*(g) = Q*(g)Q*(g) = Q*(g)`, Veinott's (4)). The paper writes `w(g)`, suppressing the
dependence on `f`; here it is `w M f g`. The (10) characterization is the theorem formalizing
Lemma 4. -/
noncomputable def w (M : Model St Act) (f g : St → Act) : St → ℝ :=
  M.Qstar g *ᵥ (-(M.y f))

/-- `z(f)` of (12) (p. 1290): the unique solution of `[I − Q(f)]z(f) = −y(f), Q*(f)z(f) = 0`.

Veinott (1966), DOI 10.1214/aoms/1177699272, p. 1290, §3, (12).

**Formalization Note.** Closed form `z(f) = H(f)(−y(f))`, with `H(f)` Blackwell's deviation
matrix `(I − Q(f) + Q*(f))⁻¹ − Q*(f)` (published `Model.Hf`); it solves (12) because
`(I − Q)H = I − Q*`, `Q*H = 0` and `Q*(f)y(f) = 0`. The (12) characterization is a separate
theorem (milestone "(12)"). -/
noncomputable def z (M : Model St Act) (f : St → Act) : St → ℝ :=
  M.Hf f *ᵥ (-(M.y f))

/-- Veinott's set `H(f)` of decision rules (p. 1290), built from the inequality, for `g ε E(f)`,

* (iii) `[−y(f) + Q(g)z(f)]_s ≧ [z(f)]_s`:

`H(f)` is the set of `g ε E(f)` such that (iii) holds for all `s` and strictly for some `s`; and for
each `s` for which (iii) holds with equality, `g(s) = f(s)`.

Veinott (1966), DOI 10.1214/aoms/1177699272, p. 1290, §3, after (12).

**Formalization Note.** Named `HSet`, not `H`: Blackwell's published `Model.Hf` is the deviation
*matrix* `H(f)`, a different object. `H(f) ⊂ E(f)` is built in as the first clause. -/
def HSet (M : Model St Act) (f : St → Act) : Set (St → Act) :=
  {g | g ∈ ESet M f ∧
      (∀ s, z M f s ≤ -(M.y f s) + M.pDot s (g s) (z M f)) ∧
      (∃ s, z M f s < -(M.y f s) + M.pDot s (g s) (z M f)) ∧
      (∀ s, -(M.y f s) + M.pDot s (g s) (z M f) = z M f s → g s = f s)}

end VeinottNoDiscount.Improve


