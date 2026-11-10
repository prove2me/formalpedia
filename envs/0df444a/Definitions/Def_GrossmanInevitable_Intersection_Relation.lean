-- Prove2me | Definitions.Def_GrossmanInevitable_Intersection_Relation
-- name    : GrossmanInevitable_Intersection_Relation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:03:39.225476+00:00
-- url     : https://prove2.me/theorems/543511c8-6da1-420a-af94-eb8610077c6a
-- title:
--   Search problems with $\bot$, $D(R\mid P)$ under a promise, and $\max_{\emptyset\ne X\times Y\subseteq f^{-1}(1)} D(R\mid X\times Y)$
-- statement:
--   Let $A$ and $B$ be finite input domains, as required in §2. A **relation** $R\subseteq A\times B\times W$ is a predicate $R(a,b,w)$; $w$ is a **witness** of $(a,b)$ if $(a,b,w)\in R$. The **search problem** of $R$ asks for a witness of $(a,b)$, or for the symbol $\bot$ if $(a,b)$ has none. An output $o\in W\cup\{\bot\}$ (Lean: `Option W`, `none` $=\bot$) is **correct** on $(a,b)$ (`CorrectOut`) if it is a witness of $(a,b)$ when $(a,b)$ has one, and $\bot$ otherwise.
--
--   For a promise $P\subseteq A\times B$, $D(R\mid P)$ is the minimum, over deterministic protocols with outputs in $W\cup\{\bot\}$ whose output is correct on every input pair in $P$, of the worst-case cost $\max_{(a,b)\in P}|\pi(a,b)|$ on $P$. Correctness and cost are measured only on $P$. For a rectangle $X\times Y$ all of whose pairs have a witness, $D(R\mid X\times Y)$ is the minimum worst-case communication of a deterministic protocol that finds an $R$-witness on every input pair in $X\times Y$.
--
--   For a decision problem $f:A\times B\to\{0,1\}$ (Lean: `Bool`, `true` $=1$), `oneRectMax f R` is
--   $$\max_{\emptyset\ne X\times Y\subseteq f^{-1}(1)} D(R\mid X\times Y),$$
--   where the maximum over an empty set is $0$.
--
--   Formalization note: `DPromise` and `oneRectMax` require `[Finite A] [Finite B]`. The minimum is an `sInf` in $\mathbb N$. Since $A$ and $B$ are finite, a protocol in which both players send their whole input is correct on $P$, so the set is nonempty and the `sInf` is attained. The maximum is an `sSup` in $\mathbb N$ over a set that is finite when $A$ and $B$ are finite. `sSup ∅ = 0` is exactly the paper's convention.
-- source:
--   Grossman, Grossman, Naor, Shulman, Inevitable Knowledge in Communication Complexity and the LOCAL Model, STOC 2027 submission (manuscript sha256 67c87783…), §1.1 p. 2 (PDF 4), §2.1 pp. 13–14 (PDF 15–16), Lemma 1.4 p. 4 (PDF 6)

import Mathlib
import Definitions.Def_OneOfManyCC_Protocol
import Definitions.Def_GrossmanInevitable_Intersection_Transcript

namespace GrossmanInevitable.Intersection

open OneOfManyCC

/-- **Correct output for the search problem of a relation** (§1.1, printed p. 2 / PDF 4; §2.1,
printed p. 13 / PDF 15). A relation `R ⊆ A × B × W` is a predicate `R a b w`; `w` is a *witness*
of `(a, b)` if `R a b w`. An output in `W ∪ {⊥}` is encoded as `Option W` (`none` = `⊥`). The
output `o` is correct on `(a, b)` if it is a witness of `(a, b)` whenever `(a, b)` has one, and
`⊥` otherwise: `some w` is correct iff `R a b w`, and `none` is correct iff `(a, b)` has no
witness. -/
def CorrectOut {A B W : Type} (R : A → B → W → Prop) (a : A) (b : B) : Option W → Prop
  | some w => R a b w
  | none => ¬ ∃ w, R a b w

/-- **`D(R|P)`**, the deterministic communication complexity of the relation `R` under the promise
`(a, b) ∈ P` (§2.1, printed p. 14 / PDF 16): the minimum, over deterministic protocols `π` with
outputs in `W ∪ {⊥}` that are correct (`CorrectOut`) on every input pair of `P`, of the worst-case
cost `max_{(a,b) ∈ P} |π(a, b)|` on `P`; correctness and cost are measured only on `P`. For
`P = X ×ˢ Y` this is `D(R|X×Y)`. On a rectangle all of whose pairs have an `R`-witness it is
"the minimum worst-case communication of a deterministic protocol that finds an R-witness on every
input pair in X × Y" (Lemma 1.4). The finite input domains required by §2 are explicit:
a protocol exchanging both inputs is
correct on `P`, so the set below is nonempty and `sInf` is its minimum. -/
noncomputable def DPromise {A B W : Type} [Finite A] [Finite B] (R : A → B → W → Prop) (P : Set (A × B)) : ℕ :=
  sInf {c : ℕ | ∃ π : Protocol A B (Option W),
    ∀ p ∈ P, CorrectOut R p.1 p.2 (π.eval p.1 p.2) ∧ cost π p.1 p.2 ≤ c}

/-- `max_{∅ ≠ X × Y ⊆ f⁻¹(1)} D(R|X×Y)`, "where the maximum over an empty set is 0"
(Lemma 1.4, printed p. 4 / PDF 6). A decision problem is `f : A → B → Bool` (`true` = 1). The set
of values is the set of `D(R|X×Y)` over nonempty rectangles `X × Y` contained in `f⁻¹(1)`. For
finite `A`, `B` this set is finite, so its `sSup` in `ℕ` is its maximum, and `sSup ∅ = 0`. -/
noncomputable def oneRectMax {A B W : Type} [Finite A] [Finite B] (f : A → B → Bool) (R : A → B → W → Prop) : ℕ :=
  sSup {d : ℕ | ∃ X : Set A, ∃ Y : Set B, (X ×ˢ Y).Nonempty ∧
    X ×ˢ Y ⊆ {p | f p.1 p.2 = true} ∧ d = DPromise R (X ×ˢ Y)}

end GrossmanInevitable.Intersection


