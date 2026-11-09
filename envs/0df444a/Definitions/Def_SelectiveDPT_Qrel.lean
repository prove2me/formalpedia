-- Prove2me | Definitions.Def_SelectiveDPT_Qrel
-- name    : SelectiveDPT_Qrel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:35.705959+00:00
-- url     : https://prove2.me/theorems/9fda9aa4-b767-4c1b-9d3a-8b735db65bdc
-- title:
--   Worst-case quantum query complexity $Q_\varepsilon(R)$ of a relation
-- statement:
--   Let $R \subseteq D \times Y$ be a relation on a domain $D \subseteq X^\iota$. A **$T$-query algorithm** has a query register ($i \in \iota$, $p \in \mathbb Z_d$) and a workspace; it starts from a fixed unit vector, applies input-independent unitaries $U_0, \dots, U_T$ with the phase oracle $O_x$ between consecutive ones, measures its whole register in the computational basis and applies an input-independent post-processing map to the outcome. Its **success probability** on $x$ is the probability that the output $y$ satisfies $(x,y) \in R$.
--
--   The **worst-case quantum query complexity** $Q_\varepsilon(R)$ is the least $T$ such that some $T$-query algorithm succeeds with probability at least $1-\varepsilon$ on **every** input $x \in D$, and $\infty$ if there is none.
--
--   **Formalization Note** The workspace is $\{0,\dots,b-1\}$ for an arbitrary $b$; the value lies in $\mathbb N \cup \{\infty\}$. With an empty index set the query register is empty and no algorithm exists.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, §2.2, pp.9–10 (query algorithms, Q_ε(R))

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_SelectiveDPT_phaseOracle

namespace SelectiveDPT

open QAlgorithms

/-- The probability that the `T`-query algorithm `A` with workspace `Fin b`, run with the phase
oracle of the input `x` and followed by a computational-basis measurement of its whole register
and the input-independent post-processing `out`, produces an output `y` with `(x, y) ∈ R`
(arXiv:2609.26678, §2.2, p.10: "The output of the quantum query algorithm is determined by
measuring the work register of `|ψ_T⟩` in the standard basis and applying some input-independent
post-processing function `q`"). -/
noncomputable def successProb {ι Y : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} [NeZero d]
    {b T : ℕ} (A : QueryAlg ι (ZMod d) (Fin b) T) (out : (ι × ZMod d) × Fin b → Y)
    (R : (ι → ZMod d) → Y → Prop) (x : ι → ZMod d) : ℝ := by
  classical
  exact probEvent (A.finalState (phaseOracle x)) fun z => R x (out z)

/-- The worst-case quantum query complexity `Q_ε(R)` of the relation `R ⊆ D × Y`
(arXiv:2609.26678, §2.2, p.10: "We use `Q_ε(R)` to denote the quantum query complexity of
computing `R` with probability at least `1 − ε` on every input"): the least `T` such that some
`T`-query algorithm (input-independent start state and unitaries `U_0, …, U_T`, phase oracle
`O` between them, §2.2, p.9) with some post-processing `out` outputs a `y` with `(x, y) ∈ R` with
probability at least `1 − ε` for **every** `x ∈ D`; `⊤` if there is none.

**Formalization Note.** The algorithm model is `QAlgorithms.QueryAlg` with query register
`ι × Z_d` (index, phase) and workspace `Fin b` for an arbitrary `b`; only the dimension of the
workspace matters. The output is read by measuring the whole register and applying `out`, which
covers measuring a designated output register. Values of `R` outside `D` are never read. -/
noncomputable def Qrel {ι Y : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} [NeZero d]
    (D : Finset (ι → ZMod d)) (R : (ι → ZMod d) → Y → Prop) (ε : ℝ) : ℕ∞ :=
  ⨅ (T : ℕ) (_ : ∃ (b : ℕ) (A : QueryAlg ι (ZMod d) (Fin b) T)
      (out : (ι × ZMod d) × Fin b → Y), ∀ x ∈ D, 1 - ε ≤ successProb A out R x), (T : ℕ∞)

end SelectiveDPT


