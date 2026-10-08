-- Prove2me | Definitions.Def_PrivateRelease_NetMechanism_Queries
-- name    : PrivateRelease_NetMechanism_Queries
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T16:07:06.016982+00:00
-- url     : https://prove2.me/theorems/217b5673-b53d-45e5-89e6-e961f087f162
-- title:
--   Databases, counting queries, global sensitivity, usefulness and α-nets (Definitions 2.2, 2.3, 2.10, 2.11)
-- statement:
--   This file fixes the objects of Section 2 of Blum, Ligett and Roth.
--
--   Let $X$ be a data universe. A **database of arbitrary size** $D\in X^*$ is a finite, nonempty multiset of elements of $X$ (records may repeat, and their order is irrelevant). The mechanism's **input** is an $n$-tuple $z=(z_1,\dots,z_n)\in X^n$, read as the multiset $\{z_1,\dots,z_n\}$. Every set of databases is an event.
--
--   1. **Counting query** (Definition 2.3). For a predicate $\varphi:X\to\{0,1\}$,
--   $$
--   Q_\varphi(D)=\frac{\sum_{x\in D}\varphi(x)}{|D|},
--   $$
--   the fraction of records of $D$, counted with multiplicity, that satisfy $\varphi$. A class $C$ of predicates is identified with its class of counting queries $\{Q_\varphi:\varphi\in C\}$.
--   2. **Global sensitivity** (Definition 2.2). For $f:X^n\to\mathbb R$,
--   $$
--   GS_f=\max_{z,z'\ \text{neighbouring}}|f(z)-f(z')|,
--   $$
--   where $z,z'\in X^n$ are neighbouring if they differ in exactly one entry. It is $0$ when there is no neighbouring pair.
--   3. **Usefulness** (Definition 2.10). A mechanism $A$, whose output on input $z$ is a random database $\hat D\in X^*$, is $(\alpha,\delta)$-useful for a class $\mathcal Q$ of queries if for every input $z\in X^n$,
--   $$
--   \Pr\big[\,|Q(\hat D)-Q(z)|\le\alpha\ \text{for all } Q\in\mathcal Q\,\big]\ \ge\ 1-\delta .
--   $$
--   4. **α-net** (Definition 2.11). A finite set $N\subseteq X^*$ is an $\alpha$-net for $\mathcal Q$ if every database $D\in X^*$ has some $D'\in N$ with $|Q(D)-Q(D')|\le\alpha$ for all $Q\in\mathcal Q$. It is a **minimum** $\alpha$-net if no $\alpha$-net has fewer members; the paper writes $N_\alpha(C)$ for such a net.
--
--   These are the objects in which every statement of the Net mechanism mission is phrased: the mechanism's privacy is measured against the neighbour relation, its accuracy by usefulness, and its range is a minimum α-net.
--
--   **Formalization Note** Databases of arbitrary size are nonempty multisets, so $Q_\varphi$ never divides by $0$. The paper's "$|D\Delta D'|\le 1$" is read as *replace one entry*, the relation `PrivLearn.Generic.Neighbors`; read literally for equal-size multisets it would force $D=D'$. Queries are functions on multisets, so the same query evaluates on inputs and on synthetic databases. The global sensitivity is a real supremum over neighbouring pairs; every theorem using it takes $X$ finite, where it is a maximum over a finite family. The paper's $\max_{Q\in C}|\cdot|\le\alpha$ is written as "for all $Q\in C$". $N_\alpha(C)$ is not defined as an infimum of cardinalities: statements quantify over minimum nets and assert that one exists.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), pp. 5–7, §2, Definitions 2.2, 2.3, 2.10, 2.11

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy

namespace PrivateRelease.NetMechanism

open MeasureTheory

/-- §2 (p. 5): a database of arbitrary size, `D ∈ X*`, read as a multiset of data records. Only
nonempty databases are admitted, so that the counting query `Q(D) = (Σ_{x∈D} φ(x))/|D|` never
divides by `0`. Synthetic outputs and members of α-nets (Definition 2.11) are of this type. -/
def Database (X : Type) : Type := {D : Multiset X // D ≠ 0}

instance (X : Type) [DecidableEq X] : DecidableEq (Database X) :=
  inferInstanceAs (DecidableEq {D : Multiset X // D ≠ 0})

/-- Outputs of mechanisms are discrete objects: every set of databases is an event. -/
instance (X : Type) : MeasurableSpace (Database X) := ⊤

/-- §2 (p. 5): the mechanism's input `z ∈ Xⁿ` (an `n`-tuple), read as the multiset of its entries
`{z 1, …, z n}` ("these tuples are not endowed with an ordering"). -/
def inputDB {X : Type} {n : ℕ} (z : Fin n → X) : Multiset X :=
  Multiset.map z Finset.univ.val

/-- Definition 2.3 (p. 6): the counting query of the predicate `φ : X → {0,1}`,
`Q_φ(D) = (Σ_{x ∈ D} φ(x)) / |D|`, the fraction of records of `D` (with multiplicity) satisfying
`φ`. On the empty multiset Lean's `0/0 = 0`; databases in statements are nonempty. -/
noncomputable def countQ {X : Type} (φ : X → Bool) (D : Multiset X) : ℝ :=
  ((D.filter fun x => φ x = true).card : ℝ) / (D.card : ℝ)

/-- p. 6: the class of counting queries `{Q_φ : φ ∈ C}` of a class `C` of predicates (the paper
identifies the two and writes `VC-DIM(C)` for the predicates' VC-dimension). -/
def countingClass {X : Type} (C : Set (X → Bool)) : Set (Multiset X → ℝ) :=
  countQ '' C

/-- Definition 2.2 (p. 6): the global sensitivity
`GS_f = max_{D, D′ ∈ Xⁿ neighbouring} |f(D) − f(D′)|` of a real function of the input, with the
replace-one-entry neighbour relation `PrivLearn.Generic.Neighbors`. For a finite universe `X` the
family is finite, so the real supremum is the maximum; it is `0` when no neighbouring pair exists. -/
noncomputable def GS {X : Type} {n : ℕ} (f : (Fin n → X) → ℝ) : ℝ :=
  ⨆ p : {p : (Fin n → X) × (Fin n → X) // PrivLearn.Generic.Neighbors p.1 p.2},
    |f p.1.1 - f p.1.2|

/-- Definition 2.10 (p. 7): a mechanism `A`, whose output on the input `z ∈ Xⁿ` has law `A z`
on `X*`, is `(α, δ)`-useful for the class of queries `QC` if for every input `z`, with
probability at least `1 − δ` the output `D̂` satisfies `|Q(D̂) − Q(z)| ≤ α` for every `Q ∈ QC`. -/
def Useful {X : Type} {n : ℕ} (QC : Set (Multiset X → ℝ)) (α δ : ℝ)
    (A : (Fin n → X) → Measure (Database X)) : Prop :=
  ∀ z : Fin n → X,
    ENNReal.ofReal (1 - δ) ≤ A z {Dh | ∀ Q ∈ QC, |Q Dh.1 - Q (inputDB z)| ≤ α}

/-- Definition 2.11 (p. 7): a finite set `N ⊆ X*` is an α-net for the class of queries `QC` if
every (nonempty) database `D ∈ X*` has some `D′ ∈ N` with `|Q(D) − Q(D′)| ≤ α` for all `Q ∈ QC`. -/
def IsNet {X : Type} (QC : Set (Multiset X → ℝ)) (α : ℝ) (N : Finset (Database X)) : Prop :=
  ∀ D : Database X, ∃ D' ∈ N, ∀ Q ∈ QC, |Q D.1 - Q D'.1| ≤ α

/-- Definition 2.11 (p. 7): `N` is an α-net of minimum cardinality among all α-nets for `QC`
(the paper's `N_α(C)`; it need not be unique). -/
def IsMinNet {X : Type} (QC : Set (Multiset X → ℝ)) (α : ℝ) (N : Finset (Database X)) : Prop :=
  IsNet QC α N ∧ ∀ N' : Finset (Database X), IsNet QC α N' → N.card ≤ N'.card

end PrivateRelease.NetMechanism


