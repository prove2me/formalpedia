-- Prove2me | Definitions.Def_OmegaLogic_Provability
-- name    : OmegaLogic_Provability
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T16:32:28.78241+00:00
-- url     : https://prove2.me/theorems/cb6b7da1-f7ed-40b9-a91b-b9531275f9b1
-- title:
--   Ω-logic II: countable transitive models, forcing, universally Baire sets, Ω-provability
-- statement:
--   This file sets up the deductive side of Ω-logic.
--
--   **Countable transitive models.** `IsZFCModel M` says that the set $M$ is transitive and that $(M, \in)$ satisfies ZFC. Pairing, Union, Infinity ($\omega \in M$) and Choice (choice sets for families of nonempty pairwise disjoint sets) are stated as closure properties. So are Power Set ($\mathcal P(x) \cap M \in M$), Separation ($\{x \in a : M \models \varphi(x, \vec p)\} \in M$ for every formula $\varphi$ and parameters $\vec p \in M$) and Collection. Extensionality and Foundation hold automatically for transitive sets. `IsCTM M` adds that $M$ is countable.
--
--   **Forcing over a c.t.m.** `IsForcingPoset M P le` says that $(P, \le) \in M$ is a partial order, where `le` is a set of ordered pairs. `IsGenericFilter M P le G` says that $G \subseteq P$ is a filter meeting every dense subset of $P$ that lies in $M$. `nameVal G τ` is the interpretation $\tau^G = \{\sigma^G : \exists p \in G\ (\sigma, p) \in \tau\}$, and `genExt M G` is $M[G] = \{\tau^G : \tau \in M\}$.
--
--   **Reals and universally Baire sets.** Reals are elements of $\omega^\omega$. Inside models they are coded by their graphs $\{(n, x(n)) : n \in \omega\}$, and `realsIn S A` is the set of codes of reals of $A$ lying in $S$. `UniversallyBaire A` (primer, Proposition 2.2 ii) says that for every compact Hausdorff space $K$ and every continuous $f : K \to \omega^\omega$, $f^{-1}(A)$ has the property of Baire.
--
--   **Strong $A$-closure** (primer, Definition 2.16). `StronglyClosed M A` says that $M[G] \cap A \in M[G]$ for every partial order $P \in M$ and every $M$-generic $G \subseteq P$.
--
--   **Ω-provability.** `OmegaProvable T φ`, written $T \vdash_\Omega \varphi$, holds iff there is a universally Baire $A \subseteq \omega^\omega$ such that for every strongly $A$-closed countable transitive model $M$ of ZFC and every ordinal $\alpha \in M$,
--   $$M_\alpha \models T \ \Longrightarrow\ M_\alpha \models \varphi, \qquad M_\alpha = \{x \in M : \mathrm{rank}(x) < \alpha\}.$$
--   This is the primer's Definition 2.29 in the form it takes under a proper class of Woodin cardinals. There, conditions 1) ($L(A,\mathbb R) \models \mathrm{AD}^+$) and 2) (every set of reals in $L(A,\mathbb R)$ is universally Baire) hold for every universally Baire $A$ (Theorem 2.28), and by Section 2.5 (Theorem 2.37 and the following discussion) using strong $A$-closure instead of $A$-closure gives the same relation.
--
--   **Ω-consistency** (primer, Definition 3.1 iv). `OmegaConsistent T` means $T \nvdash_\Omega \bot$.
-- source:
--   Wikipedia, "Ω-logic" (revision oldid=1336097018), section "Analysis" (definition of Ω-provability); formal definitions from J. Bagaria, N. Castells, P. Larson, "An Ω-logic primer", in Set Theory (Trends in Mathematics), Birkhäuser 2006, pp. 1–28, doi:10.1007/3-7643-7692-9_1; online version https://paulblarson.github.io/omegalogicmaster5.pdf, Proposition 2.2 (p. 7), Definition 2.16 (p. 9), Definition 2.29 with Theorem 2.28 (p. 16), Section 2.5 (Theorem 2.37, pp. 20–21), Definition 3.1 iv (p. 22).

import Definitions.Def_OmegaLogic_Semantics

/-!
# Ω-logic, part 2: countable transitive models, forcing, universally Baire sets, `⊢_Ω`

* `OmegaLogic.IsZFCModel M`, `OmegaLogic.IsCTM M` : (countable) transitive models of ZFC.
* `OmegaLogic.IsForcingPoset`, `OmegaLogic.IsGenericFilter`, `OmegaLogic.nameVal`,
  `OmegaLogic.genExt` : forcing over a countable transitive model, `M[G]`.
* `OmegaLogic.UniversallyBaire A`.
* `OmegaLogic.StronglyClosed M A` : `M` is strongly `A`-closed.
* `OmegaLogic.OmegaProvable T φ` : `T ⊢_Ω φ`; `OmegaLogic.OmegaConsistent T`.

Source: Bagaria–Castells–Larson, *An Ω-logic primer*, Proposition 2.2, Definitions 2.16,
2.29, 3.1 and Section 2.5.
-/

namespace OmegaLogic

universe u

open ZFSet

/-- `M` is a transitive set which is a model of ZFC (with the true membership relation).
For a transitive set, Extensionality and Foundation hold automatically, and each remaining
axiom of ZFC is expressed by the corresponding closure property of `M` (Separation and
Collection for every formula of set theory, with parameters from `M`). -/
def IsZFCModel (M : ZFSet.{u}) : Prop :=
  M.IsTransitive ∧
  -- Pairing
  (∀ x ∈ M, ∀ y ∈ M, ({x, y} : ZFSet) ∈ M) ∧
  -- Union
  (∀ x ∈ M, ⋃₀ x ∈ M) ∧
  -- Power set (the power set computed in `M`)
  (∀ x ∈ M, ZFSet.sep (· ∈ M) (powerset x) ∈ M) ∧
  -- Infinity
  ZFSet.omega ∈ M ∧
  -- Separation schema
  (∀ (k : ℕ) (φ : setLang.Formula (Fin (k + 1))) (p : Fin k → {x | x ∈ M}), ∀ a ∈ M,
    ZFSet.sep (fun x => ∃ hx : x ∈ M, φ.Realize (Fin.cons (⟨x, hx⟩ : {x | x ∈ M}) p)) a ∈ M) ∧
  -- Collection schema
  (∀ (k : ℕ) (φ : setLang.Formula (Fin (k + 2))) (p : Fin k → {x | x ∈ M}), ∀ a ∈ M,
    (∀ (x : {x | x ∈ M}), x.1 ∈ a → ∃ y : {x | x ∈ M}, φ.Realize (Fin.cons x (Fin.cons y p))) →
    ∃ b ∈ M, ∀ (x : {x | x ∈ M}), x.1 ∈ a →
      ∃ y : {x | x ∈ M}, y.1 ∈ b ∧ φ.Realize (Fin.cons x (Fin.cons y p))) ∧
  -- Choice (every family of nonempty pairwise disjoint sets has a choice set)
  (∀ x ∈ M, (∀ y ∈ x, y ≠ ∅) → (∀ y ∈ x, ∀ z ∈ x, y ≠ z → ∀ w ∈ y, w ∉ z) →
    ∃ c ∈ M, ∀ y ∈ x, ∃! w, w ∈ c ∧ w ∈ y)

/-- `M` is a countable transitive model (c.t.m.) of ZFC. -/
def IsCTM (M : ZFSet.{u}) : Prop := IsZFCModel M ∧ {x | x ∈ M}.Countable

/-- `(P, le) ∈ M` is a partial order in `M`; `le` is a set of ordered pairs, and
`pair p q ∈ le` means `p ≤ q`. -/
def IsForcingPoset (M P le : ZFSet.{u}) : Prop :=
  P ∈ M ∧ le ∈ M ∧
  (∀ z ∈ le, ∃ p ∈ P, ∃ q ∈ P, z = pair p q) ∧
  (∀ p ∈ P, pair p p ∈ le) ∧
  (∀ p q r, pair p q ∈ le → pair q r ∈ le → pair p r ∈ le) ∧
  (∀ p q, pair p q ∈ le → pair q p ∈ le → p = q)

/-- `G ⊆ P` is an `M`-generic filter on the partial order `(P, le)`: a filter meeting every
dense subset of `P` that belongs to `M`. -/
def IsGenericFilter (M P le : ZFSet.{u}) (G : Set ZFSet.{u}) : Prop :=
  (∀ p ∈ G, p ∈ P) ∧ G.Nonempty ∧
  (∀ p ∈ G, ∀ q ∈ P, pair p q ∈ le → q ∈ G) ∧
  (∀ p ∈ G, ∀ q ∈ G, ∃ r ∈ G, pair r p ∈ le ∧ pair r q ∈ le) ∧
  (∀ D ∈ M, (∀ q ∈ D, q ∈ P) → (∀ p ∈ P, ∃ q ∈ D, pair q p ∈ le) → ∃ q ∈ D, q ∈ G)

lemma rank_lt_of_mem_sUnion_sUnion {σ τ : ZFSet.{u}} (h : σ ∈ ⋃₀ ⋃₀ τ) :
    σ.rank < τ.rank :=
  (rank_lt_of_mem h).trans_le ((rank_sUnion_le _).trans (rank_sUnion_le _))

/-- The interpretation of a name by a filter `G`:
`τ^G = { σ^G | ∃ p ∈ G, (σ, p) ∈ τ }` (defined by recursion on rank). -/
noncomputable def nameVal (G : Set ZFSet.{u}) (τ : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun σ : ZFSet.sep (fun σ => ∃ p ∈ G, pair σ p ∈ τ) (⋃₀ ⋃₀ τ) =>
    nameVal G σ.1)
termination_by τ.rank
decreasing_by exact rank_lt_of_mem_sUnion_sUnion (ZFSet.mem_sep.1 σ.2).1

/-- The generic extension `M[G] = { τ^G | τ ∈ M }`. -/
def genExt (M : ZFSet.{u}) (G : Set ZFSet.{u}) : Set ZFSet.{u} :=
  {x | ∃ τ ∈ M, nameVal G τ = x}

/-- The von Neumann natural number `n` as a set. -/
noncomputable def natCode (n : ℕ) : ZFSet.{u} := Ordinal.toZFSet (n : Ordinal.{u})

/-- A real `x ∈ ω^ω` coded as a set: its graph `{(n, x n) | n ∈ ω} ⊆ ω × ω`. -/
noncomputable def realCode (x : ℕ → ℕ) : ZFSet.{u} :=
  ZFSet.range (fun n : ULift.{u} ℕ => pair (natCode n.down) (natCode (x n.down)))

/-- The set `S ∩ A` of (codes of) reals of `A` lying in the class `S`. -/
noncomputable def realsIn (S : Set ZFSet.{u}) (A : Set (ℕ → ℕ)) : ZFSet.{u} :=
  ZFSet.range (fun x : {x : ULift.{u} (ℕ → ℕ) // x.down ∈ A ∧ realCode x.down ∈ S} =>
    realCode x.1.down)

/-- **Universally Baire sets** (primer, Proposition 2.2 ii): `A ⊆ ω^ω` is universally Baire
if for every compact Hausdorff space `K` and every continuous `f : K → ω^ω`, the preimage
`f⁻¹(A)` has the property of Baire in `K`. -/
def UniversallyBaire (A : Set (ℕ → ℕ)) : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] (f : K → ℕ → ℕ),
    Continuous f → BaireMeasurableSet (f ⁻¹' A)

/-- **Strong `A`-closure** (primer, Definition 2.16): for every partial order `P ∈ M` and every
`M`-generic filter `G ⊆ P`, `M[G] ∩ A ∈ M[G]`. -/
def StronglyClosed (M : ZFSet.{u}) (A : Set (ℕ → ℕ)) : Prop :=
  ∀ P le : ZFSet.{u}, IsForcingPoset M P le → ∀ G : Set ZFSet.{u}, IsGenericFilter M P le G →
    realsIn (genExt M G) A ∈ genExt M G

/-- `M_α = V_α ∩ M` (which is `(V_α)^M` for transitive `M`). -/
def rankLevel (M : ZFSet.{u}) (α : Ordinal.{u}) : Set ZFSet.{u} := {x | x ∈ M ∧ x.rank < α}

/-- **Ω-provability** `T ⊢_Ω φ`: there is a universally Baire set `A ⊆ ω^ω` such that for every
countable transitive strongly `A`-closed model `M` of ZFC and every ordinal `α ∈ M`,
if `M_α ⊨ T` then `M_α ⊨ φ`.

This is the form of the primer's Definition 2.29 under a proper class of Woodin cardinals:
by Theorem 2.28 conditions 1) and 2) of Definition 2.29 hold for every universally Baire set,
and by Section 2.5 (Theorem 2.37) replacing `A`-closure by strong `A`-closure does not change
the relation. -/
def OmegaProvable (T : Set Sent) (φ : Sent) : Prop :=
  ∃ A : Set (ℕ → ℕ), UniversallyBaire.{u} A ∧
    ∀ M : ZFSet.{u}, IsCTM M → StronglyClosed M A →
      ∀ α : Ordinal.{u}, α.toZFSet ∈ M →
        SatTheory (rankLevel M α) T → Sat (rankLevel M α) φ

/-- **Ω-consistency** (primer, Definition 3.1 iv): `T ⊬_Ω ⊥`. -/
def OmegaConsistent (T : Set Sent) : Prop := ¬ OmegaProvable.{u} T ⊥

end OmegaLogic


