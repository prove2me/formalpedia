-- Prove2me | Definitions.Def_CogCons_consequence_space
-- name    : CogCons_consequence_space
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-30T16:24:16.442822+00:00
-- url     : https://prove2.me/theorems/fd7aff44-a205-4d07-9986-e3c788d84796
-- title:
--   Cognitive-consequence space, CWO sets and cognitive closure
-- statement:
--   A **cognitive-consequence space** consists of a countable set $C$ of mental representations, a consequence operator $\mathrm{Cn} : \mathcal P(C) \to \mathcal P(C)$ and an implication connective $\Rightarrow : C \times C \to C$ such that, for all $A, B \subseteq C$ and $X, Y \in C$:
--
--   1. $A \subseteq \mathrm{Cn}(A)$;
--   2. $A \subseteq B$ implies $\mathrm{Cn}(A) \subseteq \mathrm{Cn}(B)$;
--   3. $\mathrm{Cn}(\mathrm{Cn}(A)) = \mathrm{Cn}(A)$;
--   4. if $X \in \mathrm{Cn}(A)$ then $X \in \mathrm{Cn}(B)$ for some finite $B \subseteq A$;
--   5. if $Y \in \mathrm{Cn}(A \cup \{X\})$ then $(X \Rightarrow Y) \in \mathrm{Cn}(A)$;
--   6. $\mathrm{Cn}(\varnothing) \neq \varnothing$.
--
--   Derived notions:
--
--   - $A$ is **deductive** if $\mathrm{Cn}(A) = A$.
--   - The **cognitive-consequence topology** is $\tau = \{A \subseteq C : \mathrm{Cn}(C \setminus A) = C \setminus A\}$; its members are **consequence-wise open** (CWO), and complements of CWO sets are **consequence-wise closed** (CWC).
--   - The **cognitive closure** of $A$ is $\mathrm{Cl}^{\square}(A) = \bigcap\{D \subseteq C : D \text{ deductive},\ A \subseteq D\}$.
--   - For $C_d \subseteq C$ and $f \in C$, $f_d = \{A \subseteq C_d : f \in A \text{ and } A \text{ contains a deductive subset}\}$.
--
--   These are the objects the paper's Sections 3–4 are stated in.
--
--   **Formalization Note** The paper's syntax $\sigma$ and interpretation $I$ enter only through the connective $\Rightarrow$ (field `imp`). The paper's claim $\mathrm{Cn}(C) \neq C$ is omitted because it contradicts axiom 1.
-- source:
--   S. Acharjee and U. Gogoi, *The limit of human intelligence*, arXiv:2310.10792v2 [math.GM] (2023), https://arxiv.org/abs/2310.10792, pp. 4–5 (axioms (i)–(vi), standing assumption $\mathrm{Cn}(\varnothing)\neq\varnothing$), Definitions 3.1–3.4 (pp. 5, 7); family $f_d$ of Theorem 4.3 (p. 18)

import Mathlib

namespace CogCons

/-- A cognitive-consequence space `(C, σ, I, Cn)` (Acharjee–Gogoi, Section 3).
The syntax `σ` and interpretation `I` are not modelled beyond the implication
connective `imp` (written `X ⇒ Y` in the paper) needed to state Tarski's deduction
axiom. Fields (i)–(vi) are Tarski's axioms as listed in the paper; the last field is
the paper's standing assumption `Cn(∅) ≠ ∅`. -/
structure CognitiveConsequenceSpace (C : Type*) where
  /-- The consequence operator `Cn : 𝒫(C) → 𝒫(C)`. -/
  Cn : Set C → Set C
  /-- The implication connective `X ⇒ Y`. -/
  imp : C → C → C
  /-- (i) denumerability of the language. -/
  countable : Countable C
  /-- (ii) inclusion: `A ⊆ Cn(A)`. -/
  subset_Cn : ∀ A : Set C, A ⊆ Cn A
  /-- (iii) monotonicity. -/
  Cn_mono : ∀ A B : Set C, A ⊆ B → Cn A ⊆ Cn B
  /-- (iv) idempotence. -/
  Cn_idem : ∀ A : Set C, Cn (Cn A) = Cn A
  /-- (v) finiteness (compactness). -/
  Cn_finitary : ∀ (A : Set C) (x : C), x ∈ Cn A →
    ∃ B : Set C, B.Finite ∧ B ⊆ A ∧ x ∈ Cn B
  /-- (vi) deduction theorem. -/
  deduction : ∀ (A : Set C) (x y : C), y ∈ Cn (insert x A) → imp x y ∈ Cn A
  /-- Standing assumption: the consequence of the empty set is non-empty. -/
  Cn_empty_nonempty : (Cn ∅).Nonempty

namespace CognitiveConsequenceSpace

variable {C : Type*} (S : CognitiveConsequenceSpace C)

/-- Definition 3.1: `A` is deductive if `Cn(A) = A`. -/
def IsDeductive (A : Set C) : Prop := S.Cn A = A

/-- Definition 3.2: the cognitive-consequence topology
`τ = {A ⊆ C : Cn(C − A) = C − A}`. -/
def cct : Set (Set C) := {A | S.Cn Aᶜ = Aᶜ}

/-- Definition 3.3: `A` is consequence-wise open (CWO) if `A ∈ τ`. -/
def IsCWO (A : Set C) : Prop := A ∈ S.cct

/-- Definition 3.3: `B` is consequence-wise closed (CWC) if it is the complement of a
CWO set. -/
def IsCWC (B : Set C) : Prop := S.IsCWO Bᶜ

/-- Definition 3.4: the cognitive closure `Cl□(A)`, the intersection of all deductive
systems containing `A`. -/
def cognitiveClosure (A : Set C) : Set C :=
  ⋂₀ {D : Set C | S.IsDeductive D ∧ A ⊆ D}

/-- The family `f_d` of Theorem 4.3: subsets `A ⊆ C_d` with `f ∈ A` that contain at
least one deductive subset `B ⊆ A`. -/
def deductiveFilter (Cd : Set C) (f : C) : Set (Set C) :=
  {A : Set C | A ⊆ Cd ∧ f ∈ A ∧ ∃ B : Set C, B ⊆ A ∧ S.IsDeductive B}

end CognitiveConsequenceSpace

end CogCons


