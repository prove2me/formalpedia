-- Prove2me | Definitions.Def_ExactLearningSeparation678_Randomized_Supplement_Models
-- name    : ExactLearningSeparation678_Randomized_Supplement_Models
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:27:03.33026+00:00
-- url     : https://prove2.me/theorems/89abce9a-3026-4efd-8866-efbf8b68ccca
-- title:
--   Deterministic complexity $D(C)$, Booleanizations $Q_{\mathrm{bool}}$, $R_{\mathrm{bool}}$, and the classes $C_q$ and $C_m$
-- statement:
--   Let $C$ be a class of Boolean functions on a finite coordinate set $[N]$ (a concept class $C\subseteq\{0,1\}^N$).
--
--   1. **Deterministic exact learning.** $D(C)$ is the least $T$ such that some adaptive deterministic membership-query decision tree makes at most $T$ queries on every input and outputs the entire target $c$ for every $c\in C$, with certainty.
--   2. **Booleanizations.** For $P\subseteq C$ let $b_P(c)=1[c\in P]$. $Q(b_P)$ is the least $T$ for which a $T$-query quantum algorithm with the standard membership oracle $|x,b\rangle\mapsto|x,b\oplus c(x)\rangle$, any finite workspace and input-independent unitaries, outputs $b_P(c)$ with probability at least $2/3$ for every $c\in C$. $R(b_P)$ is the least $T$ for which a randomized decision tree making at most $T$ queries on every input outputs $b_P(c)$ with probability at least $2/3$ for every $c\in C$. Then
--   $$Q_{\mathrm{bool}}(C)=\max_{P\subseteq C}Q(b_P),\qquad R_{\mathrm{bool}}(C)=\max_{P\subseteq C}R(b_P).$$
--   3. **The bilinear class (Definition 2.1).** For an integer $q\ge2$ let $X_q=[q^2]\times\mathbb F_2^q\times\mathbb F_2^q$. For $b\in[q^2]$ and a nonzero $A\in\mathbb F_2^{q\times q}$ put $c_{b,A}(b',x,y)=1[b'=b]\,x^{\mathsf T}Ay$, let $c_0\equiv0$, and $C_q=\{c_{b,A}: b\in[q^2],\ A\neq0\}\cup\{c_0\}$.
--   4. **Dictators.** For $m\ge1$, on the domain $\{0,1\}^m$ let $c_j(z)=z_j$ and $C_m=\{c_1,\dots,c_m\}$.
--
--   These are the objects of the deterministic separation (Section 2) and of the Booleanization results (Section 4.1). The quantum and randomized exact-learning complexities $Q(C)$ and $R(C)$ are the mission's published ones.
--
--   **Formalization Note** Coordinates form an arbitrary finite type; $[q^2]$ is `Fin (q^2)` and $\mathbb F_2^q$ is `Fin q → ZMod 2`. For nonempty coordinate domains the query-budget sets are nonempty (querying every coordinate succeeds), so their natural infima are minima. For an empty coordinate domain the quantum register has no unit vector, so `boolQ` has an empty budget set and returns `0`; every class then has at most one concept and its Boolean decision complexity is indeed zero. The deterministic and randomized budget sets still contain `0` there. The maxima are finite suprema over all subsets of $C$, the empty and full subsets included.
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), exact-learning model, p.2; Definition 2.1, p.13; Booleanization, p.28; proof of Theorem 4.2, p.30; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Learning

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized.Supplement

open QAlgorithms Matrix

/-- p.2: the deterministic exact-learning complexity `D(C)`, the least worst-case depth of an
adaptive deterministic membership-query decision tree that outputs the whole target `c` with
certainty for every `c ∈ C`. The set is nonempty (query every coordinate), so `sInf` is the
minimum. -/
noncomputable def detExactComplexity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Finset (ι → Bool)) : ℕ :=
  sInf {T : ℕ | ∃ t : DecisionTree ι Bool (ι → Bool), t.MakesAtMost T ∧
    ∀ c ∈ C, t.eval c = c}

/-- p.28: the Booleanization `b_P(c) = 1[c ∈ P]`, a Boolean function of the concept. -/
noncomputable def boolz {ι : Type*} (P : Finset (ι → Bool)) (c : ι → Bool) : Bool :=
  decide (c ∈ P)

/-- p.28–29: `Q(b_P)`, the bounded-error quantum query complexity of the partial Boolean function
`b_P` on the promise `C`: the least `T` such that a `T`-query algorithm (published `QueryAlg`,
XOR membership oracle, any finite workspace, Boolean output) outputs `b_P(c)` with probability at
least `2/3` for every `c ∈ C`. -/
noncomputable def boolQ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C P : Finset (ι → Bool)) : ℕ :=
  sInf {T : ℕ | ∃ (w : ℕ) (A : QueryAlg ι Bool (Fin w) T) (out : (ι × Bool) × Fin w → Bool),
    A.ComputesWithError out C (boolz P) (1 / 3)}

/-- p.28: `R(b_P)`, the least `T` such that a randomized decision tree making at most `T`
queries on every input outputs `b_P(c)` with probability at least `2/3` for every `c ∈ C`. -/
noncomputable def boolR {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C P : Finset (ι → Bool)) : ℕ :=
  sInf {T : ℕ | ∃ R : RandDecisionTree ι Bool Bool, RandMakesAtMost R T ∧
    ∀ c ∈ C, successProb R c (boolz P c) ≥ 2 / 3}

/-- p.28: `Q_bool(C) = max_{P ⊆ C} Q(b_P)`, over all subsets `P` of `C`. -/
noncomputable def Qbool {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Finset (ι → Bool)) : ℕ :=
  C.powerset.sup fun P => boolQ C P

/-- p.28: `R_bool(C) = max_{P ⊆ C} R(b_P)`, over all subsets `P` of `C`. -/
noncomputable def Rbool {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Finset (ι → Bool)) : ℕ :=
  C.powerset.sup fun P => boolR C P

/-- Definition 2.1, p.13: the domain `X_q = [q²] × F₂^q × F₂^q`. -/
abbrev BilinDomain (q : ℕ) := Fin (q ^ 2) × (Fin q → ZMod 2) × (Fin q → ZMod 2)

/-- Definition 2.1, p.13: `c_{b,A}(b', x, y) = 1[b' = b] · xᵀ A y` over `F₂`. -/
noncomputable def bilinConcept (q : ℕ) (b : Fin (q ^ 2)) (A : Matrix (Fin q) (Fin q) (ZMod 2)) :
    BilinDomain q → Bool :=
  fun p => decide (p.1 = b ∧ p.2.1 ⬝ᵥ (A *ᵥ p.2.2) = 1)

/-- Definition 2.1, p.13: `C_q = {c_{b,A} : b ∈ [q²], A ∈ F₂^{q×q} ∖ {0}} ∪ {c₀}`, with `c₀` the
identically zero concept. -/
noncomputable def bilinClass (q : ℕ) : Finset (BilinDomain q → Bool) :=
  insert (fun _ => false)
    (((Finset.univ : Finset (Fin (q ^ 2) × Matrix (Fin q) (Fin q) (ZMod 2))).filter
      fun p => p.2 ≠ 0).image fun p => bilinConcept q p.1 p.2)

/-- Proof of Theorem 4.2, p.30: the dictator class `C_m = {c_1, …, c_m}` on the domain
`{0,1}^m`, `c_j(z) = z_j`. -/
noncomputable def dictatorClass (m : ℕ) : Finset ((Fin m → Bool) → Bool) :=
  Finset.univ.image fun j : Fin m => fun z => z j

/-! ### Sanity checks -/

example {ι : Type*} [Fintype ι] [DecidableEq ι] : detExactComplexity (∅ : Finset (ι → Bool)) = 0 :=
  Nat.sInf_eq_zero.2 (Or.inl ⟨DecisionTree.leaf (fun _ => false), fun _ => le_rfl, by simp⟩)

example (q : ℕ) : (fun _ => false) ∈ bilinClass q := Finset.mem_insert_self _ _

end ExactLearningSeparation678.Randomized.Supplement


