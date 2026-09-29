-- Prove2me | Definitions.Def_MasekPaterson_Shared_editDist
-- name    : MasekPaterson_Shared_editDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:01:30.992985+00:00
-- url     : https://prove2.me/theorems/fb50232f-ea9a-4630-8a3c-1bed4e2ffaac
-- title:
--   Edit operations, edit sequences and the edit distance $\delta(\gamma, A, B)$
-- statement:
--   Fix an alphabet $\Sigma$ and write $\lambda$ for the null string. For a string $A$ over $\Sigma$, $|A|$ is its length, $A_n$ its $n$-th character (counting from $1$), $A^{i,j} = A_i \cdots A_j$, and $A^n = A^{1,n}$ its prefix of length $n$, with $A^0 = \lambda$.
--
--   An **edit operation** $a \to b$ is a pair $(a, b) \ne (\lambda, \lambda)$ of strings of length at most one. It is a **replacement** if $a \ne \lambda$ and $b \ne \lambda$ (the case $a = b$ is allowed), a **deletion** if $b = \lambda$, and an **insertion** if $a = \lambda$. A string $B$ results from $A$ by $a \to b$ if $A = \sigma a \tau$ and $B = \sigma b \tau$ for some strings $\sigma, \tau$.
--
--   An **edit sequence** is a finite sequence $S = s_1, \dots, s_m$ of edit operations. $S$ **takes $A$ to $B$** if there are strings $C_0, \dots, C_m$ with $C_0 = A$, $C_m = B$ and $C_{i-1} \to C_i$ via $s_i$ for $1 \le i \le m$ (for $m = 0$ this means $A = B$).
--
--   A **cost function** $\gamma$ assigns a real number to each edit operation (the theorems of the mission assume it is nonnegative). The cost of an edit sequence is $\gamma(S) = \sum_{1 \le i \le m} \gamma(s_i)$, and the **edit distance** is
--
--   $$\delta(\gamma, A, B) = \min\{\gamma(S) \mid S \text{ is an edit sequence taking } A \text{ to } B\}.$$
--
--   The costs of single operations are abbreviated $R_{a,b} = \gamma(a \to b)$, $D_a = \gamma(a \to \lambda)$ and $I_a = \gamma(\lambda \to a)$ for characters $a, b$. For fixed strings $A, B$ the **edit matrix** has entries $\delta_{i,j} = \delta(\gamma, A^i, B^j)$, $0 \le i \le |A|$, $0 \le j \le |B|$. Finally, $\gamma$ is **normalized** if $\gamma(a \to b) = \delta(\gamma, a, b)$ for every edit operation $a \to b$; the paper assumes this without loss of generality.
--
--   These are the objects of Section 1.1 of Masek and Paterson (p. 19); every other statement of the paper is stated in terms of them. Used by both missions of this paper: 01-four-russians (the Wagner–Fischer recurrences, Theorems 1–2 and Corollary 1, pp. 20–21; Lemmas 3–4, p. 23; Algorithms Y and Z, pp. 22–24) and 02-discreteness-necessary (the example of Section 3, Lemmas 5–7 and Theorem 5, pp. 28–30).
--
--   **Formalization Note** Strings are `List α`; an edit operation is a structure with two `Option α` fields (`none` is $\lambda$) and a proof that they are not both `none`. "S takes A to B" is the inductive relation `Takes`. The minimum is taken as `sInf` of the set of costs $\gamma(S)$ of edit sequences taking $A$ to $B$: this set is nonempty (delete every character of $A$, then insert every character of $B$) and, for $\gamma \ge 0$, bounded below by $0$, so the infimum is the paper's minimum value; that the minimum is attained is a theorem, not part of the definition. `dmat γ A B i j` is $\delta_{i,j}$, using `A.take i` for $A^i$. `IsNormalized γ` is the normalization property. The edit distance is **not** defined by the Wagner–Fischer recurrence; that recurrence is Theorem 2.
-- source:
--   Masek, Paterson, A Faster Algorithm Computing String Edit Distances, J. Comput. System Sci. 20, 1980, p. 19, Section 1.1 (Basic Definitions)

import Mathlib

namespace MasekPaterson.Shared

/-- An edit operation `a → b` (Masek–Paterson §1.1): a pair `(a, b)` of strings of length
at most one (encoded as `Option α`), other than the pair `(λ, λ)` of two null strings. -/
structure EditOp (α : Type*) where
  /-- the string `a` that is replaced (`none` is the null string `λ`) -/
  src : Option α
  /-- the string `b` it is replaced by (`none` is the null string `λ`) -/
  tgt : Option α
  /-- `(a, b) ≠ (λ, λ)` -/
  not_null : ¬ (src = none ∧ tgt = none)

variable {α : Type*}

/-- `A → B via a → b`: `A = σ a τ` and `B = σ b τ` for some strings `σ, τ`. -/
def Yields (o : EditOp α) (A B : List α) : Prop :=
  ∃ σ τ : List α, A = σ ++ o.src.toList ++ τ ∧ B = σ ++ o.tgt.toList ++ τ

/-- `S` takes `A` to `B`: there is an `S`-derivation `A = C₀ → C₁ → ⋯ → C_m = B`
with `C_{i-1} → C_i` via `s_i`, where `S = s₁, …, s_m`. -/
inductive Takes : List (EditOp α) → List α → List α → Prop
  | nil (A : List α) : Takes [] A A
  | cons {s : EditOp α} {S : List (EditOp α)} {A C B : List α} :
      Yields s A C → Takes S C B → Takes (s :: S) A B

/-- The cost `γ(S) = ∑_{1 ≤ i ≤ m} γ(s_i)` of an edit sequence. -/
def seqCost (γ : EditOp α → ℝ) (S : List (EditOp α)) : ℝ :=
  (S.map γ).sum

/-- The edit distance `δ(γ, A, B) = min {γ(S) | S is an edit sequence taking A to B}`,
defined as the infimum of that set of real numbers. -/
noncomputable def editDist (γ : EditOp α → ℝ) (A B : List α) : ℝ :=
  sInf {c : ℝ | ∃ S : List (EditOp α), Takes S A B ∧ c = seqCost γ S}

/-- The replacement operation `a → b` (with `a = b` allowed). -/
def replOp (a b : α) : EditOp α := ⟨some a, some b, by simp⟩

/-- The deletion operation `a → λ`. -/
def delOp (a : α) : EditOp α := ⟨some a, none, by simp⟩

/-- The insertion operation `λ → a`. -/
def insOp (a : α) : EditOp α := ⟨none, some a, by simp⟩

/-- `R_{a,b} = γ(a → b)`, the cost of replacing `a` with `b`. -/
def replCost (γ : EditOp α → ℝ) (a b : α) : ℝ := γ (replOp a b)

/-- `D_a = γ(a → λ)`, the cost of deleting `a`. -/
def delCost (γ : EditOp α → ℝ) (a : α) : ℝ := γ (delOp a)

/-- `I_a = γ(λ → a)`, the cost of inserting `a`. -/
def insCost (γ : EditOp α → ℝ) (a : α) : ℝ := γ (insOp a)

/-- The edit matrix entry `δ_{i,j} = δ(γ, A^i, B^j)`, where `A^i = A₁ ⋯ A_i` is the prefix
of length `i` (`A^0 = λ`). -/
noncomputable def dmat (γ : EditOp α → ℝ) (A B : List α) (i j : ℕ) : ℝ :=
  editDist γ (A.take i) (B.take j)

/-- The normalization of §1.1: `γ(a → b) = δ(γ, a, b)` for every edit operation `a → b`. -/
def IsNormalized (γ : EditOp α → ℝ) : Prop :=
  ∀ o : EditOp α, γ o = editDist γ o.src.toList o.tgt.toList

end MasekPaterson.Shared


