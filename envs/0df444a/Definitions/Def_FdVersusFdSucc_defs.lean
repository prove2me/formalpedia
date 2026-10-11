-- Prove2me | Definitions.Def_FdVersusFdSucc_defs
-- name    : FdVersusFdSucc_defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T10:10:26.742797+00:00
-- url     : https://prove2.me/theorems/b3a2dcbe-1149-47c5-8a55-ad9dd7448690
-- title:
--   Bounded-depth Frege systems $F_d$: formulas, proofs, size, separation
-- statement:
--   Definitions for bounded-depth Frege systems $F_d$.
--
--   1. **Formulas** are in negation normal form over variables $p_0,p_1,\dots$: literals $p_i$, $\neg p_i$, and conjunctions $\bigwedge(A_1,\dots,A_m)$ and disjunctions $\bigvee(A_1,\dots,A_m)$ of any finite number $m\ge 0$ of formulas ($\bigwedge()$ is *true*, $\bigvee()$ is *false*). $\overline{A}$ denotes the De Morgan negation of $A$.
--   2. **Depth**: literals have depth $0$; $\operatorname{depth}\bigwedge(A_j)=\operatorname{depth}\bigvee(A_j)=1+\max_j\operatorname{depth}A_j$. **Size** $|A|$: number of literal and connective symbols. A **tautology** is true under every assignment.
--   3. **The system $F_d$.** Lines are sequents $\Gamma$ (finite lists of formulas, read disjunctively). Rules: axiom ($\Gamma$ contains $p_i$ and $\neg p_i$); $\wedge$-introduction (from $A,\Gamma$ for each $A\in\{A_1,\dots,A_m\}$ infer $\bigwedge(A_1,\dots,A_m),\Gamma$); $\vee$-introduction (from $A_j,\Gamma$ infer $\bigvee(A_1,\dots,A_m),\Gamma$); weakening (from $\Gamma$ infer any $\Delta\supseteq\Gamma$); cut (from $A,\Gamma$ and $\overline A,\Gamma$ infer $\Gamma$). An $F_d$-proof of $A$ is a sequence of sequents, each obtained from earlier ones by a rule, all of whose formulas have depth $\le d$, containing the one-formula sequent $A$. Its size is the total size of all formulas in all lines.
--   4. **Separation.** A family $(\tau_m)_{m\in\mathbb N}$ *requires exponential $F_d$-size* if there is $\varepsilon>0$ such that for all large $m$ every $F_d$-proof of $\tau_m$ has size $\ge 2^{|\tau_m|^{\varepsilon}}$. $\mathrm{PolySeparates}(k,d,\tau)$: all $\tau_m$ are tautologies of depth $\le k$ with $|\tau_m|\ge m$, there is $C$ with $F_{d+1}$-proofs of $\tau_m$ of size $\le C|\tau_m|^C$, and $\tau$ requires exponential $F_d$-size. $\mathrm{QuasiPolySeparates}(k,d,\tau)$: the same with $F_{d+1}$-proof size $\le 2^{C(\log_2|\tau_m|)^C}$.
--   5. **Pigeonhole principle** $\mathrm{PHP}^{n+1}_n$, with $p_{i,j}$ the variable of index $\langle i,j\rangle$ (Cantor-style pairing `Nat.pair`):
--   $$\bigvee_{i\le n}\bigwedge_{j<n}\neg p_{i,j}\ \vee\ \bigvee_{j<n}\ \bigvee_{i<i'\le n}(p_{i,j}\wedge p_{i',j}).$$
--
--   These are the objects in which all statements of the mission are phrased.
--
--   **Formalization Note** $F_d$ is presented as the dag-like one-sided (Tait-style) sequent calculus with cut restricted to depth-$\le d$ formulas, a standard formulation of bounded-depth systems (cf. the sequent calculi LK_d in Krajíček's book); Frege systems in the narrow sense (formula lines, Hilbert-style rules) are polynomially related to it, but the exact depth correspondence depends on conventions. Sequents are lists and weakening is list inclusion, so exchange and contraction are instances of weakening.
-- source:
--   Definitions following J. Krajíček, Bounded arithmetic, propositional logic, and complexity theory, CUP 1995; Open Problem Garden, 'F_d versus F_{d+1}' (J. Krajíček), http://www.openproblemgarden.org/op/f_d_versus_f_d_1

import Mathlib

/-!
# Bounded-depth Frege systems `F_d`

Definitions for the Prove2Me mission draft "`F_d` versus `F_{d+1}`"
(Open Problem Garden, problem posed by J. Krajíček).

* `Formula` — propositional formulas in negation normal form over the variables `ℕ`,
  built from literals with unbounded fan-in conjunctions and disjunctions
  (the De Morgan language).
* `Formula.depth`, `Formula.size` — depth (literals have depth `0`, a gate adds `1`)
  and size (number of symbols).
* `Formula.IsTautology` — truth under every assignment.
* `Step`, `IsDepthProof`, `IsDepthProofOf`, `proofSize` — the depth-`d` Frege system `F_d`,
  presented as the dag-like one-sided (Tait-style) sequent calculus with cut, in which
  every formula occurring in the proof has depth at most `d`.
* `RequiresExpSize`, `PolySeparates`, `QuasiPolySeparates` — the separation properties
  asked for by the problem; `php` — the pigeonhole tautologies.
-/

namespace FdVersusFdSucc

/-- Propositional formulas in negation normal form over variables indexed by `ℕ`:
positive and negative literals, and unbounded fan-in conjunctions and disjunctions.
`and []` is the constant *true* and `or []` is the constant *false*. -/
inductive Formula : Type
  | pos : ℕ → Formula
  | neg : ℕ → Formula
  | and : List Formula → Formula
  | or : List Formula → Formula

namespace Formula

/-- Truth value of a formula under the assignment `v`. -/
def eval (v : ℕ → Bool) : Formula → Bool
  | pos i => v i
  | neg i => !v i
  | and As => As.attach.all fun ⟨A, _⟩ => eval v A
  | or As => As.attach.any fun ⟨A, _⟩ => eval v A

/-- The (De Morgan) negation of a formula, again in negation normal form. -/
def dual : Formula → Formula
  | pos i => neg i
  | neg i => pos i
  | and As => or (As.attach.map fun ⟨A, _⟩ => dual A)
  | or As => and (As.attach.map fun ⟨A, _⟩ => dual A)

/-- Depth: literals have depth `0`; a conjunction or disjunction has depth one more than the
maximal depth of its arguments (so a clause has depth `1` and a CNF has depth `2`). -/
def depth : Formula → ℕ
  | pos _ => 0
  | neg _ => 0
  | and As => (As.attach.map fun ⟨A, _⟩ => depth A).foldr max 0 + 1
  | or As => (As.attach.map fun ⟨A, _⟩ => depth A).foldr max 0 + 1

/-- Size: the number of symbols (literals and connectives) in the formula. -/
def size : Formula → ℕ
  | pos _ => 1
  | neg _ => 1
  | and As => (As.attach.map fun ⟨A, _⟩ => size A).sum + 1
  | or As => (As.attach.map fun ⟨A, _⟩ => size A).sum + 1

/-- A tautology is a formula true under every assignment. -/
def IsTautology (A : Formula) : Prop := ∀ v : ℕ → Bool, A.eval v = true

end Formula

open Formula

/-- A sequent is a finite list of formulas, read disjunctively. -/
abbrev Sequent : Type := List Formula

/-- `Step prev Γ`: the sequent `Γ` follows by one inference rule from sequents occurring in
`prev` (the earlier lines of the proof). The rules are those of the one-sided sequent
calculus:
* axiom: `Γ` contains a complementary pair of literals `pᵢ, ¬pᵢ`;
* `∧`-introduction: from `A, Γ` for every `A ∈ As` infer `⋀As, Γ`
  (with `As = []` this is the axiom for the constant *true*);
* `∨`-introduction: from `A, Γ` for some `A ∈ As` infer `⋁As, Γ`;
* weakening (which also covers exchange and contraction): from `Γ` infer any `Δ` that
  contains every member of `Γ`;
* cut: from `A, Γ` and `¬A, Γ` infer `Γ`. -/
inductive Step (prev : List Sequent) : Sequent → Prop
  | ax (Γ : Sequent) (i : ℕ) : pos i ∈ Γ → neg i ∈ Γ → Step prev Γ
  | andI (Γ : Sequent) (As : List Formula) :
      (∀ A ∈ As, (A :: Γ) ∈ prev) → Step prev (and As :: Γ)
  | orI (Γ : Sequent) (As : List Formula) (A : Formula) :
      A ∈ As → (A :: Γ) ∈ prev → Step prev (or As :: Γ)
  | weaken (Γ Δ : Sequent) : Γ ∈ prev → Γ ⊆ Δ → Step prev Δ
  | cut (Γ : Sequent) (A : Formula) :
      (A :: Γ) ∈ prev → (A.dual :: Γ) ∈ prev → Step prev Γ

/-- `IsDepthProof d π`: the list of sequents `π` is a proof in the depth-`d` Frege system
`F_d`, i.e. every line follows from earlier lines by one rule of `Step` (proofs are
dag-like: a line may be used any number of times), and every formula occurring in `π` has
depth at most `d`. -/
def IsDepthProof (d : ℕ) (π : List Sequent) : Prop :=
  (∀ (i : ℕ) (h : i < π.length), Step (π.take i) π[i]) ∧
  ∀ Γ ∈ π, ∀ A ∈ Γ, A.depth ≤ d

/-- `IsDepthProofOf d π A`: `π` is an `F_d`-proof of the formula `A`, i.e. a depth-`d` proof
containing the one-formula sequent `A` as one of its lines. -/
def IsDepthProofOf (d : ℕ) (π : List Sequent) (A : Formula) : Prop :=
  IsDepthProof d π ∧ [A] ∈ π

/-- The size of a proof: the total number of symbols in all formulas of all its lines. -/
def proofSize (π : List Sequent) : ℕ :=
  (π.map fun Γ => (Γ.map Formula.size).sum).sum

/-- `RequiresExpSize d τ`: the formulas `τ m` require exponential-size proofs in `F_d`:
there is `ε > 0` such that for all sufficiently large `m`, every `F_d`-proof of `τ m` has
size at least `2^(size(τ m)^ε)`. -/
def RequiresExpSize (d : ℕ) (τ : ℕ → Formula) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ m in Filter.atTop, ∀ π, IsDepthProofOf d π (τ m) →
    (2 : ℝ) ^ (((τ m).size : ℝ) ^ ε) ≤ (proofSize π : ℝ)

/-- `PolySeparates k d τ`: the sequence `τ 0, τ 1, …` is a family of tautologies of depth at
most `k` and of unbounded size (`m ≤ size(τ m)`), which have polynomial-size `F_{d+1}`-proofs
(there is `C` such that every `τ m` has an `F_{d+1}`-proof of size at most
`C · size(τ m)^C`) but require exponential-size `F_d`-proofs (`RequiresExpSize d τ`). -/
def PolySeparates (k d : ℕ) (τ : ℕ → Formula) : Prop :=
  (∀ m, (τ m).IsTautology) ∧
  (∀ m, (τ m).depth ≤ k) ∧
  (∀ m, m ≤ (τ m).size) ∧
  (∃ C : ℕ, ∀ m, ∃ π, IsDepthProofOf (d + 1) π (τ m) ∧ proofSize π ≤ C * (τ m).size ^ C) ∧
  RequiresExpSize d τ

/-- `QuasiPolySeparates k d τ`: as `PolySeparates k d τ`, but the `F_{d+1}`-proofs are only
required to have quasi-polynomial size: there is `C` such that every `τ m` has an
`F_{d+1}`-proof of size at most `2^(C · (log₂ size(τ m))^C)`. -/
def QuasiPolySeparates (k d : ℕ) (τ : ℕ → Formula) : Prop :=
  (∀ m, (τ m).IsTautology) ∧
  (∀ m, (τ m).depth ≤ k) ∧
  (∀ m, m ≤ (τ m).size) ∧
  (∃ C : ℕ, ∀ m, ∃ π, IsDepthProofOf (d + 1) π (τ m) ∧
      (proofSize π : ℝ) ≤ (2 : ℝ) ^ ((C : ℝ) * Real.logb 2 ((τ m).size : ℝ) ^ C)) ∧
  RequiresExpSize d τ

/-- The propositional variable `p_{i,j}` ("pigeon `i` sits in hole `j`"), encoded as the
variable with index `Nat.pair i j`. -/
def phpVar (i j : ℕ) : ℕ := Nat.pair i j

/-- The pigeonhole principle `PHP^{n+1}_n` as a depth-2 formula in negation normal form:
either some pigeon `i ≤ n` sits in no hole `j < n`, or two distinct pigeons `i < i' ≤ n`
share a hole `j < n`:
`⋁_{i ≤ n} ⋀_{j < n} ¬p_{i,j}  ∨  ⋁_{j < n} ⋁_{i < i' ≤ n} (p_{i,j} ∧ p_{i',j})`. -/
def php (n : ℕ) : Formula :=
  or ((List.range (n + 1)).map (fun i => and ((List.range n).map fun j => neg (phpVar i j))) ++
    (List.range n).flatMap fun j =>
      (List.range (n + 1)).flatMap fun i =>
        ((List.range (n + 1)).filter fun i' => i < i').map fun i' =>
          and [pos (phpVar i j), pos (phpVar i' j)])

end FdVersusFdSucc


