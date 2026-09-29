-- Prove2me | Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem
-- name    : SetCoverThreshold_MaxCover_ProofSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:01:17.157846+00:00
-- url     : https://prove2.me/theorems/9fc3fc15-64ed-4ad9-a4c6-40882bc34aae
-- title:
--   The ℓ-fold two-prover system, Raz's bound as a hypothesis, and the k-prover proof system (§2.2–2.3)
-- statement:
--   This file defines the proof systems of Feige (J. ACM 45(4), 1998, §§2.2–2.3, pp. 641–643) for a 3CNF-5 formula $\varphi$ with $M$ clauses.
--
--   1. **Random strings.** For $\ell$ repetitions the verifier's random string $r$ chooses, on each coordinate $j\le \ell$, a clause $C_j$ and a position in it; the variable at that position is the *distinguished variable* $x_j$. There are $(3M)^\ell$ random strings, and all probabilities are uniform counts over them.
--   2. **The $\ell$-fold two-prover system (§2.2).** Prover 1 receives the $\ell$ clause indices and answers three bits per clause; prover 2 receives the $\ell$ distinguished variables and answers one bit per variable. The verifier accepts if on every coordinate "the assignment sent by the first prover satisfies the clause, and the assignment sent by the second prover is identical to the assignment for the same variable sent by the first prover" (p. 642).
--   3. **Theorem 2.2.2 (Raz, cited, p. 642), through its consequence.** The paper cites: "If a one-round two-prover proof system is repeated $\ell$ times independently in parallel, then the error is $2^{-c\ell}$, where $c > 0$ is a constant that depends only on the error of the original proof system (assuming this error was less than one) and on the length of the answers of the provers in the original proof system." It applies it as: "it follows from Theorem 2.2.2 that the error of our modified two-prover proof system is at most $2^{-c\ell}$, for some universal constant $c$." The proposition `RazRepetition` is this consequence: for every $\varepsilon>0$ there is $c>0$ such that, on every 3CNF-5 formula in which at most a $(1-\varepsilon)$-fraction of the clauses are simultaneously satisfiable, every pair of strategies makes the $\ell$-fold verifier accept with probability at most $2^{-c\ell}$, for every $\ell$.
--   4. **Code.** The $k$-prover system uses "a binary code that contains $k$ code words, each of length $\ell$ and weight $\ell/2$, and Hamming distance at least $\ell/3$ between any two code words."
--   5. **Questions.** "Prover $P_i$ receives $C_j$ for those coordinates $j$ in its code word that have the bit 1, and $x_j$ for those coordinates in its code word that have the bit 0."
--   6. **Canonical answers.** On a clause coordinate an answer is an assignment to the clause's three variables that satisfies the clause; on a variable coordinate it is one bit. The paper assumes this "without loss of generality" (p. 643). A strategy of a prover assigns a canonical answer to every question.
--   7. **Acceptance.** "The answer of a prover induces an assignment to the distinguished variables"; two provers are *consistent* if their induced assignments are identical. The verifier *weakly accepts* if at least one pair of distinct provers is consistent, and *strongly accepts* if every pair is consistent. The weak acceptance probability is
--   $$\Pr_r[\text{weak accept}] = \frac{\#\{r : \exists\, i\neq i',\ \text{provers } i, i' \text{ consistent on } r\}}{(3M)^\ell}.$$
--
--   These objects are the input of the reduction to max $k$-cover and the setting of Lemma 2.3.1.
--
--   **Formalization Note** Clauses and positions are 0-based. Prover 1 and the $k$ provers receive clause *indices*; variables are their indices in $\mathbb N$. Probabilities are uniform counts divided by $(3M)^\ell$ (a quotient by zero is $0$, which only occurs when $\varphi$ has no clauses). "Weight $\ell/2$" is written $2\cdot\mathrm{weight}=\ell$ and "distance at least $\ell/3$" as $\ell\le 3\cdot\mathrm{dist}$. `RazRepetition` is weaker than Raz's general theorem, so taking it as a hypothesis gives a stronger conditional result.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), pp. 641–643, Sections 2.2–2.3 (Theorem 2.2.2 and its consequence on p. 642; the k-prover system and acceptance predicates on pp. 642–643)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula

namespace SetCoverThreshold.MaxCover

open CookPvsNP

/-! ### The two-prover clause–variable game, repeated `ℓ` times (§2.2, pp. 641–642) -/

/-- A random string of the verifier for `ℓ` repetitions: on each coordinate a clause and the
position of the distinguished variable in it. There are `(3M)^ℓ` of them. -/
abbrev RandString (φ : Formula5) (ℓ : ℕ) : Type := Fin ℓ → Fin φ.M × Fin 3

/-- The verifier of the `ℓ`-fold two-prover system accepts on the random string `r`: prover 1
receives the `ℓ` clause indices and answers three bits per clause, prover 2 receives the `ℓ`
distinguished variables and answers one bit per variable; on every coordinate prover 1's bits
satisfy the clause and agree with prover 2 on the distinguished variable. -/
def twoProverAccepts (φ : Formula5) {ℓ : ℕ}
    (P₁ : (Fin ℓ → Fin φ.M) → Fin ℓ → Fin 3 → Bool) (P₂ : (Fin ℓ → ℕ) → Fin ℓ → Bool)
    (r : RandString φ ℓ) : Prop :=
  ∀ j, φ.LocalSat (r j).1 (P₁ (fun j' => (r j').1) j) ∧
    P₁ (fun j' => (r j').1) j (r j).2 = P₂ (fun j' => φ.var (r j').1 (r j').2) j

open Classical in
/-- Acceptance probability of the `ℓ`-fold two-prover system under the strategies `P₁`, `P₂`:
the fraction of the `(3M)^ℓ` random strings on which the verifier accepts. -/
noncomputable def twoProverAcceptFrac (φ : Formula5) {ℓ : ℕ}
    (P₁ : (Fin ℓ → Fin φ.M) → Fin ℓ → Fin 3 → Bool) (P₂ : (Fin ℓ → ℕ) → Fin ℓ → Bool) : ℝ :=
  ((Finset.univ.filter (twoProverAccepts φ P₁ P₂)).card : ℝ) / Fintype.card (RandString φ ℓ)

/-- **Theorem 2.2.2 (Raz, cited, p. 642), through its consequence stated on p. 642.** For every
`ε > 0` there is `c > 0` such that on every 3CNF-5 formula in which at most a `(1 − ε)`-fraction
of the clauses can be satisfied simultaneously, every pair of strategies makes the `ℓ`-fold
two-prover verifier accept with probability at most `2^{−cℓ}`. -/
def RazRepetition : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
    ∀ φ : Formula5, AtMostFracSat (1 - ε) φ.toCNF →
      ∀ (ℓ : ℕ) (P₁ : (Fin ℓ → Fin φ.M) → Fin ℓ → Fin 3 → Bool) (P₂ : (Fin ℓ → ℕ) → Fin ℓ → Bool),
        twoProverAcceptFrac φ P₁ P₂ ≤ (2 : ℝ) ^ (-(c * ℓ))

/-! ### The k-prover proof system (§2.3, pp. 642–643) -/

/-- The code of the `k`-prover system: `k` binary words of length `ℓ`, each of weight `ℓ/2`,
with pairwise Hamming distance at least `ℓ/3`. -/
def IsCode {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool) : Prop :=
  (∀ i, 2 * (Finset.univ.filter (fun j => code i j = true)).card = ℓ) ∧
    ∀ i i', i ≠ i' → ℓ ≤ 3 * hammingDist (code i) (code i')

/-- A question to one prover: on each coordinate either a clause index (`inl`) or a variable
index (`inr`). -/
abbrev Question (φ : Formula5) (ℓ : ℕ) : Type := Fin ℓ → Fin φ.M ⊕ ℕ

/-- The question of prover `i` on random string `r`: on coordinate `j` it receives the clause
`C_j` if bit `j` of its code word is `1`, and the distinguished variable `x_j` if it is `0`. -/
def question (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool) (r : RandString φ ℓ)
    (i : Fin k) : Question φ ℓ :=
  fun j => if code i j then Sum.inl (r j).1 else Sum.inr (φ.var (r j).1 (r j).2)

/-- A canonical answer on one coordinate: a satisfying assignment of the three variables of the
received clause, or one bit for a received variable. -/
def CoordAnswer (φ : Formula5) : Fin φ.M ⊕ ℕ → Type
  | Sum.inl c => {b : Fin 3 → Bool // φ.LocalSat c b}
  | Sum.inr _ => Bool

instance CoordAnswer.instFintype (φ : Formula5) : (x : Fin φ.M ⊕ ℕ) → Fintype (CoordAnswer φ x)
  | Sum.inl c => (inferInstance : Fintype {b : Fin 3 → Bool // φ.LocalSat c b})
  | Sum.inr _ => (inferInstance : Fintype Bool)

instance CoordAnswer.instDecidableEq (φ : Formula5) :
    (x : Fin φ.M ⊕ ℕ) → DecidableEq (CoordAnswer φ x)
  | Sum.inl c => (inferInstance : DecidableEq {b : Fin 3 → Bool // φ.LocalSat c b})
  | Sum.inr _ => (inferInstance : DecidableEq Bool)

/-- The bit an answer on one coordinate gives to the distinguished variable, which sits at
position `p` of the clause of that coordinate. -/
def CoordAnswer.bit {φ : Formula5} (p : Fin 3) : (x : Fin φ.M ⊕ ℕ) → CoordAnswer φ x → Bool
  | Sum.inl _, b => b.1 p
  | Sum.inr _, b => b

/-- A canonical answer to the question `q`. -/
abbrev Answer (φ : Formula5) {ℓ : ℕ} (q : Question φ ℓ) : Type := (j : Fin ℓ) → CoordAnswer φ (q j)

/-- The assignment an answer `a` induces on the distinguished variables, given the positions
`pos j` of the distinguished variables in the clauses. -/
def answerBits {φ : Formula5} {ℓ : ℕ} {q : Question φ ℓ} (pos : Fin ℓ → Fin 3) (a : Answer φ q) :
    Fin ℓ → Bool :=
  fun j => CoordAnswer.bit (pos j) (q j) (a j)

/-- A (deterministic) strategy of one prover: a canonical answer to every question. -/
abbrev Strategy (φ : Formula5) (ℓ : ℕ) : Type := (q : Question φ ℓ) → Answer φ q

/-- The assignment to the distinguished variables of `r` induced by prover `i`'s answer. -/
def induced (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool) (strat : Fin k → Strategy φ ℓ)
    (r : RandString φ ℓ) (i : Fin k) : Fin ℓ → Bool :=
  answerBits (fun j => (r j).2) (strat i (question φ code r i))

/-- Weak acceptance on `r`: at least one pair of distinct provers is consistent. -/
def WeakAccept (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    (strat : Fin k → Strategy φ ℓ) (r : RandString φ ℓ) : Prop :=
  ∃ i i', i ≠ i' ∧ induced φ code strat r i = induced φ code strat r i'

/-- Strong acceptance on `r`: every pair of provers is consistent. -/
def StrongAccept (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    (strat : Fin k → Strategy φ ℓ) (r : RandString φ ℓ) : Prop :=
  ∀ i i', induced φ code strat r i = induced φ code strat r i'

open Classical in
/-- The number of random strings on which the verifier weakly accepts. -/
noncomputable def weakAcceptCount (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    (strat : Fin k → Strategy φ ℓ) : ℕ :=
  (Finset.univ.filter (WeakAccept φ code strat)).card

/-- The weak acceptance probability: the fraction of the `(3M)^ℓ` random strings on which the
verifier weakly accepts. -/
noncomputable def weakAcceptFrac (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    (strat : Fin k → Strategy φ ℓ) : ℝ :=
  (weakAcceptCount φ code strat : ℝ) / Fintype.card (RandString φ ℓ)

end SetCoverThreshold.MaxCover


