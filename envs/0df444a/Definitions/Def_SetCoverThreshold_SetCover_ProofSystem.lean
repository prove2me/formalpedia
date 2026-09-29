-- Prove2me | Definitions.Def_SetCoverThreshold_SetCover_ProofSystem
-- name    : SetCoverThreshold_SetCover_ProofSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:53:12.495271+00:00
-- url     : https://prove2.me/theorems/54c50a4d-44bd-4270-a2f4-8b470157df25
-- title:
--   The two-prover system, Raz's repetition bound as a hypothesis, and the $k$-prover proof system
-- statement:
--   Let $\varphi$ be a 3CNF-5 formula with $n$ variables and $M$ clauses, and $\ell\ge 0$.
--
--   **Random strings.** The verifier selects $\ell$ clauses $C_1,\dots,C_\ell$ uniformly and independently, and in each clause one variable (the *distinguished* variable $x_j$) uniformly at random. A random string is $r=((c_1,p_1),\dots,(c_\ell,p_\ell))$; there are $R=(3M)^\ell=(5n)^\ell$ of them, and every probability below is the fraction of random strings with the property.
--
--   **Two-prover system (§2.2), repeated $\ell$ times.** The first prover receives the $\ell$ clauses and answers three bits per clause; the second receives the $\ell$ distinguished variables and answers one bit per variable. Strategies are arbitrary functions of the question. "The verifier accepts if the following two conditions hold for every one of the $\ell$ clauses: the assignment sent by the first prover satisfies the clause, and the assignment sent by the second prover is identical to the assignment for the same variable sent by the first prover" (p. 642).
--
--   **Raz's repetition bound (hypothesis).** Theorem 2.2.2 (p. 642, Raz 1995): "If a one-round two-prover proof system is repeated ℓ times independently in parallel, then the error is 2^{−cℓ}, where c > 0 is a constant that depends only on the error of the original proof system (assuming this error was less than one) and on the length of the answers of the provers in the original proof system." The paper uses it only through its consequence for the system above: for every $\varepsilon>0$ there is $c>0$ such that for every 3CNF-5 formula in which at most a $(1-\varepsilon)$-fraction of the clauses are simultaneously satisfiable, every $\ell$ and every strategy pair, the acceptance probability is at most $2^{-c\ell}$. That consequence is the proposition `RazRepetition`.
--
--   **Code.** A code is $k$ words $w_1,\dots,w_k\in\{0,1\}^\ell$, each of weight $\ell/2$, with Hamming distance at least $\ell/3$ between any two.
--
--   **$k$-prover system (§2.3).** "Prover $P_i$ receives $C_j$ for those coordinates $j$ in its code word that have the bit 1, and $x_j$ for those coordinates in its code word that have the bit 0." Answers are canonical: on a clause coordinate, three bits satisfying the clause; on a variable coordinate, one bit. The answer of $P_i$ *induces* an assignment to the distinguished variables (on a clause coordinate, the bit of the distinguished position). Two provers are *consistent* on $r$ if their induced assignments coincide. The acceptance predicates (p. 643):
--
--   - "Weak acceptance predicate. At least one pair of provers is consistent." (a pair of two different provers)
--   - "Strong acceptance predicate. Every pair of provers is consistent."
--
--   $\mathrm{weakAcceptFrac}$ is the fraction of random strings on which a given strategy of the $k$ provers is weakly accepted.
--
--   **Formalization Note** Probabilities are uniform counts over the finite set of random strings. Strategies are deterministic. The canonical-answer convention, which the paper adopts "without loss of generality" (p. 643), is built into the answer type: a canonical answer is three bits per coordinate, satisfying the clause on clause coordinates and carrying the bit in position $0$ (positions $1,2$ false) on variable coordinates. Weight $\ell/2$ and distance $\ell/3$ are written $2\cdot\mathrm{wt}=\ell$ and $\ell\le 3\cdot\mathrm{dist}$.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), pp. 641–642, Section 2.2 and Theorem 2.2.2; pp. 642–643, Section 2.3 (k-prover proof system, acceptance predicates)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Formula

namespace SetCoverThreshold.SetCover

namespace Formula5

variable (φ : Formula5)

/-! ### The clause–variable game and its `ℓ`-fold parallel repetition (Feige 1998, §2.2) -/

/-- A random string of the verifier for `ℓ` repetitions: for each coordinate `j`, a clause and
the position of the distinguished variable in it. There are `(3M)^ℓ` of them. -/
abbrev RandomString (ℓ : ℕ) : Type := Fin ℓ → Fin φ.M × Fin 3

/-- The `ℓ` clauses selected by a random string (the question to the first prover). -/
def clausesOf {ℓ : ℕ} (r : φ.RandomString ℓ) : Fin ℓ → Fin φ.M := fun j => (r j).1

/-- The `ℓ` distinguished variables selected by a random string (the question to the second
prover). -/
def distVars {ℓ : ℕ} (r : φ.RandomString ℓ) : Fin ℓ → Fin φ.n :=
  fun j => φ.var (r j).1 (r j).2

/-- A strategy of the first prover: to the `ℓ` clauses it answers three bits per clause (an
assignment to the three variables of that clause, in position order). -/
abbrev Prover1Strategy (ℓ : ℕ) : Type := (Fin ℓ → Fin φ.M) → Fin ℓ → Fin 3 → Bool

/-- A strategy of the second prover: to the `ℓ` variables it answers one bit per variable. -/
abbrev Prover2Strategy (ℓ : ℕ) : Type := (Fin ℓ → Fin φ.n) → Fin ℓ → Bool

/-- The verifier of the `ℓ`-fold repeated two-prover system accepts on random string `r`: on
every coordinate, the first prover's bits satisfy the clause (clause check) and agree with the
second prover's bit on the distinguished variable (consistency check). -/
def TwoProverAccepts {ℓ : ℕ} (P₁ : φ.Prover1Strategy ℓ) (P₂ : φ.Prover2Strategy ℓ)
    (r : φ.RandomString ℓ) : Prop :=
  ∀ j, φ.ClauseSatBy (r j).1 (P₁ (φ.clausesOf r) j) ∧
    P₁ (φ.clausesOf r) j (r j).2 = P₂ (φ.distVars r) j

instance {ℓ : ℕ} (P₁ : φ.Prover1Strategy ℓ) (P₂ : φ.Prover2Strategy ℓ) (r : φ.RandomString ℓ) :
    Decidable (φ.TwoProverAccepts P₁ P₂ r) := by
  unfold TwoProverAccepts; infer_instance

/-- Acceptance probability of the `ℓ`-fold two-prover system: the fraction of the `(3M)^ℓ`
random strings on which the verifier accepts. -/
noncomputable def twoProverAcceptFrac (ℓ : ℕ) (P₁ : φ.Prover1Strategy ℓ) (P₂ : φ.Prover2Strategy ℓ) : ℝ :=
  ((Finset.univ.filter (fun r : φ.RandomString ℓ => φ.TwoProverAccepts P₁ P₂ r)).card : ℝ) /
    Fintype.card (φ.RandomString ℓ)

end Formula5

/-- The consequence of Raz's parallel repetition theorem (Feige 1998, Theorem 2.2.2, p. 642) for
the two-prover system of §2.2, taken as a hypothesis: for every `ε > 0` there is `c > 0` such
that for every 3CNF-5 formula in which at most a `(1 - ε)`-fraction of the clauses are
simultaneously satisfiable, every `ℓ` and every pair of strategies, the `ℓ`-fold repeated system
accepts with probability at most `2^{-cℓ}`. -/
def RazRepetition : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
    ∀ φ : Formula5, AtMostFracSat (1 - ε) φ.toCNF →
      ∀ (ℓ : ℕ) (P₁ : φ.Prover1Strategy ℓ) (P₂ : φ.Prover2Strategy ℓ),
        φ.twoProverAcceptFrac ℓ P₁ P₂ ≤ (2 : ℝ) ^ (-(c * ℓ))

/-! ### The `k`-prover proof system (Feige 1998, §2.3) -/

/-- The binary code of §2.3: `k` code words of length `ℓ`, each of weight `ℓ/2`
(`2 · weight = ℓ`), with Hamming distance at least `ℓ/3` between any two code words
(`3 · distance ≥ ℓ`). -/
def IsCode (ℓ k : ℕ) (code : Fin k → Fin ℓ → Bool) : Prop :=
  (∀ i, 2 * (Finset.univ.filter (fun j => code i j = true)).card = ℓ) ∧
    ∀ i i', i ≠ i' → ℓ ≤ 3 * hammingDist (code i) (code i')

namespace Formula5

variable (φ : Formula5)

/-- A question coordinate: a clause (`Sum.inl`) or a variable (`Sum.inr`). -/
abbrev QCoord : Type := Fin φ.M ⊕ Fin φ.n

/-- The question to prover `P_i` on random string `r`: on coordinate `j` it receives the clause
`C_j` if bit `j` of its code word is `1`, and the distinguished variable `x_j` if it is `0`. -/
def question {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (r : φ.RandomString ℓ) (i : Fin k) :
    Fin ℓ → φ.QCoord :=
  fun j => if code i j then Sum.inl (r j).1 else Sum.inr (φ.var (r j).1 (r j).2)

/-- Canonical answer bits on one coordinate. On a clause coordinate: three bits (values of the
clause's three variables, in position order) that satisfy the clause. On a variable coordinate:
one bit, stored in position `0` (positions `1, 2` are `false`). -/
def CoordCanonical : φ.QCoord → (Fin 3 → Bool) → Prop
  | Sum.inl c, b => φ.ClauseSatBy c b
  | Sum.inr _, b => b 1 = false ∧ b 2 = false

instance (x : φ.QCoord) (b : Fin 3 → Bool) : Decidable (φ.CoordCanonical x b) := by
  cases x <;> unfold CoordCanonical <;> infer_instance

/-- The canonical answers to a question `q`. -/
def Answer {ℓ : ℕ} (q : Fin ℓ → φ.QCoord) : Type :=
  { a : Fin ℓ → Fin 3 → Bool // ∀ j, φ.CoordCanonical (q j) (a j) }

instance {ℓ : ℕ} (q : Fin ℓ → φ.QCoord) : Fintype (φ.Answer q) := by
  unfold Answer; infer_instance

instance {ℓ : ℕ} (q : Fin ℓ → φ.QCoord) : DecidableEq (φ.Answer q) := by
  unfold Answer; infer_instance

/-- A (deterministic) strategy of the `k` provers: prover `i` answers each question with a
canonical answer. -/
abbrev KStrategy (ℓ k : ℕ) : Type := (i : Fin k) → (q : Fin ℓ → φ.QCoord) → φ.Answer q

/-- The assignment to the sequence of distinguished variables of `r` that answer `a` of prover
`i` induces: on a clause coordinate, the bit at the distinguished position; on a variable
coordinate, the bit itself. -/
def inducedAssignment {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (r : φ.RandomString ℓ)
    (i : Fin k) (a : Fin ℓ → Fin 3 → Bool) : Fin ℓ → Bool :=
  fun j => if code i j then a j (r j).2 else a j 0

/-- The answers of provers `i` and `i'` on random string `r` are consistent: they induce the
same assignment to the distinguished variables. -/
def Consistent {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (A : φ.KStrategy ℓ k)
    (r : φ.RandomString ℓ) (i i' : Fin k) : Prop :=
  φ.inducedAssignment code r i (A i (φ.question code r i)).1 =
    φ.inducedAssignment code r i' (A i' (φ.question code r i')).1

/-- Weak acceptance predicate: at least one pair of (distinct) provers is consistent. -/
def WeakAccept {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (A : φ.KStrategy ℓ k)
    (r : φ.RandomString ℓ) : Prop :=
  ∃ i i', i ≠ i' ∧ φ.Consistent code A r i i'

/-- Strong acceptance predicate: every pair of provers is consistent. -/
def StrongAccept {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (A : φ.KStrategy ℓ k)
    (r : φ.RandomString ℓ) : Prop :=
  ∀ i i', φ.Consistent code A r i i'

instance {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (A : φ.KStrategy ℓ k) (r : φ.RandomString ℓ) :
    Decidable (φ.WeakAccept code A r) := by
  unfold WeakAccept Consistent; infer_instance

/-- The probability that the verifier of the `k`-prover system weakly accepts: the fraction of
the `(3M)^ℓ` random strings on which the weak acceptance predicate holds. -/
noncomputable def weakAcceptFrac {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (A : φ.KStrategy ℓ k) : ℝ :=
  ((Finset.univ.filter (fun r : φ.RandomString ℓ => φ.WeakAccept code A r)).card : ℝ) /
    Fintype.card (φ.RandomString ℓ)

end Formula5

end SetCoverThreshold.SetCover


