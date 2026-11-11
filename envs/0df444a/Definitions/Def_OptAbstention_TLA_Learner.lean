-- Prove2me | Definitions.Def_OptAbstention_TLA_Learner
-- name    : OptAbstention_TLA_Learner
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:08:10.587186+00:00
-- url     : https://prove2.me/theorems/b32acc54-cb12-4c0e-b30c-34500b325de2
-- title:
--   TLA learners (Definition 1.1): selective error for every labeling, abstention rate against every adversary kernel
-- statement:
--   Let $\eta,\delta\in(0,1)$. A program $P$ is a **$(\gamma,\eta,\delta)$-TLA learner** with respect to a distribution $D$ on $X$ if:
--
--   1. **Selective error.** For every labeled distribution $\bar D_{\mathrm{train}}$ with marginal $D$, every $n\ge1$, every test list $x_1,\dots,x_n\in X$ and every labeling $y\in\{\pm1\}^n$ fixed in advance, the set of random inputs (example stream $\sim\bar D_{\mathrm{train}}^{\mathbb N}$, tape) on which $P$ fails to halt with outputs $h_i\in\{\pm1\}$, $g_i\in\{0,1\}$ satisfying
--   $$\tfrac1n\#\{i:h_i\ne y_i\wedge g_i=1\}\le\gamma(\bar D_{\mathrm{train}},n,x,y)$$
--   has measure at most $\delta$.
--   2. **Abstention rate.** There is $N$ such that for every $\bar D_{\mathrm{train}}$ with marginal $D$, every $n\ge N$ and every Markov kernel $\kappa$ (the adversary), with $S_{\mathrm{cln}}\sim D^n$ and $S_{\mathrm{test}}\sim\kappa(S_{\mathrm{cln}},\cdot)$ independent of the example stream and the tape, the set on which $P$ run on $S_{\mathrm{test}}$ fails to output a valid $(h,g)$ with
--   $$\tfrac1n\#\{i:g_i=0\}\le d_{\mathrm{TV}}(U(S_{\mathrm{test}}),U(S_{\mathrm{cln}}))+\eta$$
--   has measure at most $\delta$.
--
--   The input is $n$ (pointer 0) and the test points (cells $0,\dots,nd-1$); the outputs are $h_i$ in cell $-1-i$ and $g_i$ in cell $-1-n-i$.
--
--   **Formalization Note.** Failure probabilities are measures of failure sets. The program sees neither the labels, nor $\bar D_{\mathrm{train}}$, nor the benchmark; $N$ does not depend on $\bar D_{\mathrm{train}}$, $n$ or the adversary.
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 2, Definition 1.1 and footnotes 2–3

import Mathlib
import Definitions.Def_OptAbstention_TLA_Empirical
import Definitions.Def_OptAbstention_TLA_Machine

/-!
# TLA learners (Definition 1.1) on the randomized sampling real RAM

Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, *Achieving the Optimal Abstention Rate
for Learning with Distribution Shift*, STOC 2027 submission (manuscript sha256 0fb30af1…),
Definition 1.1 with footnotes 2–3 (p. 2).

Encoding.
* Input: pointer `0` holds `n = |S_test|`; cells `0, …, nd − 1` hold the test points in order
  (point `i`, coordinate `j` in cell `i·d + j`); everything else is `0`. The program sees nothing
  else: neither the test labels, nor `D̄_train`, nor any benchmark.
* Output: for the `i`-th occurrence, `h_i` in cell `−1 − i` and `g_i` in cell `−1 − n − i`. A run
  that never halts, or whose output block is not `h_i ∈ {−1, 1}`, `g_i ∈ {0, 1}`, fails both
  clauses.
* Selective error: for every labeled distribution `D̄_train` with marginal `D`, every `n ≥ 1`, every
  test list and every labeling fixed in advance, the `D̄_train^ℕ ⊗ Unif^ℕ`-measure of the runs whose
  selective error exceeds `γ` is at most `δ`.
* Abstention rate: there is a clean-sample threshold `N` (independent of `D̄_train`, `n` and the
  adversary) such that for every `n ≥ N`, every Markov kernel `κ` (the adversary: it sees all of
  `S_cln` and uses its own randomness, but not the training samples or the learner's tape),
  the measure of `{(S_cln, S_test, ξ, ν) : abstention > d_TV(U(S_test), U(S_cln)) + η}` under
  `(D^n ⊗ κ) ⊗ D̄_train^ℕ ⊗ Unif^ℕ` is at most `δ`.
* Failure probabilities are measures of failure sets (outer measures if not measurable).
-/

open MeasureTheory ProbabilityTheory

namespace OptAbstention.TLA

/-- The start state on the test list `xs`. -/
noncomputable def testInit {d : ℕ} {X : Set (Pt d)} {n : ℕ} (xs : Fin n → X) : State :=
  initState (fun j => if j = 0 then (n : ℤ) else 0)
    (blockMem 0 d n (fun i j => (xs i : Pt d) j) fun _ => 0)

/-- The classifier value `h_i` in a final state. -/
def outH (S : State) (_n : ℕ) (i : ℕ) : ℝ := S.cfg.mem (-1 - (i : ℤ))

/-- The selector value `g_i` in a final state. -/
def outG (S : State) (n : ℕ) (i : ℕ) : ℝ := S.cfg.mem (-1 - (n : ℤ) - (i : ℤ))

/-- The output block of a final state is a classifier `h ∈ {±1}^n` and a selector
`g ∈ {0, 1}^n`. -/
def ValidTLAOutput (S : State) (n : ℕ) : Prop :=
  ∀ i < n, IsSign (outH S n i) ∧ (outG S n i = 0 ∨ outG S n i = 1)

open Classical in
/-- `Pr_{(x,y)∼U(S̄_test)}[h(x) ≠ y ∧ g(x) = 1]`. -/
noncomputable def selErr (S : State) {n : ℕ} (ys : Fin n → Bool) : ℝ :=
  frac fun i : Fin n => outH S n i ≠ signOf (ys i) ∧ outG S n i = 1

open Classical in
/-- `Pr_{x∼U(S_test)}[g(x) = 0]`. -/
noncomputable def abstRate (S : State) (n : ℕ) : ℝ :=
  frac fun i : Fin n => outG S n i = 0

/-- The run of `P` on the test list `xs` with random inputs `ω` halts with a valid output whose
selective error w.r.t. the labels `ys` is at most `γ`. -/
def SelectiveOK {d : ℕ} {X : Set (Pt d)} (P : Program) {n : ℕ} (xs : Fin n → X)
    (ys : Fin n → Bool) (γ : ENNReal) (ω : ExStream d × Tape) : Prop :=
  ∃ S, finalState P d ω.1 ω.2 (testInit xs) = some S ∧ ValidTLAOutput S n ∧
    ENNReal.ofReal (selErr S ys) ≤ γ

/-- The run of `P` on `S_test` with random inputs `ω` halts with a valid output whose abstention
rate is at most `d_TV(U(S_test), U(S_cln)) + η`. -/
def AbstentionOK {d : ℕ} {X : Set (Pt d)} (P : Program) {n : ℕ} (Scln Stest : Fin n → X)
    (η : ℝ) (ω : ExStream d × Tape) : Prop :=
  ∃ S, finalState P d ω.1 ω.2 (testInit Stest) = some S ∧ ValidTLAOutput S n ∧
    abstRate S n ≤ empTV Stest Scln + η

/-- Definition 1.1: `P` is a `(γ, η, δ)`-TLA learner with respect to `D` (the benchmark `γ` may
depend on `D̄_train` and the labeled test list). -/
def IsTLALearner {d : ℕ} {X : Set (Pt d)} (P : Program) (D : Measure X)
    (γ : Measure (X × Bool) → (n : ℕ) → (Fin n → X) → (Fin n → Bool) → ENNReal)
    (η δ : ℝ) : Prop :=
  (∀ (Dbar : Measure (X × Bool)) [IsProbabilityMeasure Dbar], Dbar.map Prod.fst = D →
    ∀ (n : ℕ), 1 ≤ n → ∀ (xs : Fin n → X) (ys : Fin n → Bool),
      streamLaw Dbar {ω | ¬ SelectiveOK P xs ys (γ Dbar n xs ys) ω} ≤ ENNReal.ofReal δ) ∧
  ∃ N : ℕ, ∀ (Dbar : Measure (X × Bool)) [IsProbabilityMeasure Dbar], Dbar.map Prod.fst = D →
    ∀ (n : ℕ), N ≤ n → 1 ≤ n → ∀ (κ : Kernel (Fin n → X) (Fin n → X)) [IsMarkovKernel κ],
      (((Measure.pi fun _ : Fin n => D) ⊗ₘ κ).prod (streamLaw Dbar))
        {q | ¬ AbstentionOK P q.1.1 q.1.2 η q.2} ≤ ENNReal.ofReal δ

end OptAbstention.TLA


