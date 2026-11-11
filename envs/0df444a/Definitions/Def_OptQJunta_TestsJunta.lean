-- Prove2me | Definitions.Def_OptQJunta_TestsJunta
-- name    : OptQJunta_TestsJunta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:21:20.444801+00:00
-- url     : https://prove2.me/theorems/9889a487-480a-4c3a-9113-dfba1120745a
-- title:
--   Junta Boolean Testing (Problem 4.1) with standard and with controlled queries; $\log_{2,+}$ and the bound $\min\{2^{n/2},\sqrt{(1+\log_{2,+}(\varepsilon2^k))/\varepsilon}\}$
-- statement:
--   A **$T$-query algorithm** with standard queries to $f:\{0,1\}^n\to\{0,1\}$ alternates oracle-independent unitaries with $T$ applications of $O_f|x,b\rangle=|x,b\oplus f(x)\rangle$ on its query register, starting from an oracle-independent state, on a workspace of any finite size, and outputs a function of the final measurement (the published `QAlgorithms.QueryAlg`). It **solves Junta Boolean Testing** (Problem 4.1) for $k$ and $\varepsilon$ if it outputs YES with probability at least $2/3$ on every $f\in\mathcal B_k$ and NO with probability at least $2/3$ on every $f$ with $\mathrm{dist}_{\mathcal B}(f,\mathcal B_k)\ge\varepsilon$; nothing is required on other inputs.
--
--   With **controlled queries** the query register has an extra configuration "not querying", on which the oracle acts as the identity. The module also fixes $\log_{2,+}x=\max\{0,\log_2x\}$ and the bound
--
--   $$
--   \mathrm{juntaBound}(n,k,\varepsilon)=\min\Bigl\{2^{n/2},\ \sqrt{\frac{1+\log_{2,+}(\varepsilon2^k)}{\varepsilon}}\Bigr\}
--   $$
--
--   of Theorems 4.2 and 4.8, the state $|-\rangle=(|0\rangle-|1\rangle)/\sqrt2$, and the probability of an event of the output.
--
--   These are the access model and the decision problem of every query bound in the mission.
--
--   **Formalization Note** The source's testers may use private randomness, intermediate measurements and adaptivity, and count the worst-case number of queries over all executions; by deferred measurement, purification and padding, they are exactly the algorithms of this unitary form. The output bit `true` means YES. The controlled oracle is the published `xorOracle` of the extension of $f$ by "not querying" $\mapsto0$.
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Problem 4.1, p.55; §2.5–2.5.1, pp.22–23; §2.1, p.12; Theorems 4.2, 4.8, pp.55, 59; Lemma 4.9, p.60

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_OptQJunta_IsFar

namespace OptQJunta

open QAlgorithms

/-- The controlled Boolean query (Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of
November 3, 2026, sha256 a97d09a4…, Lemma 4.9, p.60: "even with controlled queries"): the standard
query `|x, b⟩ ↦ |x, b ⊕ f(x)⟩` (§2.5.1, p.23) on the query register `Option (Qubits n) × Bool`, where
the extra configuration `none` ("not querying") is left unchanged.

**Formalization Note** It is the published `QAlgorithms.xorOracle` of the extension of `f` by
`none ↦ 0`, so `|none, b⟩ ↦ |none, b⟩`. A controlled-`O_f` call is this oracle with the control
folded into the query register; every plain query algorithm is a controlled one that never uses
`none`. -/
noncomputable def ctrlOracle {n : ℕ} (f : Qubits n → Bool) :
    Matrix (Option (Qubits n) × Bool) (Option (Qubits n) × Bool) ℂ :=
  xorOracle fun o : Option (Qubits n) => o.elim false f

/-- **Problem 4.1** (Junta Boolean Testing; Bao–Gao–Yao preprint, version of November 3, 2026, sha256
a97d09a4…, p.55), with the access model of §2.5 and §2.5.1 (pp.22–23): the `T`-query algorithm `A`
with output bit `out` (`true` = YES) distinguishes `f ∈ ℬ_k` from `dist_ℬ(f, ℬ_k) ≥ ε` with
probability at least `2/3`: it outputs `true` with probability `≥ 2/3` on every `k`-junta and
`false` with probability `≥ 2/3` on every `f` that is `ε`-far from `ℬ_k`. Nothing is required on
other inputs.

**Formalization Note** The query model is the published `QAlgorithms.QueryAlg` with query register
`Qubits n × Bool`, an arbitrary finite workspace `W`, an oracle-independent unit start state and
oracle-independent unitaries `U_0, …, U_T`, and the standard query `xorOracle f`
(`|x, b⟩ ↦ |x, b ⊕ f(x)⟩`); the output is a function of the final computational-basis measurement.
The paper's testers may use private randomness, intermediate measurements and adaptivity, and
count the worst-case number of queries over executions; by deferred measurement, purification of
the randomness and padding of shorter executions, these are exactly the `T`-query algorithms of
this form with the same output law on every `f`. -/
def TestsJunta {n : ℕ} {W : Type} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Qubits n) Bool W T) (out : (Qubits n × Bool) × W → Bool) (k : ℕ) (ε : ℝ) :
    Prop :=
  (∀ f : Qubits n → Bool, IsJunta f k → 2 / 3 ≤ A.outputProb (xorOracle f) out true) ∧
    (∀ f : Qubits n → Bool, IsFar f k ε → 2 / 3 ≤ A.outputProb (xorOracle f) out false)

/-- **Problem 4.1** with controlled queries (Bao–Gao–Yao preprint, version of November 3, 2026, sha256
a97d09a4…, p.55 and Lemma 4.9, p.60): as `TestsJunta`, for a query algorithm whose query register is
`Option (Qubits n) × Bool` and whose oracle is `ctrlOracle f`. -/
def CTestsJunta {n : ℕ} {W : Type} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Option (Qubits n)) Bool W T) (out : (Option (Qubits n) × Bool) × W → Bool)
    (k : ℕ) (ε : ℝ) : Prop :=
  (∀ f : Qubits n → Bool, IsJunta f k → 2 / 3 ≤ A.outputProb (ctrlOracle f) out true) ∧
    (∀ f : Qubits n → Bool, IsFar f k ε → 2 / 3 ≤ A.outputProb (ctrlOracle f) out false)

/-- The probability that the output `out` of the final computational-basis measurement of the query
algorithm `A` run with oracle `O` satisfies the predicate `P` (Bao–Gao–Yao preprint, version of
November 3, 2026, sha256 a97d09a4…, §2.5, p.22). Used for the set-valued outputs of Lemma 4.5. -/
noncomputable def outEventProb {ι κ W : Type} [Fintype ι] [Fintype κ] [Fintype W] [DecidableEq ι]
    [DecidableEq κ] [DecidableEq W] {T : ℕ} {β : Type} (A : QueryAlg ι κ W T)
    (O : Matrix (ι × κ) (ι × κ) ℂ) (out : (ι × κ) × W → β) (P : β → Prop) : ℝ := by
  classical
  exact probEvent (A.finalState O) fun z => P (out z)

/-- `log₂,₊ x = max{0, log₂ x}` (Bao–Gao–Yao preprint, version of November 3, 2026, sha256 a97d09a4…,
§2.1, p.12; `log` is base two). -/
noncomputable def log2p (x : ℝ) : ℝ :=
  max 0 (Real.logb 2 x)

/-- The tight bound `min{2^{n/2}, √((1 + log₂,₊(ε2^k))/ε)}` of Theorems 4.2 and 4.8 (Bao–Gao–Yao
preprint, version of November 3, 2026, sha256 a97d09a4…, pp.55 and 59). The radical covers the whole
fraction. -/
noncomputable def juntaBound (n k : ℕ) (ε : ℝ) : ℝ :=
  min ((2 : ℝ) ^ ((n : ℝ) / 2)) (Real.sqrt ((1 + log2p (ε * 2 ^ k)) / ε))

/-- The single-qubit state `|−⟩ = (|0⟩ − |1⟩)/√2` used for phase kickback (Bao–Gao–Yao preprint,
version of November 3, 2026, sha256 a97d09a4…, §2.5.1, p.23). -/
noncomputable def minusKet : EuclideanSpace ℂ Bool :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (ket false - ket true)

end OptQJunta


