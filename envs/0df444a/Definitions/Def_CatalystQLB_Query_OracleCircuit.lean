-- Prove2me | Definitions.Def_CatalystQLB_Query_OracleCircuit
-- name    : CatalystQLB_Query_OracleCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:40.914818+00:00
-- url     : https://prove2.me/theorems/68893921-ea45-4ffd-8aa4-a3f98c985d35
-- title:
--   Oracle circuits on the query, response and catalyst registers
-- statement:
--   Fix the security parameter $\lambda$ and a catalyst size $\ell$. The algorithm acts on three registers: a **query register** $Q$ and a **response register** $R$ of $\lambda$ qubits each (together the IO register), and a **catalyst register** $C$ of $\ell$ qubits; computational-basis labels are bit strings, so the basis of $Q\otimes R\otimes C$ is indexed by $(\{0,1\}^\lambda\times\{0,1\}^\lambda)\times\{0,1\}^\ell$.
--
--   For functions $f,g:\{0,1\}^\lambda\to\{0,1\}^\lambda$ the **standard (XOR) oracles** act on $Q\otimes R$ by
--   $$O_h\,|x,y\rangle=|x,\,y\oplus h(x)\rangle,\qquad h\in\{f,g\},$$
--   and as the identity on $C$. An **oracle circuit** is a finite sequence of gates, each either a fixed unitary on all $2\lambda+\ell$ qubits, or $O_f\otimes I_C$, or $O_g\otimes I_C$. For given $f,g$ it implements the unitary $U=U_k\cdots U_2U_1$, where $U_1$ is the first gate. The circuit counts its queries to $O_f$, to $O_g$, and in total.
--
--   This is the paper's model of a space-bounded quantum algorithm: arbitrary oracle-independent gates, any number of them, on exactly the $2\lambda+\ell$ qubits, with no further workspace. Every statement of the mission quantifies over these circuits.
--
--   **Formalization Note** `n` is the paper's $\lambda$. Bit strings are `QAlgorithms.Qubits n = Fin n → Bool` with `false` $=|0\rangle$; $\oplus$ is the addition of `Fin n → Bool`. The oracle is the published `QAlgorithms.xorOracle`. A unitary gate stores a fixed element of `Matrix.unitaryGroup`, so it cannot depend on $f$, $g$ or the input. The list's first element acts first.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Lemma 8, p.12 (PDF 15); footnote 3, p.10 (PDF 13); §3.4, p.20 (PDF 23); §5.3, pp.43–44 (PDF 46–47)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query

open scoped Matrix

namespace CatalystQLB.Query

open QAlgorithms

/-- The computational-basis labels of the register `Q ⊗ R ⊗ C` of Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of 2026-11-03),
§5.3, Lemma 75's proof, p.44 (PDF 47): `Q` (query) and `R` (response) hold `n` qubits each
and `C` (catalyst) holds `ℓ` qubits, `2n + ℓ` qubits in all.

**Formalization Note** `n` is the paper's security parameter `λ` (`λ` is a Lean keyword),
not the paper's `n(λ) = 2λ`. `QAlgorithms.Qubits m = Fin m → Bool`, with `false` = `|0⟩`.
The order of the factors is `((Q × R) × C)`. -/
abbrev Idx (n ℓ : ℕ) : Type := (Qubits n × Qubits n) × Qubits ℓ

/-- One gate of an oracle circuit (arXiv:2609.40323, version of 2026-11-03, footnote 3, p.10
(PDF 13); §5.3, pp.43–44 (PDF 46–47): `U = V_q O_f V_{q−1} O_f ⋯ V_2 O_f V_1`, the `V_i`
oracle-independent gates that may also query `O_g`): a fixed unitary on all `2n + ℓ` qubits,
or a query to `O_f`, or a query to `O_g`.

**Formalization Note** A `unitary` step stores a fixed matrix, so the non-oracle gates cannot
depend on `f`, `g`, `x` or `r`; their number is not bounded (p.3: "The lower bound imposes no
restriction on the number of oracle-independent gates"). -/
inductive Step (n ℓ : ℕ) where
  /-- An oracle-independent unitary on `Q ⊗ R ⊗ C`. -/
  | unitary (U : Matrix.unitaryGroup (Idx n ℓ) ℂ)
  /-- A query `O_f ⊗ I_C`. -/
  | queryF
  /-- A query `O_g ⊗ I_C`. -/
  | queryG

/-- `s` is a query to `O_f`. -/
def Step.isF {n ℓ : ℕ} : Step n ℓ → Bool
  | .queryF => true
  | _ => false

/-- `s` is a query to `O_g`. -/
def Step.isG {n ℓ : ℕ} : Step n ℓ → Bool
  | .queryG => true
  | _ => false

/-- The matrix of one step for the oracles `f, g : {0,1}^n → {0,1}^n`
(arXiv:2609.40323, version of 2026-11-03, footnote 3, p.10 (PDF 13) and §3.4, p.20 (PDF 23):
`O_h |x, y⟩ = |x, y ⊕ h(x)⟩`). A query acts as `QAlgorithms.xorOracle h` on `Q ⊗ R` and as the
identity on `C`; `⊕` is the addition of `Fin n → Bool` (Mathlib's Boolean ring, `+` = xor).

**Formalization Note** The oracles act on the fixed wires `(Q, R)`. An oracle applied to other
wires differs from this by wire permutations, which are unitary steps. -/
noncomputable def Step.mat {n ℓ : ℕ} (f g : Qubits n → Qubits n) :
    Step n ℓ → Matrix (Idx n ℓ) (Idx n ℓ) ℂ
  | .unitary U => (U : Matrix (Idx n ℓ) (Idx n ℓ) ℂ)
  | .queryF => Matrix.kronecker (xorOracle f) (1 : Matrix (Qubits ℓ) (Qubits ℓ) ℂ)
  | .queryG => Matrix.kronecker (xorOracle g) (1 : Matrix (Qubits ℓ) (Qubits ℓ) ℂ)

/-- An oracle circuit on `Q ⊗ R ⊗ C` (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of 2026-11-03), §5.3, pp.43–44 (PDF 46–47); Lemma 8, p.12
(PDF 15): "any quantum algorithm with `ℓ ≤ ⌊cλ⌋` auxiliary qubits that makes `q` queries"): a
finite list of steps, the **first element of the list applied first**. The circuit acts on
exactly the `2n + ℓ` qubits of `Idx n ℓ`; there is no other workspace.

**Formalization Note** `n` is the paper's `λ`. The paper's unitary `U` is `eval C f g`. -/
structure OracleCircuit (n ℓ : ℕ) where
  /-- The gates, in the order in which they are applied. -/
  steps : List (Step n ℓ)

namespace OracleCircuit

variable {n ℓ : ℕ}

/-- The ordered product of a list of steps: `[s₁, …, s_k]` gives `s_k ⋯ s₂ s₁` (the first
element acts first); the empty list gives the identity. -/
noncomputable def evalList (f g : Qubits n → Qubits n) : List (Step n ℓ) →
    Matrix (Idx n ℓ) (Idx n ℓ) ℂ
  | [] => 1
  | s :: rest => evalList f g rest * s.mat f g

/-- The unitary `U` that the circuit implements for the oracles `f, g`. -/
noncomputable def eval (C : OracleCircuit n ℓ) (f g : Qubits n → Qubits n) :
    Matrix (Idx n ℓ) (Idx n ℓ) ℂ :=
  evalList f g C.steps

/-- The number of queries to `O_f` (the paper's `q − 1` in the proofs of Lemmas 75, 82, 119,
121). -/
def numF (C : OracleCircuit n ℓ) : ℕ :=
  (C.steps.filter Step.isF).length

/-- The number of queries to `O_g` (the paper's `q_g`). -/
def numG (C : OracleCircuit n ℓ) : ℕ :=
  (C.steps.filter Step.isG).length

/-- The total number of oracle queries, to `O_f` and `O_g` together (Lemma 8's `q`). -/
def numQueries (C : OracleCircuit n ℓ) : ℕ :=
  C.numF + C.numG

end OracleCircuit

end CatalystQLB.Query


