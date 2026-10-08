-- Prove2me | Definitions.Def_BBBV_RandomOracle_QueryModel
-- name    : BBBV_RandomOracle_QueryModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T16:54:55.723241+00:00
-- url     : https://prove2.me/theorems/6ad46982-732c-4088-94df-60a8edbd7307
-- title:
--   §2 and §3.1, pp. 4–7 — oracle query algorithms: XOR oracle, unitaries, acceptance probability, query magnitude (Definition 3.2)
-- statement:
--   This file fixes the **query model** in which the lower bounds of Bennett, Bernstein, Brassard and Vazirani are stated, together with the objects of their Theorem 3.5.
--
--   **Configurations and states.** Let $X$ (query strings), $R$ (answers, an additive group) and $W$ (workspace) be finite sets. A basis configuration is a triple $(q, z, w)$ with $q \in X \cup \{\bot\}$, $z \in R$, $w \in W$; $q = x$ means "querying the string $x$" and $q = \bot$ means "not querying". A state is a vector $\varphi \in \mathbb{C}^{(X\cup\{\bot\}) \times R \times W}$ with the Euclidean norm.
--
--   **The oracle.** For $f : X \to R$ the oracle operator $O_f$ is the unitary permutation of basis vectors
--   $$O_f\,|x, z, w\rangle = |x, z + f(x), w\rangle, \qquad O_f\,|\bot, z, w\rangle = |\bot, z, w\rangle .$$
--   For $R = \{0,1\}^n$ with bitwise addition this is the paper's query $|x \circ b\rangle \mapsto |x \circ (b \oplus A(x))\rangle$ (§2, p. 4).
--
--   **Algorithms.** A $T$-query algorithm $M$ consists of a unit vector $\varphi_0$, unitaries $U_0, \dots, U_{T-1}$ that do not depend on the oracle, and a set of accepting basis configurations. Given oracles $g_0, \dots, g_{T-1}$ (one per step; usually all equal to one oracle $A$) its states are
--   $$\varphi_0, \qquad \varphi_{i+1} = U_i\, O_{g_i}\, \varphi_i \quad (0 \le i < T),$$
--   so $\varphi_i$ is the superposition at time $i$, before the $i$-th query, and $\varphi_T$ is the final state. The acceptance probability is $\sum_{c \text{ accepting}} |\varphi_T(c)|^2$, the probability that measuring $\varphi_T$ in the computational basis gives an accepting configuration.
--
--   **Query magnitude (Definition 3.2).** For $y \in X$ and a state $\varphi$,
--   $$q_y(\varphi) = \sum_{z \in R} \sum_{w \in W} |\varphi(y, z, w)|^2,$$
--   the total squared magnitude of the configurations that query $y$.
--
--   **Deciding.** $M$ with oracle $g$ decides a proposition $b$ (with bounded error) if it accepts with probability at least $2/3$ when $b$ holds and at most $1/3$ when $b$ fails.
--
--   **Strings and the language.** $\{0,1\}^n$ is modelled as $(\mathbb{Z}/2)^n$, and $1^n$ is the all-ones string. For an oracle $A : \{0,1\}^n \to \{0,1\}^n$ the class $\mathcal{A}$ consists of the $A$ under which $1^n$ has no preimage ($1^n \notin \mathcal{L}_A$), and $\mathcal{B}$ of those under which $1^n$ has exactly one preimage.
--
--   These objects are shared by every statement of the mission: Theorems 3.1, 3.3, Corollary 3.4 and Theorem 3.5.
--
--   **Formalization Note** The paper's oracle quantum Turing machine is replaced by this query model, which is the form its proofs use (the proof of Theorem 3.3 writes the machine as a unitary step operator applied $T$ times). Every oracle QTM running $T$ steps is such an algorithm: oracle answers on strings of other lengths are fixed and absorbed into the unitaries, and configurations querying them (or not in the pre-query state) are non-querying configurations $\bot$. The oracle returns the whole value $A(x) \in \{0,1\}^n$; one full-value query is $n$ Boolean queries, and one Boolean query of §2, p. 5, is simulated with two full-value queries. Strings are `Fin n → ZMod 2`; states are `EuclideanSpace ℂ (Option X × R × W)`, `none` being $\bot$.
-- source:
--   Bennett, Bernstein, Brassard and Vazirani, Strengths and weaknesses of quantum computing, arXiv:quant-ph/9701001v1, pp. 4–5 (§2, oracle QTMs and length-preserving oracles), p. 7 (Definition 3.2), p. 8 (the language ℒ_A in the proof of Theorem 3.5), p. 9 (the classes 𝒜 and ℬ)

import Mathlib

namespace BBBV.RandomOracle

/-- Basis configurations of a query algorithm: query register (`none` = not querying),
answer register `R`, workspace `W`. -/
abbrev Config (X R W : Type) : Type := Option X × R × W

/-- States of a query algorithm: vectors in `ℂ^(Config X R W)` with the Euclidean norm. -/
abbrev State (X R W : Type) : Type := EuclideanSpace ℂ (Config X R W)

/-- The basis permutation of the XOR oracle for `f : X → R`:
`(some x, z, w) ↦ (some x, z + f x, w)` and `(none, z, w) ↦ (none, z, w)`. -/
def oracleEquiv {X R W : Type} [AddGroup R] (f : X → R) : Config X R W ≃ Config X R W where
  toFun c :=
    match c with
    | (some x, z, w) => (some x, z + f x, w)
    | (none, z, w) => (none, z, w)
  invFun c :=
    match c with
    | (some x, z, w) => (some x, z - f x, w)
    | (none, z, w) => (none, z, w)
  left_inv c := by
    rcases c with ⟨_ | x, z, w⟩ <;> simp
  right_inv c := by
    rcases c with ⟨_ | x, z, w⟩ <;> simp

/-- The oracle operator `O_f`: the unitary mapping the basis vector `|x, z, w⟩` to
`|x, z + f(x), w⟩` and fixing every non-querying basis vector. -/
noncomputable def oracleOp {X R W : Type} [Fintype X] [Fintype R] [Fintype W] [AddGroup R]
    (f : X → R) :
    State X R W ≃ₗᵢ[ℂ] State X R W :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (oracleEquiv (W := W) f)

/-- A `T`-query algorithm: a unit initial state, `T` oracle-independent unitaries and a set
of accepting basis configurations. -/
structure QueryAlg (X R W : Type) [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
    [Fintype W] [DecidableEq W] (T : ℕ) where
  /-- the initial state `|φ₀⟩` -/
  init : State X R W
  /-- the initial state has unit length -/
  init_norm : ‖init‖ = 1
  /-- the oracle-independent unitary applied after the `i`-th query -/
  U : Fin T → (State X R W ≃ₗᵢ[ℂ] State X R W)
  /-- the accepting basis configurations -/
  accept : Finset (Config X R W)

variable {X R W : Type} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
  [AddCommGroup R] [Fintype W] [DecidableEq W] {T : ℕ}

/-- The state of `M` at time `i` (before the query of step `i`) when step `j` queries the
oracle `g j`: `φ₀ = init`, `φ_{i+1} = U_i (O_{g i} φ_i)` for `i < T`, constant after `T`. -/
noncomputable def state (M : QueryAlg X R W T) (g : Fin T → X → R) : ℕ → State X R W
  | 0 => M.init
  | i + 1 =>
    if h : i < T then M.U ⟨i, h⟩ (oracleOp (g ⟨i, h⟩) (state M g i)) else state M g i

/-- The final state `φ_T`. -/
noncomputable def final (M : QueryAlg X R W T) (g : Fin T → X → R) : State X R W :=
  state M g T

/-- The probability that measuring the final state in the computational basis yields an
accepting configuration. -/
noncomputable def acceptProb (M : QueryAlg X R W T) (g : Fin T → X → R) : ℝ :=
  ∑ c ∈ M.accept, ‖final M g c‖ ^ 2

/-- Query magnitude `q_y(φ)` (Definition 3.2): the total squared magnitude in `φ` of the
configurations querying the string `y`. -/
noncomputable def queryMag (y : X) (φ : State X R W) : ℝ :=
  ∑ z : R, ∑ w : W, ‖φ (some y, z, w)‖ ^ 2

/-- `M` with oracle `g` decides the proposition `b` with bounded error: it accepts with
probability at least `2/3` if `b` holds and at most `1/3` if it fails. -/
def Decides (M : QueryAlg X R W T) (g : Fin T → X → R) (b : Prop) : Prop :=
  (b → 2 / 3 ≤ acceptProb M g) ∧ (¬ b → acceptProb M g ≤ 1 / 3)

/-- Binary strings of length `n`, with bitwise exclusive-or as addition. -/
abbrev Str (n : ℕ) : Type := Fin n → ZMod 2

/-- The string `1ⁿ`. -/
def ones (n : ℕ) : Str n := fun _ => 1

/-- The class `𝒜`: oracles at length `n` under which `1ⁿ` has no preimage. -/
def NoInverse {n : ℕ} (A : Str n → Str n) : Prop := ∀ x, A x ≠ ones n

/-- The class `ℬ`: oracles at length `n` under which `1ⁿ` has exactly one preimage. -/
def UniqueInverse {n : ℕ} (A : Str n → Str n) : Prop := ∃! x, A x = ones n

end BBBV.RandomOracle


