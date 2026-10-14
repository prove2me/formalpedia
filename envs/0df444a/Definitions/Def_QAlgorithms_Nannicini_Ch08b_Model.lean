-- Prove2me | Definitions.Def_QAlgorithms_Nannicini_Ch08b_Model
-- name    : QAlgorithms_Nannicini_Ch08b_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:48:53.761496+00:00
-- url     : https://prove2.me/theorems/abf083d4-9910-4410-8fbb-d054f63e87da
-- title:
--   Nannicini Ch08b: supporting definitions
-- statement:
--   Nannicini, Chapter 8 (part b): the MaxCut SDP relaxation by inexact mirror descent
--
--   ## QAlgorithms.Nannicini.mcQram
--
--   For natural numbers $b,r$ and any map $M$ from $b$-bit to $r$-bit strings, this complex matrix on $b+r$ wires sends each basis vector $|j,z\rangle$ to $|j,z\mathbin{\oplus}M(j)\rangle$, with the first $b$ bits the address and final $r$ the target. Its corresponding row-column entry is one exactly when the address is unchanged and the target is updated by coordinatewise XOR with $M(j)$, and zero otherwise. Either register can be empty.
--
--   ## QAlgorithms.Nannicini.MCPrepOp
--
--   This instruction type has rational constants; addition, subtraction, multiplication, and division with two natural operand indices; square root and arccosine with one natural operand index; and complex argument with two natural operand indices. Neither index bounds nor numerical-domain conditions are imposed.
--
--   ## QAlgorithms.Nannicini.MCPrepOp.value
--
--   Given any finite real list, let $v_i$ be its zero-based entry at natural index $i$, with default zero outside the list. Constants evaluate to their rational values coerced to real, while the other instruction values are $v_i+v_j$, $v_i-v_j$, $v_iv_j$, $v_i/v_j$, $\sqrt{v_i}$, $\arccos(v_i)$, and the principal argument of $v_i+\mathrm{i}v_j$, respectively. These operations are total: division by zero, square root of negative inputs, and argument of zero return zero, while arccosine is $\pi$ below $-1$ and zero above $1$. No operand or index preconditions are required.
--
--   ## QAlgorithms.Nannicini.mcPrepExec
--
--   For any finite preparation program and finite real input list, process instructions in listed order, evaluating each on the full current list and appending its result. All inputs and prior results remain in the list; unavailable operand indices read zero, and no index validity is assumed. An empty program returns the input.
--
--   ## QAlgorithms.Nannicini.mcInput
--
--   For any natural number $n$ and real $n$ by $n$ matrix $C$, this list contains the entries $C_{ij}$ in increasing row order and, within each row, increasing column order. Its length is $n^2$, and it is empty when $n=0$.
--
--   ## QAlgorithms.Nannicini.mcStaticWords
--
--   For natural numbers $b,r,n$, a finite preparation program, an address map from $b$-bit strings to natural numbers, and an arbitrary real $n$ by $n$ matrix $C$, execute the program on the row-ordered list of $C$'s entries. At each address read the resulting list at its assigned zero-based natural index, defaulting to zero when absent; take natural-number floor, returning zero on negative input; and encode the result modulo $2^r$ as an $r$-bit string, most significant first. No bounds or precision conditions are imposed; for $r=0$ every word is empty.
--
--   ## QAlgorithms.Nannicini.mcSplitWords
--
--   For natural numbers $b,r$ and maps $\operatorname{stat},\operatorname{dyn}$ from $b$-bit to $r$-bit strings, this map on $(b+1)$-bit strings applies $\operatorname{dyn}$ to the remaining $b$ bits when the first bit is true, and $\operatorname{stat}$ to them when it is false. The selector bit exists even for $b=0$, and outputs are empty when $r=0$.
--
--   ## QAlgorithms.Nannicini.mcRoundState
--
--   For natural numbers $m,b,r$, a finite oracle circuit on $m$ wires with unitary ordinary gates of arity exactly two and one oracle label of arity $(b+1)+r$, and two word maps $\operatorname{stat},\operatorname{dyn}$ from $b$-bit to $r$-bit strings, this is the complex vector obtained by applying its circuit matrix to the all-false basis vector. Its oracle preserves the first $b+1$ query bits and XORs into the last $r$ bits the static word if the first query bit is false and the dynamic word if true, using the remaining $b$ query bits as address. Circuit steps act in listed order: ordinary gates apply their matrices on injectively specified wires, acting as identity elsewhere; queries apply the oracle or conjugate transpose according to their adjoint flag, and a present control outside those wires activates that matrix only when the control bit is true. The circuit matrix is the product of step matrices in reverse list order, with identity for the empty list. Zero widths are included; the step type enforces the necessary wire distinctness.
--
--   ## QAlgorithms.Nannicini.mcHistProb
--
--   For natural numbers $m,b,r,R$, a circuit family assigning to every natural $k$ and $k$-term history of $m$-bit outcomes a circuit on $m$ wires with unitary two-wire ordinary gates and one oracle of arity $(b+1)+r$, a dynamic-word family depending on the same $k$ and history, fixed static words, and a full $R$-term history $h$, this is $\prod_{k=0}^{R-1}|\psi_k(h_k)|^2$. Here $\psi_k$ is produced afresh from the all-false basis vector by the circuit selected using the strict prefix $(h_0,\ldots,h_{k-1})$, with its sole oracle selecting static or prefix-dependent dynamic words by its leading selector bit and XORing that word into its target. Gate and query steps act in list order, with adjoint and optional control honored. Both word maps take $b$-bit addresses to $r$-bit words; all finite histories are admitted, and $R=0$ gives the empty product one.
--
--   ## QAlgorithms.Nannicini.mcHistCost
--
--   For natural numbers $m,b,r,R$, a circuit family assigning to every natural $k$ and $k$-term history of $m$-bit outcomes a circuit on $m$ wires with unitary two-wire ordinary gates and a single oracle label of arity $(b+1)+r$, and any $R$-term history $h$, this natural number sums over $0\le k<R$ the number of queries to label zero plus the number of ordinary gate steps in the circuit selected by $k$ and the strict prefix $(h_0,\ldots,h_{k-1})$. Each query counts once regardless of adjoint or control, and each ordinary gate counts once, so each summand equals its circuit list length. No history probability or word values enter this definition; $R=0$ gives zero cost.
--
--   ## QAlgorithms.Nannicini.mcSuccessProb
--
--   For natural numbers $m,b,r,R$, a circuit family indexed by every natural $k$ and $k$-term history of $m$-bit outcomes, a dynamic-word family on those prefixes, fixed static words, and any predicate $\operatorname{Good}$ on $R$-term histories, this is the finite sum over all such histories $h$ of their history probability if $\operatorname{Good}(h)$ holds, and zero otherwise. A history probability is the product over $k<R$ of the squared amplitude modulus of outcome $h_k$ in the state produced afresh from the all-false basis vector by the strict-prefix-selected circuit on $m$ wires, with unitary two-wire ordinary gates and one oracle of arity $(b+1)+r$ that selects static or prefix-dependent dynamic $r$-bit words using a leading selector and a $b$-bit address, XORs them into the target, and honors adjoint and optional control flags. No restriction on $\operatorname{Good}$ is imposed. For $R=0$ there is one empty history of probability one, so the result is one or zero according to the predicate on that history.
--
--   ## QAlgorithms.Nannicini.mcGibbsMixture
--
--   For any natural number $n$, real $n$ by $n$ matrix $C$, and finite list $L$ of pairs $(u,v)$ with $u$ a two-coordinate real vector and $v$ an $n$-coordinate real vector, this complex matrix is $|L|^{-1}\sum_{(u,v)\in L}G(H_{u,v})$, where $H_{u,v}=u_0\widehat C+u_1\operatorname{diag}(v)$, $\widehat C=\|C_{\mathbb C}\|_F^{-1}C_{\mathbb C}$ is the complex coercion normalized using Frobenius norm, and $G(H)=(\operatorname{tr}\exp H)^{-1}\exp H$. All real entries and coefficients are coerced to complex numbers; repeated list entries contribute repeatedly. No symmetry, Hermiticity, or nonzero-trace assumptions are present, and inverses are total with inverse zero equal to zero. Hence zero $C$ gives zero $\widehat C$, an empty list yields the zero matrix, and a zero exponential trace yields zero for that summand.
--
--   ## QAlgorithms.Nannicini.IsMaxCutSDPSolution
--
--   For any natural number $n$, arbitrary real $n$ by $n$ matrix $C$, real $\varepsilon$, and complex $n$ by $n$ matrix $\rho$, this says that $\rho$ is positive semidefinite with complex trace exactly one, that $\sum_{j=0}^{n-1}|\operatorname{Re}\rho_{jj}-n^{-1}|\le\varepsilon$, and that for every complex $n$ by $n$ matrix $\sigma$ which is positive semidefinite with trace one and has each complex diagonal entry equal to $n^{-1}$, one has $\operatorname{Re}\operatorname{tr}(\widehat C\sigma)-\varepsilon\le\operatorname{Re}\operatorname{tr}(\widehat C\rho)$. Here $\widehat C=\|C_{\mathbb C}\|_F^{-1}C_{\mathbb C}$, with inverse zero set to zero. There is no symmetry requirement on $C$ or sign assumption on $\varepsilon$; the condition on $\rho$ bounds the sum of absolute errors of diagonal real parts, while the comparison matrices have exactly specified complex diagonals. At $n=0$ the reciprocal and diagonal sum are zero, but an empty matrix cannot have trace one.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Nannicini/Ch08b.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_SDP
/-!
# Nannicini, Chapter 8 (part b): the MaxCut SDP relaxation by inexact mirror descent

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), §8.4.2–8.4.3: Proposition 8.28 (p.201), Lemma 8.29 (p.201), Theorem 8.30 (p.202),
Lemma 8.33 (p.204), and Proposition 8.34 (p.204) as a corrected statement in a hybrid
classical–quantum QRAM cost model defined below.

Standing assumptions (§8.4, pp.198–200). `C ∈ ℝ^{n×n}` is symmetric (p.198), given here as a real
matrix `C` with `C.IsSymm` and used through its complex image `C.map (↑)`; `Ĉ = C/‖C‖_F` is the
frozen `SDP.cHat` and needs `C ≠ 0`. The binary-search guess is `γ ∈ [−1, 1]` (p.199) and the
precision is `ϵ > 0`. The function `f_γ(ρ) = max{γ − Tr(Ĉρ), Σ_j |ρ_jj − 1/n|}` of Eq. (8.26) is the
frozen `SDP.maxCutF`. The estimate-driven subgradient of pp.200–201 is the frozen
`SDP.maxCutSubgrad`, fed with estimates `estC` of `Tr(Ĉρ)` and `estD j` of `ρ_jj` satisfying
Eq. (8.27). Subgradients and `ϵ`-subgradients (Def. 5.24, p.120) are the frozen `IsEpsSubgradOn`;
the vector space is the real space of Hermitian matrices (Rem. 8.6, 8.9: subgradient steps are taken
in the space of Hermitian matrices), and the dual pairing is the trace inner product
`⟨G, X⟩ = Tr(G X†)` (frozen `traceRePairing`). The iterates of Alg. 6 (p.183) are the frozen
`mmwuIterate`: `ρ^(t) = exp(−η Σ_{τ<t} G^(τ)) / Tr(⋯)`, `ρ^(1) = I/n`. `log` is base 2 (p.11).
-/

namespace QAlgorithms.Nannicini

open QAlgorithms.SDP





/-- Nannicini p.128, Definition 5.39 (QRAM), for the statement of Prop. 8.34 (chunk-local copy of
the QRAM of the Prop. 7.29 and Cor. 5.45 chunks, which a chunk may not import): for stored words
`M_j ∈ {0,1}^r`, `U_QRAM |j⟩|y⟩ = |j⟩|y ⊕ M_j⟩` for all addresses `j ∈ {0,1}^b`, `y ∈ {0,1}^r`.
Address register first. Its size in the sense of Def. 5.39 is `2^b · r`. -/
noncomputable def mcQram (b r : ℕ) (M : Qubits b → Qubits r) :
    Matrix (Qubits (b + r)) (Qubits (b + r)) ℂ :=
  Matrix.reindex (qubitsAppendEquiv b r).symm (qubitsAppendEquiv b r).symm (xorOracle M)

/-- One classical arithmetic operation of the preprocessing that reads the input `C` (chunk-local
copy of the straight-line real-arithmetic model of the Prop. 7.29 chunk, p.168: the "`Õ(n²)`
classical operations" of Prop. 8.34 are, by its proof, those of Prop. 7.29 preparing the QRAM data
structures for `Ĉ`). Each instruction reads earlier values by index and appends one value; each
counts as one operation: `+, −, ×, ÷, √, arccos`, the argument of a complex number, and rational
constants. -/
inductive MCPrepOp where
  | const (c : ℚ)
  | add (i j : ℕ)
  | sub (i j : ℕ)
  | mul (i j : ℕ)
  | div (i j : ℕ)
  | sqrt (i : ℕ)
  | arccos (i : ℕ)
  | arg (i j : ℕ)

/-- The value an instruction appends, given the values computed so far (an out-of-range index
reads `0`; `t / 0 = 0` as in Lean). `arg i j` is the argument of `vals[i] + i·vals[j]`. -/
noncomputable def MCPrepOp.value (vals : List ℝ) : MCPrepOp → ℝ
  | .const c => (c : ℝ)
  | .add i j => vals.getD i 0 + vals.getD j 0
  | .sub i j => vals.getD i 0 - vals.getD j 0
  | .mul i j => vals.getD i 0 * vals.getD j 0
  | .div i j => vals.getD i 0 / vals.getD j 0
  | .sqrt i => Real.sqrt (vals.getD i 0)
  | .arccos i => Real.arccos (vals.getD i 0)
  | .arg i j => Complex.arg ⟨vals.getD i 0, vals.getD j 0⟩

/-- All values of a straight-line program run on an input list (inputs first, then one value per
instruction). The cost of the program is its length. -/
noncomputable def mcPrepExec (Prog : List MCPrepOp) (input : List ℝ) : List ℝ :=
  Prog.foldl (fun vals g => vals ++ [g.value vals]) input

/-- The classical description of the real matrix `C ∈ ℝ^{n×n}` given to the preprocessing: its
entries row by row, `C_00, C_01, …`. -/
def mcInput {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) : List ℝ :=
  (List.ofFn fun i => List.ofFn fun j => C i j).flatten

/-- The input part of the QRAM, written classically by the preprocessing (Rem. 5.40): word `j` is
the `r`-bit binary expansion (most significant bit first) of the integer part of the program value
with index `addr j`. This is the only way the input `C` reaches the rest of the algorithm. -/
noncomputable def mcStaticWords (b r : ℕ) (Prog : List MCPrepOp) (addr : Qubits b → ℕ) {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) : Qubits b → Qubits r :=
  fun j => natToBits r ⌊(mcPrepExec Prog (mcInput C)).getD (addr j) 0⌋₊

/-- The QRAM of Prop. 8.34 holds two halves (address bit `0` selects): the input half `stat`,
written once by the preprocessing from `C` (the data structure for `Ĉ`, Prop. 7.29), and the work
half `dyn`, rewritten by the classical controller between quantum runs (the diagonal matrix `D` of
Lem. 8.33, "stored in QRAM and queried at unit cost", p.204). -/
def mcSplitWords (b r : ℕ) (stat dyn : Qubits b → Qubits r) : Qubits (b + 1) → Qubits r :=
  fun j => if j 0 then dyn (Fin.tail j) else stat (Fin.tail j)

/-- The state before measurement of one quantum run of the hybrid algorithm: the circuit, over
two-qubit gates ("additional gates") and calls to the QRAM (any orientation, possibly controlled),
applied to `|0⟩` on `m` qubits. -/
noncomputable def mcRoundState {m b r : ℕ}
    (circ : OracleCircuit twoQubitGateSet (fun _ : Fin 1 => (b + 1) + r) m)
    (stat dyn : Qubits b → Qubits r) : EuclideanSpace ℂ (Qubits m) :=
  act (circ.unitary fun _ => mcQram (b + 1) r (mcSplitWords b r stat dyn)) (zeroKet m)

/-- The probability of the measurement record `h` (outcome `h k` of the full computational-basis
measurement in run `k`) of a hybrid algorithm with `R` runs. The circuit and the work-QRAM
contents of run `k` are chosen by the classical controller from the outcomes of runs `0, …, k−1`
only. -/
noncomputable def mcHistProb {m b r R : ℕ}
    (circ : (k : ℕ) → (Fin k → Qubits m) →
      OracleCircuit twoQubitGateSet (fun _ : Fin 1 => (b + 1) + r) m)
    (dyn : (k : ℕ) → (Fin k → Qubits m) → Qubits b → Qubits r) (stat : Qubits b → Qubits r)
    (h : Fin R → Qubits m) : ℝ :=
  ∏ k : Fin R, prob (mcRoundState (circ k fun i => h ⟨i, i.isLt.trans k.isLt⟩) stat
    (dyn k fun i => h ⟨i, i.isLt.trans k.isLt⟩)) (h k)

/-- The quantum cost along the measurement record `h`: the total number of QRAM accesses plus
additional gates of the `R` circuits actually run. -/
def mcHistCost {m b r R : ℕ}
    (circ : (k : ℕ) → (Fin k → Qubits m) →
      OracleCircuit twoQubitGateSet (fun _ : Fin 1 => (b + 1) + r) m)
    (h : Fin R → Qubits m) : ℕ :=
  ∑ k : Fin R, ((circ k fun i => h ⟨i, i.isLt.trans k.isLt⟩).queryCount 0 +
    (circ k fun i => h ⟨i, i.isLt.trans k.isLt⟩).gateCount)

/-- The probability that the measurement record satisfies `Good`. -/
noncomputable def mcSuccessProb {m b r R : ℕ}
    (circ : (k : ℕ) → (Fin k → Qubits m) →
      OracleCircuit twoQubitGateSet (fun _ : Fin 1 => (b + 1) + r) m)
    (dyn : (k : ℕ) → (Fin k → Qubits m) → Qubits b → Qubits r) (stat : Qubits b → Qubits r)
    (Good : (Fin R → Qubits m) → Prop) : ℝ :=
  open Classical in
  ∑ h : Fin R → Qubits m, if Good h then mcHistProb circ dyn stat h else 0

/-- The solution "determined" by the algorithm, in the source's representation (Rem. 8.27,
p.200: the iterates are kept classically as Hamiltonians, never as explicit matrices; Lem. 8.33,
p.204: `H = y_1 Ĉ + y_2 D` with `D` diagonal): a list of pairs `(y, d)` stands for the average of
the Gibbs states `exp(y_1 Ĉ + y_2 diag(d)) / Tr(⋯)` (Def. 7.34, frozen `gibbsState`), `Ĉ` being the
true normalized input. The empty list stands for the zero matrix, which is not a solution. -/
noncomputable def mcGibbsMixture {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (L : List ((Fin 2 → ℝ) × (Fin n → ℝ))) : Matrix (Fin n) (Fin n) ℂ :=
  ((L.length : ℂ))⁻¹ • (L.map fun p => gibbsState (((p.1 0 : ℝ) : ℂ) • cHat (C.map ((↑) : ℝ → ℂ)) +
    ((p.1 1 : ℝ) : ℂ) • Matrix.diagonal fun j => ((p.2 j : ℝ) : ℂ))).sum

/-- A solution of (MaxCutSDP) (p.199) with optimality and feasibility tolerance `ϵ`: a density
matrix `ρ` (the constraints `Tr ρ = 1`, `ρ ⪰ 0` are kept exactly, p.200) whose diagonal is within
`ϵ` of `(1/n)𝟙` in `ℓ₁` (the norm of `f_γ`, Eq. (8.26)) and whose objective `Tr(Ĉρ)` is within `ϵ`
of the optimum, i.e. of `Tr(Ĉσ)` for every feasible `σ` (density matrix with `diag(σ) = (1/n)𝟙`). -/
def IsMaxCutSDPSolution {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (ρ : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  IsDensityMatrix ρ ∧ ∑ j, |(ρ j j).re - (n : ℝ)⁻¹| ≤ ε ∧
    ∀ σ : Matrix (Fin n) (Fin n) ℂ, IsDensityMatrix σ → (∀ j, σ j j = ((n : ℂ))⁻¹) →
      (cHat (C.map ((↑) : ℝ → ℂ)) * σ).trace.re - ε ≤ (cHat (C.map ((↑) : ℝ → ℂ)) * ρ).trace.re

example {m b r : ℕ}
    (circ : (k : ℕ) → (Fin k → Qubits m) →
      OracleCircuit twoQubitGateSet (fun _ : Fin 1 => (b + 1) + r) m)
    (dyn : (k : ℕ) → (Fin k → Qubits m) → Qubits b → Qubits r) (stat : Qubits b → Qubits r)
    (h : Fin 0 → Qubits m) : mcHistProb circ dyn stat h = 1 := by
  simp [mcHistProb]

example (b r : ℕ) (stat dyn : Qubits b → Qubits r) (j : Qubits b) :
    mcSplitWords b r stat dyn (Fin.cons false j) = stat j := by
  simp [mcSplitWords]


end QAlgorithms.Nannicini


