-- Prove2me | Definitions.Def_EntanglingOps_BinaryPhase_Model
-- name    : EntanglingOps_BinaryPhase_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:28:33.014003+00:00
-- url     : https://prove2.me/theorems/a7c495cb-2d1a-4e4a-ba26-2a3a35ca8b29
-- title:
--   Eqs. (1), (4)–(5), (9)–(13), pp. 1–3 — Kraus maps and their operator E, Pauli labels, U(α), ψ_α, Bell basis, step Kraus operators, the N-step protocol, E(ψ), f_N, f_∞
-- statement:
--   The objects of the mission: the operator of a completely positive map (general dimension $d$), and the two-qubit gates, resource states, Bell measurements and multi-step protocol of p. 3.
--
--   **General $d$ (Eqs. (1), (4), (5), p. 2).** Each of the systems $A_1,A_2,A_3,B_1,B_2,B_3$ is $\mathbb C^d$ with the computational basis $S=\{|i\rangle\}$.
--
--   1. $|\Phi\rangle = d^{-1/2}\sum_{i}|i\rangle|i\rangle$ and $P=|\Phi\rangle\langle\Phi|$ (Eq. (5)).
--   2. A completely positive map on $A_1B_1$ is given by a finite Kraus family, $\mathcal E(\rho)=\sum_k O_k\rho O_k^\dagger$ (Eq. (1)).
--   3. Its operator (Eq. (4)) is
--   $$E_{A_1A_2,B_1B_2}=\sum_k (O_k\otimes\mathbb 1_{A_2B_2})\,(P_{A_1A_2}\otimes P_{B_1B_2})\,(O_k\otimes\mathbb 1_{A_2B_2})^\dagger ,$$
--   an operator on $\mathcal H_A\otimes\mathcal H_B$ with $\mathcal H_A=\mathcal H_{A_1}\otimes\mathcal H_{A_2}$, $\mathcal H_B=\mathcal H_{B_1}\otimes\mathcal H_{B_2}$.
--   4. $P_{A_2A_3}P_{B_2B_3}$ is $P\otimes P$ on $A_2A_3B_2B_3$, regrouped as an operator on $(A_2B_2)(A_3B_3)$.
--
--   **Qubits (Eqs. (9)–(10), p. 3).**
--
--   1. Pauli operators $\sigma_{1,1}=\mathbb 1$, $\sigma_{1,2}=\sigma_x$, $\sigma_{2,1}=\sigma_y$, $\sigma_{2,2}=\sigma_z$.
--   2. $\alpha_N=\pi/2^N$ and the gate $U(\alpha)=e^{-i\alpha\,\sigma_x^{A_1}\otimes\sigma_x^{B_1}}$ (matrix exponential), for every real $\alpha$.
--   3. The Bell vectors $|\Phi^+\rangle=(|00\rangle+|11\rangle)/\sqrt2$, $|\Psi^+\rangle=(|01\rangle+|10\rangle)/\sqrt2$ and the resource state of Eq. (10),
--   $$|\psi_\beta\rangle=\cos\beta\,|\Phi^+\rangle_{A_1A_2}|\Phi^+\rangle_{B_1B_2}-i\sin\beta\,|\Psi^+\rangle_{A_1A_2}|\Psi^+\rangle_{B_1B_2}.$$
--   4. The Bell basis $|\Psi_{i_1,i_2}\rangle=(\mathbb 1\otimes\sigma_{i_1,i_2})|\Phi\rangle$ on $A_2A_3$ (and on $B_2B_3$), with $|\Phi\rangle$ of Eq. (5).
--   5. **One step** with resource $|\psi_\beta\rangle$ and outcome $(i,j)$ (Alice's label on $A_2A_3$, Bob's on $B_2B_3$): the operator from $A_3B_3$ to $A_1B_1$ obtained by projecting $A_2A_3$ onto $|\Psi_i\rangle$ and $B_2B_3$ onto $|\Psi_j\rangle$ and then applying $\sigma_i$ to $A_1$ and $\sigma_j$ to $B_1$:
--   $$K_\beta(i,j)=(\sigma_i\otimes\sigma_j)\,\big(\langle\Psi_i|_{A_2A_3}\langle\Psi_j|_{B_2B_3}\big)\,|\psi_\beta\rangle_{A_1A_2B_1B_2}.$$
--   The step succeeds when $i_1=j_1$.
--   6. **The protocol.** Step $k$ ($k=1,\dots,N$) uses $|\psi_{2^{k-1}\alpha_N}\rangle$. A history $(o_1,\dots,o_m)$ of outcomes has the operator $K_{2^{m-1}\alpha_N}(o_m)\cdots K_{\alpha_N}(o_1)$. The terminal histories are those whose first $m-1$ outcomes fail and whose last outcome succeeds or is the outcome of step $N$. The probability that step $k$ is performed on an input $\rho$ is $\sum\operatorname{Re}\operatorname{Tr}(K\rho K^\dagger)$ over the histories of $k-1$ failing outcomes.
--   7. **Cost.** The entropy of entanglement $E(\psi)$ of a pure state on $A_1A_2B_1B_2$ is the von Neumann entropy (base 2) of $\operatorname{tr}_{B_1B_2}|\psi\rangle\langle\psi|$ (Eq. (11)). Then
--   $$f_N=\frac1\pi\sum_{k=1}^N2^kE(\psi_{\alpha_k}),\qquad f_\infty=\frac1\pi\sum_{k=1}^\infty2^kE(\psi_{\alpha_k}),$$
--   $\bar E[U(\alpha_N)]=\sum_{k=1}^N P(\text{step }k)\,E(\psi_{2^{k-1}\alpha_N})$ (Eq. (12)), and the average communication in each direction is $\sum_{k=1}^{N-1}P(\text{step }k)$ (one bit per step; step $N$ implements the local gate $U(\pi/2)$, footnote [20]).
--
--   These are the objects every statement of the mission is about. Nothing in the protocol is defined through the gate $U$: the step operators are the literal contractions, and the probabilities are computed from them.
--
--   **Formalization Note** All labels and steps are 0-based (`Fin 2 × Fin 2`; list position $s$ is the paper's step $s+1$). Two-system operators are matrices on product index types in Mathlib's Kronecker convention. The resource is indexed $((a_1,a_2),(b_1,b_2))$, so `WildeQIT.partialTraceRight` traces $B_1B_2$; the step operator has rows $(a_1,b_1)$ and columns $(a_3,b_3)$. `regroup` is `Equiv.prodProdProdComm`, $((x_1,x_2),(y_1,y_2))\mapsto((x_1,y_1),(x_2,y_2))$. The entropy is `QAlgorithms.vnEntropy` (bits). `fInf` is a `tsum`; every statement about it asserts summability. The undefined $|\Psi\rangle$ of the Bell basis is read as $|\Phi\rangle$ of Eq. (5).
-- source:
--   Cirac, Dür, Kraus, Lewenstein, Entangling operations and their implementation using a small amount of entanglement, arXiv:quant-ph/0007057v1, p. 1, Eq. (1); p. 2, Eqs. (4)–(5); p. 3, Eqs. (9)–(13) and the protocol paragraph; footnote [20], p. 4

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_QAlgorithms_Defs_Ensemble

namespace EntanglingOps.BinaryPhase

open Matrix
open scoped Kronecker

noncomputable section

/-! ### The operator of a completely positive map, Eqs. (1), (4)–(5), p. 2 (general `d`)

Each of the systems A₁, A₂, A₃, B₁, B₂, B₃ is `ℂ^d` with computational basis `Fin d`
(the paper's `S = {|i⟩}_{i=1}^d`, 0-based). A two-system operator is a matrix indexed by a
product type in Mathlib's Kronecker convention (`⊗ₖ`, first factor first). -/

/-- Eq. (5), p. 2: the maximally entangled vector `|Φ⟩ = d^{-1/2} ∑_i |i⟩|i⟩` on `ℂ^d ⊗ ℂ^d`,
indexed `(x, y)`. -/
def phiVec (d : ℕ) : Fin d × Fin d → ℂ :=
  fun p => if p.1 = p.2 then ((Real.sqrt d)⁻¹ : ℂ) else 0

/-- Eq. (5), p. 2: the projector `P = |Φ⟩⟨Φ|`. -/
def projPhi (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  vecMulVec (phiVec d) (star (phiVec d))

/-- The index permutation `((x₁, x₂), (y₁, y₂)) ↦ ((x₁, y₁), (x₂, y₂))`. With `x = A`-systems and
`y = B`-systems it carries the grouping `(A₁A₂)(B₁B₂)` to `(A₁B₁)(A₂B₂)`; it is Mathlib's
`Equiv.prodProdProdComm`. -/
def regroup (d : ℕ) : (Fin d × Fin d) × (Fin d × Fin d) ≃ (Fin d × Fin d) × (Fin d × Fin d) :=
  Equiv.prodProdProdComm (Fin d) (Fin d) (Fin d) (Fin d)

/-- Eq. (1), p. 1: the completely positive map `ℰ(ρ) = ∑_k O_k ρ O_k†` on `A₁B₁` given by a finite
Kraus family `O`, each `O_k` indexed `(a₁, b₁)`. -/
def krausMap {κ : Type} [Fintype κ] {d : ℕ}
    (O : κ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (ρ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ∑ k, O k * ρ * (O k)ᴴ

/-- `P_{A₂A₃} P_{B₂B₃}`, i.e. `P_{A₂A₃} ⊗ P_{B₂B₃}`, as an operator indexed
`((a₂, b₂), (a₃, b₃))` (the systems `A₂B₂` first, then `A₃B₃`). -/
def projPhiPair (d : ℕ) :
    Matrix ((Fin d × Fin d) × (Fin d × Fin d)) ((Fin d × Fin d) × (Fin d × Fin d)) ℂ :=
  reindex (regroup d) (regroup d) (projPhi d ⊗ₖ projPhi d)

/-- Eq. (4), p. 2: the operator `E_{A₁A₂,B₁B₂} = ℰ(P_{A₁A₂} ⊗ P_{B₁B₂})` of the map `ℰ` with Kraus
family `O`, where `ℰ` acts on `A₁B₁` and as the identity on `A₂B₂`:
`E = ∑_k (O_k ⊗ 𝟙_{A₂B₂}) (P_{A₁A₂} ⊗ P_{B₁B₂}) (O_k ⊗ 𝟙_{A₂B₂})†`, computed on the grouping
`((a₁, b₁), (a₂, b₂))` and returned on the grouping `((a₁, a₂), (b₁, b₂))` of `ℋ_A ⊗ ℋ_B`. -/
def choiOp {κ : Type} [Fintype κ] {d : ℕ}
    (O : κ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix ((Fin d × Fin d) × (Fin d × Fin d)) ((Fin d × Fin d) × (Fin d × Fin d)) ℂ :=
  ∑ k, reindex (regroup d).symm (regroup d).symm
    ((O k ⊗ₖ (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) *
      reindex (regroup d) (regroup d) (projPhi d ⊗ₖ projPhi d) *
      (O k ⊗ₖ (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ))ᴴ)

/-! ### Qubits: Pauli operators, the gates (9) and the resource states (10), p. 3 -/

/-- The paper's `σ_{i₁,i₂}` (p. 3), with the 1-based labels `(i₁, i₂) ∈ {1,2}²` shifted to
0-based `Fin 2 × Fin 2`: `(0,0) ↦ 𝟙 = σ_{1,1}`, `(0,1) ↦ σ_x = σ_{1,2}`, `(1,0) ↦ σ_y = σ_{2,1}`,
`(1,1) ↦ σ_z = σ_{2,2}`. -/
def pauli : Fin 2 × Fin 2 → Matrix (Fin 2) (Fin 2) ℂ
  | (0, 0) => !![1, 0; 0, 1]
  | (0, 1) => !![0, 1; 1, 0]
  | (1, 0) => !![0, -Complex.I; Complex.I, 0]
  | (1, 1) => !![1, 0; 0, -1]

/-- `σ_x`. -/
def sx : Matrix (Fin 2) (Fin 2) ℂ := pauli (0, 1)

/-- Eq. (9), p. 3: `α_N = π / 2^N`. -/
def alphaN (N : ℕ) : ℝ := Real.pi / 2 ^ N

/-- Eq. (9), p. 3: the two-qubit gate `U(α) = exp(−i α σ_x^{A₁} ⊗ σ_x^{B₁})` (matrix exponential),
indexed `(a₁, b₁)`. The paper's gate is `U(α_N)`; `U(α)` is defined for every real `α`. -/
def gate (α : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  NormedSpace.exp ((-(Complex.I * (α : ℂ))) • (sx ⊗ₖ sx))

/-- The Bell vector `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` (p. 3), indexed `(x, y)`. -/
def phiPlus : Fin 2 × Fin 2 → ℂ :=
  fun p => if p.1 = p.2 then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0

/-- The Bell vector `|Ψ⁺⟩ = (|01⟩ + |10⟩)/√2` (p. 3), indexed `(x, y)`. -/
def psiPlus : Fin 2 × Fin 2 → ℂ :=
  fun p => if p.1 = p.2 then 0 else ((1 / Real.sqrt 2 : ℝ) : ℂ)

/-- Eq. (10), p. 3, as printed: the resource state on `A₁A₂B₁B₂`,
`|ψ_β⟩ = cos β |Φ⁺⟩_{A₁A₂}|Φ⁺⟩_{B₁B₂} − i sin β |Ψ⁺⟩_{A₁A₂}|Ψ⁺⟩_{B₁B₂}`,
indexed `((a₁, a₂), (b₁, b₂))` (so the cut `(A₁A₂)|(B₁B₂)` is the outer product). The paper's
`|ψ_{α_N}⟩` is `resource (alphaN N)`. -/
def resource (β : ℝ) : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) → ℂ :=
  fun x => (Real.cos β : ℂ) * phiPlus x.1 * phiPlus x.2 -
    Complex.I * (Real.sin β : ℂ) * psiPlus x.1 * psiPlus x.2

/-- The Bell basis of p. 3, `|Ψ_{i₁,i₂}⟩ = 𝟙 ⊗ σ_{i₁,i₂} |Φ⟩` with `|Φ⟩` of Eq. (5) at `d = 2`
(`= |Φ⁺⟩`), on the pair `A₂A₃` (or `B₂B₃`), indexed `(x₂, x₃)`:
`bellVec i (x₂, x₃) = ∑_y (σ_i)_{x₃ y} Φ⁺(x₂, y)`. -/
def bellVec (i : Fin 2 × Fin 2) : Fin 2 × Fin 2 → ℂ :=
  fun x => ∑ y : Fin 2, pauli i x.2 y * phiPlus (x.1, y)

/-- An outcome of one step of the protocol: Alice's Bell label `i` (on `A₂A₃`) and Bob's Bell
label `j` (on `B₂B₃`). -/
abbrev Outcome := (Fin 2 × Fin 2) × (Fin 2 × Fin 2)

/-- The step succeeds when `i₁ = j₁` (p. 3, case (i)); with 0-based labels, `o.1.1 = o.2.1`. -/
def succeeds (o : Outcome) : Prop := o.1.1 = o.2.1

instance : DecidablePred succeeds := fun o => inferInstanceAs (Decidable (o.1.1 = o.2.1))

/-- One step of the protocol of p. 3 with resource `|ψ_β⟩` on `A₁A₂B₁B₂` and outcome `(i, j)`,
as a (non-normalized) Kraus operator from the input `A₃B₃` (columns `(a₃, b₃)`) to the output
`A₁B₁` (rows `(a₁, b₁)`): project `A₂A₃` onto `|Ψ_i⟩` and `B₂B₃` onto `|Ψ_j⟩`, then apply
`σ_i` to `A₁` and `σ_j` to `B₁`. The contraction is
`M_{(a₁,b₁),(a₃,b₃)} = ∑_{a₂,b₂} conj(Ψ_i(a₂,a₃)) conj(Ψ_j(b₂,b₃)) ψ_β((a₁,a₂),(b₁,b₂))`
and the step operator is `(σ_i ⊗ σ_j) M`. -/
def stepKraus (β : ℝ) (i j : Fin 2 × Fin 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (pauli i ⊗ₖ pauli j) *
    Matrix.of fun (r c : Fin 2 × Fin 2) =>
      ∑ a₂ : Fin 2, ∑ b₂ : Fin 2,
        star (bellVec i (a₂, c.1)) * star (bellVec j (b₂, c.2)) * resource β ((r.1, a₂), (r.2, b₂))

/-- Auxiliary for `branchKraus`: the product of the step operators of a history `l` whose first
entry is the outcome of the 0-based step `m`, which uses `|ψ_{2^m α_N}⟩`. -/
def branchKrausFrom (N : ℕ) : ℕ → List Outcome → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ
  | _, [] => 1
  | m, o :: l => branchKrausFrom N (m + 1) l * stepKraus (2 ^ m * alphaN N) o.1 o.2

/-- The Kraus operator of a protocol history `l = [o₀, …, o_m]` (p. 3): the 0-based step `s`
(the paper's step `s + 1`) uses `|ψ_{2^s α_N}⟩` and has outcome `o_s`, and later steps act on the
left: `branchKraus N l = K_{2^m α_N}(o_m) ⋯ K_{α_N}(o₀)`. -/
def branchKraus (N : ℕ) (l : List Outcome) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  branchKrausFrom N 0 l

/-- The histories of `k` failing outcomes (`k` steps performed, all with `i₁ ≠ j₁`); after such a
history the paper's step `k + 1` is performed. -/
def failing (k : ℕ) : Finset (List Outcome) :=
  (Finset.univ.filter fun f : Fin k → Outcome => ∀ s, ¬ succeeds (f s)).image List.ofFn

/-- The terminal histories of the `N`-step protocol (p. 3): `k` failing outcomes followed by one
more outcome, which either succeeds or is the outcome of the last step `N` (`k + 1 = N`), for
`0 ≤ k < N`. -/
def terminal (N : ℕ) : Finset (List Outcome) :=
  (Finset.range N).biUnion fun k =>
    (failing k ×ˢ Finset.univ.filter fun o => succeeds o ∨ k + 1 = N).image
      fun p => p.1 ++ [p.2]

/-- The probability that the paper's (1-based) step `k` has to be performed on the input `ρ`
(on `A₃B₃`): the total weight `∑ Re Tr(K ρ K†)` of the histories of `k − 1` failing outcomes. -/
def reachProb (N : ℕ) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (k : ℕ) : ℝ :=
  ∑ l ∈ failing (k - 1), (Matrix.trace (branchKraus N l * ρ * (branchKraus N l)ᴴ)).re

/-- Eq. (11), p. 3: the entropy of entanglement (in bits) of a pure state `ψ` on `A₁A₂B₁B₂` across
the cut `(A₁A₂)|(B₁B₂)`: the von Neumann entropy of `tr_{B₁B₂} |ψ⟩⟨ψ|`. -/
def entEntropy (ψ : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) → ℂ) : ℝ :=
  QAlgorithms.vnEntropy (WildeQIT.partialTraceRight (vecMulVec ψ (star ψ)))

/-- Eq. (13), p. 3: `f_N = (1/π) ∑_{k=1}^N 2^k E(ψ_{α_k})`. -/
def fN (N : ℕ) : ℝ :=
  (1 / Real.pi) * ∑ k ∈ Finset.Icc 1 N, (2 : ℝ) ^ k * entEntropy (resource (alphaN k))

/-- Eq. (13), p. 3: `f_∞ = (1/π) ∑_{k=1}^∞ 2^k E(ψ_{α_k})` (the series is indexed from `0` with
`k + 1` in place of `k`; statements about `fInf` assert summability). -/
def fInf : ℝ :=
  (1 / Real.pi) * ∑' k : ℕ, (2 : ℝ) ^ (k + 1) * entEntropy (resource (alphaN (k + 1)))

/-- Eq. (12), p. 3: the average entanglement `Ē[U(α_N)]` consumed by the protocol on the input
`ρ`: the sum over the paper's steps `k = 1, …, N` of the probability that step `k` is performed
times the entanglement of its resource `|ψ_{2^{k−1} α_N}⟩`. -/
def avgEnt (N : ℕ) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, reachProb N ρ k * entEntropy (resource (2 ^ (k - 1) * alphaN N))

/-- p. 3 and footnote [20], p. 4: the average number of classical bits sent in each direction,
one per performed step `k = 1, …, N − 1` (step `N`, which implements the local gate
`U(2^{N−1} α_N) = U(π/2)`, needs no communication). -/
def avgComm (N : ℕ) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (N - 1), reachProb N ρ k

end

end EntanglingOps.BinaryPhase


