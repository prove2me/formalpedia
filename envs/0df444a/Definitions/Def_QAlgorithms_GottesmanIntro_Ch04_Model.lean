-- Prove2me | Definitions.Def_QAlgorithms_GottesmanIntro_Ch04_Model
-- name    : QAlgorithms_GottesmanIntro_Ch04_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:58:40.343105+00:00
-- url     : https://prove2.me/theorems/b4008cae-c718-44f9-8be7-ed3deb034011
-- title:
--   GottesmanIntro Ch04: supporting definitions
-- statement:
--   Gottesman, *An introduction to quantum error correction*, §4.4: Steane error correction
--
--   ## QAlgorithms.GottesmanIntro.transCnot
--
--   For every natural number $n$, this is the complex matrix on pairs of $n$-bit strings with entry at row $(y,z)$ and column $(u,v)$ equal to the product over $0\leq i<n$ of the two-bit CNOT entry. Thus the entry is $1$ exactly when $y=u$ and $z_i=v_i\mathbin{\mathrm{xor}}u_i$ for every coordinate, and otherwise $0$. At $n=0$ the empty product is $1$ and the matrix has its unique entry equal to $1$.
--
--   ## QAlgorithms.GottesmanIntro.ActsWithinPair
--
--   For every natural number $n$, finite subset $g$ of the $n$ coordinate indices, and arbitrary complex matrix $G$ indexed by pairs of $n$-bit strings, this holds precisely when there exists a complex matrix $G'$ indexed by $2n$-bit strings such that $G((y,z),(u,v))=G'(y\Vert z,u\Vert v)$ and $G'$ acts within the coordinate set $F=\{i:i\in g\}\cup\{n+i:i\in g\}$. Here acting within $F$ means that there exist a natural number $k$, an injection $w:\{0,\ldots,k-1\}\to\{0,\ldots,2n-1\}$ with image contained in $F$, and an arbitrary matrix $M$ on $k$-bit strings such that $G'(a,b)=M(a\circ w,b\circ w)$ when $a,b$ agree outside the image of $w$, and $0$ otherwise. Unitarity is not required. Empty $g$, including $n=0$, allows $k=0$, hence scalar multiples of the identity.
--
--   ## QAlgorithms.GottesmanIntro.liftDataPhase
--
--   For any natural number $n$, any type $R$ with decidable equality, and any complex matrix $M$ on pairs of $n$-bit strings, this defines a matrix on indices $((d,r),(a,b))$. Its entry from column $((d',r'),(a',b'))$ to row $((d,r),(a,b))$ is $M((d,a),(d',a'))$ if $r=r'$ and $b=b'$, and is $0$ otherwise. There is no finiteness assumption on $R$ and no unitarity assumption on $M$; $n=0$ and empty $R$ are included.
--
--   ## QAlgorithms.GottesmanIntro.liftDataBit
--
--   For any natural number $n$, any type $R$ with decidable equality, and any complex matrix $M$ on pairs of $n$-bit strings, this defines a matrix on indices $((d,r),(a,b))$. Its entry from column $((d',r'),(a',b'))$ to row $((d,r),(a,b))$ is $M((d,b),(d',b'))$ if $r=r'$ and $a=a'$, and is $0$ otherwise. There is no finiteness assumption on $R$ and no unitarity assumption on $M$; $n=0$ and empty $R$ are included.
--
--   ## QAlgorithms.GottesmanIntro.steaneECOutput
--
--   For any natural number $n$, finite type $R$ with decidable equality, binary linear subspaces $C_1,C_2\subseteq\mathbb F_2^n$, arbitrary functions $\mathrm{dec}_P,\mathrm{dec}_B:\mathbb F_2^n\to\mathbb F_2^n$, arbitrary complex matrices $F_P,F_B,H_P,H_B$ on $n$-bit strings and $G_P,G_B$ on pairs of such strings, arbitrary vector $\psi$ on $(n\text{-bit strings})\times R$, and arbitrary $w_P,w_B\in\mathbb F_2^n$, this defines the following vector on the data and reference indices. Let $|v\rangle$ mean the basis vector corresponding to the Boolean string with true bits precisely where $v_i=1$, let $C_2^\perp=\{v:\sum_i c_iv_i=0\text{ for all }c\in C_2\}$, and initialize $s_0=\psi\otimes F_P\sum_{v\in C_2^\perp}|v\rangle\otimes F_B\sum_{u\in C_1}|u\rangle$. First apply $G_P$ after the map $(d,a)\mapsto(d\mathbin{\mathrm{xor}}a,a)$ on data and the first ancillary register, leaving $R$ and the second register fixed, to obtain $s_1$. Then apply $G_B$ after $(d,b)\mapsto(d,b\mathbin{\mathrm{xor}}d)$ on data and the second ancillary register, leaving $R$ and the first register fixed, to obtain $s_2$. Obtain $s_3$ by applying $H_PH^{\otimes n}$ to the first ancillary register and $H_B$ to the second, leaving data and $R$ fixed, where $H_{xy}=2^{-1/2}(-1)^{xy}$. Extract the vector $v(d,r)=s_3((d,r),(\mathrm{bits}(w_P),\mathrm{bits}(w_B)))$, and return $(\bigotimes_i Z^{(\mathrm{dec}_P(w_P))_i}X^{(\mathrm{dec}_B(w_B))_i}\otimes I_R)v$, with $X$ flipping a bit and $Z$ multiplying a true bit by $-1$. The ancillary sums and the extracted vector are not normalized, no assumptions relating $C_1,C_2$ or constraining the supplied maps, matrices, or vector are imposed, and $n=0$ and empty $R$ are included.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/GottesmanIntro/Ch04.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_BinaryStabilizer
/-!
# Gottesman, *An introduction to quantum error correction*, §4.4: Steane error correction

D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum
computation* (arXiv:0904.2557), cited "Gottesman intro p.N" (PDF pages): Claim 1 (p.28), inside
the proof that Steane error correction satisfies property EC A.

The Steane EC circuit (p.27, Figure 3) is needed only here, so it is a chunk-local definition.
The joint register is indexed by `(Qubits n × R) × (Qubits n × Qubits n)`: the data block with a
reference system `R` (the data may be entangled with it), then the phase ancilla block and the
bit-flip ancilla block. Qubit `i` of every block is wire `i`.
-/

namespace QAlgorithms.GottesmanIntro

/-- Transversal CNOT between two `n`-qubit blocks (Gottesman intro p.27, Figure 3): the frozen
two-qubit `cnot` applied to qubit `i` of both blocks for every `i`; the first block is the
control, the second the target, i.e. `|c, t⟩ ↦ |c, t ⊕ c⟩`. -/
def transCnot (n : ℕ) : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ :=
  Matrix.of fun p q => ∏ i : Fin n, cnot (p.1 i, p.2 i) (q.1 i, q.2 i)

/-- An operator on two `n`-qubit blocks acts only on qubit `i` of both blocks for `i ∈ g`
(Gottesman intro p.28: "each such faulty gate location can affect both the corresponding data
qubit and ancilla qubit"): read as an operator on `n + n` qubits (first block = first `n`
wires), it acts within the wires `{i, n + i : i ∈ g}`. -/
def ActsWithinPair {n : ℕ} (g : Finset (Fin n))
    (G : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ) : Prop :=
  ∃ G' : Matrix (Qubits (n + n)) (Qubits (n + n)) ℂ,
    ActsWithin (g.image (Fin.castAdd n) ∪ g.image (Fin.natAdd n)) G' ∧
      G = G'.submatrix (qubitsAppendEquiv n n).symm (qubitsAppendEquiv n n).symm

/-- An operator on (data block, phase ancilla block), lifted to the joint register (identity on
the reference and on the bit-flip ancilla). -/
def liftDataPhase {n : ℕ} {R : Type*} [DecidableEq R]
    (M : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ) :
    Matrix ((Qubits n × R) × (Qubits n × Qubits n)) ((Qubits n × R) × (Qubits n × Qubits n)) ℂ :=
  Matrix.of fun p q =>
    if p.1.2 = q.1.2 ∧ p.2.2 = q.2.2 then M (p.1.1, p.2.1) (q.1.1, q.2.1) else 0

/-- An operator on (data block, bit-flip ancilla block), lifted to the joint register (identity
on the reference and on the phase ancilla). -/
def liftDataBit {n : ℕ} {R : Type*} [DecidableEq R]
    (M : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ) :
    Matrix ((Qubits n × R) × (Qubits n × Qubits n)) ((Qubits n × R) × (Qubits n × Qubits n)) ℂ :=
  Matrix.of fun p q =>
    if p.1.2 = q.1.2 ∧ p.2.1 = q.2.1 then M (p.1.1, p.2.2) (q.1.1, q.2.2) else 0

/-- The (unnormalized) data ⊗ reference state after faulty Steane error correction on the CSS
code of `C1, C2` (Gottesman intro p.27–28), in the branch where the phase ancilla gives outcome
`wP` and the bit-flip ancilla outcome `wB`:

1. the phase ancilla is the encoded `|0⟩ = Σ_{w ∈ C2⊥} |w⟩` with the preparation errors `FP`,
   the bit-flip ancilla the encoded `|0⟩ + |1⟩ = Σ_{u ∈ C1} |u⟩` with the preparation errors
   `FB`; the incoming data ⊗ reference vector is `ψ`;
2. transversal CNOT with the phase ancilla as control and the data as target, followed by the
   CNOT faults `GP` on (data, phase ancilla);
3. transversal CNOT with the data as control and the bit-flip ancilla as target, followed by the
   CNOT faults `GB` on (data, bit-flip ancilla);
4. transversal Hadamard on the phase ancilla, then the faults `HP` (Hadamard and measurement of
   the phase ancilla) and `HB` (measurement of the bit-flip ancilla);
5. both ancillas measured in the standard basis, projected on outcomes `wP`, `wB`;
6. the classical decoders give `d = decP wP` (as a `C2` word with errors) and `decB wB` (as a
   `C1` word with errors), and the correction `Z` on the qubits of `decP wP` and `X` on the
   qubits of `decB wB` is applied to the data (fault-free, p.28). -/
noncomputable def steaneECOutput {n : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (C1 C2 : Submodule (ZMod 2) (Fin n → ZMod 2))
    (decP decB : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (FP FB HP HB : Matrix (Qubits n) (Qubits n) ℂ)
    (GP GB : Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ)
    (ψ : EuclideanSpace ℂ (Qubits n × R)) (wP wB : Fin n → ZMod 2) :
    EuclideanSpace ℂ (Qubits n × R) :=
  let s0 := tensorVec ψ (tensorVec (act FP (cssZeroState C2)) (act FB (cssPlusState C1)))
  let s1 := act (liftDataPhase (R := R) (GP * (transCnot n).submatrix Prod.swap Prod.swap)) s0
  let s2 := act (liftDataBit (R := R) (GB * transCnot n)) s1
  let s3 := act (Matrix.kronecker (1 : Matrix (Qubits n × R) (Qubits n × R) ℂ)
    (Matrix.kronecker (HP * hadamardN n) HB)) s2
  let v : EuclideanSpace ℂ (Qubits n × R) :=
    WithLp.toLp 2 fun p => s3 (p, (bitsOfZMod wP, bitsOfZMod wB))
  act (Matrix.kronecker (rowPauli (decB wB) (decP wP)) (1 : Matrix R R ℂ)) v


end QAlgorithms.GottesmanIntro


