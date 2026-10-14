-- Prove2me | Definitions.Def_QAlgorithms_Defs_BinaryStabilizer
-- name    : QAlgorithms_Defs_BinaryStabilizer
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:58:06.066147+00:00
-- url     : https://prove2.me/theorems/fffe10ce-c5a8-415b-bf34-2d83301de76f
-- title:
--   Binary standard form of a stabilizer and the encoding network (shared definition layer)
-- statement:
--   Binary standard form of a stabilizer and the encoding network (shared definition layer)
--
--   ### QAlgorithms.SymplecticCommuting
--
--   **Setting.** $m,n$ are natural numbers, and $H_x, H_z$ are $m\times n$ matrices over $\mathbb{F}_2$.
--
--   **Definition.** The property holds iff
--
--   $$
--   H_x H_z^{\mathsf T} + H_z H_x^{\mathsf T} = 0
--   $$
--
--   as an $m\times m$ matrix over $\mathbb{F}_2$. Entrywise, this says that for all rows $i,j$:
--
--   $$
--   \sum_{q=0}^{n-1}\big((H_x)_{iq}(H_z)_{jq} + (H_z)_{iq}(H_x)_{jq}\big) = 0 \pmod 2 .
--   $$
--
--   **Edge cases.**
--   - The diagonal conditions $i=j$ hold automatically over $\mathbb{F}_2$.
--   - The property is vacuously true when $m=0$.
--   - When $n=0$ it holds trivially, since the sums are empty.
--
--   ### QAlgorithms.IsBinaryStabilizerMatrix
--
--   **Setting.** $m,n$ are natural numbers, and $H_x,H_z$ are $m\times n$ matrices over $\mathbb{F}_2$.
--
--   **Definition.** The property holds iff both of the following hold:
--   1. **Symplectic commutation:** $H_xH_z^{\mathsf T}+H_zH_x^{\mathsf T}=0$ over $\mathbb{F}_2$.
--   2. **Row independence:** the $m$ rows of the $m\times 2n$ block matrix $[\,H_x \mid H_z\,]$ (columns of $H_x$ followed by columns of $H_z$) are linearly independent over $\mathbb{F}_2$.
--
--   **Edge cases.**
--   - Condition 2 forces $m\le 2n$ and forces every row of $[H_x\mid H_z]$ to be nonzero.
--   - For $m=0$ the property holds trivially.
--
--   ### QAlgorithms.IsStandardForm
--
--   **Setting.**
--   - $m,k,r$ are natural numbers.
--   - $H_x,H_z$ are $m\times(m+k)$ matrices over $\mathbb{F}_2$.
--   - Rows are indexed $0,\dots,m-1$ and columns $0,\dots,m+k-1$ (0-based).
--
--   **Definition.** The property holds iff all of the following hold:
--   1. $r\le m$.
--   2. For all rows $i<r$ and columns $j<r$: $(H_x)_{ij}=\delta_{ij}$. That is, the top-left $r\times r$ block of $H_x$ is the identity.
--   3. For all rows $i\ge r$ and **all** columns $j$: $(H_x)_{ij}=0$.
--   4. For all rows $i\ge r$ and columns $j$ with $r\le j<m$: $(H_z)_{ij}=\delta_{ij}$. That is, the block of $H_z$ in rows $r,\dots,m-1$ and columns $r,\dots,m-1$ is the identity.
--
--   **Unconstrained entries.** Nothing else is required:
--   - the entries of $H_x$ in rows $i<r$, columns $j\ge r$,
--   - all of $H_z$ in rows $i<r$, and
--   - the entries of $H_z$ in rows $i\ge r$, columns $j<r$ or $j\ge m$
--
--   are arbitrary.
--
--   **Not required.** Neither symplectic commutation nor row independence is required.
--
--   ### QAlgorithms.kronAll
--
--   **Setting.** $n$ is a natural number, and $M_0,\dots,M_{n-1}$ are complex $2\times 2$ matrices indexed by $\{0,1\}$.
--
--   **Definition.** $\mathrm{kronAll}(M)$ is the $2^n\times 2^n$ matrix indexed by bit strings $y,z\in\{0,1\}^n$, with
--
--   $$
--   \mathrm{kronAll}(M)_{y,z} = \prod_{q=0}^{n-1} (M_q)_{y_q,\,z_q},
--   $$
--
--   i.e. the tensor product $M_0\otimes M_1\otimes\cdots\otimes M_{n-1}$, with $M_q$ acting on wire $q$ (wire $0$ most significant).
--
--   **Edge case.** For $n=0$ it is the $1\times 1$ matrix $(1)$.
--
--   ### QAlgorithms.rowPauli
--
--   **Setting.** $n$ is a natural number, and $a,b\in\mathbb{F}_2^n$.
--
--   **Definition.** $\mathrm{rowPauli}(a,b)$ is the $2^n\times 2^n$ complex matrix
--
--   $$
--   \mathrm{rowPauli}(a,b) = \bigotimes_{q=0}^{n-1} Z^{b_q}X^{a_q},
--   \qquad\text{i.e.}\qquad
--   \mathrm{rowPauli}(a,b)_{y,z}=\prod_q \big(Z^{b_q}X^{a_q}\big)_{y_q,z_q},
--   $$
--
--   where:
--   - $X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$,
--   - $Z=\operatorname{diag}(1,-1)$ (sign $-1$ on bit $1$), and
--   - $Z^{0}=X^{0}=I$.
--
--   On each qubit the factor is the matrix product $Z$-part times $X$-part, so $X$ is applied first.
--
--   **Edge cases.**
--   - No global phase is included.
--   - When $a_q=b_q=1$, the factor is $ZX=\begin{pmatrix}0&1\\-1&0\end{pmatrix}=iY$, not $Y$.
--   - For $n=0$ the matrix is $(1)$.
--
--   ### QAlgorithms.logicalXRow
--
--   **Setting.**
--   - $m,k,r$ are natural numbers.
--   - $H_z$ is an $m\times(m+k)$ matrix over $\mathbb{F}_2$ (0-based indices).
--   - $i\in\{0,\dots,k-1\}$.
--
--   **Definition.** $\mathrm{logicalXRow}(r,H_z,i)$ is a pair $(a,b)$ of vectors in $\mathbb{F}_2^{m+k}$. Their entries, indexed by $j\in\{0,\dots,m+k-1\}$, are as follows.
--
--   The first vector $a$:
--
--   $$
--   a_j=\begin{cases}
--   (H_z)_{j,\,m+i} & \text{if } r\le j<m,\\
--   0 & \text{if } j<\min(r,m)\ \ (\text{i.e. } j<m,\ j<r),\\
--   1 & \text{if } j = m+i,\\
--   0 & \text{if } j\ge m,\ j\neq m+i.
--   \end{cases}
--   $$
--
--   The second vector $b$:
--
--   $$
--   b_j=\begin{cases}
--   \displaystyle\sum_{\substack{l=0\\ l\ge r}}^{m-1} (H_z)_{l,\,m+i}\,(H_z)_{j,\,l} \;+\; (H_z)_{j,\,m+i} & \text{if } j<r \text{ and } j<m,\\[2ex]
--   0 & \text{otherwise,}
--   \end{cases}
--   $$
--
--   with all arithmetic in $\mathbb{F}_2$. The sum runs over $l=r,\dots,m-1$, and in $(H_z)_{j,l}$ the index $l<m$ is used as a column index.
--
--   **Notes.**
--   - Only $H_z$ enters; there is no $H_x$ argument.
--   - No standard-form hypothesis on $H_z$ is assumed.
--   - If $r\ge m$, then:
--     - $a$ is the unit vector at position $m+i$, and
--     - $b_j=(H_z)_{j,m+i}$ for $j<m$ (the sum being empty), with $b_j=0$ for $j\ge m$.
--
--   ### QAlgorithms.logicalX
--
--   **Inputs.**
--   - Natural numbers $m, k, r$.
--   - A binary matrix $H_z \in \mathbb{F}_2^{m \times (m+k)}$, with rows indexed by $0,\dots,m-1$ and columns by $0,\dots,m+k-1$.
--   - An index $i \in \{0,\dots,k-1\}$.
--
--   **Output.** The $2^{m+k}\times 2^{m+k}$ complex matrix $\bar X_i$ on $m+k$ qubits. Its rows and columns are indexed by bit strings $y, z \in \{0,1\}^{m+k}$.
--
--   **The Pauli operator.** First define two vectors $a, b \in \mathbb{F}_2^{m+k}$ (given below). Then
--   $$\bar X_i = \bigotimes_{q=0}^{m+k-1} Z^{b_q} X^{a_q}, \qquad (\bar X_i)_{y,z} = \prod_{q=0}^{m+k-1} \big(Z^{b_q}X^{a_q}\big)_{y_q, z_q}.$$
--   Here $X = \begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $Z = \mathrm{diag}(1,-1)$. A power with exponent $0$ is the identity. The product $Z^{b_q}X^{a_q}$ is an ordinary matrix product, so on a vector $X$ acts first. There is no phase factor.
--
--   **The vector $a$.** For $j < m$:
--   $$a_j = \begin{cases} (H_z)_{j,\,m+i} & \text{if } r \le j,\\ 0 & \text{if } j < r.\end{cases}$$
--   For $j \ge m$: $a_j = 1$ if $j = m+i$, and $a_j = 0$ otherwise.
--
--   **The vector $b$.** For $j < \min(r, m)$, with arithmetic in $\mathbb{F}_2$:
--   $$b_j = \sum_{\substack{l=0 \\ r \le l}}^{m-1} (H_z)_{l,\,m+i}\,(H_z)_{j,\,l} \;+\; (H_z)_{j,\,m+i}.$$
--   For all other $j$ (that is, $j \ge r$ or $j \ge m$): $b_j = 0$.
--
--   **Edge cases.**
--   - No relation between $r$ and $m$ is assumed.
--   - If $r \ge m$, then $a$ is zero on the first $m$ positions, and the sum in $b_j$ is empty. So $b_j = (H_z)_{j,m+i}$ for every $j < m$.
--   - If $r = 0$, then $b = 0$.
--
--   ### QAlgorithms.stabEncodedState
--
--   **Inputs.**
--   - Natural numbers $m, k, r$.
--   - Binary matrices $H_x, H_z \in \mathbb{F}_2^{m\times(m+k)}$.
--   - A bit string $c \in \{0,1\}^k$.
--
--   **Output.** A vector $|\bar c\rangle \in \mathbb{C}^{\{0,1\}^{m+k}}$.
--
--   **Ingredients.**
--   - For each row $i$, let $g_i = \bigotimes_q Z^{(H_z)_{i,q}}X^{(H_x)_{i,q}}$. This is the phase-free Pauli operator built from row $i$ of $(H_x, H_z)$, using the same tensor-product convention as in `logicalX`.
--   - Let $\bar X_i$ be the operator `logicalX` defined above, built from $r, H_z, i$.
--
--   **Definition.**
--   $$|\bar c\rangle = (I + g_{m-1})(I+g_{m-2})\cdots(I+g_0)\;\bar X_{k-1}^{\,c_{k-1}}\cdots \bar X_1^{\,c_1}\bar X_0^{\,c_0}\;|0\cdots0\rangle.$$
--
--   **Reading the formula.**
--   - $\bar X_i^{\,1} = \bar X_i$ and $\bar X_i^{\,0} = I$.
--   - The rightmost factor is applied first. So $\bar X_0^{c_0}$ acts first on $|0^{m+k}\rangle$, and $I+g_{m-1}$ acts last.
--
--   **Edge cases.**
--   - No normalization is applied, so the result need not be a unit vector. It may even be the zero vector.
--   - No hypotheses are placed on $H_x, H_z, r$.
--   - If $m = 0$, the left product is the identity.
--   - If $k = 0$, the middle product is the identity.
--
--   ### QAlgorithms.stabEncoderGateSet
--
--   This is a set of five gates.
--
--   **Single-qubit gates (arity 1).** Each is a $2\times 2$ matrix indexed by the one bit of a 1-qubit string:
--   - the Hadamard gate
--   $$H = \tfrac{1}{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix};$$
--   - the Pauli gate $Z = \mathrm{diag}(1,-1)$.
--
--   **Two-qubit gates (arity 2).** For every pair of bits $(a,b) \neq (0,0)$, there is a gate
--   $$C(Z^bX^a) = |0\rangle\langle 0| \otimes I + |1\rangle\langle 1| \otimes Z^bX^a.$$
--   - The first qubit is the control and the second is the target.
--   - The matrix entries are $\delta_{p_1,q_1}\,(M_{p_1})_{p_2,q_2}$, where $M_0 = I$ and $M_1 = Z^bX^a$.
--   - Concretely the three gates are controlled-$X$ (when $(a,b)=(1,0)$), controlled-$Z$ (when $(a,b)=(0,1)$), and controlled-$ZX$ (when $(a,b)=(1,1)$), where
--   $$ZX = \begin{pmatrix}0&1\\-1&0\end{pmatrix}.$$
--
--   ### QAlgorithms.stabCtrlApp
--
--   **Inputs.**
--   - A number of wires $N$.
--   - Bits $a, b$ with $(a,b) \neq (0,0)$.
--   - Distinct wires $c \neq t$ in $\{0,\dots,N-1\}$.
--
--   **Output.** A gate application in an $N$-wire circuit over the gate set `stabEncoderGateSet`:
--   - The gate is the two-qubit gate $C(Z^bX^a) = |0\rangle\langle0|\otimes I + |1\rangle\langle1|\otimes Z^bX^a$.
--   - Its first qubit (the control) is placed on wire $c$.
--   - Its second qubit (the target) is placed on wire $t$.
--
--   **Effect inside a circuit.** It acts on all $N$ qubits as $C(Z^bX^a)$ on wires $(c,t)$ and as the identity on all other wires.
--
--   ### QAlgorithms.stabEncoder
--
--   **Inputs.**
--   - Natural numbers $m, k, r$.
--   - Binary matrices $H_x, H_z \in \mathbb{F}_2^{m\times(m+k)}$.
--
--   **Output.** A circuit on $m+k$ wires over `stabEncoderGateSet`. It is a list of gate applications, executed in list order (first element applied first). Each gate acts as the identity off its wires.
--
--   **Part 1** comes first in the list. For $i = 0, 1, \dots, k-1$ in increasing order, and within each $i$ for $j = 0,\dots,m-1$ in increasing order:
--   - If $r \le j$ and $(H_z)_{j,\,m+i} = 1$, append a controlled-$X$ with control wire $m+i$ and target wire $j$.
--
--   **Part 2** comes after Part 1. For $i = 0,\dots,m-1$ in increasing order:
--   - If $i \ge r$, append nothing.
--   - If $i < r$, append in this order:
--     1. a Hadamard on wire $i$;
--     2. if $(H_z)_{i,i} = 1$, a $Z$ gate on wire $i$;
--     3. for $q = 0,\dots,m+k-1$ in increasing order, a gate whenever $q \neq i$ and $\big((H_x)_{i,q},(H_z)_{i,q}\big) \neq (0,0)$. The gate is $C\big(Z^{(H_z)_{i,q}}X^{(H_x)_{i,q}}\big)$, with control wire $i$ and target wire $q$.
--
--   **Edge cases.**
--   - No hypotheses are placed on $r$, $H_x$, $H_z$.
--   - If $r = 0$, Part 2 is empty.
--   - If $r \ge m$, Part 1 is empty.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/BinaryStabilizer.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_QECC
/-!
# Binary standard form of a stabilizer and the encoding network (shared definition layer)

D. Gottesman, *Stabilizer codes and quantum error correction* (PhD thesis, 1997), cited
"Gottesman thesis p.N" (PDF pages), §§4.1–4.2, with the author's errata (Grassl's gate order;
controlled-`Y` read as controlled-`XZ` in the real form `Y = XZ`; every generator of sign `+1`).

Conventions. A code on `n = m + k` qubits encoding `k` qubits has `m = n − k` generators (no `ℕ`
subtraction); its binary generator matrix is the pair `(H_x | H_z)` of `m × n` matrices over `F₂`
(`H_x` the `σx` part, `H_z` the `σz` part, `σy ↦ (1|1)`). Wire `q : Fin (m + k)` is the source's
qubit `q + 1`; the source's 1-based generator `M_{i+1}` and logical `X̄_{i+1}` are index `i`.
-/

namespace QAlgorithms

open scoped Matrix

/-- Gottesman thesis p.39 (§4.1) and p.40 (eq. (3.23), cited): the generators with binary rows
`(a|b)` of `(H_x | H_z)` pairwise commute: `a · b′ + b · a′ = 0` over `F₂` for every pair of rows,
i.e. `H_x H_zᵀ + H_z H_xᵀ = 0`. -/
def SymplecticCommuting {m n : ℕ} (Hx Hz : Matrix (Fin m) (Fin n) (ZMod 2)) : Prop :=
  Hx * Hzᵀ + Hz * Hxᵀ = 0

/-- Gottesman thesis p.39 (§4.1, via §3.4): `(H_x | H_z)` is the binary generator matrix of a
stabilizer with `m` independent generators: the rows commute symplectically and the `m` rows
`(a|b) ∈ F₂^{2n}` are linearly independent. -/
def IsBinaryStabilizerMatrix {m n : ℕ} (Hx Hz : Matrix (Fin m) (Fin n) (ZMod 2)) : Prop :=
  SymplecticCommuting Hx Hz ∧ LinearIndependent (ZMod 2) (Matrix.fromCols Hx Hz)

/-- Gottesman thesis p.39 (§4.1, eq. (4.3)): the standard form
```
     r      m−r     k        r     m−r    k
r  [ I      A1      A2   |   B     C1     C2 ]
m−r[ 0      0       0    |   D     I      E  ]
```
with `r ≤ m`: the `σx` half has the identity `I_r` in rows and columns `< r` and zero rows `≥ r`;
the `σz` half has the identity `I_{m−r}` in rows `≥ r` and columns `[r, m)`; the blocks
`A1, A2, B, C1, C2, D, E` are arbitrary. -/
def IsStandardForm {m k : ℕ} (r : ℕ) (Hx Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2)) : Prop :=
  r ≤ m ∧
    (∀ (i : Fin m) (j : Fin (m + k)), (i : ℕ) < r → (j : ℕ) < r →
      Hx i j = if (i : ℕ) = (j : ℕ) then 1 else 0) ∧
    (∀ (i : Fin m) (j : Fin (m + k)), r ≤ (i : ℕ) → Hx i j = 0) ∧
    (∀ (i : Fin m) (j : Fin (m + k)), r ≤ (i : ℕ) → r ≤ (j : ℕ) → (j : ℕ) < m →
      Hz i j = if (i : ℕ) = (j : ℕ) then 1 else 0)

/-- Gottesman thesis p.41 (§4.2): the tensor product `M_0 ⊗ ⋯ ⊗ M_{n−1}` of one single-qubit
operator per qubit (factor `q` on wire `q`). -/
def kronAll {n : ℕ} (M : Fin n → Matrix Bool Bool ℂ) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun y z => ∏ q, M q (y q) (z q)

/-- Gottesman thesis p.41 (§4.2) with the author's errata: the sign-`+1` Pauli operator of the
binary row `(a|b)` in the real form, `⊗_q σz^{b_q} σx^{a_q}` (`σx` applied first; a `σy` factor is
`σzσx`, the errata's "controlled-XZ"). This is the only convention under which the page's
"performing `σz` after the Hadamard transform" is correct. -/
def rowPauli {n : ℕ} (a b : Fin n → ZMod 2) : Matrix (Qubits n) (Qubits n) ℂ :=
  kronAll fun q => (if b q = 1 then pauliZ else 1) * (if a q = 1 then pauliX else 1)

/-- Gottesman thesis p.40 (§4.1, "Suppose we pick `U3 = I`. Then we can take `V3 = 0`, and by
equation (4.5), `U2 = Eᵀ` and `V1 = EᵀC1ᵀ + C2ᵀ`"): the binary row (`σx` part, `σz` part) of the
standard-form logical `X̄_i`, `i : Fin k`. With the blocks of `H_z` (`C1`: rows `< r`, columns
`[r, m)`; `C2`: rows `< r`, columns `≥ m`; `E`: rows `[r, m)`, columns `≥ m`), the `σx` part is
`0` on columns `< r`, `E_{j−r, i}` on columns `j ∈ [r, m)` and `δ_{ij}` on column `m + j`; the
`σz` part is `(EᵀC1ᵀ + C2ᵀ)_{ij} = Σ_{l ∈ [r, m)} E_{l−r, i} (C1)_{j, l−r} + (C2)_{j i}` on
columns `j < r` and `0` elsewhere. (`H_x` does not enter.) -/
def logicalXRow {m k : ℕ} (r : ℕ) (Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2)) (i : Fin k) :
    (Fin (m + k) → ZMod 2) × (Fin (m + k) → ZMod 2) :=
  (fun j => if h : (j : ℕ) < m then
      (if r ≤ (j : ℕ) then Hz ⟨j, h⟩ (Fin.natAdd m i) else 0)
    else if (j : ℕ) = m + (i : ℕ) then 1 else 0,
   fun j => if h : (j : ℕ) < r ∧ (j : ℕ) < m then
      (∑ l : Fin m, if r ≤ (l : ℕ) then Hz l (Fin.natAdd m i) * Hz ⟨j, h.2⟩ (Fin.castAdd k l) else 0) +
        Hz ⟨j, h.2⟩ (Fin.natAdd m i)
    else 0)

/-- Gottesman thesis p.40 (§4.1): the standard-form logical operator `X̄_i` (sign `+1`, real
form). -/
def logicalX {m k : ℕ} (r : ℕ) (Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2)) (i : Fin k) :
    Matrix (Qubits (m + k)) (Qubits (m + k)) ℂ :=
  rowPauli (logicalXRow r Hz i).1 (logicalXRow r Hz i).2

/-- Gottesman thesis p.41 (§4.2, eqs. (4.7)–(4.8)): the encoded basis state
`(I + M_1) ⋯ (I + M_{n−k}) X̄_1^{c_1} ⋯ X̄_k^{c_k} |0 … 0⟩`, unnormalized, with `M_i` the sign-`+1`
operators of the rows of `(H_x | H_z)`. Products are frozen `orderedProd`s; their factors commute,
so the order is immaterial. -/
noncomputable def stabEncodedState {m k : ℕ} (r : ℕ) (Hx Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2))
    (c : Qubits k) : EuclideanSpace ℂ (Qubits (m + k)) :=
  act (orderedProd fun i : Fin m => 1 + rowPauli (Hx i) (Hz i))
    (act (orderedProd fun i : Fin k => if c i then logicalX r Hz i else 1) (zeroKet (m + k)))

/-- Gottesman thesis pp.41–42 (§4.2): the gates of the encoding network: the Hadamard transform
`R` (4.12), `σz`, and the controlled gates `σz^b σx^a` for `(a, b) ≠ (0, 0)` (controlled-`σx` =
CNOT, controlled-`σz`, controlled-`σzσx`), the control on the first qubit (frozen
`controlled`). -/
def stabEncoderGateSet : Set Gate :=
  {Gate.ofMatrix1 hadamard, Gate.ofMatrix1 pauliZ} ∪
    {g | ∃ a b : Bool, (a, b) ≠ (false, false) ∧
      g = Gate.ofMatrix2 (controlled ((if b then pauliZ else 1) * (if a then pauliX else 1)))}

/-- Gottesman thesis p.42 (§4.2): the controlled gate `σz^b σx^a` with control wire `c` and target
wire `t` (helper for `stabEncoder`). -/
def stabCtrlApp {N : ℕ} (a b : Bool) (hab : (a, b) ≠ (false, false)) (c t : Fin N) (h : c ≠ t) :
    GateApp stabEncoderGateSet N :=
  ⟨Gate.ofMatrix2 (controlled ((if b then pauliZ else 1) * (if a then pauliX else 1))),
    Set.mem_union_right _ ⟨a, b, hab, rfl⟩, Stabilizer.wire2 c t h⟩

theorem castAdd_ne_natAdd {m k : ℕ} (j : Fin m) (i : Fin k) : Fin.natAdd m i ≠ Fin.castAdd k j := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.coe_natAdd, Fin.coe_castAdd] at this
  omega

/-- Gottesman thesis pp.41–43 (§4.2) with the author's errata: the encoding network as a frozen
`Circuit` (head of the list applied first) on `m + k` wires, input `|0 … 0⟩|c⟩` (`c` on wires
`m, …, m + k − 1`).
1. For each `i < k` and each `j ∈ [r, m)` with `E_{j−r, i} = (H_z)_{j, m+i} = 1`, a CNOT from wire
   `m + i` to wire `j` (the `σx` part of `X̄_i` conditioned on `c_i`; its `σz` part acts trivially
   on `|0⟩`).
2. Then, for `i = 0, …, r − 1` in turn: `R` on wire `i`, `σz` on wire `i` if `B_ii = (H_z)_{ii} = 1`,
   and for every wire `q ≠ i` on which `M_i` acts, the gate `σz^{(H_z)_{iq}} σx^{(H_x)_{iq}}`
   controlled on wire `i` (errata: the Hadamard on qubit `i` immediately precedes its control dots).
No gates for the generators `i ≥ r` (products of `σz`, p.42). -/
noncomputable def stabEncoder {m k : ℕ} (r : ℕ) (Hx Hz : Matrix (Fin m) (Fin (m + k)) (ZMod 2)) :
    Circuit stabEncoderGateSet (m + k) :=
  ((List.finRange k).flatMap fun (i : Fin k) => (List.finRange m).filterMap fun (j : Fin m) =>
      if r ≤ (j : ℕ) ∧ Hz j (Fin.natAdd m i) = 1 then
        some (stabCtrlApp true false (by simp) (Fin.natAdd m i) (Fin.castAdd k j)
          (castAdd_ne_natAdd j i))
      else none) ++
  ((List.finRange m).flatMap fun (i : Fin m) =>
    if (i : ℕ) < r then
      [⟨Gate.ofMatrix1 hadamard, Set.mem_union_left _ (Set.mem_insert _ _),
          Stabilizer.wire1 (Fin.castAdd k i)⟩] ++
      (if Hz i (Fin.castAdd k i) = 1 then
        [⟨Gate.ofMatrix1 pauliZ, Set.mem_union_left _ (Set.mem_insert_of_mem _ rfl),
          Stabilizer.wire1 (Fin.castAdd k i)⟩] else []) ++
      (List.finRange (m + k)).filterMap fun (q : Fin (m + k)) =>
        if h : q ≠ Fin.castAdd k i ∧
            (decide (Hx i q = 1), decide (Hz i q = 1)) ≠ (false, false) then
          some (stabCtrlApp (decide (Hx i q = 1)) (decide (Hz i q = 1)) h.2
            (Fin.castAdd k i) q (Ne.symm h.1))
        else none
    else [])

/-! ### Sanity tests -/

example {n : ℕ} : rowPauli (0 : Fin n → ZMod 2) 0 = 1 := by
  ext y z
  simp [rowPauli, kronAll, Matrix.one_apply, Finset.prod_boole, funext_iff]

example : rowPauli (![1] : Fin 1 → ZMod 2) ![0] = (Gate.ofMatrix1 pauliX).mat := by
  ext y z
  simp [rowPauli, kronAll, Gate.ofMatrix1]

example {k : ℕ} (r : ℕ) (Hx Hz : Matrix (Fin 0) (Fin (0 + k)) (ZMod 2)) :
    stabEncoder r Hx Hz = [] := by
  simp [stabEncoder]

example {k : ℕ} (Hz : Matrix (Fin 0) (Fin (0 + k)) (ZMod 2)) (i : Fin k) (j : Fin (0 + k)) :
    (logicalXRow 0 Hz i).1 j = (if (j : ℕ) = (i : ℕ) then 1 else 0) ∧
      (logicalXRow 0 Hz i).2 j = 0 := by
  simp [logicalXRow]

example {k : ℕ} (Hx Hz : Matrix (Fin 0) (Fin (0 + k)) (ZMod 2)) : IsStandardForm 0 Hx Hz := by
  refine ⟨le_rfl, ?_, ?_, ?_⟩ <;> intro i <;> exact Fin.elim0 i

example : SymplecticCommuting (!![1, 0] : Matrix (Fin 1) (Fin 2) (ZMod 2)) !![0, 1] := by
  unfold SymplecticCommuting
  decide

end QAlgorithms


