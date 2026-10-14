-- Prove2me | Definitions.Def_QAlgorithms_Defs_CompressedOracle
-- name    : QAlgorithms_Defs_CompressedOracle
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:33:00.536804+00:00
-- url     : https://prove2.me/theorems/b3610022-e32f-4749-9aa6-9326da9e9c06
-- title:
--   The compressed oracle (shared definition layer)
-- statement:
--   The compressed oracle (shared definition layer)
--
--   ### QAlgorithms.hadKet
--
--   For a natural number $m$ and a bit string $y \in \{0,1\}^m$, this defines a vector $|\hat y\rangle$ in the complex Euclidean space indexed by $\{\bot\} \cup \{0,1\}^m$. Here $\bot$ is an extra "empty" label adjoined to the $2^m$ bit strings.
--
--   Its coordinates are:
--
--   $$
--   |\hat y\rangle_\bot = 0,\qquad |\hat y\rangle_z = (H^{\otimes m})_{z,y} = \frac{(-1)^{y\cdot z}}{(\sqrt2)^m}\quad (z\in\{0,1\}^m).
--   $$
--
--   In this formula:
--
--   - $H^{\otimes m}$ is the matrix whose $(z,y)$ entry is $-(1/\sqrt2)^m$ when the bit inner product $y\cdot z$ is $1$ and $+(1/\sqrt2)^m$ otherwise.
--   - $y\cdot z = \bigoplus_k (y_k \wedge z_k)$ is the sum of the bitwise ANDs taken in $\{0,1\}$ with addition as XOR, i.e. the parity of $\sum_k y_k z_k$.
--
--   ### QAlgorithms.compressionUnitary
--
--   For a natural number $m$, this defines a square complex matrix $C_m$ indexed by $\{\bot\}\cup\{0,1\}^m$, where $\bot$ is an extra label. Its entries are, for $z,w \in \{0,1\}^m$:
--
--   $$
--   (C_m)_{\bot,\bot} = 0,\qquad (C_m)_{\bot,w} = (C_m)_{z,\bot} = \Big(\tfrac{1}{\sqrt2}\Big)^{m},\qquad (C_m)_{z,w} = \delta_{z,w} - \Big(\big(\tfrac{1}{\sqrt2}\big)^{m}\Big)^{2} = \delta_{z,w} - 2^{-m}.
--   $$
--
--   Here $\delta_{z,w}$ is $1$ if $z = w$ and $0$ otherwise. Nothing is asserted about this matrix (e.g. unitarity); it is only defined.
--
--   ### QAlgorithms.compressAll
--
--   For natural numbers $n, m$, this defines a square complex matrix $C_m^{\otimes n}$. It is indexed by "databases" $D : \{0,\dots,n-1\} \to \{\bot\}\cup\{0,1\}^m$, i.e. $n$-tuples each of whose entries is either $\bot$ or an $m$-bit string. Its entries are
--
--   $$
--   (C_m^{\otimes n})_{D,D'} = \prod_{i=0}^{n-1} (C_m)_{D(i),\,D'(i)}.
--   $$
--
--   Here $C_m$ is the matrix of `compressionUnitary`, so this is the $n$-fold tensor power of $C_m$. For $n = 0$ there is exactly one database (the empty one), and the matrix is the $1\times1$ matrix $(1)$, since the product is empty.
--
--   ### QAlgorithms.lookupUnitary
--
--   Fix natural numbers $n, m$ and a type $W$ with decidable equality (no finiteness is required here). Basis labels are quadruples $(x,u,w,D)$ where:
--
--   - $x \in \{0,\dots,n-1\}$;
--   - $u \in \{0,1\}^m$;
--   - $w \in W$;
--   - $D : \{0,\dots,n-1\}\to\{\bot\}\cup\{0,1\}^m$ is a database.
--
--   The matrix $L$ has entry $L_{(x,u,w,D),(x',u',w',D')}$ equal to $1$ exactly when all of the following hold, and $0$ otherwise:
--
--   - $x = x'$;
--   - $w = w'$;
--   - $D = D'$;
--   - the $u$-component is updated as follows:
--
--   $$
--   u = \begin{cases} u' \oplus v & \text{if } D'(x') = v \in \{0,1\}^m,\\ u' & \text{if } D'(x') = \bot.\end{cases}
--   $$
--
--   Here $\oplus$ is bitwise XOR. In other words, $L$ sends $|x,u',w,D\rangle$ to $|x, u'\oplus D(x), w, D\rangle$ when $D(x)\neq\bot$, and fixes it when $D(x) = \bot$.
--
--   ### QAlgorithms.compressedOracle
--
--   Fix natural numbers $n, m$ and a finite type $W$ with decidable equality. On the space with the basis labels $(x,u,w,D)$ described for `lookupUnitary`, this defines the matrix
--
--   $$
--   \mathcal O_{\mathrm{comp}} = \big(I \otimes C_m^{\otimes n}\big)\, L\, \big(I \otimes C_m^{\otimes n}\big),
--   $$
--
--   where:
--
--   - $I$ is the identity on the register indexed by $(x,u,w)\in\{0,\dots,n-1\}\times\{0,1\}^m\times W$;
--   - $C_m^{\otimes n}$ is the matrix of `compressAll`, acting on the database register $D$;
--   - $L$ is the matrix of `lookupUnitary`;
--   - $\otimes$ is the Kronecker product, with the $(x,u,w)$ factor first and the database factor second.
--
--   ### QAlgorithms.compressedPhaseOracle
--
--   With the same $n, m, W$ and basis labels $(x,u,w,D)$ as in `compressedOracle`, this defines the matrix
--
--   $$
--   \mathcal O_{\mathrm{comp}}^{\mathrm{ph}} = \big(I_n \otimes H^{\otimes m} \otimes I_W \otimes C_m^{\otimes n}\big)\, L\, \big(I_n \otimes H^{\otimes m} \otimes I_W \otimes C_m^{\otimes n}\big),
--   $$
--
--   where:
--
--   - $I_n$ is the identity on the $x$-register $\{0,\dots,n-1\}$;
--   - $H^{\otimes m}$ is the $m$-qubit Hadamard matrix (entries $(-1)^{y\cdot z}2^{-m/2}$) acting on the $u$-register;
--   - $I_W$ is the identity on $W$;
--   - $C_m^{\otimes n}$ is the matrix of `compressAll`, acting on the database $D$;
--   - $L$ is the matrix of `lookupUnitary`.
--
--   The Kronecker products are nested in the order $((I_n\otimes H^{\otimes m})\otimes I_W)\otimes C_m^{\otimes n}$, matching the label order $(x,u,w,D)$.
--
--   ### QAlgorithms.containsZeroProj
--
--   With $n, m, W$ as above ($W$ finite with decidable equality) and basis labels $(x,u,w,D)$, this is the diagonal $0/1$ matrix $P_0$ with
--
--   $$
--   (P_0)_{(x,u,w,D),(x,u,w,D)} = \begin{cases}1 & \text{if there is some } i\in\{0,\dots,n-1\} \text{ with } D(i) = 0^m,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--
--   Here $0^m$ is the all-zeros bit string, as opposed to $\bot$. All off-diagonal entries are $0$. Only the database component $D$ of the label matters.
--
--   ### QAlgorithms.randomOracleSuccess
--
--   **Inputs.** Fix natural numbers $n, m, k, t$ and a finite type $W$ with decidable equality. The definition takes:
--
--   - a $t$-query algorithm $A$ over input alphabet $\{0,\dots,n-1\}$ and answer alphabet $\{0,1\}^m$ with workspace $W$;
--   - an output map $\mathrm{out}$ assigning to each basis label $z=(x,u,w)$ a $k$-tuple $\mathrm{out}(z) = \big((x_1,y_1),\dots,(x_k,y_k)\big)$ of pairs in $\{0,\dots,n-1\}\times\{0,1\}^m$;
--   - a finite set $R \subseteq \{0,\dots,n-1\}\times\{0,1\}^m$.
--
--   **The query algorithm.** $A$ consists of a vector $|\mathrm{start}\rangle$ of norm $1$ in the space indexed by $(x,u,w)$, together with unitaries $U_0,\dots,U_t$. Given an oracle matrix $O$, its final state is
--
--   $$
--   |\psi_A^O\rangle = U_t\,(O\otimes I_W)\,U_{t-1}\cdots U_1\,(O\otimes I_W)\,U_0\,|\mathrm{start}\rangle,
--   $$
--
--   which contains $t$ applications of $O\otimes I_W$.
--
--   **The XOR oracle.** For a function $f:\{0,\dots,n-1\}\to\{0,1\}^m$, the matrix $O_f$ has entry $1$ at $\big((x,u),(x',u')\big)$ iff $x = x'$ and $u = u'\oplus f(x')$, and $0$ otherwise. That is, $|x,u\rangle\mapsto|x,u\oplus f(x)\rangle$.
--
--   **The value.** The definition is
--
--   $$
--   \mathrm{randomOracleSuccess}(A,\mathrm{out},R) = \frac{1}{2^{mn}}\sum_{f:\{0,\dots,n-1\}\to\{0,1\}^m}\ \sum_{z \in E_f} \big|\langle z|\psi_A^{O_f}\rangle\big|^2,
--   $$
--
--   where $E_f$ is the set of basis labels $z$ such that, for every $i\in\{1,\dots,k\}$, both $(x_i,y_i)\in R$ and $f(x_i) = y_i$, with $(x_i,y_i)$ the $i$-th entry of $\mathrm{out}(z)$.
--
--   **Edge cases.**
--
--   - The pairs in $\mathrm{out}(z)$ are not required to be distinct.
--   - For $k=0$ the condition is vacuous, so $E_f$ is the set of all labels.
--
--   ### QAlgorithms.compressedStateAt
--
--   **Inputs.** Fix natural numbers $n, m, t$ and a finite type $W$ with decidable equality. Let $A$ be a $t$-query algorithm as in `randomOracleSuccess`, with start vector $|\mathrm{start}\rangle$ and unitaries $U_0,\dots,U_t$ on the register indexed by $(x,u,w)\in\{0,\dots,n-1\}\times\{0,1\}^m\times W$.
--
--   **Definition.** This defines a sequence of vectors $|\phi_0\rangle,\dots,|\phi_t\rangle$ in the space with basis labels $(x,u,w,D)$, where $D:\{0,\dots,n-1\}\to\{\bot\}\cup\{0,1\}^m$ is a database. The sequence is given by
--
--   $$
--   |\phi_0\rangle = (U_0\otimes I_{\mathcal D})\big(|\mathrm{start}\rangle\otimes|\bot^n\rangle\big),\qquad
--   |\phi_{s+1}\rangle = (U_{s+1}\otimes I_{\mathcal D})\,\mathcal O_{\mathrm{comp}}\,|\phi_s\rangle\quad (0\le s<t).
--   $$
--
--   In these formulas:
--
--   - $|\bot^n\rangle$ is the basis vector of the all-$\bot$ database $D(i)=\bot$ for all $i$;
--   - $|\mathrm{start}\rangle\otimes|\bot^n\rangle$ is the product vector with coordinates $\mathrm{start}_{(x,u,w)}\cdot[D=\bot^n]$;
--   - $I_{\mathcal D}$ is the identity on the database register;
--   - $\mathcal O_{\mathrm{comp}} = (I\otimes C_m^{\otimes n})\,L\,(I\otimes C_m^{\otimes n})$ is the matrix of `compressedOracle`.
--
--   ### QAlgorithms.compressedFinalState
--
--   For $n, m, t$, a finite type $W$ with decidable equality, and a $t$-query algorithm $A$ as above, this is the last vector of the `compressedStateAt` sequence:
--
--   $$
--   |\phi_t\rangle = (U_t\otimes I_{\mathcal D})\,\mathcal O_{\mathrm{comp}}\,(U_{t-1}\otimes I_{\mathcal D})\cdots \mathcal O_{\mathrm{comp}}\,(U_0\otimes I_{\mathcal D})\big(|\mathrm{start}\rangle\otimes|\bot^n\rangle\big).
--   $$
--
--   This applies $\mathcal O_{\mathrm{comp}}$ (the matrix of `compressedOracle`) exactly $t$ times. For $t=0$ it is just $(U_0\otimes I_{\mathcal D})(|\mathrm{start}\rangle\otimes|\bot^n\rangle)$.
--
--   ### QAlgorithms.compressedSuccess
--
--   **Inputs.** Fix natural numbers $n, m, k, t$ and a finite type $W$ with decidable equality. The definition takes:
--
--   - a $t$-query algorithm $A$;
--   - an output map $\mathrm{out}$ sending each label $z=(x,u,w)$ to a $k$-tuple $\big((x_1,y_1),\dots,(x_k,y_k)\big)$ of pairs in $\{0,\dots,n-1\}\times\{0,1\}^m$;
--   - a finite set $R$ of such pairs.
--
--   **The value.** It is the real number
--
--   $$
--   \mathrm{compressedSuccess}(A,\mathrm{out},R) = \sum_{(z,D)\in F} \big|\langle z,D\,|\,\phi_t\rangle\big|^2,
--   $$
--
--   where:
--
--   - $|\phi_t\rangle$ is the vector of `compressedFinalState`;
--   - $\langle z,D|\phi_t\rangle$ is its coordinate at the label $(z,D)$;
--   - $F$ is the set of labels $(z,D)$ such that, for every $i\in\{1,\dots,k\}$, both $(x_i,y_i)\in R$ and $D(x_i) = y_i$, with $(x_i,y_i)$ the $i$-th entry of $\mathrm{out}(z)$.
--
--   The condition $D(x_i) = y_i$ means in particular that $D(x_i)\neq\bot$.
--
--   **Edge cases.**
--
--   - The pairs need not be distinct.
--   - For $k = 0$ the condition is vacuous, and the value is the sum of $|\cdot|^2$ over all coordinates of $|\phi_t\rangle$.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/CompressedOracle.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_Polynomial
/-!
# The compressed oracle (shared definition layer)

Childs §26: a random function `f : [n] → Σ`, `Σ = {0,1}^m` (here `Fin n → Qubits m`). The oracle
register holds one symbol of `Σ ∪ {⊥}` per input, modelled as `Option (Qubits m)` with
`none = ⊥`. The full register of an algorithm with the oracle register attached is indexed by
`((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m))`, i.e. `|x, z, w, y⟩` as in (26.30).
-/

namespace QAlgorithms

/-- Childs p.133 (§26.1): `|ŷ⟩ = H^{⊗m}|y⟩`, as a vector of the oracle-register space
`span({|y⟩ : y ∈ Σ} ∪ {|⊥⟩})` (no `|⊥⟩` component). -/
noncomputable def hadKet (m : ℕ) (y : Qubits m) : EuclideanSpace ℂ (Option (Qubits m)) :=
  WithLp.toLp 2 fun o => match o with
    | none => 0
    | some z => hadamardN m z y

/-- Childs p.133 ((26.2)–(26.4)), p.137: the compression unitary
`C = I_Σ + |⊥⟩⟨0̂| + |0̂⟩⟨⊥| − |0̂⟩⟨0̂|`, i.e. `C|⊥⟩ = |0̂⟩`, `C|0̂⟩ = |⊥⟩`, `C|ŷ⟩ = |ŷ⟩` for
`y ≠ 0`, where `|0̂⟩ = 2^{−m/2} Σ_y |y⟩`. Entrywise: `C(⊥, ⊥) = 0`, `C(⊥, w) = C(z, ⊥) = 2^{−m/2}`,
`C(z, w) = δ_{zw} − 2^{−m}`. -/
noncomputable def compressionUnitary (m : ℕ) : Matrix (Option (Qubits m)) (Option (Qubits m)) ℂ :=
  Matrix.of fun o o' => match o, o' with
    | none, none => 0
    | none, some _ => (((Real.sqrt 2)⁻¹ ^ m : ℝ) : ℂ)
    | some _, none => (((Real.sqrt 2)⁻¹ ^ m : ℝ) : ℂ)
    | some z, some w => (if z = w then 1 else 0) - ((((Real.sqrt 2)⁻¹ ^ m) ^ 2 : ℝ) : ℂ)

/-- Childs p.133: `C^{⊗n}`, the compression unitary on each of the `n` oracle registers. -/
noncomputable def compressAll (n m : ℕ) :
    Matrix (Fin n → Option (Qubits m)) (Fin n → Option (Qubits m)) ℂ :=
  Matrix.of fun y y' => ∏ i : Fin n, compressionUnitary m (y i) (y' i)

/-- Childs p.133 ((26.1), extended as stated after (26.4)): the lookup unitary
`Λ |x⟩|z⟩|w⟩|y_1, …, y_n⟩ = |x⟩|z ⊕ y_x⟩|w⟩|y_1, …, y_n⟩` when `y_x ∈ Σ`, and the identity when
`y_x = ⊥`; the identity on the workspace `W`. -/
def lookupUnitary (n m : ℕ) (W : Type*) [DecidableEq W] :
    Matrix (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m)))
      (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m))) ℂ :=
  Matrix.of fun p q =>
    if p.1.1.1 = q.1.1.1 ∧ p.1.2 = q.1.2 ∧ p.2 = q.2 ∧
        p.1.1.2 = (match q.2 q.1.1.1 with
          | some v => q.1.1.2 + v
          | none => q.1.1.2)
    then 1 else 0

/-- Childs p.133 (§26.1): the compressed oracle `(I ⊗ I ⊗ C^{⊗n}) Λ (I ⊗ I ⊗ C^{⊗n})`, the
identity on the workspace. -/
noncomputable def compressedOracle (n m : ℕ) (W : Type*) [Fintype W] [DecidableEq W] :
    Matrix (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m)))
      (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m))) ℂ :=
  Matrix.kronecker (1 : Matrix ((Fin n × Qubits m) × W) ((Fin n × Qubits m) × W) ℂ)
      (compressAll n m) * lookupUnitary n m W *
    Matrix.kronecker (1 : Matrix ((Fin n × Qubits m) × W) ((Fin n × Qubits m) × W) ℂ)
      (compressAll n m)

/-- Childs p.136 ((26.29)): the compressed phase oracle
`Φ = (I ⊗ H^{⊗m} ⊗ C^{⊗n}) Λ (I ⊗ H^{⊗m} ⊗ C^{⊗n})` (Hadamards on the output register `z`), the
identity on the workspace. -/
noncomputable def compressedPhaseOracle (n m : ℕ) (W : Type*) [Fintype W] [DecidableEq W] :
    Matrix (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m)))
      (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m))) ℂ :=
  Matrix.kronecker (Matrix.kronecker (Matrix.kronecker (1 : Matrix (Fin n) (Fin n) ℂ) (hadamardN m))
      (1 : Matrix W W ℂ)) (compressAll n m) * lookupUnitary n m W *
    Matrix.kronecker (Matrix.kronecker (Matrix.kronecker (1 : Matrix (Fin n) (Fin n) ℂ) (hadamardN m))
      (1 : Matrix W W ℂ)) (compressAll n m)

/-- Childs p.136 (§26.3, `P`): the projection onto the basis states whose oracle register contains
a zero (`∃ x*, y_{x*} = 0^m`; `⊥` is not a zero). -/
def containsZeroProj (n m : ℕ) (W : Type*) [Fintype W] [DecidableEq W] :
    Matrix (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m)))
      (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m))) ℂ :=
  Matrix.diagonal fun p => if ∃ x, p.2 x = some 0 then 1 else 0

/-- Childs p.133–134 (Lemma 26.1, `p`): the probability, over a uniformly random
`f : [n] → {0,1}^m` and the algorithm's measurement, that the algorithm `A` (standard queries
`|x⟩|z⟩ ↦ |x⟩|z ⊕ f(x)⟩`) outputs `k` pairs `(x_i, z_i) = out(outcome) i` that all lie in `R` and
satisfy `f(x_i) = z_i`. -/
noncomputable def randomOracleSuccess {n m k : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {t : ℕ}
    (A : QueryAlg (Fin n) (Qubits m) W t) (out : (Fin n × Qubits m) × W → (Fin k → Fin n × Qubits m))
    (R : Finset (Fin n × Qubits m)) : ℝ :=
  ((2 : ℝ) ^ (m * n))⁻¹ * ∑ f : Fin n → Qubits m,
    probEvent (A.finalState (xorOracle f)) fun z => ∀ i, out z i ∈ R ∧ f (out z i).1 = (out z i).2

/-- Childs p.133 (§26.1): the state of the algorithm `A` run with the compressed oracle: the same
unitaries `U_s ⊗ I` (identity on the oracle register), `compressedOracle` in place of each query,
from `|start⟩ ⊗ |⊥⟩^{⊗n}`; the state after `U_s`. -/
noncomputable def compressedStateAt {n m : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {t : ℕ}
    (A : QueryAlg (Fin n) (Qubits m) W t) :
    Fin (t + 1) → EuclideanSpace ℂ (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m))) :=
  Fin.induction
    (act (Matrix.kronecker (A.U 0 : Matrix _ _ ℂ)
      (1 : Matrix (Fin n → Option (Qubits m)) (Fin n → Option (Qubits m)) ℂ))
      (tensorVec A.start (ket fun _ => none)))
    (fun s ψ => act (Matrix.kronecker (A.U s.succ : Matrix _ _ ℂ)
      (1 : Matrix (Fin n → Option (Qubits m)) (Fin n → Option (Qubits m)) ℂ))
      (act (compressedOracle n m W) ψ))

/-- The final state of `A` run with the compressed oracle. -/
noncomputable def compressedFinalState {n m : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {t : ℕ}
    (A : QueryAlg (Fin n) (Qubits m) W t) :
    EuclideanSpace ℂ (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m))) :=
  compressedStateAt A (Fin.last t)

/-- Childs p.134 (Lemma 26.1, `p′`): run with the compressed oracle and measure all registers
(the oracle register included) in the computational basis; the probability that the output pairs
`(x_i, z_i)` all lie in `R` and the oracle register at `x_i` holds `z_i` (a `⊥` never matches). -/
noncomputable def compressedSuccess {n m k : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {t : ℕ}
    (A : QueryAlg (Fin n) (Qubits m) W t) (out : (Fin n × Qubits m) × W → (Fin k → Fin n × Qubits m))
    (R : Finset (Fin n × Qubits m)) : ℝ :=
  probEvent (compressedFinalState A) fun p =>
    ∀ i, out p.1 i ∈ R ∧ p.2 (out p.1 i).1 = some (out p.1 i).2

/-! ### Sanity tests -/

/-- For `m = 0` (`Σ` a single symbol, `|0̂⟩ = |0⟩`), `C` swaps `|⊥⟩` and `|0⟩`. -/
example : compressionUnitary 0 none none = 0 ∧ compressionUnitary 0 (some 0) none = 1 ∧
    compressionUnitary 0 (some 0) (some 0) = 0 := by
  simp [compressionUnitary]

/-- `C|⊥⟩ = |0̂⟩`: every entry of the `⊥` column on `Σ` is `2^{−m/2}`. -/
example (m : ℕ) (z : Qubits m) :
    compressionUnitary m (some z) none = (((Real.sqrt 2)⁻¹ ^ m : ℝ) : ℂ) := rfl

/-- `Λ` leaves a query to an unrecorded (`⊥`) position unchanged. -/
example (n m : ℕ) (W : Type*) [DecidableEq W] (x : Fin n) (z : Qubits m) (w : W)
    (y : Fin n → Option (Qubits m)) (hy : y x = none) :
    lookupUnitary n m W (((x, z), w), y) (((x, z), w), y) = 1 := by
  simp [lookupUnitary, hy]

/-- `Λ` adds the recorded value into the output register. -/
example (n m : ℕ) (W : Type*) [DecidableEq W] (x : Fin n) (z v : Qubits m) (w : W)
    (y : Fin n → Option (Qubits m)) (hy : y x = some v) :
    lookupUnitary n m W (((x, z + v), w), y) (((x, z), w), y) = 1 := by
  simp [lookupUnitary, hy]

end QAlgorithms


