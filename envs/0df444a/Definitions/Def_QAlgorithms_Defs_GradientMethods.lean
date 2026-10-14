-- Prove2me | Definitions.Def_QAlgorithms_Defs_GradientMethods
-- name    : QAlgorithms_Defs_GradientMethods
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:44:27.695023+00:00
-- url     : https://prove2.me/theorems/92de926a-2790-4290-9197-e29e08902b74
-- title:
--   Gradient algorithms, function oracles, subgradients, amplitude encoding, gate sets
-- statement:
--   Gradient algorithms, function oracles, subgradients, amplitude encoding, gate sets
--
--   ### QAlgorithms.modAddOracle
--
--   This definition fixes $d, q \in \mathbb{N}$ and a function $F : (\{0,1\}^q)^d \to \mathbb{N}$. It defines a complex square matrix $M$ indexed by pairs $(x, y)$, where $x = (x_1,\dots,x_d)$ is a $d$-tuple of $q$-bit strings and $y$ is a $q$-bit string. Its entries are
--   $$M_{(x',y'),(x,y)} = \begin{cases}1 & x' = x \text{ and } y' = \beta_q\bigl(N(y) + F(x)\bigr),\\ 0 & \text{otherwise,}\end{cases}$$
--   where:
--
--   - $N(y)$ is the number with most-significant-first binary expansion $y$;
--   - $\beta_q(k)$ is the $q$-bit most-significant-first expansion of $k \bmod 2^q$.
--
--   Thus $M$ is the permutation matrix of
--   $$|x, y\rangle \mapsto |x,\ (N(y) + F(x)) \bmod 2^q\rangle.$$
--   For $q = 0$, the second register is trivial and $M$ is the identity.
--
--   ### QAlgorithms.piKron
--
--   This definition fixes an index type $\iota$, a number $d \in \mathbb{N}$ and a complex matrix $M$ indexed by $\iota \times \iota$. It defines the matrix $M^{\otimes d}$, indexed by $d$-tuples in $\iota^d$, with entries
--   $$(M^{\otimes d})_{x,y} = \prod_{i=1}^{d} M_{x_i, y_i}.$$
--   This is the $d$-fold tensor (Kronecker) power, acting factor-wise on each of the $d$ coordinates. For $d = 0$ the index set has one element and the matrix is $[1]$ (the empty product).
--
--   ### QAlgorithms.jordanGradientState
--
--   This definition fixes $d, q \in \mathbb{N}$ and $F : (\{0,1\}^q)^d \to \mathbb{N}$. It defines a vector in the space with orthonormal basis $|x, y\rangle$, where $x \in (\{0,1\}^q)^d$ and $y \in \{0,1\}^q$:
--   $$\Psi = \bigl((F_q^\dagger)^{\otimes d} \otimes I\bigr)\; M_F\; \Bigl( (H^{\otimes q})^{\otimes d}|0\cdots0\rangle \;\otimes\; F_q|1^q\rangle \Bigr).$$
--   The ingredients are:
--
--   - $|0\cdots0\rangle$ is the basis vector with all $dq$ bits equal to $0$. Applying $H^{\otimes q}$ to each of the $d$ registers gives the uniform superposition, with every amplitude $2^{-dq/2}$. Here $H^{\otimes q}_{j,i} = (-1)^{i\cdot j}2^{-q/2}$.
--   - $F_q$ is the Fourier matrix with entries
--     $$(F_q)_{y,z} = \frac{e^{2\pi i N(y)N(z)/2^q}}{\sqrt{2^q}}.$$
--     It is applied to $|1^q\rangle$, the all-ones string, for which $N = 2^q - 1$. The amplitude of $F_q|1^q\rangle$ at $y$ is
--     $$\frac{e^{2\pi i N(y)(2^q-1)/2^q}}{\sqrt{2^q}} = \frac{e^{-2\pi i N(y)/2^q}}{\sqrt{2^q}}.$$
--   - $\otimes$ of vectors is the product state, with amplitude $\phi(x)\chi(y)$.
--   - $M_F$ is `modAddOracle`, the permutation $|x,y\rangle\mapsto|x,(N(y)+F(x)) \bmod 2^q\rangle$.
--   - $(F_q^\dagger)^{\otimes d}\otimes I$ applies the conjugate transpose of $F_q$ to each of the $d$ registers and leaves the last register unchanged.
--
--   ### QAlgorithms.gridPoint
--
--   This definition fixes $q \in \mathbb{N}$ and a $q$-bit string $j$. It defines the real number
--   $$g_q(j) = \frac{N(j)}{2^q} - \frac12 + \frac{1}{2^{q+1}},$$
--   where $N(j) \in \{0,\dots,2^q-1\}$ is the most-significant-first binary value of $j$. These are the $2^q$ midpoints of the equal subintervals of $[-\tfrac12,\tfrac12]$. They range from $-\tfrac12 + 2^{-q-1}$ to $\tfrac12 - 2^{-q-1}$. For $q = 0$ the single point is $0$.
--
--   ### QAlgorithms.gridQFT
--
--   This definition fixes $q \in \mathbb{N}$. It defines the complex matrix $\tilde F_q$, indexed by pairs of $q$-bit strings, with entries
--   $$(\tilde F_q)_{j,k} = \frac{1}{\sqrt{2^q}}\exp\!\bigl(2\pi i\, 2^q\, g_q(j)\, g_q(k)\bigr).$$
--   Here $g_q(j) = N(j)/2^q - \tfrac12 + 2^{-q-1}$ is the grid point of `gridPoint`.
--
--   ### QAlgorithms.gradientAlgState
--
--   This definition fixes $d, q \in \mathbb{N}$ and an arbitrary real function $f : \mathbb{R}^d \to \mathbb{R}$. No regularity is assumed. It defines a vector in the space with orthonormal basis $|x\rangle$, $x = (x_1,\dots,x_d) \in (\{0,1\}^q)^d$:
--   $$\Psi_f = (\tilde F_q^\dagger)^{\otimes d}\; D_f\; (H^{\otimes q})^{\otimes d}\,|0\cdots0\rangle.$$
--   The ingredients are:
--
--   - $|0\cdots0\rangle$ is the all-zeros basis vector.
--   - $(H^{\otimes q})^{\otimes d}$ applies the $q$-qubit Hadamard transform to each register, producing the uniform superposition with amplitudes $2^{-dq/2}$.
--   - $D_f$ is diagonal with entries
--     $$(D_f)_{x,x} = \exp\!\bigl(2\pi i\, 2^q\, f(g_q(x_1),\dots,g_q(x_d))\bigr),$$
--     where $g_q$ is the grid-point map of `gridPoint`.
--   - $(\tilde F_q^\dagger)^{\otimes d}$ applies the conjugate transpose of the `gridQFT` matrix $\tilde F_q$ to each of the $d$ registers.
--
--   ### QAlgorithms.IsProbabilityOracle
--
--   This predicate fixes:
--
--   - finite types $\kappa$ and $X$ with decidable equality;
--   - a distinguished element $z_0 \in \kappa$, so $\kappa$ is nonempty;
--   - a complex matrix $W$ on the space with basis $|b, z, x\rangle$, where $b \in \{0,1\}$, $z \in \kappa$, $x \in X$;
--   - a function $f : X \to \mathbb{R}$.
--
--   It asserts the conjunction of three conditions.
--
--   1. $W$ is unitary.
--   2. $0 \le f(x) \le 1$ for every $x \in X$.
--   3. For every $x \in X$ there exist vectors $\psi_0^{(x)}, \psi_1^{(x)}$ in the space with basis $|z,x'\rangle$ ($z\in\kappa$, $x'\in X$), each of norm exactly $1$, such that
--      $$W\,|0, z_0, x\rangle = \sqrt{f(x)}\;|1\rangle\otimes\psi_1^{(x)} \;+\; \sqrt{1-f(x)}\;|0\rangle\otimes\psi_0^{(x)}.$$
--
--   The vectors $\psi_0^{(x)}, \psi_1^{(x)}$ may depend arbitrarily on $x$. They are not required to retain $x$ in the last register. When $f(x) \in \{0,1\}$, the vector whose coefficient vanishes must still exist as a unit vector, but it is otherwise unconstrained. If $X$ is empty, only unitarity is required.
--
--   ### QAlgorithms.hadamardTestCircuit
--
--   This definition fixes $n \in \mathbb{N}$, a finite type $X$ with decidable equality, and two arbitrary complex matrices:
--
--   - $U$ on $n$ qubits;
--   - $V$ on the space with basis $|z, x\rangle$, $z \in \{0,1\}^n$, $x \in X$.
--
--   No unitarity is assumed for either. The definition gives a matrix on the space with basis $|b, z, x\rangle$, where $b \in \{0,1\}$ is a control qubit:
--   $$\mathcal{C}(U,V) = X_c\, H_c\, \Lambda(V)\, X_c\, \Lambda(U\otimes I_X)\, X_c\, H_c.$$
--   The ingredients are:
--
--   - $H_c = H\otimes I$ applies the single-qubit Hadamard to the control, where
--     $$H = \tfrac{1}{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}.$$
--   - $X_c = X \otimes I$ applies the Pauli bit flip to the control.
--   - $\Lambda(A)$ is the controlled operator. It is block diagonal, acting as the identity on the block where the control is $0$ and as $A$ on the block where the control is $1$.
--
--   Read right to left as operations on a vector, the circuit applies, in order: $H_c$, $X_c$, $\Lambda(U\otimes I_X)$, $X_c$, $\Lambda(V)$, $H_c$, $X_c$.
--
--   ### QAlgorithms.IsEpsSubgradOn
--
--   This predicate fixes:
--
--   - a real vector space $E$;
--   - a set $D \subseteq E$;
--   - a function $f : E \to \mathbb{R}$;
--   - a real number $\varepsilon$, with no sign constraint;
--   - a point $\bar x \in E$, not required to lie in $D$;
--   - a real-linear functional $g : E \to \mathbb{R}$.
--
--   It asserts that
--   $$f(\bar x) + g(x - \bar x) - \varepsilon \le f(x) \qquad \text{for every } x \in D.$$
--   If $D$ is empty, the condition holds vacuously.
--
--   ### QAlgorithms.traceRePairing
--
--   This definition fixes a finite index type $\iota$ and a complex square matrix $G$ indexed by $\iota\times\iota$. It defines the real-linear functional on complex $\iota\times\iota$ matrices
--   $$X \mapsto \operatorname{Re}\operatorname{tr}\bigl(G\,X^\dagger\bigr) = \operatorname{Re}\sum_{i,j} G_{ij}\,\overline{X_{ij}},$$
--   where $X^\dagger$ is the conjugate transpose. The space of matrices is regarded here as a real vector space, and the map is additive and homogeneous with respect to real scalars.
--
--   ### QAlgorithms.fdGradient
--
--   This is a definition, not a theorem. It takes a dimension $d \in \mathbb{N}$, a step size $\eta \in \mathbb{R}$, a function $f : \mathbb{R}^d \to \mathbb{R}$ and a point $x \in \mathbb{R}^d$. It returns the vector in $\mathbb{R}^d$ whose $j$-th component, for $j \in \{0,\dots,d-1\}$, is the central finite difference
--
--   $$
--   \big(\nabla_\eta f(x)\big)_j \;=\; \big(f(x+\eta e_j) - f(x-\eta e_j)\big)\cdot (2\eta)^{-1},
--   $$
--
--   where $e_j$ is the $j$-th standard basis vector.
--
--   There are no hypotheses on $\eta$ or $f$. If $\eta = 0$, then $(2\eta)^{-1}$ is taken to be $0$, so every component is $0$. If $\eta < 0$, the formula is used as written. If $d = 0$, the result is the unique (empty) vector.
--
--   ### QAlgorithms.fdLaplacian
--
--   This is a definition. It takes $d \in \mathbb{N}$, a step size $\eta \in \mathbb{R}$, a function $f : \mathbb{R}^d \to \mathbb{R}$ and a point $x \in \mathbb{R}^d$. It returns the real number
--
--   $$
--   \Delta_\eta f(x) \;=\; \sum_{j=0}^{d-1} \big(f(x+\eta e_j) - 2 f(x) + f(x-\eta e_j)\big)\cdot (\eta^2)^{-1},
--   $$
--
--   where $e_j$ is the $j$-th standard basis vector. This is the second-order central-difference approximation of the Laplacian.
--
--   Two degenerate cases follow from the conventions. If $\eta = 0$, then $(\eta^2)^{-1}$ is taken to be $0$, so the value is $0$. If $d = 0$, the sum is empty and the value is $0$.
--
--   ### QAlgorithms.ballL1
--
--   This is a definition. For $d \in \mathbb{N}$, a centre $x \in \mathbb{R}^d$ and a radius $r \in \mathbb{R}$, it is the closed $\ell^1$-ball
--
--   $$
--   B_1(x,r) \;=\; \Big\{\, y \in \mathbb{R}^d \;:\; \sum_{i=0}^{d-1} |x_i - y_i| \le r \,\Big\}.
--   $$
--
--   The inequality is non-strict. No sign condition is placed on $r$:
--
--   - If $r < 0$, the set is empty.
--   - If $r = 0$, the set is $\{x\}$.
--   - If $d = 0$, the set is the whole one-point space $\mathbb{R}^0$ when $r \ge 0$, and empty when $r < 0$.
--
--   ### QAlgorithms.rotY
--
--   This is a definition. For an angle $\theta \in \mathbb{R}$, it is the complex $2\times 2$ matrix indexed by $\{0,1\}$, with row and column $0$ first:
--
--   $$
--   R_y(\theta) \;=\; \begin{pmatrix} \cos(\theta/2) & -\sin(\theta/2) \\ \sin(\theta/2) & \cos(\theta/2) \end{pmatrix}.
--   $$
--
--   Equivalently, its entries are:
--
--   - $(0,0)$ and $(1,1)$ are $\cos(\theta/2)$;
--   - $(0,1)$ is $-\sin(\theta/2)$;
--   - $(1,0)$ is $\sin(\theta/2)$.
--
--   ### QAlgorithms.ampTreeValue
--
--   This is a definition. It takes $n \in \mathbb{N}$, a real vector $x = (x_0,\dots,x_{2^n-1})$ of length $2^n$, and natural numbers $k, j$. It returns
--
--   $$
--   \mathrm{AT}_{n,x}(k,j) \;=\; \sum_{\substack{0 \le i < 2^n \\ \lfloor i / 2^{\,n \dot- k} \rfloor = j}} x_i^2 .
--   $$
--
--   Here $\lfloor\cdot\rfloor$ is natural-number floor division, and $n \dot- k = \max(n-k,0)$ is truncated subtraction.
--
--   For $k \le n$, this sums $x_i^2$ over the $2^{n-k}$ consecutive indices $i \in [\,j\,2^{n-k},\,(j+1)2^{n-k})$. These are the indices whose top $k$ bits encode $j$.
--
--   The degenerate cases are:
--
--   - For $k \ge n$, the divisor is $2^0 = 1$, so the value is $x_j^2$ if $j < 2^n$ and $0$ otherwise.
--   - For $k \le n$ and $j \ge 2^k$, the sum is empty and the value is $0$.
--
--   ### QAlgorithms.prefixVal
--
--   This is a definition. For $n \in \mathbb{N}$, a bit string $z = (z_0,\dots,z_{n-1}) \in \{0,1\}^n$ and $k \in \mathbb{N}$, it is
--
--   $$
--   \mathrm{pre}(z,k) \;=\; \sum_{\substack{0 \le i < n \\ i < k,\; z_i = 1}} 2^{\,k-1-i}.
--   $$
--
--   For $k \le n$, this is the integer whose $k$-bit binary expansion, most significant bit first, is $z_0 z_1 \cdots z_{k-1}$. The exponent $k-1-i$ is a genuine nonnegative integer because $i<k$.
--
--   The degenerate cases are:
--
--   - For $k = 0$, the value is $0$.
--   - For $k > n$, only the $n$ existing bits contribute. The value is then $2^{k-n}$ times the integer encoded by all of $z$, which amounts to padding $z$ with $k-n$ trailing zeros.
--
--   ### QAlgorithms.alg4Angle
--
--   This is a definition. It takes $n \in \mathbb{N}$, $x \in \mathbb{R}^{2^n}$ and $k, j \in \mathbb{N}$. Using the quantity $\mathrm{AT}_{n,x}$ defined under ampTreeValue above, set
--
--   $$
--   a = \mathrm{AT}_{n,x}(k+1,\,2j), \qquad b = \mathrm{AT}_{n,x}(k+1,\,2j+1).
--   $$
--
--   These are the sums of $x_i^2$ over the index blocks at level $k+1$ labelled $2j$ and $2j+1$. The angle is
--
--   $$
--   \theta_{n,x}(k,j) \;=\; 2\arccos\!\Big(\sqrt{a\cdot(a+b)^{-1}}\Big).
--   $$
--
--   Since $a,b \ge 0$, the ratio lies in $[0,1]$ whenever $a+b>0$. If $a+b = 0$, then $(a+b)^{-1}$ is taken to be $0$, so the square root is $0$ and the angle is $2\arccos 0 = \pi$.
--
--   ### QAlgorithms.alg4Step
--
--   This is a definition. For $n \in \mathbb{N}$, $x \in \mathbb{R}^{2^n}$ and a wire $k \in \{0,\dots,n-1\}$, it is the complex matrix $S_k$ indexed by $\{0,1\}^n \times \{0,1\}^n$ with entries
--
--   $$
--   (S_k)_{y,z} \;=\; \begin{cases} R_y\big(\theta_{n,x}(k,\ \mathrm{pre}(z,k))\big)_{\,y_k,\, z_k} & \text{if } y_a = z_a \text{ for all } a \ne k,\\[2pt] 0 & \text{otherwise.}\end{cases}
--   $$
--
--   The symbols are those defined earlier in this list:
--
--   - $R_y$ is the matrix defined under rotY.
--   - $\theta_{n,x}$ is the angle defined under alg4Angle.
--   - $\mathrm{pre}(z,k)$ is the integer encoded by the bits $z_0\cdots z_{k-1}$ of the column index $z$, most significant bit first, as defined under prefixVal.
--
--   Thus $S_k$ acts as a $2\times2$ rotation $R_y(\cdot)$ on wire $k$. Its angle is selected by the values of wires $0,\dots,k-1$, and it leaves all other wires unchanged.
--
--   ### QAlgorithms.alg4Unitary
--
--   This is a definition. For $n \in \mathbb{N}$ and $x \in \mathbb{R}^{2^n}$, it is the matrix on $\{0,1\}^n$ given by
--
--   $$
--   U_x \;=\; D_x \cdot S_{n-1} S_{n-2} \cdots S_1 S_0 .
--   $$
--
--   Here $S_k$ is the matrix defined under alg4Step. The product is ordered so that $S_0$ is applied first and $S_{n-1}$ last.
--
--   $D_x$ is the diagonal matrix with entries
--
--   $$
--   (D_x)_{z,z} = \begin{cases} -1 & \text{if } x_{\mathrm{int}(z)} < 0,\\ 1 & \text{otherwise,}\end{cases}
--   $$
--
--   where $\mathrm{int}(z) = \sum_{i:\,z_i=1} 2^{\,n-1-i}$ reads $z$ as a binary number with $z_0$ the most significant bit. The inequality is strict, so entries with $x_i = 0$ get sign $+1$.
--
--   If $n = 0$, the product of the $S_k$ is empty and equals the identity. In that case $U_x$ is the $1\times1$ matrix $(-1)$ if $x_0<0$ and $(1)$ otherwise.
--
--   No hypothesis is placed on $x$; for example, $x$ need not be normalized or nonzero.
--
--   ### QAlgorithms.htcxGateSet
--
--   This is a definition. It is the set consisting of exactly three gates.
--
--   1. **Hadamard.** The 1-qubit gate whose matrix on $\{0,1\}^1$ is
--      $$H = \tfrac{1}{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix},$$
--      indexed by the single bit.
--   2. **T gate.** The 1-qubit gate $T = \mathrm{diag}(1,\ e^{i\pi/4})$.
--   3. **CNOT.** The 2-qubit gate whose matrix on $\{0,1\}^2$, indexed by the pair (bit $0$, bit $1$), sends $|c,t\rangle \mapsto |c,\ t \oplus c\rangle$. Bit $0$ is the control and bit $1$ is the target. Concretely, the entry at row $(p_1,p_2)$ and column $(q_1,q_2)$ is $1$ if $p_1=q_1$ and $p_2 = q_2 \oplus q_1$, and $0$ otherwise.
--
--   A gate here is a pair consisting of an arity and a matrix on bit strings of that arity. Membership in the set therefore means equality with one of these three pairs. A gate's placement on wires is not part of the gate.
--
--   ### QAlgorithms.twoQubitGateSet
--
--   This is a definition. It is the set of all gates $g$ with:
--
--   - arity exactly $2$, and
--   - matrix (a $4\times4$ complex matrix indexed by $\{0,1\}^2$) that is unitary, i.e. $g^* g = g g^* = 1$.
--
--   It contains every two-qubit unitary, including those that are tensor products of one-qubit unitaries or the identity. It contains no gates of any other arity.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/GradientMethods.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
/-!
# Gradient algorithms, function oracles, subgradients, amplitude encoding, gate sets
(shared definition layer)

G. Nannicini, *Quantum algorithms for optimizers* (arXiv:2408.07086v5), cited "Nannicini p.N"
(PDF pages), Chapters 1, 4, 5 and 7. A collection of `d` registers of `q` qubits each is indexed by
`Fin d → Qubits q` (register `i` is the source's register `i + 1`); binary strings are read as
integers most significant bit first (`bitsToNat`).
-/

namespace QAlgorithms

/-- Nannicini p.106, Def. 5.1 and the binary oracle below it:
`U_F |x_1⟩ ⋯ |x_d⟩ |y⟩ = |x_1⟩ ⋯ |x_d⟩ |y ⊞ F(x)⟩`, where `⊞` is addition modulo `2^q` of the
integers represented (most significant bit first) by the `q`-bit output register. `F` takes
integer (here natural-number) values, reduced modulo `2^q` by `natToBits`. A permutation matrix;
column `r` is the image of `|r⟩`. (Not the frozen `xorOracle`, which adds bitwise.) -/
def modAddOracle (d q : ℕ) (F : (Fin d → Qubits q) → ℕ) :
    Matrix ((Fin d → Qubits q) × Qubits q) ((Fin d → Qubits q) × Qubits q) ℂ :=
  Matrix.of fun p r => if p.1 = r.1 ∧ p.2 = natToBits q (bitsToNat r.2 + F r.1) then 1 else 0

/-- Nannicini p.107 (§5.1.1) and p.110 (Alg. 3): the operator `M ⊗ ⋯ ⊗ M` acting with the same
matrix `M` on each of `d` registers (register `i` = index `i`), entry `∏_i M_{x_i, y_i}`. -/
def piKron {ι : Type*} (d : ℕ) (M : Matrix ι ι ℂ) : Matrix (Fin d → ι) (Fin d → ι) ℂ :=
  Matrix.of fun x y => ∏ i, M (x i) (y i)

/-- Nannicini p.108, Fig. 5.1 (and pp.107–108): the state before measurement of Jordan's gradient
circuit: start in `|0⟩_q^{⊗d} ⊗ |1⃗⟩_q`, apply `H^{⊗q}` to each of the `d` input registers and the
QFT `Q_q` (frozen `qftQubits`) to the output register, apply the binary oracle `U_F` once, then
`Q_q†` to each input register. -/
noncomputable def jordanGradientState (d q : ℕ) (F : (Fin d → Qubits q) → ℕ) :
    EuclideanSpace ℂ ((Fin d → Qubits q) × Qubits q) :=
  act (Matrix.kronecker (piKron d (star (qftQubits q))) (1 : Matrix (Qubits q) (Qubits q) ℂ))
    (act (modAddOracle d q F)
      (tensorVec (act (piKron d (hadamardN q)) (ket fun _ _ => false))
        (act (qftQubits q) (ket fun _ => true))))

/-- Nannicini p.109, §5.1.1: the point `ĵ = j/2^q − 1/2 + 1/2^{q+1}` of the symmetric grid
`G_q ⊂ [−1/2, 1/2]` represented by the `q`-bit string `j`. -/
noncomputable def gridPoint (q : ℕ) (j : Qubits q) : ℝ :=
  (bitsToNat j : ℝ) * ((2 : ℝ) ^ q)⁻¹ - 2⁻¹ + ((2 : ℝ) ^ (q + 1))⁻¹

/-- Nannicini p.109, §5.1.1: the Fourier transform on the grid `G_q`,
`Q_{G_q} |k⟩ = 2^{−q/2} Σ_j e^{2πi 2^q ĵ k̂} |j⟩` (column `k` is the image of `|k⟩`). -/
noncomputable def gridQFT (q : ℕ) : Matrix (Qubits q) (Qubits q) ℂ :=
  Matrix.of fun j k =>
    Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (gridPoint q j : ℂ) * (gridPoint q k : ℂ)) *
      ((Real.sqrt ((2 : ℝ) ^ q))⁻¹ : ℂ)

/-- Nannicini p.110, Alg. 3 (with the phase oracle of Def. 5.10 as used there): the state before
measurement of the gradient algorithm: `d` registers of `q` qubits in `|0⟩`, `H^{⊗q}` on each,
the phase oracle `U_f |x⟩ = e^{2πi 2^q f(x̂)} |x⟩` (`x̂` the grid point of `x`), then `Q_{G_q}†` on
each register. The outcome `k_j` of register `j` gives `g̃_j = gridPoint q k_j`. -/
noncomputable def gradientAlgState (d q : ℕ) (f : (Fin d → ℝ) → ℝ) :
    EuclideanSpace ℂ (Fin d → Qubits q) :=
  act (piKron d (star (gridQFT q)))
    (act (Matrix.diagonal fun x : Fin d → Qubits q =>
        Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ) ^ q * (f fun i => gridPoint q (x i) : ℂ)))
      (act (piKron d (hadamardN q)) (ket fun _ _ => false)))

/-- Nannicini p.112, Def. 5.9: `W` is a probability oracle for `f : X → [0, 1]`: `W` is unitary,
`f` takes values in `[0, 1]`, and for every `x`,
`W |0⟩|0⃗⟩|x⟩ = √f(x) |1⟩|ψ_x^{(1)}⟩ + √(1 − f(x)) |0⟩|ψ_x^{(0)}⟩` for some states `ψ_x^{(0)},
ψ_x^{(1)}`. Register order: the flag qubit first, then the work register (whose `|0⃗⟩` is `z0`)
together with the `x` register. -/
def IsProbabilityOracle {κ X : Type*} [Fintype κ] [DecidableEq κ] [Fintype X] [DecidableEq X]
    (z0 : κ) (W : Matrix (Bool × (κ × X)) (Bool × (κ × X)) ℂ) (f : X → ℝ) : Prop :=
  W ∈ Matrix.unitaryGroup (Bool × (κ × X)) ℂ ∧ (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
    ∀ x, ∃ ψ0 ψ1 : EuclideanSpace ℂ (κ × X), IsState ψ0 ∧ IsState ψ1 ∧
      act W (ket (false, (z0, x))) =
        (Real.sqrt (f x) : ℂ) • tensorVec (ket true) ψ1 +
          (Real.sqrt (1 - f x) : ℂ) • tensorVec (ket false) ψ0

/-- Nannicini p.115, Fig. 5.3: the Hadamard-test circuit on a flag qubit (first), a work register
of `n` qubits and an `x` register: in time order `H`, `X` on the flag, controlled-`U` on the work
register, `X`, controlled-`V` on work and `x` registers, `H`, `X`. Since `U` is sandwiched between
`X` gates it acts when the original flag is `|0⟩`; `V` acts when it is `|1⟩`. One controlled-`U`,
one controlled-`V` and five single-qubit gates. -/
noncomputable def hadamardTestCircuit {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (U : Matrix (Qubits n) (Qubits n) ℂ) (V : Matrix (Qubits n × X) (Qubits n × X) ℂ) :
    Matrix (Bool × (Qubits n × X)) (Bool × (Qubits n × X)) ℂ :=
  let Hf := Matrix.kronecker hadamard (1 : Matrix (Qubits n × X) (Qubits n × X) ℂ)
  let Xf := Matrix.kronecker pauliX (1 : Matrix (Qubits n × X) (Qubits n × X) ℂ)
  Xf * Hf * controlled V * Xf * controlled (Matrix.kronecker U (1 : Matrix X X ℂ)) * Xf * Hf

/-- Nannicini p.120, Def. 5.24 (and p.181, Rem. 8.6): `g ∈ V*` is an `ε`-subgradient of `f` at
`x̄` over the domain `D`: `f(x) ≥ f(x̄) + ⟨g, x − x̄⟩ − ε` for every `x ∈ D` (`ε = 0` is a
subgradient). The pairing `⟨g, x⟩` is the linear functional `g` applied to `x`. -/
def IsEpsSubgradOn {E : Type*} [AddCommGroup E] [Module ℝ E] (D : Set E) (f : E → ℝ) (ε : ℝ)
    (xbar : E) (g : Module.Dual ℝ E) : Prop :=
  ∀ x ∈ D, f xbar + g (x - xbar) - ε ≤ f x

/-- Nannicini p.181, §8.1: the trace inner product `⟨G, X⟩ = Tr(G X†)` as a real-linear functional
on matrices (real part; it is real when `G` and `X` are Hermitian). -/
noncomputable def traceRePairing {ι : Type*} [Fintype ι] (G : Matrix ι ι ℂ) :
    Module.Dual ℝ (Matrix ι ι ℂ) where
  toFun X := (G * X.conjTranspose).trace.re
  map_add' X Y := by
    simp [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.trace_add]
  map_smul' r X := by
    simp [Matrix.conjTranspose_smul, Matrix.trace_smul]

/-- Nannicini p.121, Def. 5.26: the central finite-difference gradient approximation
`∇^{(η)} f(x)_j = (f(x + η e_j) − f(x − η e_j)) / (2η)`. Junk value `0` at `η = 0`; the source
has `η > 0`, a hypothesis of the statements. -/
noncomputable def fdGradient {d : ℕ} (η : ℝ) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun j => (f (x + η • Pi.single j 1) - f (x - η • Pi.single j 1)) * (2 * η)⁻¹

/-- Nannicini p.121, Def. 5.27: the finite-difference Laplace approximation
`Δ^{(η)} f(x) = Σ_j (f(x + η e_j) − 2 f(x) + f(x − η e_j)) / η²`. Junk value `0` at `η = 0`. -/
noncomputable def fdLaplacian {d : ℕ} (η : ℝ) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ j, (f (x + η • Pi.single j 1) - 2 * f x + f (x - η • Pi.single j 1)) * (η ^ 2)⁻¹

/-- Nannicini p.119, Def. 5.20 (`p = 1`): the closed `ℓ₁` ball `B_1(x, r) = {y : ‖x − y‖₁ ≤ r}`.
The `ℓ_∞` ball is Mathlib's `Metric.closedBall` (the sup norm is the norm of `Fin d → ℝ`). -/
def ballL1 {d : ℕ} (x : Fin d → ℝ) (r : ℝ) : Set (Fin d → ℝ) :=
  {y | ∑ i, |x i - y i| ≤ r}

/-- Nannicini p.90, Def. 4.26: the rotation `R_Y(θ) = [[cos θ/2, −sin θ/2], [sin θ/2, cos θ/2]]`,
indexed by `Bool` (`false` = `|0⟩` = row/column 0). -/
noncomputable def rotY (θ : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => match a, b with
    | false, false => (Real.cos (θ / 2) : ℂ)
    | false, true => -(Real.sin (θ / 2) : ℂ)
    | true, false => (Real.sin (θ / 2) : ℂ)
    | true, true => (Real.cos (θ / 2) : ℂ)

/-- Nannicini p.124 (§5.2) and p.125 (Fig. 5.6): the value `N(k, j)` of node `(k, j)` (level `k`,
position `j`, both 0-based) of the binary tree built from `x ∈ ℝ^{2^n}`: the sum of `x_i²` over the
`j`-th block of `2^{n−k}` consecutive indices. `N(0, 0) = ‖x‖²`, `N(n, i) = x_i²`. -/
noncomputable def ampTreeValue (n : ℕ) (x : Fin (2 ^ n) → ℝ) (k j : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ n) => (i : ℕ) / 2 ^ (n - k) = j), x i ^ 2

/-- Nannicini p.126, Alg. 4: the integer value `j` (most significant bit first) of the first `k`
wires of `z`. -/
def prefixVal {n : ℕ} (z : Qubits n) (k : ℕ) : ℕ :=
  ∑ i : Fin n, if (i : ℕ) < k ∧ z i = true then 2 ^ (k - 1 - (i : ℕ)) else 0

/-- Nannicini p.126, Alg. 4, lines 2 and 5: the rotation angle
`2 arccos √(N(k+1, 2j) / (N(k+1, 2j) + N(k+1, 2j+1)))` used on wire `k` (0-based) when the first
`k` wires hold the value `j` (`k = 0` is line 2). A zero denominator gives the junk angle `π`; that
branch has amplitude `√N(k, j) = 0`, so it does not affect the state. -/
noncomputable def alg4Angle (n : ℕ) (x : Fin (2 ^ n) → ℝ) (k j : ℕ) : ℝ :=
  2 * Real.arccos (Real.sqrt (ampTreeValue n x (k + 1) (2 * j) *
    (ampTreeValue n x (k + 1) (2 * j) + ampTreeValue n x (k + 1) (2 * j + 1))⁻¹))

/-- Nannicini p.126, Alg. 4, line 5: the controlled rotation `Σ_j |j⟩⟨j| ⊗ R_Y(angle k j)` with
the first `k` wires as control and wire `k` as target, acting as the identity on the later wires:
entry `(y, z)` is `R_Y(angle k j)_{y_k, z_k}` if `y` and `z` agree off wire `k` (with `j` the value
of the first `k` wires), else `0`. -/
noncomputable def alg4Step (n : ℕ) (x : Fin (2 ^ n) → ℝ) (k : Fin n) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun y z =>
    if ∀ a, a ≠ k → y a = z a then rotY (alg4Angle n x k (prefixVal z k)) (y k) (z k) else 0

/-- Nannicini p.124 (§5.2) and p.126 (Alg. 4): the `n`-qubit circuit returned by Alg. 4, in time
order: the rotations `alg4Step n x k` for `k = 0, …, n − 1` (the source appends wire `k` in `|0⟩`
just before step `k`; here all `n` wires are present from the start, the later ones still in
`|0⟩`), then the sign diagonal `Σ_j sign(x_j) |j⟩⟨j|` of line 7, with sign `+1` at `x_j = 0` so
that it is unitary. -/
noncomputable def alg4Unitary (n : ℕ) (x : Fin (2 ^ n) → ℝ) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.diagonal (fun z => if x (bitsEquivFin n z) < 0 then -1 else 1) * orderedProd (alg4Step n x)

/-- Nannicini p.28, Thm. 1.43: the universal gate set `{H, T, CX}` in which gates are counted. -/
def htcxGateSet : Set Gate :=
  {Gate.ofMatrix1 hadamard, Gate.ofMatrix1 gateT, Gate.ofMatrix2 cnot}

/-- Nannicini p.172 (Lem. 7.39) and p.173 (Prop. 7.41): "two-qubit gates", i.e. arbitrary unitary
gates acting on two qubits. -/
def twoQubitGateSet : Set Gate :=
  {g | g.arity = 2 ∧ g.IsUnitary}

/-! ### Sanity tests -/

theorem natToBits_bitsToNat {q : ℕ} (z : Qubits q) : natToBits q (bitsToNat z) = z := by
  have h := (bitsEquivFin q z).isLt
  rw [bitsEquivFin_apply] at h
  unfold natToBits
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp [bitsEquivFin_apply, Nat.mod_eq_of_lt h]

example (d q : ℕ) : modAddOracle d q (fun _ => 0) = 1 := by
  ext p r
  by_cases h : p = r
  · subst h; simp [modAddOracle, natToBits_bitsToNat]
  · simp only [modAddOracle, Matrix.of_apply, add_zero, natToBits_bitsToNat, Matrix.one_apply, h,
      if_false]
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact h (Prod.ext h1 h2)

example {ι : Type*} [DecidableEq ι] (d : ℕ) : piKron d (1 : Matrix ι ι ℂ) = 1 := by
  ext x y
  simp [piKron, Matrix.one_apply, Finset.prod_boole, funext_iff]

example : gridPoint 1 ![false] = -(1 / 4) ∧ gridPoint 1 ![true] = 1 / 4 := by
  constructor <;> norm_num [gridPoint, bitsToNat]

example {d : ℕ} (η c : ℝ) (x : Fin d → ℝ) : fdGradient η (fun _ => c) x = 0 := by
  funext j; simp [fdGradient]

example {E : Type*} [AddCommGroup E] [Module ℝ E] (c : ℝ) (x : E) :
    IsEpsSubgradOn Set.univ (fun _ => c) 0 x 0 := by
  intro y _; simp

example : rotY 0 = 1 := by
  ext a b; cases a <;> cases b <;> simp [rotY]

example (n : ℕ) (x : Fin (2 ^ n) → ℝ) : ampTreeValue n x 0 0 = ∑ i, x i ^ 2 := by
  rw [ampTreeValue, Finset.filter_true_of_mem]
  intro i _
  simpa using Nat.div_eq_of_lt i.isLt

example : alg4Unitary 0 (fun _ => 1) = 1 := by
  simp [alg4Unitary, orderedProd]
  funext z
  norm_num

end QAlgorithms


