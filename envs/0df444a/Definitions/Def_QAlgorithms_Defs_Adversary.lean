-- Prove2me | Definitions.Def_QAlgorithms_Defs_Adversary
-- name    : QAlgorithms_Defs_Adversary
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:29:47.384977+00:00
-- url     : https://prove2.me/theorems/77568192-0740-404b-b640-d526ecd7bf20
-- title:
--   The generalized (negative-weights) adversary bound (shared definition layer)
-- statement:
--   The generalized (negative-weights) adversary bound (shared definition layer)
--
--   ### QAlgorithms.IsAdversaryMatrix
--
--   This defines a predicate on three objects:
--   - a Boolean function $f$ on Boolean strings $\iota \to \{\text{true},\text{false}\}$, indexed by a type $\iota$;
--   - a finite set $D$ of such strings;
--   - a real matrix $\Gamma$ with rows and columns indexed by the elements of $D$.
--
--   The predicate holds when both of the following are true:
--   1. $\Gamma$ is symmetric: $\Gamma_{xy} = \Gamma_{yx}$ for all $x, y \in D$.
--   2. $\Gamma_{xy} = 0$ whenever $f(x) = f(y)$. In particular all diagonal entries are $0$.
--
--   No nonnegativity of entries is required, and the zero matrix satisfies the predicate.
--
--   ### QAlgorithms.maskMatrix
--
--   Given a finite set $D$ of Boolean strings indexed by $\iota$, a real $D\times D$ matrix $\Gamma$, and a position $i \in \iota$, this defines the $D\times D$ real matrix $\Gamma_i$ by
--
--   $$
--   (\Gamma_i)_{xy} = \begin{cases} \Gamma_{xy} & \text{if } x_i \neq y_i,\\ 0 & \text{if } x_i = y_i. \end{cases}
--   $$
--
--   That is, $\Gamma_i$ keeps only the entries of pairs of strings that differ at position $i$.
--
--   ### QAlgorithms.maxMaskedNorm
--
--   Given a finite set $D$ of Boolean strings indexed by $\iota$ and a real $D\times D$ matrix $\Gamma$, this defines the real number
--
--   $$
--   \sup_{i\in\iota} \|\Gamma_i\|,
--   $$
--
--   with the following meanings:
--   - $\Gamma_i$ is the masked matrix of `maskMatrix`, keeping $\Gamma_{xy}$ only where $x_i \ne y_i$.
--   - $\|\cdot\|$ is the spectral norm, i.e. the $\ell^2\to\ell^2$ operator norm, i.e. the largest singular value.
--
--   The supremum is taken in $\mathbb{R}$ with its total-function convention:
--   - **Empty index set.** If $\iota$ is empty, the value is $0$.
--   - **Unbounded set.** The value would also be $0$ if the set of norms were unbounded above.
--
--   This second case cannot happen for finite $\iota$, where the supremum is a maximum.
--
--   ### QAlgorithms.progressMeasure
--
--   **Inputs.**
--   - A finite workspace type $W$ with decidable equality.
--   - A query count $T\in\mathbb{N}$.
--   - A finite set $D$ of Boolean strings indexed by $\iota$.
--   - A query algorithm $\mathcal{A}$ on input index set $\iota$, answer alphabet $\{\text{true},\text{false}\}$, workspace $W$, and $T$ queries. It consists of:
--     - a unit vector $\psi_{\text{start}}$ in $\mathbb{C}^{(\iota\times\text{Bool})\times W}$;
--     - unitaries $U_0,\dots,U_T$ on that space.
--   - A real $D\times D$ matrix $\Gamma$.
--   - Complex weights $\alpha : D \to \mathbb{C}$.
--   - A time step $t\in\{0,\dots,T\}$.
--
--   **States.** For a string $x$, let $O_x$ be the XOR oracle, $O_x|i,b\rangle = |i, b \oplus x_i\rangle$. The states are defined recursively:
--
--   $$
--   \psi^0_x = U_0\,\psi_{\text{start}}, \qquad \psi^{s+1}_x = U_{s+1}\,(O_x\otimes I_W)\,\psi^s_x .
--   $$
--
--   **The value.** The definition is the complex number
--
--   $$
--   W_t = \sum_{x\in D}\sum_{y\in D} \Gamma_{xy}\,\overline{\alpha_x}\,\alpha_y\,\big\langle \psi^t_x,\ \psi^t_y\big\rangle .
--   $$
--
--   The inner product is conjugate-linear in the first argument. No conditions are imposed on $\Gamma$ or $\alpha$ (e.g. no symmetry, adversary property, or normalisation).
--
--   ### QAlgorithms.advPm
--
--   For a Boolean function $f$ on Boolean strings indexed by $\iota$ and a finite set $D$ of such strings, this defines an element of $[0,\infty]$:
--
--   $$
--   \mathrm{ADV}^{\pm}(f,D) = \sup\Big\{\ \max\!\Big(0,\ \frac{\|\Gamma\|}{\max_i \|\Gamma_i\|}\Big)\ :\ \Gamma \in \mathbb{R}^{D\times D},\ \Gamma \text{ an adversary matrix},\ \Gamma\neq 0 \Big\}.
--   $$
--
--   **Terms in the formula.**
--   - **Adversary matrix.** "Adversary matrix" is the predicate `IsAdversaryMatrix`: $\Gamma$ is symmetric and $\Gamma_{xy}=0$ whenever $f(x)=f(y)$.
--   - **Spectral norm.** $\|\Gamma\|$ is the spectral norm.
--   - **Denominator.** $\max_i\|\Gamma_i\|$ is `maxMaskedNorm`: the real supremum over $i\in\iota$ of the spectral norm of $\Gamma$ restricted to pairs differing at position $i$. It is $0$ if $\iota$ is empty.
--
--   **Junk-value and edge-case conventions.**
--   - **Division by zero.** The ratio is a real number in which division by $0$ yields $0$. So any $\Gamma$ with zero denominator contributes $0$.
--   - **Truncation.** The ratio is mapped into $[0,\infty]$ by truncating negative values to $0$.
--   - **Empty supremum.** The supremum is taken in $[0,\infty]$. It is $0$ if there is no nonzero adversary matrix, e.g. when $f$ is constant on $D$ or $D$ has fewer than two elements.
--   - **Unboundedness.** The supremum may be $\infty$ if the ratios are unbounded.
--
--   ### QAlgorithms.DualFeasibleChilds
--
--   This is a predicate on four pieces of data:
--
--   - a Boolean function $f : \{0,1\}^\iota \to \{0,1\}$ on bit strings indexed by a finite type $\iota$;
--   - a finite set $D \subseteq \{0,1\}^\iota$ of inputs (the promise domain);
--   - a natural number $d$;
--   - a family of vectors $v_{x,i} \in \mathbb{C}^d$, one for each $x \in D$ and each coordinate $i \in \iota$, where $\mathbb{C}^d$ carries the standard Hermitian inner product.
--
--   The predicate holds iff, for every pair of **distinct** inputs $x \neq y$ in $D$,
--   $$\sum_{i \in \iota,\; x_i \neq y_i} \langle v_{x,i}, v_{y,i} \rangle \;=\; \begin{cases} 0 & \text{if } f(x) = f(y),\\ 1 & \text{if } f(x) \neq f(y).\end{cases}$$
--   The inner product $\langle a, b\rangle = \sum_k \overline{a_k}\, b_k$ is conjugate-linear in its first argument. The sum runs only over the coordinates where $x$ and $y$ differ.
--
--   Edge cases:
--
--   - Pairs with $x = y$ are not constrained.
--   - If $D$ has at most one element, the condition holds vacuously.
--   - If $d = 0$, every vector is zero and every such sum is $0$. The condition then holds iff $f$ takes the same value on all of $D$.
--
--   ### QAlgorithms.childsBComplexity
--
--   Take $f$, $D$, $d$ and the vector family $v_{x,i} \in \mathbb{C}^d$ as above (with $d$ implicit), together with a bit $b \in \{0,1\}$. This defines the nonnegative real number
--   $$C_b(f,D,v) \;=\; \max_{x \in D,\; f(x) = b}\; \sum_{i \in \iota} \|v_{x,i}\|^2,$$
--   where $\|\cdot\|$ is the Euclidean norm on $\mathbb{C}^d$.
--
--   The maximum is taken in the nonnegative reals. If no $x \in D$ has $f(x) = b$, including when $D = \emptyset$, the value is $0$.
--
--   ### QAlgorithms.childsDualObjective
--
--   For $f$, $D$ and $v$ as above, this is the nonnegative real number
--   $$\max\bigl(C_0(f,D,v),\; C_1(f,D,v)\bigr).$$
--   Here $C_b(f,D,v) = \max_{x\in D,\, f(x)=b} \sum_{i} \|v_{x,i}\|^2$, with the convention that an empty maximum is $0$.
--
--   Equivalently, the value is $\max_{x \in D} \sum_i \|v_{x,i}\|^2$, and it is $0$ if $D$ is empty.
--
--   ### QAlgorithms.DualFeasibleDeWolf
--
--   The data are:
--
--   - $f : \{0,1\}^\iota \to \{0,1\}$, with $\iota$ a finite index type;
--   - a finite set $D \subseteq \{0,1\}^\iota$;
--   - $d \in \mathbb{N}$;
--   - **two** vector families $u_{x,j}, v_{x,j} \in \mathbb{C}^d$, for $x \in D$ and $j \in \iota$.
--
--   The predicate holds iff, for **all** pairs $x, y \in D$ (including $x = y$),
--   $$\sum_{j \in \iota,\; x_j \neq y_j} \langle u_{x,j}, v_{y,j} \rangle \;=\; \begin{cases} 1 & \text{if } f(x) \neq f(y),\\ 0 & \text{if } f(x) = f(y).\end{cases}$$
--   The inner product is the standard Hermitian one, conjugate-linear in the first slot (the $u$-vector).
--
--   Edge cases:
--
--   - For $x = y$ the sum is empty and the right-hand side is $0$, so diagonal pairs are automatically satisfied.
--   - The condition is not symmetric in $x, y$, since $u$ always appears on the left and $v$ on the right.
--   - If $d = 0$, the condition holds iff $f$ is constant on $D$.
--   - If $D = \emptyset$, the condition holds vacuously.
--
--   ### QAlgorithms.dewolfDualObjective
--
--   Given a finite set $D \subseteq \{0,1\}^\iota$, a dimension $d$ (both implicit), and two vector families $u_{x,j}, v_{x,j} \in \mathbb{C}^d$ for $x \in D$ and $j \in \iota$, this is the nonnegative real number
--   $$\max_{x \in D}\; \max\Bigl(\sum_{j\in\iota} \|u_{x,j}\|^2,\; \sum_{j\in\iota} \|v_{x,j}\|^2\Bigr).$$
--   The value is $0$ when $D$ is empty. No function $f$ enters this quantity.
--
--   ### QAlgorithms.blockCompose
--
--   Let $f : \{0,1\}^\iota \to \{0,1\}$ and $g : \{0,1\}^\kappa \to \{0,1\}$. The block composition is the Boolean function on $\{0,1\}^{\iota\times\kappa}$ given by
--   $$(f \circ g)(y) \;=\; f\Bigl(\bigl(g\bigl((y_{i,j})_{j\in\kappa}\bigr)\bigr)_{i\in\iota}\Bigr).$$
--   In words, the input $y$ is split into blocks $y_{i,\cdot}$, one for each $i \in \iota$. The function $g$ is applied to each block, and $f$ is applied to the resulting string of $|\iota|$ bits.
--
--   ### QAlgorithms.reflProduct
--
--   Let $E$ be a finite-dimensional complex inner product space, and let $K, L \subseteq E$ be complex linear subspaces. This defines the continuous linear operator
--   $$R_K \circ R_L : E \to E.$$
--   Here $R_M = 2P_M - I$ is the reflection through the subspace $M$. It fixes $M$ pointwise and negates its orthogonal complement $M^\perp$. $P_M$ denotes the orthogonal projection onto $M$.
--
--   In the composition, $R_L$ is applied first and $R_K$ second.
--
--   ### QAlgorithms.eigenProjection
--
--   Let $E$ be a finite-dimensional complex inner product space, $U : E \to E$ a continuous linear operator, and $S \subseteq \mathbb{C}$ any set of complex numbers. This defines the orthogonal projection of $E$ onto the subspace
--   $$\sum_{\mu \in S} \ker(U - \mu I),$$
--   the span of all eigenspaces of $U$ for the values $\mu \in S$. The result is viewed as an operator $E \to E$.
--
--   For $\mu \in S$ that are not eigenvalues of $U$, the eigenspace is $\{0\}$ and contributes nothing. If $S$ contains no eigenvalue of $U$, the result is the zero operator.
--
--   No assumption is made on $U$ (such as unitarity or normality), so the eigenspaces need not be mutually orthogonal.
--
--   ### QAlgorithms.AdvSpace
--
--   For natural numbers $N$ and $d$, this is the complex Hilbert space
--   $$\mathbb{C}^{\{0,\dots,N\}\times\{0,1\}\times\{0,\dots,d\}}$$
--   with the standard Hermitian inner product. Its orthonormal basis vectors are $|j, b, k\rangle$ with $j \in \{0,\dots,N\}$, $b \in \{0,1\}$ and $k \in \{0,\dots,d\}$.
--
--   The space has dimension $2(N+1)(d+1)$. It can be read as three registers: one of dimension $N+1$, one of dimension $2$, and one of dimension $d+1$.
--
--   ### QAlgorithms.AdvAlg
--
--   For a natural number $N$, an object $P$ of this type bundles five pieces of data:
--
--   - a finite set $D \subseteq \{0,1\}^N$;
--   - an arbitrary function $f : \{0,1\}^N \to \{0,1\}$;
--   - a natural number $d$;
--   - two vector families $u_{y,j} \in \mathbb{C}^d$ and $v_{y,j} \in \mathbb{C}^d$, indexed by $y \in D$ and $j \in \{0,\dots,N-1\}$.
--
--   No conditions are imposed on these data. In particular, $u, v$ are not required to satisfy any feasibility constraint relative to $f$ and $D$, and $D$ may be empty.
--
--   ### QAlgorithms.AdvAlg.A
--
--   For a bundle $P = (D, f, d, u, v)$ of the type above, this is the real number
--   $$A \;=\; \max_{y \in D}\; \max\Bigl(\sum_{j=0}^{N-1} \|u_{y,j}\|^2,\; \sum_{j=0}^{N-1} \|v_{y,j}\|^2\Bigr),$$
--   the de Wolf objective of $(u, v)$ converted to a real number.
--
--   $A \ge 0$ always. $A = 0$ exactly when $D$ is empty or all the vectors $u_{y,j}, v_{y,j}$ are zero.
--
--   ### QAlgorithms.AdvAlg.thirdReg
--
--   For a bundle $P$ as above, with vector dimension $d$, and a vector $w = (w_0,\dots,w_{d-1}) \in \mathbb{C}^d$, this is the vector
--   $$(0, w_0, w_1, \dots, w_{d-1}) \in \mathbb{C}^{d+1}.$$
--   Coordinate $0$ is set to $0$, and coordinate $k+1$ equals $w_k$ for $k = 0,\dots,d-1$.
--
--   In basis notation this is $\sum_{k=0}^{d-1} w_k\, |k+1\rangle$, which is orthogonal to $|0\rangle$. The map preserves the norm.
--
--   ### QAlgorithms.AdvAlg.tPlus
--
--   **Setting.** Fix a natural number $N$ and a data package $P$ consisting of:
--
--   - a finite set $D \subseteq \{0,1\}^N$ of inputs;
--   - a Boolean function $f : \{0,1\}^N \to \{0,1\}$;
--   - a natural number $d$;
--   - two families of vectors $u_{x,j}, v_{x,j} \in \mathbb{C}^d$, indexed by $x \in D$ and $j \in \{0,\dots,N-1\}$.
--
--   The ambient space is the Euclidean space
--   $$\mathcal{H}_{N,d} = \mathbb{C}^{\{0,\dots,N\} \times \{0,1\} \times \{0,\dots,d\}},$$
--   with standard basis vectors $|i, b, k\rangle$.
--
--   **Definition.** For any $x \in \{0,1\}^N$ (not required to lie in $D$),
--   $$t^+_x = \tfrac{1}{\sqrt 2}\big(|0,0,0\rangle + |1, f(x), 0\rangle\big) \in \mathcal{H}_{N,d}.$$
--
--   **Edge case $N = 0$.** The first index ranges only over $\{0\}$, and the label "$1$" in that register wraps around to $0$. The second ket is then $|0, f(x), 0\rangle$. So if moreover $f(x) = 0$, the two kets coincide and $t^+_x = \sqrt 2\,|0,0,0\rangle$, which has norm $\sqrt 2$ rather than $1$.
--
--   ### QAlgorithms.AdvAlg.tMinus
--
--   **Setting.** As for `tPlus`: $N$ and $P = (D, f, d, u, v)$, with ambient space $\mathcal{H}_{N,d} = \mathbb{C}^{\{0,\dots,N\}\times\{0,1\}\times\{0,\dots,d\}}$.
--
--   **Definition.** For any $x \in \{0,1\}^N$ (not required to lie in $D$),
--   $$t^-_x = \tfrac{1}{\sqrt 2}\big(|0,0,0\rangle - |1, f(x), 0\rangle\big).$$
--
--   **Edge case $N = 0$.** The register label "$1$" wraps to $0$. If moreover $f(x) = 0$, the two kets coincide and $t^-_x = 0$.
--
--   ### QAlgorithms.AdvAlg.psi
--
--   **Setting.** As above: $N$, $P = (D, f, d, u, v)$, and $\mathcal{H}_{N,d}$.
--
--   **The constant $A$.** Let
--   $$A = \max_{x \in D} \max\Big(\sum_{j} \|u_{x,j}\|^2,\ \sum_j \|v_{x,j}\|^2\Big),$$
--   with the convention $A = 0$ when $D = \emptyset$.
--
--   **The padding map.** For $w \in \mathbb{C}^d$, let $\hat w \in \mathbb{C}^{d+1}$ be $w$ with a $0$ prepended:
--   $$\hat w = (0, w_0, \dots, w_{d-1}).$$
--
--   **Definition.** For each $y \in D$,
--   $$\psi_y = \frac{0.01}{\sqrt A}\, t^-_y \;-\; \sum_{j=0}^{N-1} |j+1\rangle \otimes |\neg y_j\rangle \otimes \widehat{v_{y,j}}.$$
--
--   Here:
--
--   - $t^-_y = \tfrac{1}{\sqrt2}\big(|0,0,0\rangle - |1,f(y),0\rangle\big)$, as in `tMinus`;
--   - $\otimes$ is the tensor product of coordinate vectors, so the $j$-th summand has entry $(v_{y,j})_k$ at basis index $(j+1, \neg y_j, k+1)$ and zero elsewhere.
--
--   **Remarks.**
--
--   - Only the vectors $v$ enter directly; $u$ enters only through $A$.
--   - If $A = 0$, then $\frac{0.01}{\sqrt A}$ is evaluated as $0$ (division by zero yields $0$), and $\psi_y$ reduces to the negated sum.
--   - If $N = 0$, the sum is empty.
--
--   ### QAlgorithms.AdvAlg.lambdaSpace
--
--   **Setting.** $N$ and $P$ as above.
--
--   **Definition.**
--   $$\Lambda = \big(\operatorname{span}_{\mathbb{C}}\{\psi_y : y \in D\}\big)^{\perp} \subseteq \mathcal{H}_{N,d},$$
--   the orthogonal complement of the span of the vectors $\psi_y$ from `psi`.
--
--   **Edge case.** If $D = \emptyset$, the span is $\{0\}$ and $\Lambda$ is all of $\mathcal{H}_{N,d}$.
--
--   ### QAlgorithms.AdvAlg.piSpace
--
--   **Setting.** $N$ and $P$ as above.
--
--   **Definition.** For $x \in \{0,1\}^N$, $\Pi_x \subseteq \mathcal{H}_{N,d}$ is the span of the standard basis vectors $|i, b, k\rangle$ satisfying at least one of the following:
--
--   - $i = j+1$ and $b = x_j$ for some $j \in \{0,\dots,N-1\}$, with arbitrary $k$; or
--   - $k = 0$, with arbitrary $i$ and $b$.
--
--   **Remark.** Only $x$ and the dimension $d$ of $P$ enter; $D$, $f$, $u$ and $v$ play no role.
--
--   ### QAlgorithms.AdvAlg.walk
--
--   **Setting.** $N$ and $P$ as above.
--
--   **Definition.** For $x \in \{0,1\}^N$, the walk operator is the continuous linear map on $\mathcal{H}_{N,d}$
--   $$W_x = R_{\Pi_x} \circ R_{\Lambda}.$$
--
--   Here:
--
--   - $R_K = 2\,\mathrm{Proj}_K - I$ denotes the orthogonal reflection through a subspace $K$; it fixes $K$ and negates $K^\perp$;
--   - $\Pi_x$ is from `piSpace` and $\Lambda$ is from `lambdaSpace`.
--
--   So $W_x$ applies $R_\Lambda$ first and then $R_{\Pi_x}$.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/Adversary.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_Search
/-!
# The generalized (negative-weights) adversary bound (shared definition layer)

Inputs are bit strings `x : ι → Bool` over a finite index type `ι` (the source's `[N]` or
`{1, …, n}`); a (possibly partial) Boolean function is `f : (ι → Bool) → Bool` together with
its domain `D : Finset (ι → Bool)`; only the values of `f` on `D` are ever read.
-/

namespace QAlgorithms

open scoped ComplexConjugate NNReal ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- de Wolf p.111 (§12.1), Childs p.118 (§23.2): `Γ` is an adversary matrix for `f` on `D`: a real
(possibly negative) symmetric `|D| × |D|` matrix with `Γ_{xy} = 0` whenever `f(x) = f(y)`. -/
def IsAdversaryMatrix (f : (ι → Bool) → Bool) (D : Finset (ι → Bool)) (Γ : Matrix D D ℝ) : Prop :=
  Γ.IsSymm ∧ ∀ x y : D, f x = f y → Γ x y = 0

/-- de Wolf p.112 (§12.1, Claim 2), Childs p.120 ((23.30)): `Γ_i`, obtained from `Γ` by setting
`Γ_{xy}` to `0` when `x_i = y_i`. -/
def maskMatrix {D : Finset (ι → Bool)} (Γ : Matrix D D ℝ) (i : ι) : Matrix D D ℝ :=
  Matrix.of fun x y => if (x : ι → Bool) i ≠ (y : ι → Bool) i then Γ x y else 0

/-- de Wolf p.112, Childs p.120: `max_i ‖Γ_i‖` (spectral norms). It is a supremum over the finite
type `ι`, hence a finite maximum; it is `0` when `ι` is empty (then `|D| ≤ 1` and every adversary
matrix is `0`). -/
noncomputable def maxMaskedNorm {D : Finset (ι → Bool)} (Γ : Matrix D D ℝ) : ℝ :=
  ⨆ i : ι, specNorm (maskMatrix Γ i)

/-- de Wolf p.111 (§12.1): the progress measure `S_t = Σ_{x,y ∈ D} Γ_{xy} α_x^* α_y ⟨ψ_x^t|ψ_y^t⟩`
of the algorithm `A` (standard queries to `x`) for the weights `α` (statements add
`Σ_x |α_x|² = 1`). -/
noncomputable def progressMeasure {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    {D : Finset (ι → Bool)} (A : QueryAlg ι Bool W T) (Γ : Matrix D D ℝ) (α : D → ℂ)
    (t : Fin (T + 1)) : ℂ :=
  ∑ x : D, ∑ y : D, (Γ x y : ℂ) * conj (α x) * α y *
    inner ℂ (A.stateAt (xorOracle (x : ι → Bool)) t) (A.stateAt (xorOracle (y : ι → Bool)) t)

/-- Childs p.123 ((24.1)): `Adv±(f) = max_Γ ‖Γ‖ / max_i ‖Γ_i‖` over the nonzero adversary matrices
of `f` on `D`. Taken in `ℝ≥0∞` so that the supremum is never a junk value (trap 5); it is `0`
when no nonzero adversary matrix exists (i.e. `f` constant on `D`), the convention for the
source's `0/0`. For `Γ ≠ 0` the denominator is positive (a nonzero `Γ_{xy}` has `x ≠ y`, hence
appears in some `Γ_i`). A total function is the case `D = Finset.univ`. -/
noncomputable def advPm (f : (ι → Bool) → Bool) (D : Finset (ι → Bool)) : ℝ≥0∞ :=
  ⨆ (Γ : Matrix D D ℝ) (_ : IsAdversaryMatrix f D Γ ∧ Γ ≠ 0),
    ENNReal.ofReal (specNorm Γ / maxMaskedNorm Γ)

/-- Childs p.124 (§24.1, (24.3)): the vectors `|v_{x,i}⟩ ∈ ℂ^d` (`x ∈ D`, `i ∈ ι`) are feasible for
the adversary dual: `Σ_{i : x_i ≠ y_i} ⟨v_{x,i}|v_{y,i}⟩ = 1 − δ_{f(x), f(y)}` for all `x ≠ y`. -/
def DualFeasibleChilds (f : (ι → Bool) → Bool) (D : Finset (ι → Bool)) (d : ℕ)
    (v : D → ι → EuclideanSpace ℂ (Fin d)) : Prop :=
  ∀ x y : D, x ≠ y →
    ∑ i ∈ Finset.univ.filter (fun i => (x : ι → Bool) i ≠ (y : ι → Bool) i),
      inner ℂ (v x i) (v y i) = if f x = f y then 0 else 1

/-- Childs p.124: the `b`-complexity `C_b = max_{x ∈ f^{−1}(b)} Σ_i ‖v_{x,i}‖²` (a maximum over a
finite set, `0` if `f` takes no value `b` on `D`). -/
noncomputable def childsBComplexity (f : (ι → Bool) → Bool) (D : Finset (ι → Bool)) {d : ℕ}
    (v : D → ι → EuclideanSpace ℂ (Fin d)) (b : Bool) : ℝ≥0 :=
  (Finset.univ.filter fun x : D => f x = b).sup fun x => ∑ i, ‖v x i‖₊ ^ 2

/-- Childs p.124 ((24.2)): the dual objective `max{C_0, C_1}`. -/
noncomputable def childsDualObjective (f : (ι → Bool) → Bool) (D : Finset (ι → Bool)) {d : ℕ}
    (v : D → ι → EuclideanSpace ℂ (Fin d)) : ℝ≥0 :=
  max (childsBComplexity f D v false) (childsBComplexity f D v true)

/-- de Wolf p.113 (§12.2): the vectors `u_{xj}, v_{xj} ∈ ℂ^d` are feasible for de Wolf's dual SDP:
`Σ_{j : x_j ≠ y_j} ⟨u_{xj}|v_{yj}⟩ = [f(x) ≠ f(y)]` for all `x, y ∈ D`. -/
def DualFeasibleDeWolf (f : (ι → Bool) → Bool) (D : Finset (ι → Bool)) (d : ℕ)
    (u v : D → ι → EuclideanSpace ℂ (Fin d)) : Prop :=
  ∀ x y : D,
    ∑ j ∈ Finset.univ.filter (fun j => (x : ι → Bool) j ≠ (y : ι → Bool) j),
      inner ℂ (u x j) (v y j) = if f x ≠ f y then 1 else 0

/-- de Wolf p.113 (§12.2): the dual objective `max_{x ∈ D} max(Σ_j ‖u_{xj}‖², Σ_j ‖v_{xj}‖²)`. -/
noncomputable def dewolfDualObjective {D : Finset (ι → Bool)} {d : ℕ}
    (u v : D → ι → EuclideanSpace ℂ (Fin d)) : ℝ≥0 :=
  Finset.univ.sup fun x : D => max (∑ j, ‖u x j‖₊ ^ 2) (∑ j, ‖v x j‖₊ ^ 2)

/-- Childs p.126 (§24.5): the composition `f ∘ g`, `(f ∘ g)(y) = f(g(y¹), …, g(yⁿ))`, where block
`i` of the input is `yⁱ = (y(i, j))_j` (the source's `n` consecutive blocks of `m` bits, up to the
relabelling `finProdFinEquiv`, under which `Adv±` is invariant). -/
def blockCompose {κ : Type*} (f : (ι → Bool) → Bool) (g : (κ → Bool) → Bool) :
    (ι × κ → Bool) → Bool :=
  fun y => f fun i => g fun j => y (i, j)

/-- Childs p.128 (§24.6, `U := (2Π − I)(2∆ − I)`), de Wolf p.114–115 (§12.3,
`U_x = (2Π_x − I)(2Λ − I)`): the product of the reflections through `K` and through `L` (the
reflection through `L` is applied first), on a finite-dimensional complex inner-product space. -/
noncomputable def reflProduct {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (K L : Submodule ℂ E) : E →L[ℂ] E :=
  K.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp
    L.reflection.toContinuousLinearEquiv.toContinuousLinearMap

/-- Childs p.128 (Lemma 24.3: "`P_ω` the projector onto eigenvectors of `U` with eigenvalues `e^{iθ}`
with `|θ| < ω`"), de Wolf p.115 (§12.3: `P_Θ = Σ_{β : |θ_β| ≤ Θ} |β⟩⟨β|`): the orthogonal
projection onto the span of the eigenvectors of `U` whose eigenvalue lies in `S`. For a unitary
`U` (orthogonal eigenspaces) this is `Σ_{β : λ_β ∈ S} |β⟩⟨β|` for any orthonormal eigenbasis.
Childs's `P_ω` is `S = {λ | |arg λ| < ω}`, de Wolf's `P_Θ` is `S = {λ | |arg λ| ≤ Θ}`; `Complex.arg`
takes values in `(−π, π]`, the sources' range for `θ`. -/
noncomputable def eigenProjection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (U : E →L[ℂ] E) (S : Set ℂ) : E →L[ℂ] E :=
  (⨆ μ ∈ S, Module.End.eigenspace (U : E →ₗ[ℂ] E) μ).starProjection

/-! ### The objects of de Wolf §12.3 -/

/-- de Wolf p.114 (§12.3): the state space of the algorithm: a first register with basis `|0⟩` and
`|j⟩`, `j ∈ [N]` (input position `j : Fin N` is index `j.succ`), one qubit, and a third register
with basis `|0⟩, |1⟩, …, |d⟩` (a vector `w ∈ ℂ^d` sits on the indices `1, …, d`). -/
abbrev AdvSpace (N d : ℕ) := EuclideanSpace ℂ (Fin (N + 1) × (Bool × Fin (d + 1)))

/-- de Wolf p.114 (§12.3): the data of the algorithm: a function `f` on the domain `D ⊆ {0,1}^N`
and vectors `u_{xj}, v_{xj} ∈ ℂ^d` (a solution of the dual SDP, whose feasibility
`DualFeasibleDeWolf` is a hypothesis of the statements). -/
structure AdvAlg (N : ℕ) where
  /-- The domain of the partial function. -/
  D : Finset (Fin N → Bool)
  /-- The function (only its values on `D` matter). -/
  f : (Fin N → Bool) → Bool
  /-- The dimension of the dual vectors. -/
  d : ℕ
  /-- The vectors `u_{xj}`. -/
  u : D → Fin N → EuclideanSpace ℂ (Fin d)
  /-- The vectors `v_{xj}`. -/
  v : D → Fin N → EuclideanSpace ℂ (Fin d)

namespace AdvAlg

variable {N : ℕ} (P : AdvAlg N)

/-- de Wolf p.114: `A`, the objective value of the dual solution. -/
noncomputable def A : ℝ :=
  (dewolfDualObjective P.u P.v : ℝ)

/-- A vector of `ℂ^d` placed on the basis states `|1⟩, …, |d⟩` of the third register. -/
noncomputable def thirdReg (w : EuclideanSpace ℂ (Fin P.d)) : EuclideanSpace ℂ (Fin (P.d + 1)) :=
  WithLp.toLp 2 (Fin.cons 0 fun k => w k)

/-- de Wolf p.114: `|t^+_x⟩ = (|0⟩|0⟩|0⟩ + |1⟩|f(x)⟩|0⟩)/√2`, with `|1⟩` the first-register basis
state of index `1` (copied literally; it needs `N ≥ 1`, for `N = 0` the index `1` wraps to `0`). -/
noncomputable def tPlus (x : Fin N → Bool) : AdvSpace N P.d :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (ket ((0 : Fin (N + 1)), (false, (0 : Fin (P.d + 1)))) +
    ket ((1 : Fin (N + 1)), (P.f x, (0 : Fin (P.d + 1)))))

/-- de Wolf p.114: `|t^−_x⟩ = (|0⟩|0⟩|0⟩ − |1⟩|f(x)⟩|0⟩)/√2`. -/
noncomputable def tMinus (x : Fin N → Bool) : AdvSpace N P.d :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (ket ((0 : Fin (N + 1)), (false, (0 : Fin (P.d + 1)))) -
    ket ((1 : Fin (N + 1)), (P.f x, (0 : Fin (P.d + 1)))))

/-- de Wolf p.114: the (unnormalized) state `|ψ_y⟩ = (0.01/√A) |t^−_y⟩ − Σ_j |j⟩|ȳ_j⟩|v_{yj}⟩`,
`ȳ_j = 1 − y_j`. (Statements assume `A ≥ 1`, as the source does, so `√A > 0`.) -/
noncomputable def psi (y : P.D) : AdvSpace N P.d :=
  ((0.01 / Real.sqrt P.A : ℝ) : ℂ) • P.tMinus y -
    ∑ j : Fin N, tensorVec (ket j.succ) (tensorVec (ket (!(y : Fin N → Bool) j)) (P.thirdReg (P.v y j)))

/-- de Wolf p.114–115: the subspace of `Λ`, orthogonal to the span of the `|ψ_y⟩`, `y ∈ D`. -/
noncomputable def lambdaSpace : Submodule ℂ (AdvSpace N P.d) :=
  (Submodule.span ℂ (Set.range P.psi))ᗮ

/-- de Wolf p.115: the subspace of `Π_x`, spanned by the states with `|j⟩|x_j⟩` in the first two
registers (`j ∈ [N]`, any third register) and the states with `|0⟩` in the third register. -/
noncomputable def piSpace (x : Fin N → Bool) : Submodule ℂ (AdvSpace N P.d) :=
  Submodule.span ℂ (ket '' {z : Fin (N + 1) × (Bool × Fin (P.d + 1)) |
    (∃ j : Fin N, z.1 = j.succ ∧ z.2.1 = x j) ∨ z.2.2 = 0})

/-- de Wolf p.114: `U_x = (2Π_x − I)(2Λ − I)`. -/
noncomputable def walk (x : Fin N → Bool) : AdvSpace N P.d →L[ℂ] AdvSpace N P.d :=
  reflProduct (P.piSpace x) P.lambdaSpace

end AdvAlg

/-! ### Sanity tests -/

/-- The zero matrix is an adversary matrix for every function. -/
example (f : (ι → Bool) → Bool) (D : Finset (ι → Bool)) : IsAdversaryMatrix f D 0 :=
  ⟨Matrix.isSymm_zero, fun _ _ _ => rfl⟩

/-- `Γ_i` keeps exactly the entries where `x_i ≠ y_i`. -/
example {D : Finset (ι → Bool)} (Γ : Matrix D D ℝ) (i : ι) (x : D) : maskMatrix Γ i x x = 0 := by
  simp [maskMatrix]

/-- A constant function has no nonzero adversary matrix, so `Adv± = 0`. -/
example (D : Finset (ι → Bool)) : advPm (fun _ => true) D = 0 := by
  refine le_antisymm (iSup₂_le fun Γ hΓ => ?_) bot_le
  exfalso
  exact hΓ.2 (Matrix.ext fun x y => hΓ.1.2 x y rfl)

/-- A reflection is an involution, so `(2Π_K − I)(2Π_K − I) = I`. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (K : Submodule ℂ E) (v : E) : reflProduct K K v = v := by
  simp [reflProduct, Submodule.reflection_reflection]

/-- The reflection through the whole space is the identity: `2Π − I = I` for `Π = I`. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (v : E) : (⊤ : Submodule ℂ E).reflection v = v := by
  simp [Submodule.reflection_apply, Submodule.starProjection_top, two_smul]

/-- de Wolf p.116 (§12.4): composing with the identity on one block gives `f` back. -/
example (f : (ι → Bool) → Bool) (y : ι × Unit → Bool) :
    blockCompose f (fun z : Unit → Bool => z ()) y = f fun i => y (i, ()) := rfl

end QAlgorithms


