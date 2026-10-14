-- Prove2me | Definitions.Def_QAlgorithms_Defs_Fourier
-- name    : QAlgorithms_Defs_Fourier
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:28:23.693013+00:00
-- url     : https://prove2.me/theorems/e3a12e8d-53f8-4b04-a941-6a1005d2bf1f
-- title:
--   Quantum Fourier transform, phase estimation, period finding, Abelian HSP
-- statement:
--   Quantum Fourier transform, phase estimation, period finding, Abelian HSP
--
--   ### QAlgorithms.qftMatrix
--
--   For a natural number $N$, this is the $N\times N$ complex matrix indexed by $j,k \in \{0,\dots,N-1\}$ with entries
--
--   $$
--   (F_N)_{j,k} \;=\; \frac{1}{\sqrt N}\,\exp\!\Big(\frac{2\pi i\, jk}{N}\Big),
--   $$
--
--   where the product $jk$ is the ordinary natural-number product. The sign in the exponent is $+$. For $N=0$ the index set is empty, so the matrix is the empty matrix.
--
--   ### QAlgorithms.qftQubits
--
--   For a natural number $n$, this is the matrix on $n$-bit strings $\{0,1\}^n$ obtained by reindexing $F_{2^n}$ (the matrix of `qftMatrix` with $N = 2^n$). Its entries are
--
--   $$
--   (\mathrm{QFT}_n)_{y,z} = (F_{2^n})_{e(y),e(z)} = \frac{1}{\sqrt{2^n}}\exp\!\Big(\frac{2\pi i\, e(y)e(z)}{2^n}\Big).
--   $$
--
--   Here $e : \{0,1\}^n \to \{0,\dots,2^n-1\}$ is the bijection $e(b) = \sum_{i=0}^{n-1} b_i\,2^{\,n-1-i}$, with $b_i \in \{0,1\}$. That is, position $0$ is the most significant bit (big-endian). For $n=0$ this is the $1\times 1$ matrix $(1)$.
--
--   ### QAlgorithms.qftGateSet
--
--   This is a set of gates. A gate is a pair consisting of an arity $k$ and a complex matrix on $\{0,1\}^k$, and membership means equality of both components. The set is the union of three parts:
--
--   1. **Hadamard.** The single 1-qubit gate whose matrix is $\frac{1}{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$, read on the value of bit $0$.
--   2. **Controlled rotations.** For every natural number $s\ge 1$, the 2-qubit gate whose matrix acts on $|b_0 b_1\rangle$ as follows:
--      - it is diagonal;
--      - its entry at $|b_0 b_1\rangle$ is $e^{2\pi i/2^s}$ when $b_0=b_1=1$, and $1$ otherwise.
--
--      This is the controlled version of $R_s = \mathrm{diag}(1, e^{2\pi i/2^s})$, with bit $0$ as the control and bit $1$ as the target.
--   3. **Swap.** The 2-qubit gate with matrix entry $1$ at row $(p_0,p_1)$, column $(q_0,q_1)$ exactly when $(p_0,p_1)=(q_1,q_0)$, and $0$ otherwise. That is, it maps $|b_0b_1\rangle \mapsto |b_1b_0\rangle$.
--
--   ### QAlgorithms.controlledPower
--
--   This takes the following data:
--
--   - a finite index type $\kappa$ with decidable equality;
--   - a natural number $n$;
--   - an arbitrary complex matrix $U$ on $\kappa$ (no unitarity is assumed).
--
--   It is the matrix on $\{0,1\}^n\times\kappa$ with entries
--
--   $$
--   C_U\big((y,a),(z,b)\big) = \begin{cases} \big(U^{\,\nu(y)}\big)_{a,b} & y=z,\\ 0 & y\neq z,\end{cases}
--   \qquad \nu(y)=\sum_{i=0}^{n-1} y_i\,2^{\,n-1-i}.
--   $$
--
--   In words, $C_U$ is block-diagonal. It acts as $U^{\nu(y)}$ on the second register when the first register holds the string $y$, read big-endian as a number. The block for $y=0^n$ is $U^0=I$.
--
--   ### QAlgorithms.phaseEstimationState
--
--   This takes the following data:
--
--   - a finite index type $\kappa$ with decidable equality;
--   - a natural number $n$;
--   - an arbitrary complex matrix $U$ on $\kappa$;
--   - an arbitrary vector $\psi$ in the complex Euclidean space on $\kappa$. Neither unitarity of $U$ nor normalisation of $\psi$ is assumed.
--
--   The vector is
--
--   $$
--   (\mathrm{QFT}_n^{*}\otimes I)\;C_U\;(\mathrm{QFT}_n\otimes I)\;\big(|0^n\rangle\otimes\psi\big).
--   $$
--
--   The pieces are as follows:
--
--   - $|0^n\rangle\otimes\psi$ is the vector with value $\psi(a)$ at $(0^n,a)$ and $0$ at every $(y,a)$ with $y\neq 0^n$.
--   - $\mathrm{QFT}_n$ is the matrix with entries $2^{-n/2}\exp(2\pi i\,e(y)e(z)/2^n)$, where $e$ is the big-endian bijection $\{0,1\}^n \to \{0,\dots,2^n-1\}$.
--   - $\mathrm{QFT}_n^{*}$ is its conjugate transpose.
--   - $C_U$ is the block-diagonal matrix that applies $U^{e(y)}$ to the second register when the first register is $y$.
--
--   The rightmost matrix is applied first, so the forward QFT acts first and its conjugate transpose acts last.
--
--   ### QAlgorithms.HasPeriod
--
--   For $f:\mathbb N\to\mathbb N$ and $r\in\mathbb N$, the statement $\mathrm{HasPeriod}(f,r)$ means
--
--   $$
--   \forall a,b\in\mathbb N:\quad f(a)=f(b) \iff a\equiv b \pmod r .
--   $$
--
--   $r=0$ is not excluded. Congruence modulo $0$ means equality, so $\mathrm{HasPeriod}(f,0)$ says that $f$ is injective. $\mathrm{HasPeriod}(f,1)$ says that $f$ is constant.
--
--   ### QAlgorithms.shorEll
--
--   For $N\in\mathbb N$, this is $\ell(N)=\lceil \log_2(N^2+1)\rceil$. Precisely, $\ell(N)$ is the least natural number $\ell$ with $N^2+1\le 2^{\ell}$, equivalently $N^2<2^\ell$. Edge values: $\ell(0)=0$ and $\ell(1)=1$.
--
--   ### QAlgorithms.shorRunState
--
--   Let $N\in\mathbb N$ and $f:\mathbb N\to\mathbb N$ be arbitrary. Write $\ell = \ell(N)$, the least $\ell$ with $N^2+1\le 2^\ell$, and $m$ for the least natural number with $N\le 2^m$. Note $m=0$ when $N\le 1$. The vector lives in the Euclidean space with basis $|a,b\rangle$, $a\in\{0,1\}^\ell$, $b\in\{0,1\}^m$, and equals
--
--   $$
--   (\mathrm{QFT}_\ell\otimes I)\;O_g\;(\mathrm{QFT}_\ell\otimes I)\;|0^\ell,0^m\rangle .
--   $$
--
--   The pieces are as follows:
--
--   - $\mathrm{QFT}_\ell$ has entries $2^{-\ell/2}\exp(2\pi i\,e(a)e(a')/2^\ell)$, where $e$ reads a string big-endian as a number.
--   - $O_g|a,b\rangle=|a,b\oplus g(a)\rangle$, with $\oplus$ the bitwise XOR.
--   - $g(a)$ is the $m$-bit big-endian representation of $f(e(a)) \bmod 2^m$. Values of $f$ are therefore reduced modulo $2^m$.
--
--   The forward QFT (not its inverse) is applied both before and after the oracle. No hypothesis on $f$ is imposed.
--
--   ### QAlgorithms.abelianChar
--
--   Let $l\in\mathbb N$, and let $N_0,\dots,N_{l-1}$ be positive natural numbers. Consider the group $G=\prod_{i<l}\mathbb Z/N_i\mathbb Z$. For $g,h\in G$, define
--
--   $$
--   \chi(g,h)=\prod_{i=0}^{l-1}\exp\!\Big(\frac{2\pi i\,\bar g_i\,\bar h_i}{N_i}\Big),
--   $$
--
--   where $\bar g_i,\bar h_i\in\{0,\dots,N_i-1\}$ are the canonical representatives of the components $g_i,h_i$. For $l=0$ the product is empty and $\chi=1$.
--
--   ### QAlgorithms.annihilator
--
--   Let $G=\prod_{i<l}\mathbb Z/N_i\mathbb Z$ with all $N_i>0$. For an additive subgroup $H\le G$, this is the set
--
--   $$
--   H^{\perp}=\{g\in G : \chi(g,h)=1 \text{ for all } h\in H\}.
--   $$
--
--   Here $\chi(g,h)=\prod_i \exp(2\pi i\,\bar g_i\bar h_i/N_i)$, with $\bar g_i,\bar h_i$ the representatives of $g_i,h_i$ in $\{0,\dots,N_i-1\}$.
--
--   ### QAlgorithms.qftAbelian
--
--   Let $G=\prod_{i<l}\mathbb Z/N_i\mathbb Z$ with all $N_i>0$. This is the complex matrix indexed by $G\times G$ with entries
--
--   $$
--   (F_G)_{g,k}=\frac{1}{\sqrt{|G|}}\;\chi(k,g),\qquad |G|=\prod_{i} N_i,
--   $$
--
--   where $\chi(k,g)=\prod_i\exp(2\pi i\,\bar k_i\bar g_i/N_i)$ and $\bar k_i,\bar g_i\in\{0,\dots,N_i-1\}$ are the canonical representatives. For $l=0$ the group has one element and $F_G=(1)$.
--
--   ### QAlgorithms.Hides
--
--   This defines a predicate on a function $f : G \to S$ and a subgroup $H \le G$, where $G$ is any group (written multiplicatively) and $S$ is any type. No finiteness or other structure is assumed on $G$ or $S$. We say $f$ **hides** $H$ when
--
--   $$
--   \forall x, y \in G:\quad f(x) = f(y) \iff x^{-1} y \in H .
--   $$
--
--   Equivalently, $f$ is constant on each left coset $xH$ and takes distinct values on distinct left cosets.
--
--   The attribute also generates an additive version, `AddHides`, for an additive group $G$ and an additive subgroup $H$. It states:
--
--   $$
--   \forall x, y \in G:\quad f(x) = f(y) \iff -x + y \in H .
--   $$
--
--   ### QAlgorithms.uniformState
--
--   For a finite type $\iota$, this defines a vector $u_\iota$ in the complex Euclidean space $\mathbb{C}^\iota$ with the standard $\ell^2$ inner product. Every coordinate of the vector equals the same constant:
--
--   $$
--   (u_\iota)_i = \frac{1}{\sqrt{|\iota|}} \quad \text{for all } i \in \iota .
--   $$
--
--   For nonempty $\iota$ this is the uniform superposition $\frac{1}{\sqrt{|\iota|}}\sum_i |i\rangle$, a unit vector. If $\iota$ is empty, the space is zero-dimensional and the vector is the zero vector.
--
--   ### QAlgorithms.hspStandardState
--
--   **Inputs.**
--   - A length $l \in \mathbb{N}$ and moduli $N : \{0,\dots,l-1\} \to \mathbb{N}$ with every $N_i \neq 0$.
--   - The group $G = \prod_{i<l} \mathbb{Z}/N_i\mathbb{Z}$ (for $l = 0$ this is the trivial one-element group).
--   - A finite additive commutative group $S$ with decidable equality.
--   - A function $f : G \to S$. No condition on $f$ is imposed; in particular it is not required to hide any subgroup.
--
--   **The vector.** This defines a vector in $\mathbb{C}^{G \times S}$, namely
--
--   $$
--   \big(F_G \otimes I_S\big)\, O_f\, \big(u_G \otimes |0\rangle\big).
--   $$
--
--   The matrix product is applied to the vector as a single matrix, so $O_f$ acts first. The ingredients are:
--
--   - **Uniform state.** $u_G$ is the uniform vector on $G$, with every entry equal to $1/\sqrt{|G|}$ and $|G| = \prod_i N_i$.
--   - **Initial basis vector.** $|0\rangle$ is the standard basis vector of $\mathbb{C}^S$ at $0 \in S$.
--   - **Tensor product.** $\otimes$ is the tensor product of vectors, $(\psi\otimes\varphi)_{(g,s)} = \psi_g\varphi_s$, and the Kronecker product of matrices indexed by $G \times S$.
--   - **XOR oracle.** $O_f$ is the $(G\times S)\times(G\times S)$ matrix whose $((g',s'),(g,s))$ entry is $1$ if $g' = g$ and $s' = s + f(g)$, and $0$ otherwise. Thus $O_f|g,s\rangle = |g, s+f(g)\rangle$.
--   - **Fourier matrix.** $F_G$ is the $G\times G$ matrix with entries
--     $$
--     (F_G)_{g,k} = \frac{1}{\sqrt{|G|}}\,\chi(k,g), \qquad \chi(k,g) = \prod_{i<l} \exp\!\Big(\frac{2\pi i\, \bar k_i\, \bar g_i}{N_i}\Big),
--     $$
--     where $\bar k_i, \bar g_i \in \{0,\dots,N_i-1\}$ are the canonical representatives.
--   - **Identity.** $I_S$ is the identity matrix on $S$.
--
--   **Explicit amplitudes.** Unfolding gives the amplitude at $(k,s)$:
--
--   $$
--   \frac{1}{|G|}\sum_{g \in G,\ f(g)=s} \chi(g,k).
--   $$
--
--   This is only the state vector; no measurement is part of the definition.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/Fourier.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_Query
/-!
# Quantum Fourier transform, phase estimation, period finding, Abelian HSP
(shared definition layer)

Conventions: `ω_N = e^{2πi/N}` with sign `+` and normalization `1/√N` (de Wolf p.41; trap Q9);
the qubit QFT uses the most-significant-bit-first index map `bitsEquivFin`.
-/

namespace QAlgorithms

/-- de Wolf p.41 (§4.1): the Fourier matrix `F_N`, whose `(j, k)` entry is
`ω_N^{jk} / √N = e^{2πi jk/N} / √N` (rows and columns indexed by `0, …, N − 1`). Its inverse is the
conjugate transpose `star (qftMatrix N)` (entries `ω_N^{−jk}/√N`, p.42). -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k =>
    Complex.exp (2 * Real.pi * Complex.I * (((j : ℕ) * (k : ℕ) : ℕ) : ℂ) / (N : ℂ)) /
      (Real.sqrt N : ℂ)

/-- de Wolf p.43 (§4.4), p.44 (§4.5): the `n`-qubit quantum Fourier transform `F_{2ⁿ}`, with
`|k⟩ = |k₁ … kₙ⟩`, `k₁` the most significant bit (the index map `bitsEquivFin`). -/
noncomputable def qftQubits (n : ℕ) : Matrix (Qubits n) (Qubits n) ℂ :=
  (qftMatrix (2 ^ n)).submatrix (bitsEquivFin n) (bitsEquivFin n)

/-- de Wolf p.44–45 (§4.5): the elementary gates allowed for the QFT circuit: Hadamards,
controlled-`R_s` gates (`s ≥ 1`; `R_1 = Z`, as the source notes), and the swap gates used at the
end of the circuit. -/
def qftGateSet : Set Gate :=
  {Gate.ofMatrix1 hadamard} ∪ {g | ∃ s : ℕ, 1 ≤ s ∧ g = Gate.ofMatrix2 (controlled (rotR s))} ∪
    {Gate.ofMatrix2 swapGate}

/-- de Wolf p.46 (§4.6, step 3): the map `|j⟩|ψ⟩ ↦ |j⟩ U^j |ψ⟩` (apply `U` to the second register
`j` times, `j` read most significant bit first), i.e. `Σ_j |j⟩⟨j| ⊗ U^j`. -/
def controlledPower {κ : Type*} [Fintype κ] [DecidableEq κ] (n : ℕ) (U : Matrix κ κ ℂ) :
    Matrix (Qubits n × κ) (Qubits n × κ) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then (U ^ bitsToNat p.1) p.2 q.2 else 0

/-- de Wolf p.46 (§4.6, steps 1–4): the state of phase estimation before the final measurement:
from `|0ⁿ⟩|ψ⟩`, apply `F_{2ⁿ}` to the first register, the controlled powers `|j⟩|ψ⟩ ↦ |j⟩U^j|ψ⟩`,
and `F_{2ⁿ}^{−1}` to the first register. The law of the measured estimate is `marginalFst`. -/
noncomputable def phaseEstimationState {κ : Type*} [Fintype κ] [DecidableEq κ] (n : ℕ)
    (U : Matrix κ κ ℂ) (ψ : EuclideanSpace ℂ κ) : EuclideanSpace ℂ (Qubits n × κ) :=
  act (Matrix.kronecker (star (qftQubits n)) (1 : Matrix κ κ ℂ) * controlledPower n U *
    Matrix.kronecker (qftQubits n) (1 : Matrix κ κ ℂ)) (tensorVec (zeroKet n) ψ)

/-- de Wolf p.50 (§5.2, the period-finding problem): `f` has period `r`: `f(a) = f(b)` iff
`a = b mod r`. (The problem adds `r ∈ {1, …, N}` and `f : ℕ → {0, …, N − 1}`.) -/
def HasPeriod (f : ℕ → ℕ) (r : ℕ) : Prop :=
  ∀ a b, f a = f b ↔ a ≡ b [MOD r]

/-- de Wolf p.51 (§5.3: "pick some `q = 2^ℓ` such that `N² < q ≤ 2N²`"): `ℓ`, the least natural
number with `2^ℓ > N²` (`Nat.clog 2 (N² + 1)`); for `N ≥ 1`, `q = 2^ℓ` satisfies
`N² < q ≤ 2N²`. -/
def shorEll (N : ℕ) : ℕ :=
  Nat.clog 2 (N ^ 2 + 1)

/-- de Wolf p.51 (§5.3): one run of Shor's period-finding circuit before the measurements: from
`|0^ℓ⟩|0ⁿ⟩` (`ℓ = shorEll N`, `n = ⌈log N⌉ = Nat.clog 2 N`), apply `F_q` to the first register,
`O_f : |a⟩|y⟩ ↦ |a⟩|y ⊕ f(a)⟩` (`a` read as an integer, `f(a)` written in `n` bits), and `F_q` to
the first register. The law of the measured `b` is `marginalFst`, `b` read as `bitsToNat b`. -/
noncomputable def shorRunState (N : ℕ) (f : ℕ → ℕ) :
    EuclideanSpace ℂ (Qubits (shorEll N) × Qubits (Nat.clog 2 N)) :=
  act (Matrix.kronecker (qftQubits (shorEll N)) (1 : Matrix (Qubits (Nat.clog 2 N))
      (Qubits (Nat.clog 2 N)) ℂ) *
    xorOracle (fun a : Qubits (shorEll N) => natToBits (Nat.clog 2 N) (f (bitsToNat a))) *
    Matrix.kronecker (qftQubits (shorEll N)) (1 : Matrix (Qubits (Nat.clog 2 N))
      (Qubits (Nat.clog 2 N)) ℂ)) (ket (0, 0))

/-- de Wolf p.59 (§6.2.1): for `G = Z_{N_1} × ⋯ × Z_{N_l}`, the character
`χ_g(h) = Π_i ω_{N_i}^{g_i h_i} = Π_i e^{2πi g_i h_i / N_i}` (`g_i, h_i` read in `{0, …, N_i − 1}`). -/
noncomputable def abelianChar {l : ℕ} {N : Fin l → ℕ} [∀ i, NeZero (N i)]
    (g h : (i : Fin l) → ZMod (N i)) : ℂ :=
  ∏ i : Fin l, Complex.exp (2 * Real.pi * Complex.I * (((g i).val * (h i).val : ℕ) : ℂ) / (N i : ℂ))

/-- de Wolf p.59 (§6.2.1): the labels of `H^⊥ = {χ_g : χ_g(h) = 1 for all h ∈ H}`. -/
def annihilator {l : ℕ} {N : Fin l → ℕ} [∀ i, NeZero (N i)]
    (H : AddSubgroup ((i : Fin l) → ZMod (N i))) : Set ((i : Fin l) → ZMod (N i)) :=
  {g | ∀ h ∈ H, abelianChar g h = 1}

/-- de Wolf p.60 (§6.2.2): the QFT over `G = Z_{N_1} × ⋯ × Z_{N_l}`, `|k⟩ ↦ |χ_k⟩ =
|G|^{−1/2} Σ_g χ_k(g) |g⟩` (the tensor product `F_{N_1} ⊗ ⋯ ⊗ F_{N_l}`). -/
noncomputable def qftAbelian {l : ℕ} (N : Fin l → ℕ) [∀ i, NeZero (N i)] :
    Matrix ((i : Fin l) → ZMod (N i)) ((i : Fin l) → ZMod (N i)) ℂ :=
  Matrix.of fun g k =>
    ((Real.sqrt (Fintype.card ((i : Fin l) → ZMod (N i))))⁻¹ : ℂ) * abelianChar k g

/-- de Wolf p.58 (§6.1.2: "`f` is constant within each coset, and distinct on different cosets:
`f(g) = f(g')` iff `gH = g'H`"), Childs p.30 (§5.3): `f` hides the subgroup `H`:
`f x = f y ↔ x⁻¹ y ∈ H`. Both directions are required (trap Q17). The additive version
`AddHides` (`f x = f y ↔ −x + y ∈ H`) is de Wolf's `f(g) = f(g')` iff `g − g' ∈ H` for an
Abelian group. -/
@[to_additive AddHides]
def Hides {G S : Type*} [Group G] (f : G → S) (H : Subgroup G) : Prop :=
  ∀ x y, f x = f y ↔ x⁻¹ * y ∈ H

/-- de Wolf p.60 (§6.2.2, step 2), p.65 (§7.2): the uniform superposition
`|ι|^{−1/2} Σ_i |i⟩` over a finite index set. (For `n` qubits it is `H^{⊗n}|0ⁿ⟩`.) -/
noncomputable def uniformState (ι : Type*) [Fintype ι] : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 fun _ => ((Real.sqrt (Fintype.card ι))⁻¹ : ℂ)

/-- de Wolf p.60 (§6.2.2, steps 1–5): the state of the standard Abelian HSP algorithm before the
final measurement: the uniform superposition over `G` with `|0⟩` in the second register, one query
`|g, y⟩ ↦ |g, y + f(g)⟩`, then the QFT over `G` on the first register. (The step-4 measurement of
the second register does not change the law `marginalFst` of the first register; the answer set
`S` carries an Abelian group structure only to define the unitary query.) -/
noncomputable def hspStandardState {l : ℕ} (N : Fin l → ℕ) [∀ i, NeZero (N i)] {S : Type*}
    [AddCommGroup S] [Fintype S] [DecidableEq S] (f : ((i : Fin l) → ZMod (N i)) → S) :
    EuclideanSpace ℂ (((i : Fin l) → ZMod (N i)) × S) :=
  act (Matrix.kronecker (qftAbelian N) (1 : Matrix S S ℂ) * xorOracle f)
    (tensorVec (uniformState ((i : Fin l) → ZMod (N i))) (ket 0))

/-! ### Sanity tests -/

theorem qftMatrix_apply (N : ℕ) (j k : Fin N) :
    qftMatrix N j k = Complex.exp (2 * Real.pi * Complex.I * (((j : ℕ) * (k : ℕ) : ℕ) : ℂ) /
      (N : ℂ)) / (Real.sqrt N : ℂ) := rfl

example : qftMatrix 1 = 1 := by
  ext j k
  fin_cases j; fin_cases k
  simp [qftMatrix]

/-- `F_2` is the Hadamard gate (de Wolf p.41), under `Fin 2 ≃ Bool`. -/
theorem qftMatrix_two (j k : Fin 2) : qftMatrix 2 j k = hadamard (finTwoEquiv j) (finTwoEquiv k) := by
  have hpi : Complex.exp (2 * Real.pi * Complex.I * 2⁻¹) = -1 := by
    rw [show (2 * Real.pi * Complex.I * 2⁻¹ : ℂ) = Real.pi * Complex.I by ring]
    exact Complex.exp_pi_mul_I
  fin_cases j <;> fin_cases k <;> simp [qftMatrix, hadamard, finTwoEquiv, div_eq_mul_inv, hpi]

/-- The one-qubit QFT is the Hadamard gate (de Wolf p.41: `F_2 = H`). -/
example (y z : Qubits 1) : qftQubits 1 y z = hadamard (y 0) (z 0) := by
  have hb : ∀ b : Qubits 1, (bitsEquivFin 1 b : Fin 2) = finTwoEquiv.symm (b 0) := by
    intro b
    apply Fin.ext
    rw [bitsEquivFin_apply]
    cases h : b 0 <;> simp only [bitsToNat, Fin.sum_univ_one, h] <;> rfl
  simp only [qftQubits, Matrix.submatrix_apply]
  rw [hb y, hb z]
  exact (qftMatrix_two (finTwoEquiv.symm (y 0)) (finTwoEquiv.symm (z 0))).trans (by simp)

/-- `shorEll` pins `q = 2^ℓ` with `N² < q ≤ 2N²`: at `N = 3`, `q = 16`. -/
example : shorEll 3 = 4 := by decide

example : shorEll 1 = 1 := by decide

example : HasPeriod (fun a => a % 3) 3 := fun _ _ => Iff.rfl

end QAlgorithms


