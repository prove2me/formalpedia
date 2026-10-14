-- Prove2me | Definitions.Def_QAlgorithms_Defs_Channel
-- name    : QAlgorithms_Defs_Channel
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:55:21.661976+00:00
-- url     : https://prove2.me/theorems/7e36e526-3fa5-46b5-b36b-6f546e39574a
-- title:
--   Superoperators, quantum channels in Kraus form, the erasure channel, achievable rates
-- statement:
--   Superoperators, quantum channels in Kraus form, the erasure channel, achievable rates
--
--   ### QAlgorithms.Superop
--
--   For index types $\iota$ and $\kappa$, $\mathrm{Superop}(\iota,\kappa)$ is the type of **all functions** from complex $\iota\times\iota$ matrices to complex $\kappa\times\kappa$ matrices:
--
--   $$
--   \Phi : \mathbb{C}^{\iota\times\iota} \to \mathbb{C}^{\kappa\times\kappa}.
--   $$
--
--   Nothing else is required of such a map. It need not be linear, trace-preserving, positive, or completely positive. The index types need not be finite.
--
--   ### QAlgorithms.IsKrausFamily
--
--   Let $K$ and $\kappa$ be finite types, and let $\iota$ be a type with decidable equality; $\iota$ need not be finite. Let $(E_j)_{j\in K}$ be a family of complex $\kappa\times\iota$ matrices, so each $E_j$ maps $\mathbb{C}^\iota$ to $\mathbb{C}^\kappa$.
--
--   The family is a *Kraus family* exactly when
--
--   $$
--   \sum_{j\in K} E_j^{\dagger} E_j = I_\iota,
--   $$
--
--   where $E_j^\dagger$ is the conjugate transpose and $I_\iota$ is the $\iota\times\iota$ identity matrix.
--
--   Edge cases:
--
--   - If $K$ is empty, the sum is the zero matrix. The condition then holds only when $\iota$ is empty.
--   - If $\kappa$ is empty, every $E_j^\dagger E_j$ is zero, so again the condition holds only when $\iota$ is empty.
--
--   ### QAlgorithms.krausApply
--
--   Let $K$ and $\iota$ be finite types, $\kappa$ any type, and $(E_j)_{j\in K}$ a family of complex $\kappa\times\iota$ matrices. Then $\mathrm{krausApply}(E)$ is the map in $\mathrm{Superop}(\iota,\kappa)$ given by
--
--   $$
--   \rho \;\longmapsto\; \sum_{j\in K} E_j\,\rho\,E_j^{\dagger}.
--   $$
--
--   This is defined for **every** complex $\iota\times\iota$ matrix $\rho$, not only density matrices. No condition is placed on the $E_j$; in particular, the Kraus completeness relation is not assumed. If $K$ is empty, the map is identically zero.
--
--   ### QAlgorithms.IsChannel
--
--   Let $\iota$ and $\kappa$ be finite types, with decidable equality on $\iota$. A map $\Phi\in\mathrm{Superop}(\iota,\kappa)$ (an arbitrary function from $\iota\times\iota$ to $\kappa\times\kappa$ complex matrices) is a *channel* when the following holds.
--
--   There exist a natural number $m$ and complex $\kappa\times\iota$ matrices $E_0,\dots,E_{m-1}$ such that:
--
--   1. the Kraus completeness relation holds:
--   $$
--   \sum_{j=0}^{m-1}E_j^\dagger E_j=I_\iota;
--   $$
--   2. $\Phi$ agrees with the Kraus map on every complex $\iota\times\iota$ matrix (not only density matrices):
--   $$
--   \Phi(\rho)=\sum_{j=0}^{m-1}E_j\rho E_j^\dagger \quad\text{for all } \rho.
--   $$
--
--   Edge case: $m=0$ is allowed. It satisfies condition 1 only when $\iota$ is empty. Hence for nonempty $\iota$, at least one Kraus operator is needed.
--
--   ### QAlgorithms.conjSuperop
--
--   Let $\iota$ be a finite type, $\kappa$ any type, and $A$ a complex $\kappa\times\iota$ matrix. Then $\mathrm{conjSuperop}(A)\in\mathrm{Superop}(\iota,\kappa)$ is the map
--
--   $$
--   \rho\longmapsto A\,\rho\,A^\dagger,
--   $$
--
--   defined on all complex $\iota\times\iota$ matrices $\rho$. No unitarity, isometry, or norm condition is imposed on $A$.
--
--   ### QAlgorithms.piSuperop
--
--   Let $\iota$ be a finite type with decidable equality, $\kappa$ any type, and $k\in\mathbb{N}$. Let $\Phi_0,\dots,\Phi_{k-1}$ be arbitrary maps in $\mathrm{Superop}(\iota,\kappa)$.
--
--   $\mathrm{piSuperop}(\Phi)$ is a map from matrices indexed by tuples $x=(x_0,\dots,x_{k-1})\in\iota^k$ to matrices indexed by tuples $y\in\kappa^k$. For an input $X$ and output indices $y,y'\in\kappa^k$, its entries are
--
--   $$
--   \big(\mathrm{piSuperop}(\Phi)(X)\big)_{y,y'}
--   =\sum_{x\in\iota^k}\sum_{x'\in\iota^k} X_{x,x'}\prod_{i=0}^{k-1}\Big(\Phi_i\big(\mathbf{E}_{x_i,x'_i}\big)\Big)_{y_i,\,y'_i}.
--   $$
--
--   Here $\mathbf{E}_{a,b}$ is the $\iota\times\iota$ matrix unit: entry $1$ at position $(a,b)$ and $0$ elsewhere.
--
--   So the output is obtained by applying each $\Phi_i$ only to matrix units and extending linearly in $X$. Consequences:
--
--   - The result is always linear in $X$, even when the $\Phi_i$ are not linear.
--   - If the $\Phi_i$ are linear, it coincides with $\Phi_0\otimes\cdots\otimes\Phi_{k-1}$.
--
--   Edge case: for $k=0$, both index sets are a single point and the empty product is $1$. The output's single entry then equals $X$'s single entry, so the map is the identity on $1\times1$ matrices.
--
--   ### QAlgorithms.idTensorSuperop
--
--   Let $R$, $\iota$, $\kappa$ be arbitrary types (no finiteness required) and $\Phi\in\mathrm{Superop}(\iota,\kappa)$ an arbitrary map. Then $\mathrm{idTensorSuperop}(\Phi)$ maps $(R\times\iota)$-indexed matrices to $(R\times\kappa)$-indexed matrices. The first factor $R$ is untouched and $\Phi$ acts on the second.
--
--   Take a matrix $X$ and output indices $(r,j)$, $(r',j')$ with $r,r'\in R$ and $j,j'\in\kappa$. Form the $(r,r')$ block of $X$, the $\iota\times\iota$ matrix
--
--   $$
--   X^{(r,r')}_{i,i'} = X_{(r,i),(r',i')}.
--   $$
--
--   Then
--
--   $$
--   \big(\mathrm{idTensorSuperop}(\Phi)(X)\big)_{(r,j),(r',j')}=\Big(\Phi\big(X^{(r,r')}\big)\Big)_{j,j'}.
--   $$
--
--   That is, $\Phi$ is applied separately to each block $X^{(r,r')}$. When $\Phi$ is linear this is $\mathrm{id}_R\otimes\Phi$. For nonlinear $\Phi$ it is still literally this blockwise application.
--
--   ### QAlgorithms.overwrite
--
--   Let $\alpha$ be any type, $k,N\in\mathbb{N}$, and $w:\{0,\dots,k-1\}\to\{0,\dots,N-1\}$ an injective map (an ordered choice of $k$ distinct wires). Let $y:\{0,\dots,N-1\}\to\alpha$ and $z:\{0,\dots,k-1\}\to\alpha$.
--
--   The result is the function on $\{0,\dots,N-1\}$ that writes $z$ onto the wires of $w$ and keeps $y$ elsewhere:
--
--   $$
--   \mathrm{overwrite}_w(y,z)(a)=\begin{cases} z_i & \text{if } a=w(i) \text{ for some } i,\\ y_a & \text{if } a\notin\operatorname{range}(w).\end{cases}
--   $$
--
--   The index $i$ in the first case is unique because $w$ is injective.
--
--   ### QAlgorithms.liftSuperop
--
--   Let $\alpha$ and $E$ be arbitrary types, $k,N\in\mathbb{N}$, and $w$ an injective map from $\{0,\dots,k-1\}$ into $\{0,\dots,N-1\}$. Let $\Psi$ be an arbitrary map from matrices indexed by $\alpha^{k}\times E$ to matrices with the same index set. The result is a map on matrices indexed by $\alpha^{N}\times E$.
--
--   Fix an input matrix $X$ and output indices $p=(y,e)$, $q=(y',e')$, where $y,y'\in\alpha^N$ and $e,e'\in E$.
--
--   First form the $(\alpha^k\times E)$-indexed matrix $M^{p,q}$. For $a,b\in\alpha^k$ and $f,g\in E$:
--
--   $$
--   M^{p,q}_{(a,f),(b,g)} = X_{(\mathrm{overwrite}_w(y,a),\,f),\ (\mathrm{overwrite}_w(y',b),\,g)}.
--   $$
--
--   In words: the wires outside the range of $w$ are frozen to their values in $y$ (row side) and $y'$ (column side). The wires in the range of $w$ are replaced by $a$ and $b$. The $E$ components range freely.
--
--   Then
--
--   $$
--   \big(\mathrm{liftSuperop}_w(\Psi)(X)\big)_{p,q}=\Psi\big(M^{p,q}\big)_{(y\circ w,\ e),\ (y'\circ w,\ e')},
--   $$
--
--   where $y\circ w\in\alpha^k$ is the restriction of $y$ to the wires of $w$, in the order given by $w$.
--
--   So $\Psi$ is applied to the block of $X$ selected by the complement-wire values of $p$ and $q$, and the result is read off at the $w$-wire and $E$ coordinates of $p$ and $q$. No linearity or channel property of $\Psi$ is assumed.
--
--   ### QAlgorithms.maxEntangled
--
--   For $k\in\mathbb{N}$, $\mathrm{maxEntangled}(k)$ is the vector $|\Phi_k\rangle$ in the Euclidean space $\mathbb{C}^{\{0,1\}^k\times\{0,1\}^k}$ (two $k$-qubit registers). Its coordinates are
--
--   $$
--   |\Phi_k\rangle_{(a,b)}=\begin{cases} \dfrac{1}{\sqrt{2^k}} & a=b,\\[4pt] 0 & a\neq b,\end{cases}
--   \qquad\text{i.e.}\qquad
--   |\Phi_k\rangle=\frac{1}{\sqrt{2^k}}\sum_{a\in\{0,1\}^k}|a\rangle|a\rangle .
--   $$
--
--   For $k=0$ it is the single coordinate $1$.
--
--   ### QAlgorithms.entanglementFidelity
--
--   Let $k\in\mathbb{N}$ and let $\Phi\in\mathrm{Superop}(\{0,1\}^k,\{0,1\}^k)$ be an arbitrary map on $2^k\times2^k$ complex matrices; it is not assumed to be a channel.
--
--   Let $|\Phi_k\rangle=2^{-k/2}\sum_a|a\rangle|a\rangle$ be the vector above. Let $\rho_{\Phi_k}$ be its outer product, with entries
--
--   $$
--   (\rho_{\Phi_k})_{a,b}=(\Phi_k)_a\,\overline{(\Phi_k)_b}.
--   $$
--
--   Let $\mathrm{id}\otimes\Phi$ denote the blockwise map described under `idTensorSuperop`. The first (reference) register is left alone and $\Phi$ is applied to each $(r,r')$ block on the second register.
--
--   The entanglement fidelity is the real number
--
--   $$
--   F_e(\Phi)=\operatorname{Re}\sum_{a}\sum_{b}\overline{(\Phi_k)_a}\,\Big[(\mathrm{id}\otimes\Phi)(\rho_{\Phi_k})\Big]_{a,b}\,(\Phi_k)_b
--   =\operatorname{Re}\,\langle\Phi_k|\,(\mathrm{id}\otimes\Phi)(|\Phi_k\rangle\langle\Phi_k|)\,|\Phi_k\rangle .
--   $$
--
--   Here $a$ and $b$ range over pairs in $\{0,1\}^k\times\{0,1\}^k$. The real part is taken explicitly, so any imaginary part is discarded.
--
--   ### QAlgorithms.erasureKraus
--
--   For a real parameter $p$, $\mathrm{erasureKraus}(p)$ is a list of five complex $4\times2$ matrices $E_0,\dots,E_4$. Each maps a qubit $\mathbb{C}^{\{0,1\}}$ into $\mathbb{C}^{\{0,1\}\times\{0,1\}}$, where an output index is a pair (bit, flag).
--
--   - **$E_0$, no erasure.** It keeps the bit and sets the flag to $0$:
--   $$
--   E_0=\sqrt{1-p}\,\sum_{b\in\{0,1\}}|b,0\rangle\langle b|.
--   $$
--   - **$E_1,\dots,E_4$, erasure.** For $(a,c)$ taken in the order $(0,0),(0,1),(1,0),(1,1)$:
--   $$
--   E_{(a,c)}=\sqrt{p/2}\;|a,1\rangle\langle c|.
--   $$
--   Each has the single nonzero entry $\sqrt{p/2}$ at row $(a,1)$, column $c$. It sends input $|c\rangle$ to output bit $a$ with flag $1$.
--
--   No range restriction is placed on $p$. The square roots are real square roots truncated at $0$:
--
--   - for $p>1$, $\sqrt{1-p}$ is taken to be $0$, so $E_0=0$;
--   - for $p<0$, $\sqrt{p/2}$ is taken to be $0$, so $E_1=\dots=E_4=0$.
--
--   ### QAlgorithms.erasureChannel
--
--   This definition takes a number of qubits $n \in \mathbb{N}$ and a real parameter $p$, with **no hypothesis on $p$**. It returns a map $\mathcal{E}_{n,p}$ from complex matrices indexed by $\{0,1\}^n$ (the $n$-qubit input space) to complex matrices indexed by $(\{0,1\}\times\{0,1\})^n$. Each output wire $q$ carries a pair $(a_q, f_q)$: $a_q$ is a data bit and $f_q$ a flag bit.
--
--   The map is built from five single-qubit operators $K_0,\dots,K_4$, each a $4\times 2$ matrix with rows indexed by pairs $(a,f)$ and columns indexed by a bit $b$:
--
--   - $K_0(a,f;\,b) = \sqrt{1-p}$ if $(a,f) = (b,0)$, and $0$ otherwise. So $K_0$ sends $|b\rangle \mapsto \sqrt{1-p}\,|b,0\rangle$.
--   - For $(a,c) \in \{(0,0),(0,1),(1,0),(1,1)\}$, giving $K_1,K_2,K_3,K_4$ in that order:
--     $$K(a,f;\,b) = \sqrt{p/2} \text{ if } (a,f)=(a,1) \text{ and } b = c, \text{ and } 0 \text{ otherwise}.$$
--     So $|c\rangle \mapsto \sqrt{p/2}\,|a,1\rangle$, and $K$ kills $|1-c\rangle$.
--
--   Here $\sqrt{\cdot}$ is the real square root, which returns $0$ on negative arguments. Thus for $p<0$ all of $K_1,\dots,K_4$ are zero, and for $p>1$ the operator $K_0$ is zero.
--
--   For each assignment $j : \{1,\dots,n\} \to \{0,\dots,4\}$, define the $n$-fold product operator
--   $$E_j(y, z) = \prod_{q} K_{j_q}(y_q,\, z_q),$$
--   where $y \in (\{0,1\}^2)^n$ and $z \in \{0,1\}^n$. The map is then, for **every** complex matrix $\rho$ (not only density matrices),
--   $$\mathcal{E}_{n,p}(\rho) = \sum_{j \in \{0,\dots,4\}^n} E_j\,\rho\,E_j^{\dagger}.$$
--
--   The definition does not assert that this is trace preserving. The completeness relation $\sum_j E_j^\dagger E_j = I$ is not part of the definition.
--
--   ### QAlgorithms.IsAchievableQRate
--
--   The data are:
--
--   - a family of finite index types $\mathrm{Out}_n$ with decidable equality, one for each $n\in\mathbb{N}$;
--   - a family of maps $\mathcal{N}_n$, each sending complex matrices indexed by $\{0,1\}^n$ to complex matrices indexed by $\mathrm{Out}_n$. These are arbitrary functions on matrices, not assumed linear, completely positive or trace preserving;
--   - a real number $R$.
--
--   The predicate says that $R$ is an achievable rate for $(\mathcal{N}_n)$, meaning: for every $\varepsilon>0$ and every $\delta>0$ there is $N_0\in\mathbb{N}$ such that for every $n \ge N_0$ there exist a natural number $k$ with
--   $$(R-\delta)\,n \le k$$
--   and two maps $\mathrm{Enc}$ and $\mathrm{Dec}$ with the following properties.
--
--   - **Encoder.** $\mathrm{Enc}$ maps $k$-qubit matrices to $n$-qubit matrices and is a channel. Here "is a channel" means there exist $m\in\mathbb{N}$ and matrices $A_1,\dots,A_m$ of size $2^n\times 2^k$ such that $\sum_i A_i^\dagger A_i = I_{2^k}$ and $\mathrm{Enc}(\rho)=\sum_i A_i\rho A_i^\dagger$ for all $\rho$.
--   - **Decoder.** $\mathrm{Dec}$ maps matrices indexed by $\mathrm{Out}_n$ to $k$-qubit matrices and is a channel in the same sense.
--   - **Fidelity.** The composite $\Phi = \mathrm{Dec}\circ\mathcal{N}_n\circ\mathrm{Enc}$ satisfies
--     $$1-\varepsilon \le F(\Phi).$$
--
--   The entanglement fidelity $F$ is defined as follows. Let
--   $$|\Phi_k\rangle = 2^{-k/2}\sum_{x\in\{0,1\}^k}|x\rangle|x\rangle$$
--   on two $k$-qubit registers. Let $(\mathrm{id}\otimes\Phi)$ act on the second register only; its $((p_1,p_2),(q_1,q_2))$ entry is $\Phi$ applied to the block $X_{(p_1,\cdot),(q_1,\cdot)}$, evaluated at $(p_2,q_2)$. Then
--   $$F(\Phi)=\operatorname{Re}\,\langle\Phi_k|\,(\mathrm{id}\otimes\Phi)\big(|\Phi_k\rangle\langle\Phi_k|\big)\,|\Phi_k\rangle.$$
--
--   Edge cases:
--
--   - $k$ has no upper bound, so $k>n$ is allowed.
--   - When $R-\delta\le 0$, the choice $k=0$ (a one-dimensional space) is permitted.
--   - $\mathcal{N}_n$ is applied as an arbitrary function.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/Channel.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
/-!
# Superoperators, quantum channels in Kraus form, the erasure channel, achievable rates
(shared definition layer)

D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum
computation* (arXiv:0904.2557), cited "Gottesman intro p.N", and D. Gottesman, *Stabilizer
codes and quantum error correction* (PhD thesis, 1997), cited "Gottesman thesis p.N" (PDF pages).

A superoperator is a plain function on matrices (`Superop ι κ`); a quantum operation in the
sources' sense (intro eq. (23), p.4–5: "ρ → Σ_i E_i ρ E_i†, where the E_i s are normalized so
Σ E_i† E_i = I") is a superoperator with a finite normalized Kraus family (`IsChannel`). Equality
of superoperators is equality on every operator, hence (by linearity) on every input state,
superpositions and parts of entangled states included.
-/

namespace QAlgorithms

open scoped ComplexConjugate Matrix

/-- Gottesman intro p.5, eq. (23), and p.20 (§4.2): a superoperator, i.e. a map from operators on
the space indexed by `ι` to operators on the space indexed by `κ`. Unbundled: linearity is
supplied by `IsChannel` or by construction. -/
abbrev Superop (ι κ : Type*) := Matrix ι ι ℂ → Matrix κ κ ℂ

/-- Gottesman intro p.5, eq. (23) (thesis p.90, §7.5): the Kraus operators `E j : κ × ι` are
normalized, `Σ_j E_j† E_j = I`. -/
def IsKrausFamily {K ι κ : Type*} [Fintype K] [Fintype κ] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) : Prop :=
  ∑ j, (E j)ᴴ * E j = 1

/-- Gottesman intro p.5, eq. (23): the map `ρ ↦ Σ_j E_j ρ E_j†`. -/
noncomputable def krausApply {K ι κ : Type*} [Fintype K] [Fintype ι]
    (E : K → Matrix κ ι ℂ) : Superop ι κ :=
  fun ρ => ∑ j, E j * ρ * (E j)ᴴ

/-- Gottesman intro pp.4–5, eq. (23) (thesis p.90): `Φ` is a quantum operation ("the most
general quantum operation, including decoherence"): it is given by some finite normalized Kraus
family. In finite dimension these are exactly the trace-preserving completely positive maps. -/
def IsChannel {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] (Φ : Superop ι κ) : Prop :=
  ∃ (m : ℕ) (E : Fin m → Matrix κ ι ℂ), IsKrausFamily E ∧ ∀ ρ, Φ ρ = krausApply E ρ

/-- Gottesman intro p.19 (Def. 1) and p.37 (the *-decoder): the single-Kraus map
`ρ ↦ A ρ A†` (a unitary gate, an isometry, a projector such as an r-filter). -/
def conjSuperop {ι κ : Type*} [Fintype ι] (A : Matrix κ ι ℂ) : Superop ι κ :=
  fun ρ => A * ρ * Aᴴ

/-- Gottesman intro p.21 (Def. 4) and p.35 (Def. 8): the tensor product
`Φ_0 ⊗ ⋯ ⊗ Φ_{k−1}` of superoperators acting on `k` registers (a separate filter, decoder or EC
on each block), defined on every operator through the matrix-unit expansion
`X = Σ_{x,x'} X_{x x'} ⊗_i |x_i⟩⟨x'_i|`, so entangled inputs are included. -/
noncomputable def piSuperop {ι κ : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (Φ : Fin k → Superop ι κ) : Superop (Fin k → ι) (Fin k → κ) :=
  fun X => Matrix.of fun y y' =>
    ∑ x : Fin k → ι, ∑ x' : Fin k → ι,
      X x x' * ∏ i, Φ i (Matrix.single (x i) (x' i) 1) (y i) (y' i)

/-- Gottesman thesis p.90 (§7.4–7.5, the 1-EPP picture): `id_R ⊗ Φ`, with the reference `R` the
first factor: `Φ` is applied to every block `X_{a a'} = (X_{(a,i),(a',i')})_{i,i'}`. -/
def idTensorSuperop {R ι κ : Type*} (Φ : Superop ι κ) : Superop (R × ι) (R × κ) :=
  fun X => Matrix.of fun p q => Φ (Matrix.of fun i i' => X (p.1, i) (q.1, i')) p.2 q.2

/-- Overwrite the registers in the range of `w` of the configuration `y` by `z` (helper for
`liftSuperop`). -/
noncomputable def overwrite {α : Type*} {k N : ℕ} (w : Fin k ↪ Fin N) (y : Fin N → α)
    (z : Fin k → α) : Fin N → α :=
  open Classical in
  fun a => if h : ∃ i, w i = a then z h.choose else y a

/-- Gottesman intro p.18 (§4.1: "an error that can affect all of the qubits involved in the
action") and p.40 (Def. 12): the superoperator `Ψ`, acting on the `k` registers in the range of
`w` together with an extra factor `E` (the environment), lifted to `N` registers, the identity on
the registers outside the range of `w`. Entry `((y, e), (y', e'))` is `Ψ` applied to the block of
`X` with the outside configurations of `y` and `y'` held fixed, evaluated at the inside
configurations `y ∘ w`, `y' ∘ w`; this is `id_outside ⊗ Ψ` (off-diagonal outside blocks are kept,
as for any superoperator that is the identity on a factor). -/
noncomputable def liftSuperop {α E : Type*} {k N : ℕ} (w : Fin k ↪ Fin N)
    (Ψ : Superop ((Fin k → α) × E) ((Fin k → α) × E)) :
    Superop ((Fin N → α) × E) ((Fin N → α) × E) :=
  fun X => Matrix.of fun p q =>
    Ψ (Matrix.of fun a b => X (overwrite w p.1 a.1, a.2) (overwrite w q.1 b.1, b.2))
      (p.1 ∘ w, p.2) (q.1 ∘ w, q.2)

/-- Gottesman thesis pp.89–90 (§7.4–7.5): `k` EPR pairs, the maximally entangled state
`|Φ_k⟩ = 2^{−k/2} Σ_{x ∈ {0,1}^k} |x⟩|x⟩` on `Qubits k × Qubits k`, reference register first. -/
noncomputable def maxEntangled (k : ℕ) : EuclideanSpace ℂ (Qubits k × Qubits k) :=
  WithLp.toLp 2 fun p => if p.1 = p.2 then ((Real.sqrt ((2 : ℝ) ^ k))⁻¹ : ℂ) else 0

/-- Gottesman thesis pp.89–90 (§7.4: a 1-EPP succeeds when Bob's pairs are good EPR pairs): the
entanglement fidelity `⟨Φ_k| (id ⊗ Φ)(|Φ_k⟩⟨Φ_k|) |Φ_k⟩` of a superoperator `Φ` on `k` qubits
(real part; it is real for a channel). -/
noncomputable def entanglementFidelity {k : ℕ} (Φ : Superop (Qubits k) (Qubits k)) : ℝ :=
  (∑ a, ∑ b, conj (maxEntangled k a) *
    (idTensorSuperop (R := Qubits k) Φ (pureDensity (maxEntangled k))) a b *
      maxEntangled k b).re

/-- Gottesman thesis p.90 (§7.5): the Kraus operators of the qubit erasure channel with erasure
probability `p` and an erasure flag (output `(qubit, flag)`). Index `0` is `√(1−p) |ψ⟩ ↦ |ψ⟩|0⟩`;
indices `1, …, 4` are `√(p/2) |a⟩|1⟩⟨c|` for `(a, c) = (0,0), (0,1), (1,0), (1,1)`. The channel is
`ρ ↦ (1 − p) ρ ⊗ |0⟩⟨0| + p Tr(ρ) (I/2) ⊗ |1⟩⟨1|`: with probability `p` the qubit is replaced by
the maximally mixed state ("totally randomized") and the receiver learns which qubit it was.
Normalized for `0 ≤ p ≤ 1`, the source's range (a hypothesis of the statements). -/
noncomputable def erasureKraus (p : ℝ) : Fin 5 → Matrix (Bool × Bool) Bool ℂ :=
  let flip : Bool → Bool → Matrix (Bool × Bool) Bool ℂ := fun a c =>
    Matrix.of fun o b => if o = (a, true) ∧ b = c then (Real.sqrt (p / 2) : ℂ) else 0
  ![Matrix.of fun o b => if o = (b, false) then (Real.sqrt (1 - p) : ℂ) else 0,
    flip false false, flip false true, flip true false, flip true true]

/-- Gottesman thesis p.90 (§7.5): the erasure channel applied independently to each of `n`
qubits, with product Kraus operators; output register `q` holds `(qubit q, flag q)`. -/
noncomputable def erasureChannel (n : ℕ) (p : ℝ) : Superop (Qubits n) (Fin n → Bool × Bool) :=
  krausApply fun j : Fin n → Fin 5 => Matrix.of fun y z => ∏ q, erasureKraus p (j q) (y q) (z q)

/-- Gottesman thesis p.80 (§7.1: capacity in the limit of infinitely many qubits sent, rate
`k/n`), p.89 (§7.4: quantum codes = 1-EPPs, success = good EPR pairs) and p.91 (§7.5): `R` is an
achievable rate of unassisted quantum communication over the family `Nch n` of `n`-use channels:
for every `ε, δ > 0`, for all large `n` there are `k ≥ (R − δ) n` and an encoding channel and a
decoding channel (arbitrary quantum operations; no back communication) with entanglement fidelity
at least `1 − ε`. The capacity is the supremum of the achievable rates; statements give it as a
two-sided threshold. -/
def IsAchievableQRate {Out : ℕ → Type*} [∀ n, Fintype (Out n)] [∀ n, DecidableEq (Out n)]
    (Nch : (n : ℕ) → Superop (Qubits n) (Out n)) (R : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ δ > (0 : ℝ), ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ k : ℕ, (R - δ) * n ≤ k ∧
    ∃ Enc : Superop (Qubits k) (Qubits n), IsChannel Enc ∧
      ∃ Dec : Superop (Out n) (Qubits k), IsChannel Dec ∧
        1 - ε ≤ entanglementFidelity (Dec ∘ Nch n ∘ Enc)

/-! ### Sanity tests -/

example {ι : Type*} [Fintype ι] [DecidableEq ι] : IsChannel (fun ρ : Matrix ι ι ℂ => ρ) :=
  ⟨1, fun _ => 1, by simp [IsKrausFamily], fun ρ => by simp [krausApply]⟩

example {ι κ : Type*} [Fintype ι] (A : Matrix κ ι ℂ) (ρ : Matrix ι ι ℂ) :
    conjSuperop A ρ = krausApply (fun _ : Fin 1 => A) ρ := by
  simp [conjSuperop, krausApply]

example {R ι : Type*} (X : Matrix (R × ι) (R × ι) ℂ) :
    idTensorSuperop (R := R) (fun ρ : Matrix ι ι ℂ => ρ) X = X := by
  ext p q; rfl

example : maxEntangled 0 (fun _ => false, fun _ => false) = 1 := by
  simp [maxEntangled]

example (k : ℕ) (x : Qubits k) :
    maxEntangled k (x, x) = ((Real.sqrt ((2 : ℝ) ^ k))⁻¹ : ℂ) := by
  simp [maxEntangled]

example : erasureKraus 0 0 (true, false) true = 1 ∧ erasureKraus 0 1 (false, true) false = 0 := by
  simp [erasureKraus]

theorem erasureKraus_isKraus {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsKrausFamily (erasureKraus p) := by
  have ha : ((Real.sqrt (1 - p) : ℂ)) * (Real.sqrt (1 - p) : ℂ) = ((1 - p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  have hb : ((Real.sqrt (p / 2) : ℂ)) * (Real.sqrt (p / 2) : ℂ) = ((p / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  ext b c
  simp only [IsKrausFamily, Fin.sum_univ_five, Matrix.add_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fintype.sum_bool, erasureKraus,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.of_apply]
  have hp2 : ((Real.sqrt p : ℝ) : ℂ) ^ 2 = (p : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt h0]
  have h22 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have key : ((Real.sqrt p : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ) *
      (((Real.sqrt p : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) = (p : ℂ) / 2 := by
    rw [div_mul_div_comm, ← sq, ← sq, hp2, h22]
  cases b <;> cases c <;> simp [Matrix.one_apply, Complex.conj_ofReal, ha, hb] <;>
    rw [key] <;> ring

end QAlgorithms


