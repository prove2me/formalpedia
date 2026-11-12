-- Prove2me | Definitions.Def_PassiveAdiabaticFT_Thermal_Operators
-- name    : PassiveAdiabaticFT_Thermal_Operators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:19.944361+00:00
-- url     : https://prove2.me/theorems/913763ef-6e2d-444d-8dd3-4232d085279d
-- title:
--   Qubit operators, Bohr frequency components and the thermal (Davies) generator
-- statement:
--   A register of qubits labelled by a finite set $Q$ has the computational basis $\{|x\rangle : x\in\{0,1\}^Q\}$; operators on it are complex matrices indexed by bit strings. This file fixes the general objects used throughout the mission.
--
--   1. **Paulis.** $X,Y,Z$ are the single-qubit Pauli matrices; $F=X_q,Y_q,Z_q$ is such a matrix on qubit $q$ tensored with the identity elsewhere. A Pauli operator is $c\,\sigma_{v_1}\otimes\cdots\otimes\sigma_{v_n}$ with $|c|=1$ and $\sigma_v\in\{I,X,Y,Z\}$.
--   2. **Locality and strength.** An operator $O$ *acts on* a qubit set $S$ if $O=A\otimes I_{S^c}$; it is $\ell$-local if it acts on some set of at most $\ell$ qubits. The *support* of $O$ is the least set it acts on. For a family of terms $(h_i)$, the interaction on $S$ is $\sum_{i:\,\mathrm{supp}\,h_i=S}h_i$, the sum of the terms whose support is exactly $S$. The bound $\|O\|_\infty\le c$ is stated as $\|Ov\|_2^2\le c^2\|v\|_2^2$ for all $v$.
--   3. **Spectral data.** For a Hermitian $H$ with distinct eigenvalues $\lambda$ and spectral projectors $\Pi_\lambda$ (onto the whole eigenspace), the Bohr frequencies are all differences $\lambda'-\lambda$ (including $0$), and the frequency component of an operator $F$ is
--   $$F_\omega=\sum_{\lambda,\lambda'\in\operatorname{spec}H,\ \lambda'-\lambda=\omega}\Pi_\lambda F\Pi_{\lambda'}.$$
--   4. **Thermal generator** (1.16)–(1.17). With $D[L](\rho)=L\rho L^\dagger-\tfrac12\{L^\dagger L,\rho\}$, jump operators $F_\alpha$, rates $\gamma_\alpha^{(\omega)}$ and Lamb coefficients $\kappa_\alpha^{(\omega)}$,
--   $$\mathcal L(\rho)=-i[H+H_{LS},\rho]+\sum_{\alpha,\omega}\gamma_\alpha^{(\omega)}D[F_{\alpha,\omega}](\rho),\qquad H_{LS}=\sum_{\alpha,\omega}\kappa_\alpha^{(\omega)}F_{\alpha,\omega}^\dagger F_{\alpha,\omega},$$
--   the sums over all $\alpha$ and all Bohr frequencies of $H$; the same generator tensored with the identity on a reference register is also defined.
--   5. **Bath assumptions** (1.18)–(1.19) at inverse temperature $\beta$ with bounds $\gamma,\kappa$: $0\le\gamma_\alpha^{(\omega)}\le\gamma$, $|\kappa_\alpha^{(\omega)}|\le\kappa$ for all $\alpha,\omega$, and $\gamma_\alpha^{(-\omega)}=e^{-\beta\omega}\gamma_\alpha^{(\omega)}$ for every $\omega>0$.
--   6. **Evolutions.** A solution of $\dot\rho(t)=\mathcal L_t(\rho(t))$ on $[0,T]$ is a matrix function continuous on $[0,T]$ whose derivative equals $\mathcal L_t(\rho(t))$ at every time outside a countable set; a propagator of $\dot U=-iK(t)U$ is such a solution with $U(0)=I$.
--   7. **Circuits and output.** A gate is a unitary on a set of at most two of the $n$ qubits; a circuit of $T$ gates has unitary $\mathcal C=U_T\cdots U_1$ and ideal output $\mathcal C|0^n\rangle\langle0^n|\mathcal C^\dagger$. The trace distance is $\tfrac12\|\rho-\sigma\|_1$ with $\|M\|_1=\operatorname{Tr}\sqrt{M^\dagger M}$, and the partial trace onto designated qubits $\mathrm{out}(1),\dots,\mathrm{out}(n)$ traces out all others.
--
--   These are the noise model of §1.2 and the simulation notion of p. 11, stated for any Hamiltonian; the paper-specific Hamiltonian path is built on them in the later definition files.
--
--   **Formalization Note** Eigenvalues are read off the characteristic polynomial and $\Pi_\lambda$ is the continuous functional calculus of the indicator of $\{\lambda\}$; for Hermitian $H$ these are the usual spectral data. The countable exceptional set in the solution notion admits generators that jump at finitely many level crossings. The trace norm is the published `QAlgorithms.traceNorm`.
-- source:
--   Arsalan Motamedi, Peter Love, Fault Tolerant Adiabatic Quantum Computation from Passive Error Correcting Codes, STOC 2027 submission #1144 (October 2026), source.pdf SHA-256 96d4a748a9114e6a9ed0c5252e84434a63b2a1ef07b286134f01f6761c2503b8, §1.1 (pp. 3–5), §1.2 eqs. (1.15)–(1.19) (pp. 5–6), §3.2 eqs. (3.3)–(3.4) (p. 20), and the simulation notion after Theorem 1.8 (p. 11)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

/-!
# Qubit operators, spectral data and the thermal (Davies) generator

Arsalan Motamedi, Peter Love, *Fault Tolerant Adiabatic Quantum Computation from Passive Error
Correcting Codes*, STOC 2027 submission #1144 (October 2026): §1.1 (pp. 3–5), §1.2 (pp. 5–6),
eqs. (1.15)–(1.19), §3.2 (3.3)–(3.4) (p. 20), and the simulation notion of p. 11.

A register of qubits labelled by a finite type `Q` has computational basis `Q → Fin 2`; operators
are complex matrices indexed by bit strings.
-/

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix

namespace PassiveAdiabaticFT.Thermal

/-- Operators on the qubit register labelled by `Q`: matrices indexed by bit strings `Q → Fin 2`. -/
abbrev Op (Q : Type) := Matrix (Q → Fin 2) (Q → Fin 2) ℂ

/-- The three single-qubit Pauli matrices `X, Y, Z`, indexed by `Fin 3`. -/
def pauli1 : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, 1; 1, 0]
  | 1 => !![0, -Complex.I; Complex.I, 0]
  | 2 => !![1, 0; 0, -1]

/-- The four single-qubit Pauli matrices `I, X, Y, Z`, indexed by `Fin 4` (`0 ↦ I`). -/
def pauli4 : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | 1 => !![0, 1; 1, 0]
  | 2 => !![0, -Complex.I; Complex.I, 0]
  | 3 => !![1, 0; 0, -1]

variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-- The operator `A ⊗ I` that acts as `A` on the qubits of `S` and as the identity elsewhere. -/
def embedOp (S : Finset Q) (A : Matrix (S → Fin 2) (S → Fin 2) ℂ) : Op Q :=
  fun x y => if ∀ j, j ∉ S → x j = y j then A (fun j => x j) (fun j => y j) else 0

/-- The single-qubit Pauli `pauli1 c` acting on qubit `q` (`X_q, Y_q, Z_q`). -/
def singlePauli (q : Q) (c : Fin 3) : Op Q :=
  fun x y => if ∀ j, j ≠ q → x j = y j then pauli1 c (x q) (y q) else 0

/-- The Pauli string `⊗_j σ_{v j}` (no phase). -/
def pauliString (v : Q → Fin 4) : Op Q :=
  fun x y => ∏ j, pauli4 (v j) (x j) (y j)

/-- `P` is a Pauli operator up to a phase: `P = c · ⊗_j σ_{v j}` with `|c| = 1`. -/
def IsPauli (P : Op Q) : Prop :=
  ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ v : Q → Fin 4, P = c • pauliString v

/-- `O` acts on the qubit set `S`: `O = A ⊗ I` for some operator `A` on the qubits of `S`.
An operator is `ℓ`-local when it acts on some set of at most `ℓ` qubits. -/
def ActsOn (O : Op Q) (S : Finset Q) : Prop :=
  ∃ A : Matrix (S → Fin 2) (S → Fin 2) ℂ, O = embedOp S A

/-- `S` is the support of `O`: `O` acts on `S`, and every qubit set on which `O` acts
contains `S` (the least such set). -/
def IsLeastSupport (O : Op Q) (S : Finset Q) : Prop :=
  ActsOn O S ∧ ∀ S' : Finset Q, ActsOn O S' → S ⊆ S'

open Classical in
/-- The interaction of a family of terms `h` on the qubit set `S`: the sum of the terms whose
support is exactly `S`. Interaction strength is bounded on these merged terms, so splitting
one interaction into several copies on the same qubits does not lower its strength. -/
def termsOn {ι : Type} [Fintype ι] (h : ι → Op Q) (S : Finset Q) : Op Q :=
  ∑ i ∈ Finset.univ.filter (fun i => IsLeastSupport (h i) S), h i

/-- Operator-norm bound `‖O‖_∞ ≤ c`, stated through the Euclidean norm:
`‖O v‖₂² ≤ c² ‖v‖₂²` for every vector `v`. -/
def OpNormLe {ι κ : Type} [Fintype ι] [Fintype κ] (O : Matrix ι κ ℂ) (c : ℝ) : Prop :=
  ∀ v : κ → ℂ, ∑ i, ‖(O *ᵥ v) i‖ ^ 2 ≤ c ^ 2 * ∑ j, ‖v j‖ ^ 2

/-- The computational basis vector `|0…0⟩`. -/
def ketZero : (Q → Fin 2) → ℂ := fun x => if x = 0 then 1 else 0

/-- The pure state `|0…0⟩⟨0…0|`. -/
def ketbraZero : Op Q := fun x y => if x = 0 ∧ y = 0 then 1 else 0

/-- `v` is a ground state of `K`: a nonzero eigenvector whose eigenvalue `e` is the minimum of
the Rayleigh quotient, `e ‖w‖² ≤ Re ⟨w, K w⟩` for all `w`. -/
def IsGroundState {ι : Type} [Fintype ι] (K : Matrix ι ι ℂ) (v : ι → ℂ) : Prop :=
  v ≠ 0 ∧ ∃ e : ℝ, K *ᵥ v = (e : ℂ) • v ∧
    ∀ w : ι → ℂ, e * ∑ i, ‖w i‖ ^ 2 ≤ (star w ⬝ᵥ (K *ᵥ w)).re

/-- Gluing a bit string on the embedded qubits `range out` with one on the remaining qubits. -/
def glue {n : ℕ} (out : Fin n ↪ Q) (x : Fin n → Fin 2)
    (z : {q : Q // q ∉ Set.range out} → Fin 2) : Q → Fin 2 :=
  fun q => if h : q ∈ Set.range out then x (out.invOfMemRange ⟨q, h⟩) else z ⟨q, h⟩

open Classical in
/-- The partial trace onto the qubits `out(0), …, out(n-1)` (in this order), tracing out all
other qubits of `Q`. -/
def reduceTo {n : ℕ} (out : Fin n ↪ Q) (σ : Op Q) : Op (Fin n) :=
  fun x y => ∑ z : ({q : Q // q ∉ Set.range out} → Fin 2), σ (glue out x z) (glue out y z)

/-- The trace distance `½ ‖ρ − σ‖₁`, with the (unhalved) trace norm `‖M‖₁ = Tr √(M†M)`. -/
def traceDist {ι : Type} [Fintype ι] [DecidableEq ι] (ρ σ : Matrix ι ι ℂ) : ℝ :=
  (1 / 2 : ℝ) * QAlgorithms.traceNorm (ρ - σ)

/-- The tensor product `X ⊗ I_R` with the identity on a reference register `R`. -/
def liftRef {ι R : Type} [Fintype R] [DecidableEq R] (X : Matrix ι ι ℂ) :
    Matrix (ι × R) (ι × R) ℂ :=
  Matrix.kroneckerMap (· * ·) X (1 : Matrix R R ℂ)

/-! ### Spectral data of a Hermitian matrix (eqs. (1.15), (3.4)) -/

section Spectral

variable {ι : Type} [Fintype ι] [DecidableEq ι]

open Classical in
/-- The eigenvalues of `H`, as a finite set of reals (the real parts of the roots of the
characteristic polynomial; for Hermitian `H` these are exactly its eigenvalues). -/
def spec (H : Matrix ι ι ℂ) : Finset ℝ :=
  (H.charpoly.roots.map Complex.re).toFinset

open Classical in
/-- The spectral projector `Π_λ` of `H` onto its whole `λ`-eigenspace (zero if `λ` is not an
eigenvalue), via the continuous functional calculus of the self-adjoint matrix `H`. -/
def specProj (H : Matrix ι ι ℂ) (l : ℝ) : Matrix ι ι ℂ :=
  cfc (fun x : ℝ => if x = l then (1 : ℝ) else 0) H

open Classical in
/-- The Bohr frequencies of `H`: all differences `λ' − λ` of eigenvalues, `ω = 0` included. -/
def bohrFreqs (H : Matrix ι ι ℂ) : Finset ℝ :=
  ((spec H) ×ˢ (spec H)).image (fun p => p.2 - p.1)

open Classical in
/-- The frequency component (1.15)/(3.4): `F_ω = Σ_{λ, λ' ∈ spec H, λ' − λ = ω} Π_λ F Π_{λ'}`. -/
def bohrComp (H F : Matrix ι ι ℂ) (ω : ℝ) : Matrix ι ι ℂ :=
  ∑ l ∈ spec H, ∑ l' ∈ spec H, if l' - l = ω then specProj H l * F * specProj H l' else 0

/-- The dissipator `D[L](ρ) = L ρ L† − ½ {L† L, ρ}`. -/
def dissipator {κ : Type} [Fintype κ] (L ρ : Matrix κ κ ℂ) : Matrix κ κ ℂ :=
  L * ρ * Lᴴ - (1 / 2 : ℂ) • (Lᴴ * L * ρ + ρ * (Lᴴ * L))

variable {α : Type} [Fintype α]

/-- The Lamb-shift Hamiltonian (1.16): `H_LS = Σ_{α, ω} κ_α(ω) F_{α,ω}† F_{α,ω}`, the sum over
the jump operators `F α` and the Bohr frequencies of `H`. -/
def lambShift (H : Matrix ι ι ℂ) (F : α → Matrix ι ι ℂ) (κr : α → ℝ → ℝ) : Matrix ι ι ℂ :=
  ∑ a, ∑ ω ∈ bohrFreqs H, ((κr a ω : ℝ) : ℂ) • ((bohrComp H (F a) ω)ᴴ * bohrComp H (F a) ω)

/-- The effective thermal Lindbladian (1.17)/(3.3) of the instantaneous Hamiltonian `H`, with
jump operators `F α`, rates `γ_α(ω)` and Lamb coefficients `κ_α(ω)`:
`ρ ↦ −i[H + H_LS, ρ] + Σ_{α,ω} γ_α(ω) D[F_{α,ω}](ρ)`. -/
def daviesGen (H : Matrix ι ι ℂ) (F : α → Matrix ι ι ℂ) (γr κr : α → ℝ → ℝ)
    (ρ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (-Complex.I) • ((H + lambShift H F κr) * ρ - ρ * (H + lambShift H F κr)) +
    ∑ a, ∑ ω ∈ bohrFreqs H, ((γr a ω : ℝ) : ℂ) • dissipator (bohrComp H (F a) ω) ρ

/-- The same generator tensored with the identity on a reference register `R`:
`L ⊗ id_R`. -/
def daviesGenRef {R : Type} [Fintype R] [DecidableEq R] (H : Matrix ι ι ℂ)
    (F : α → Matrix ι ι ℂ) (γr κr : α → ℝ → ℝ) (ρ : Matrix (ι × R) (ι × R) ℂ) :
    Matrix (ι × R) (ι × R) ℂ :=
  (-Complex.I) • (liftRef (H + lambShift H F κr) * ρ - ρ * liftRef (H + lambShift H F κr)) +
    ∑ a, ∑ ω ∈ bohrFreqs H, ((γr a ω : ℝ) : ℂ) • dissipator (liftRef (bohrComp H (F a) ω)) ρ

/-- The bath assumptions (1.18)–(1.19) at inverse temperature `β` with bounds `γ, κ`:
`0 ≤ γ_α(ω) ≤ γ` and `|κ_α(ω)| ≤ κ` for all `α, ω`, and detailed balance
`γ_α(−ω) = e^{−βω} γ_α(ω)` for every `ω > 0`. -/
def RatesAdmissible (β γ κ : ℝ) (γr κr : α → ℝ → ℝ) : Prop :=
  (∀ a ω, 0 ≤ γr a ω ∧ γr a ω ≤ γ) ∧
    (∀ a ω, 0 < ω → γr a (-ω) = Real.exp (-(β * ω)) * γr a ω) ∧
    (∀ a ω, |κr a ω| ≤ κ)

end Spectral

/-! ### Solutions of time-dependent linear matrix equations -/

/-- `ρ` solves `ρ'(t) = L(t)(ρ(t))` on `[0, T]`: every entry is continuous on `[0, T]` and has
derivative (within `[0, T]`) given by `L(t)(ρ(t))` at every `t ∈ [0, T]` outside a countable
set. The exceptional set allows generators that jump at finitely many level crossings. -/
def IsSolution {ι κ : Type} (L : ℝ → Matrix ι κ ℂ → Matrix ι κ ℂ) (T : ℝ)
    (ρ : ℝ → Matrix ι κ ℂ) : Prop :=
  (∀ i j, ContinuousOn (fun t => ρ t i j) (Set.Icc 0 T)) ∧
    ∃ S : Set ℝ, S.Countable ∧ ∀ t ∈ Set.Icc 0 T \ S, ∀ i j,
      HasDerivWithinAt (fun u => ρ u i j) (L t (ρ t) i j) (Set.Icc 0 T) t

/-- `U` is a propagator of the Schrödinger equation `U'(t) = −i K(t) U(t)`, `U(0) = I`, on
`[0, T]` (the time-ordered exponential `T exp(−i∫₀ᵗ K)`, (1.34)/(3.2)). -/
def IsPropagator {ι : Type} [Fintype ι] [DecidableEq ι] (K : ℝ → Matrix ι ι ℂ) (T : ℝ)
    (U : ℝ → Matrix ι ι ℂ) : Prop :=
  U 0 = 1 ∧ IsSolution (fun t X => (-Complex.I) • (K t * X)) T U

/-! ### Circuits of at most two-qubit gates -/

/-- A gate on `n` qubits: a unitary on a set of at most two qubits. -/
structure Gate (n : ℕ) where
  supp : Finset (Fin n)
  supp_card : supp.card ≤ 2
  U : Matrix (supp → Fin 2) (supp → Fin 2) ℂ
  U_unitary : U ∈ Matrix.unitaryGroup (supp → Fin 2) ℂ

/-- The gate as an operator on all `n` qubits (`U ⊗ I`). -/
def Gate.op {n : ℕ} (g : Gate n) : Op (Fin n) := embedOp g.supp g.U

/-- A quantum circuit of `T` gates on `n` qubits. -/
abbrev Circuit (n T : ℕ) := Fin T → Gate n

/-- The circuit unitary `U_T ⋯ U_2 U_1` (gate `0` is applied first). -/
def Circuit.unitary {n T : ℕ} (c : Circuit n T) : Op (Fin n) :=
  (List.ofFn fun i => (c i).op).reverse.prod

/-- The ideal circuit output `𝒞|0ⁿ⟩⟨0ⁿ|𝒞†`. -/
def Circuit.output {n T : ℕ} (c : Circuit n T) : Op (Fin n) :=
  c.unitary * ketbraZero * c.unitaryᴴ

end PassiveAdiabaticFT.Thermal


