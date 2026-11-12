-- Prove2me | Definitions.Def_PassiveAdiabaticFT_Thermal_Blocks
-- name    : PassiveAdiabaticFT_Thermal_Blocks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:32.082122+00:00
-- url     : https://prove2.me/theorems/e765e60f-d4a4-40d5-8cd4-f3551006484a
-- title:
--   $N$ code blocks: $W^{\otimes N}$, product decoder and encodings, the dressed Hamiltonian, noisy generator and classical chain
-- statement:
--   Take $N$ blocks of the same code $C$ with the same decoder; the physical qubits are pairs (block $i$, qubit $q$), the logical qubits pairs (block $i$, logical qubit $j$), and the syndrome register is indexed by $\mathbf s=(s_1,\dots,s_N)\in\Omega^N$.
--
--   1. $W^{\otimes N}$, $V^{\otimes N}$, the product decoder $\mathrm{Dec}^{\otimes N}$ with Kraus operators $\bigotimes_iV^\dagger R_{s_i}\Pi_{s_i}$, and these maps tensored with the identity on a reference register $R$.
--   2. The product Gibbs weight $\pi_\beta(\mathbf s)=\prod_i\pi_\beta(s_i)$ and energy (3.6); for any real vector $p$ on $\Omega^N$ and joint logical–reference operator $\sigma_{Q,R}$,
--   $$\bar\sigma_p=W^{\otimes N}\big(\sigma_{Q,R}\otimes\tau_p\big)(W^{\otimes N})^\dagger,\qquad \tau_p=\sum_{\mathbf s}p(\mathbf s)|\mathbf s\rangle\langle\mathbf s|,$$
--   so that $(\mathrm{Enc}_{\beta'}\otimes\mathcal I_R)(\sigma_{Q,R})=\bar\sigma_{\pi_{\beta'}}$ (3.5); the code-space encoding $V^{\otimes N}\rho(V^{\otimes N})^\dagger$.
--   3. For a logical Hamiltonian $K$ on the $Nk$ logical qubits, the dressed operator $\hat K=W^{\otimes N}(K\otimes I_S)(W^{\otimes N})^\dagger$ (1.29) and the physical Hamiltonian
--   $$H=\sum_{i=1}^NH_0^{(i)}+\hat K\qquad(3.1),$$
--   with $H_0^{(i)}$ the code Hamiltonian of block $i$.
--   4. The noisy generator $\mathcal L_\beta$ (3.3): the thermal generator of $H$ whose jump operators are all $3Nb$ physical single-qubit Paulis $F_\alpha^{(i)}$, with rates $\gamma_\alpha^{(i)}$ and Lamb coefficients $\kappa_\alpha^{(i)}$.
--   5. $D_\alpha^{(i)}$, the syndromes whose $i$-th component lies in $D_\alpha$; $f_\alpha^{(i)}$, applying $f_\alpha$ to block $i$; $\delta_\alpha[s_i]=E[s_i]-E[f_\alpha(s_i)]$; and the classical generator (3.7)
--   $$(\mathsf M_\alpha^{(i)}p)(\mathbf s)=\mathbf 1_{\{\mathbf s\notin D_\alpha^{(i)}\}}\Big(\gamma_\alpha^{(-\delta_\alpha[s_i])}p(f_\alpha^{(i)}(\mathbf s))-\gamma_\alpha^{(\delta_\alpha[s_i])}p(\mathbf s)\Big),$$
--   together with its single-block version as a matrix on $\Omega$.
--
--   These are the comparison objects of §3.2 (Lemma 3.1, Lemma 3.4, Theorem 3.3).
--
--   **Formalization Note** One code and one decoder serve all blocks, as in the paper's construction (3.44). The physical register is indexed by bit strings on $\mathrm{Fin}\,N\times\mathrm{Fin}\,b$, so locality is counted in physical qubits of all blocks.
-- source:
--   Arsalan Motamedi, Peter Love, Fault Tolerant Adiabatic Quantum Computation from Passive Error Correcting Codes, STOC 2027 submission #1144 (October 2026), source.pdf SHA-256 96d4a748a9114e6a9ed0c5252e84434a63b2a1ef07b286134f01f6761c2503b8, (1.28)–(1.30) (p. 8), §3.1 (3.1) (pp. 19–20), §3.2 (3.3)–(3.7) and the definitions of τ_p, σ̄_p (pp. 20–21), (3.33)–(3.36) (p. 24), (3.44) (p. 26)

import Mathlib
import Definitions.Def_PassiveAdiabaticFT_Thermal_CodeBlock

/-!
# `N` code blocks: product decoder, thermal encoding, the dressed Hamiltonian path and its noise

Arsalan Motamedi, Peter Love, *Fault Tolerant Adiabatic Quantum Computation from Passive Error
Correcting Codes*, STOC 2027 submission #1144 (October 2026): (1.28)–(1.30) (p. 8),
§3.1 (3.1) (pp. 19–20), §3.2 (3.3)–(3.7), the states `τ_p`, `σ̄_p` (pp. 20–21), (3.33)–(3.36)
(p. 24), (3.44) (p. 26).

`N` blocks of the same code `C` with the same decoder. Physical qubits are `(i, q)`,
`i : Fin N` the block and `q : Fin b` the qubit in the block; logical qubits are `(i, j)`,
`j : Fin k`; the syndrome register is `Fin N → Ω`.
-/

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix

namespace PassiveAdiabaticFT.Thermal

/-- The bit string of block `i` of a string on `Fin N × Fin r`. -/
def blk {N r : ℕ} (x : Fin N × Fin r → Fin 2) (i : Fin N) : Fin r → Fin 2 := fun q => x (i, q)

/-- An operator `A` on one block placed on block `i` (identity on all other blocks). -/
def onBlock {N r : ℕ} (i : Fin N) (A : Op (Fin r)) : Op (Fin N × Fin r) :=
  fun x y => if ∀ j, j ≠ i → blk x j = blk y j then A (blk x i) (blk y i) else 0

namespace StabCode

variable {b : ℕ} (C : StabCode b) (N : ℕ)

/-- `V^{⊗N}`. -/
def VN : Matrix (Fin N × Fin b → Fin 2) (Fin N × Fin C.k → Fin 2) ℂ :=
  fun x ψ => ∏ i, C.V (blk x i) (blk ψ i)

/-- The product Gibbs weight (3.6): `π_β(s) = ∏_i π_β(s_i)` on `Ω^N`. -/
def gibbsN (J β : ℝ) (s : Fin N → C.Om) : ℝ := ∏ i, C.gibbs J β (s i).1

/-- The weight `p(S) = Σ_{s ∈ S} p(s)` of a set of `N`-block syndromes. -/
def massN (p : (Fin N → C.Om) → ℝ) (S : Finset (Fin N → C.Om)) : ℝ := ∑ s ∈ S, p s

/-- The code-space encoding `Enc^{⊗N}(ρ) = V^{⊗N} ρ (V^{⊗N})†` (the `β' = ∞` case, p. 25). -/
def encCodeN (ρ : Op (Fin N × Fin C.k)) : Op (Fin N × Fin b) := C.VN N * ρ * (C.VN N)ᴴ

/-- `(Enc^{⊗N} ⊗ id_R)(σ)` for the code-space encoding. -/
def encCodeNRef {R : Type} [Fintype R] [DecidableEq R]
    (σ : Matrix ((Fin N × Fin C.k → Fin 2) × R) ((Fin N × Fin C.k → Fin 2) × R) ℂ) :
    Matrix ((Fin N × Fin b → Fin 2) × R) ((Fin N × Fin b → Fin 2) × R) ℂ :=
  Matrix.kroneckerMap (· * ·) (C.VN N) (1 : Matrix R R ℂ) * σ *
    (Matrix.kroneckerMap (· * ·) (C.VN N) (1 : Matrix R R ℂ))ᴴ

/-- `f_α^{(i)}`: apply `f_α` to the `i`-th block of an `N`-block syndrome. -/
def fN (i : Fin N) (α : Fin b × Fin 3) (s : Fin N → C.Om) : Fin N → C.Om :=
  Function.update s i (C.fOm α (s i))

/-- `δ_α[s] = E[s] − E[f_α(s)]` for one block. -/
def dE (J : ℝ) (α : Fin b × Fin 3) (s : Fin C.m → ZMod 2) : ℝ :=
  C.energy J s - C.energy J (C.f α s)

end StabCode

namespace PauliDecoder

variable {b : ℕ} {C : StabCode b} (D : PauliDecoder C) (N : ℕ)

/-- `W^{⊗N}`, from logical register ⊗ syndrome register `(Fin N → Ω)` to the `N b` physical
qubits. -/
def WN : Matrix (Fin N × Fin b → Fin 2) ((Fin N × Fin C.k → Fin 2) × (Fin N → C.Om)) ℂ :=
  fun x p => ∏ i, D.W (blk x i) (blk p.1 i, p.2 i)

/-- The Kraus operator `⊗_i V† R_{s_i} Π_{s_i}` of the product decoder at syndrome `s ∈ Ω^N`. -/
def decKraus (s : Fin N → C.Om) : Matrix (Fin N × Fin C.k → Fin 2) (Fin N × Fin b → Fin 2) ℂ :=
  fun ψ x => ∏ i, (C.Vᴴ * D.R (s i).1 * synProj C.P (s i).1) (blk ψ i) (blk x i)

/-- The product decoder `Dec^{⊗N}` (block-wise (1.3)). -/
def decN (ρ : Op (Fin N × Fin b)) : Op (Fin N × Fin C.k) :=
  ∑ s : Fin N → C.Om, D.decKraus N s * ρ * (D.decKraus N s)ᴴ

/-- `Dec^{⊗N} ⊗ id_R` on a physical–reference operator. -/
def decNRef {R : Type} [Fintype R] [DecidableEq R]
    (ρ : Matrix ((Fin N × Fin b → Fin 2) × R) ((Fin N × Fin b → Fin 2) × R) ℂ) :
    Matrix ((Fin N × Fin C.k → Fin 2) × R) ((Fin N × Fin C.k → Fin 2) × R) ℂ :=
  ∑ s : Fin N → C.Om, Matrix.kroneckerMap (· * ·) (D.decKraus N s) (1 : Matrix R R ℂ) * ρ *
    (Matrix.kroneckerMap (· * ·) (D.decKraus N s) (1 : Matrix R R ℂ))ᴴ

/-- `σ̄_p = W^{⊗N} (σ_{Q,R} ⊗ τ_p) (W^{⊗N})†` (p. 20), `τ_p = Σ_s p(s) |s⟩⟨s|`, for a
logical–reference operator `σ` and any real vector `p` on `Ω^N`. -/
def sigmaBar {R : Type} [Fintype R]
    (σ : Matrix ((Fin N × Fin C.k → Fin 2) × R) ((Fin N × Fin C.k → Fin 2) × R) ℂ)
    (p : (Fin N → C.Om) → ℝ) :
    Matrix ((Fin N × Fin b → Fin 2) × R) ((Fin N × Fin b → Fin 2) × R) ℂ :=
  fun x y => ∑ ψ, ∑ φ, ∑ s, D.WN N x.1 (ψ, s) * σ (ψ, x.2) (φ, y.2) * ((p s : ℝ) : ℂ) *
    star (D.WN N y.1 (φ, s))

/-- The joint thermal encoding (3.5): `(Enc_{β'}^{⊗N} ⊗ id_R)(σ) = σ̄_{π_{β'}}`. -/
def encThNRef {R : Type} [Fintype R] (J β' : ℝ)
    (σ : Matrix ((Fin N × Fin C.k → Fin 2) × R) ((Fin N × Fin C.k → Fin 2) × R) ℂ) :
    Matrix ((Fin N × Fin b → Fin 2) × R) ((Fin N × Fin b → Fin 2) × R) ℂ :=
  D.sigmaBar N σ (C.gibbsN N J β')

/-- The thermal encoding `Enc_{β'}^{⊗N}(ρ) = W^{⊗N}(ρ ⊗ Σ_s π_{β'}(s)|s⟩⟨s|)(W^{⊗N})†`
of a logical state (independent Gibbs syndromes in the blocks). -/
def encThN (J β' : ℝ) (ρ : Op (Fin N × Fin C.k)) : Op (Fin N × Fin b) :=
  D.WN N * Matrix.kroneckerMap (· * ·) ρ
    (Matrix.diagonal fun s : Fin N → C.Om => ((C.gibbsN N J β' s : ℝ) : ℂ)) * (D.WN N)ᴴ

/-- The dressed logical operator on `N` blocks (1.29): `K̂ = W^{⊗N} (K ⊗ I_S) (W^{⊗N})†`. -/
def dressedN (K : Op (Fin N × Fin C.k)) : Op (Fin N × Fin b) :=
  D.WN N * Matrix.kroneckerMap (· * ·) K (1 : Matrix (Fin N → C.Om) (Fin N → C.Om) ℂ) *
    (D.WN N)ᴴ

/-- The physical Hamiltonian (1.28)/(3.1)/(3.44) for a logical Hamiltonian `K`:
`H = Σ_i H_0^{(i)} + K̂`, `H_0^{(i)} = J Σ_a (I − P_a^{(i)})`. -/
def Hphys (J : ℝ) (K : Op (Fin N × Fin C.k)) : Op (Fin N × Fin b) :=
  ∑ i, onBlock i (C.H0 J) + D.dressedN N K

/-- The physical single-qubit Paulis `F_α^{(i)}`, indexed by (block, qubit, Pauli type). -/
def Fphys (a : Fin N × (Fin b × Fin 3)) : Op (Fin N × Fin b) := onBlock a.1 (Fα a.2)

/-- The noisy generator `L_β(t)` of (3.3) at a time where the logical Hamiltonian is `K`: the
Davies generator of `H = Σ_i H_0^{(i)} + K̂` with jump operators all `3Nb` physical
single-qubit Paulis `F_α^{(i)}`, rates `γ_α^{(i)}(ω)` and Lamb coefficients `κ_α^{(i)}(ω)`. -/
def noisyGen (J : ℝ) (γr κr : Fin N × (Fin b × Fin 3) → ℝ → ℝ) (K : Op (Fin N × Fin C.k))
    (ρ : Op (Fin N × Fin b)) : Op (Fin N × Fin b) :=
  daviesGen (D.Hphys N J K) (Fphys N) γr κr ρ

/-- `L_β(t) ⊗ id_R`. -/
def noisyGenRef {R : Type} [Fintype R] [DecidableEq R] (J : ℝ)
    (γr κr : Fin N × (Fin b × Fin 3) → ℝ → ℝ) (K : Op (Fin N × Fin C.k))
    (ρ : Matrix ((Fin N × Fin b → Fin 2) × R) ((Fin N × Fin b → Fin 2) × R) ℂ) :
    Matrix ((Fin N × Fin b → Fin 2) × R) ((Fin N × Fin b → Fin 2) × R) ℂ :=
  daviesGenRef (D.Hphys N J K) (Fphys N) γr κr ρ

open Classical in
/-- `D_α^{(i)}`: the `N`-block syndromes whose `i`-th component is dangerous for `F_α` (p. 20). -/
def DsetN (i : Fin N) (α : Fin b × Fin 3) : Finset (Fin N → C.Om) :=
  Finset.univ.filter fun s => (s i).1 ∈ D.Dset α

open Classical in
/-- The classical generator (3.7) on `N` blocks:
`(M_α^{(i)} p)(s) = 1{s ∉ D_α^{(i)}} (γ_α^{(−δ_α[s_i])} p(f_α^{(i)}(s)) − γ_α^{(δ_α[s_i])} p(s))`,
with the rate function `g = γ_α^{(i)}`. -/
def MN (J : ℝ) (i : Fin N) (α : Fin b × Fin 3) (g : ℝ → ℝ) (p : (Fin N → C.Om) → ℝ)
    (s : Fin N → C.Om) : ℝ :=
  if (s i).1 ∈ D.Dset α then 0 else
    g (-(C.dE J α (s i).1)) * p (C.fN N i α s) - g (C.dE J α (s i).1) * p s

open Classical in
/-- The single-block classical generator (3.7) as a matrix on `Ω`:
`(M_α q)(s) = 1{s ∉ D_α}(γ_α^{(−δ_α[s])} q(f_α(s)) − γ_α^{(δ_α[s])} q(s))`. -/
def Mblock (J : ℝ) (α : Fin b × Fin 3) (g : ℝ → ℝ) : Matrix C.Om C.Om ℝ :=
  fun s s' => if s.1 ∈ D.Dset α then 0 else
    (if s' = C.fOm α s then g (-(C.dE J α s.1)) else 0) - (if s' = s then g (C.dE J α s.1) else 0)

end PauliDecoder

end PassiveAdiabaticFT.Thermal


