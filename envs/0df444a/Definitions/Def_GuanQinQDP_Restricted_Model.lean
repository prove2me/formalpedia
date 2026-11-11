-- Prove2me | Definitions.Def_GuanQinQDP_Restricted_Model
-- name    : GuanQinQDP_Restricted_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:41:28.139214+00:00
-- url     : https://prove2.me/theorems/2766a7a1-9c14-47d1-99dc-ee35606429a2
-- title:
--   Local-operation neighbors, privacy profiles, pullbacks and the equal-marginal program $L_{\gamma,i}$
-- statement:
--   All Hilbert spaces are finite dimensional; a qubit is $\mathbb C^2$. A **density operator** is a positive semidefinite operator of trace one, an **effect** is an operator $M$ with $0\preceq M\preceq I$, and a **channel** is a linear, completely positive, trace-preserving map. For a map $\Phi$ on the first tensor factor, $(\Phi\otimes\mathrm{id}_R)(X)$ applies $\Phi$ to every block $X_{r,r'}$ of $X$, so entangled inputs are included.
--
--   1. **Local-operation neighbors** (Definition 2.1). States $\rho,\sigma$ on $H=\bigotimes_{j=1}^n H_j$ are neighboring at register $i$, written $\rho\sim_i\sigma$, if
--   $$\sigma=(\Phi\otimes\mathrm{id}_{\bar\imath})(\rho)\quad\text{or}\quad\rho=(\Phi\otimes\mathrm{id}_{\bar\imath})(\sigma)$$
--   for some channel $\Phi$ on $L(H_i)$. Here $H_{\bar\imath}=\bigotimes_{j\ne i}H_j$. The relation is defined both for $n$ qubit registers (after regrouping $H\cong H_i\otimes H_{\bar\imath}$) and for a bipartite space $H_i\otimes C$ with an arbitrary complement $C$.
--   2. **Privacy profile** (Definition 2.3). For a map $A$ on the input, a set $\mathcal E$ of events on its output and $\gamma\ge1$,
--   $$\Delta^{\mathcal E}_{A,i}(\gamma)=\sup_{\rho\sim_i\sigma}\ \sup_{M\in\mathcal E}\operatorname{Tr}\big[M\big(A(\rho)-\gamma A(\sigma)\big)\big],\qquad \Delta^{\mathcal E}_{A}(\gamma)=\max_{i\in[n]}\Delta^{\mathcal E}_{A,i}(\gamma).$$
--   3. **Standalone profile** (§2.4–2.5). For a channel $E$ with a single register every pair of inputs is neighboring, so $\Delta^{\mathrm{ALL}}_E(\gamma)$ is the supremum of $\operatorname{Tr}[M(E(\rho)-\gamma E(\sigma))]$ over all pairs of input states and all output effects. For $A=\bigotimes_j A_j$ one writes $\Delta_j=\Delta^{\mathrm{ALL}}_{A_j}$.
--   4. **Tensor channel.** $A=\bigotimes_{j=1}^nA_j$ for qubit maps $A_j:M_2\to M_2$, defined on all operators of $(\mathbb C^2)^{\otimes n}$.
--   5. **Pullback.** $A^\dagger(M)$ is the Hilbert–Schmidt adjoint: $\operatorname{Tr}[A^\dagger(M)X]=\operatorname{Tr}[MA(X)]$.
--   6. **Equal-marginal program** (§3.1). For an operator $B$ on $\mathbb C^2\otimes R$,
--   $$L_{\gamma,i}(B)=\max\big\{\operatorname{Tr}[B(\rho-\gamma\sigma)] : \rho,\sigma\in D(\mathbb C^2\otimes R),\ \operatorname{Tr}_i\rho=\operatorname{Tr}_i\sigma\big\}.$$
--   Its value is signed and can be negative.
--   7. **Compression** (§3.2). For an isometry $V:\mathbb C^s\to H_{\bar\imath}$ onto a subspace $S$, the compressed pullback is $B_{M,S}=(I_i\otimes V^\dagger)A^\dagger(M)(I_i\otimes V)$. An operator on $H_i\otimes H_{\bar\imath}$ is supported on $H_i\otimes S$ if it is unchanged by compression with the projection $I_i\otimes VV^\dagger$ on both sides.
--
--   These objects state the exact characterization of §3 and the maximum rule of §4.
--
--   **Formalization Note** Operators are complex matrices over finite index types. The changed register is the first tensor factor, so $\operatorname{Tr}_i$ is the published `traceLeft`. Suprema are `sSup` of real sets. Every set used is nonempty, because the identity channel makes each state its own neighbor (proved as `neighborFirst_refl`). Every set is bounded, because acceptance probabilities lie in $[0,1]$. The maximum over subspaces $S$ is a supremum over the isometries $V$ onto them. $L_{\gamma,i}(B_{M,S})$ does not depend on which isometry is chosen, because a unitary on $\mathbb C^s$ preserves the marginal constraint. Traces are taken by real part.
-- source:
--   Ji Guan, Yecheng Qin, Parallel Composition of Quantum Differential Privacy: The Role of Measurement Restrictions, STOC 2027 submission #1640 (October 2026), source.pdf SHA-256 da23c8347251683a16df4c61de3fa1604211cdbf34d757a7a45feb0efd54c694, §2.1 Definition 2.1 (printed p. 13 / PDF p. 14), §2.3 Definition 2.3 and §2.4–2.5 (printed p. 14 / PDF p. 15), §3.1–3.2 (printed p. 16 / PDF p. 17)

import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WildeQIT_EntBreaking_IsQuantumChannel

/-!
# Local-operation neighbors, privacy profiles and the equal-marginal program

Ji Guan, Yecheng Qin, *Parallel Composition of Quantum Differential Privacy: The Role of
Measurement Restrictions*, STOC 2027 submission #1640 (October 2026):
§2.1 (printed p. 13 / PDF p. 14), §2.3–2.5 (printed pp. 13–14 / PDF pp. 14–15),
§3.1–3.2 (printed p. 16 / PDF p. 17).

Conventions. All Hilbert spaces are finite dimensional: operators on `ℂ^ι` are complex matrices
indexed by a finite type `ι`; a qubit is `Fin 2`. A density operator is a PSD matrix of trace one
(`QAlgorithms.IsDensityMatrix`), an effect is `0 ⪯ M ⪯ I` (`QAlgorithms.IsEffect`), and the
acceptance probability is the real part of `Tr(M ω)` (`QAlgorithms.effectProb`). A channel is a
`ℂ`-linear, completely positive, trace-preserving map
(`WildeQIT.EntBreaking.IsQuantumChannel`). In the bipartite constructions of §3 the changed
register `i` is the **first** tensor factor and its complement `ī` the second one, so that
`Tr_i` is `QAlgorithms.traceLeft`.
-/

namespace GuanQinQDP.Restricted

open QAlgorithms
open scoped Matrix ComplexOrder

/-- A qubit register: operators on `ℂ²` are matrices indexed by `Fin 2`. -/
abbrev Qubit := Fin 2

/-- `(Φ ⊗ id_R)(X)` for a map `Φ` acting on the **first** tensor factor: the block of `X` with
second-factor indices `(r, r')` is sent to its image under `Φ`. Off-diagonal blocks are kept, so
this is the tensor extension on every operator, entangled inputs included. -/
def applyFirst {I J R : Type*} (Φ : Matrix I I ℂ → Matrix J J ℂ)
    (X : Matrix (I × R) (I × R) ℂ) : Matrix (J × R) (J × R) ℂ :=
  Matrix.of fun p q => Φ (Matrix.of fun i i' => X (i, p.2) (i', q.2)) p.1 q.1

/-- Definition 2.1 (printed p. 13 / PDF p. 14), bipartite form: states on `H_i ⊗ R` are
neighboring at the first register when `σ = (Φ ⊗ id)(ρ)` **or** `ρ = (Φ ⊗ id)(σ)` for some
channel `Φ` on `L(H_i)` (same input and output space). The relation is symmetric. -/
def NeighborFirst {I R : Type} [Fintype I] (ρ σ : Matrix (I × R) (I × R) ℂ) : Prop :=
  ∃ Φ : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ, WildeQIT.EntBreaking.IsQuantumChannel Φ ∧
    (σ = applyFirst Φ ρ ∨ ρ = applyFirst Φ σ)

/-- The canonical regrouping `H = ⨂_j H_j ≅ H_i ⊗ H_ī` of `n` qubit registers, register `i`
first and the other `n − 1` registers (indexed by `{j // j ≠ i}`) second. -/
def splitEquiv {n : ℕ} (i : Fin n) :
    (Fin n → Qubit) ≃ Qubit × ({j : Fin n // j ≠ i} → Qubit) :=
  Equiv.piSplitAt i (fun _ => Qubit)

/-- An operator on `n` qubit registers, rewritten on `H_i ⊗ H_ī` (a relabelling of indices). -/
def splitAt {n : ℕ} (i : Fin n) (X : Matrix (Fin n → Qubit) (Fin n → Qubit) ℂ) :
    Matrix (Qubit × ({j : Fin n // j ≠ i} → Qubit)) (Qubit × ({j : Fin n // j ≠ i} → Qubit)) ℂ :=
  Matrix.reindex (splitEquiv i) (splitEquiv i) X

/-- Definition 2.1 (printed p. 13 / PDF p. 14): `ρ ∼ᵢ σ` for states on `n` qubit registers:
`σ = (Φ ⊗ id_ī)(ρ)` or `ρ = (Φ ⊗ id_ī)(σ)` for some channel `Φ` on `L(H_i)`. -/
def NeighborAt {n : ℕ} (i : Fin n) (ρ σ : Matrix (Fin n → Qubit) (Fin n → Qubit) ℂ) : Prop :=
  NeighborFirst (splitAt i ρ) (splitAt i σ)

/-- The deficit `Tr[M A(ρ)] − γ Tr[M A(σ)] = Tr[M (A(ρ) − γ A(σ))]` of an event `M`. -/
noncomputable def deficit {ι κ : Type*} [Fintype κ] (A : Matrix ι ι ℂ → Matrix κ κ ℂ)
    (M : Matrix κ κ ℂ) (ρ σ : Matrix ι ι ℂ) (γ : ℝ) : ℝ :=
  effectProb M (A ρ) - γ * effectProb M (A σ)

/-- Definition 2.3 (printed p. 14 / PDF p. 15), bipartite form: the profile at the first register
against the event set `E`,
`Δ^E_{A}(γ) = sup_{ρ ∼ σ} sup_{M ∈ E} Tr[M(A(ρ) − γA(σ))]`, the supremum over all pairs of
density operators on `H_i ⊗ C` neighboring at the first register and all `M ∈ E`. -/
noncomputable def profileFirst {I C K : Type} [Fintype I] [Fintype C] [Fintype K]
    (E : Set (Matrix K K ℂ)) (A : Matrix (I × C) (I × C) ℂ → Matrix K K ℂ) (γ : ℝ) : ℝ :=
  sSup {x | ∃ ρ σ : Matrix (I × C) (I × C) ℂ, ∃ M ∈ E,
    IsDensityMatrix ρ ∧ IsDensityMatrix σ ∧ NeighborFirst ρ σ ∧ x = deficit A M ρ σ γ}

/-- Definition 2.3 (printed p. 14 / PDF p. 15): the profile at register `i` of a map `A` on `n`
qubit registers against the event set `E` on its output,
`Δ^E_{A,i}(γ) = sup_{ρ ∼ᵢ σ} sup_{M ∈ E} Tr[M(A(ρ) − γA(σ))]`. -/
noncomputable def profileAt {n : ℕ} {K : Type} [Fintype K] (E : Set (Matrix K K ℂ))
    (A : Matrix (Fin n → Qubit) (Fin n → Qubit) ℂ → Matrix K K ℂ) (i : Fin n) (γ : ℝ) : ℝ :=
  sSup {x | ∃ ρ σ : Matrix (Fin n → Qubit) (Fin n → Qubit) ℂ, ∃ M ∈ E,
    IsDensityMatrix ρ ∧ IsDensityMatrix σ ∧ NeighborAt i ρ σ ∧ x = deficit A M ρ σ γ}

/-- Definition 2.3 (printed p. 14 / PDF p. 15): the privacy profile
`Δ^E_A(γ) = max_{i ∈ [n]} Δ^E_{A,i}(γ)` (a finite maximum for `n ≥ 1`). -/
noncomputable def profile {n : ℕ} {K : Type} [Fintype K] (E : Set (Matrix K K ℂ))
    (A : Matrix (Fin n → Qubit) (Fin n → Qubit) ℂ → Matrix K K ℂ) (γ : ℝ) : ℝ :=
  ⨆ i : Fin n, profileAt E A i γ

/-- §2.4–2.5 (printed p. 14 / PDF p. 15): the standalone profile `Δ^ALL_E(γ)` of a channel with
a single register. With one register every ordered pair of input states is neighboring (§2.1,
via the replacement channel), so this is the supremum of `Tr[M(E(ρ) − γE(σ))]` over **all**
pairs of input density operators and **all** effects on the output. -/
noncomputable def standaloneProfile {a b : Type} [Fintype a] [Fintype b] [DecidableEq b]
    (E : Matrix a a ℂ → Matrix b b ℂ) (γ : ℝ) : ℝ :=
  sSup {x | ∃ ρ σ : Matrix a a ℂ, ∃ M : Matrix b b ℂ,
    IsDensityMatrix ρ ∧ IsDensityMatrix σ ∧ IsEffect M ∧ x = deficit E M ρ σ γ}

/-- §2.5 (printed p. 14 / PDF p. 15): `A = ⨂_{j=1}^n A_j` for qubit maps `A_j : M₂ → M₂`,
defined on every operator through the matrix-unit expansion (the published `piSuperop`), so
entangled inputs are included. -/
noncomputable def tensorChannel {n : ℕ} (A : Fin n → (Matrix Qubit Qubit ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ)) :
    Matrix (Fin n → Qubit) (Fin n → Qubit) ℂ → Matrix (Fin n → Qubit) (Fin n → Qubit) ℂ :=
  piSuperop fun j => ⇑(A j)

/-- §2.1 (printed p. 13 / PDF p. 14): the pullback `A†(M)`, the Hilbert–Schmidt adjoint, with
`Tr[A†(M) X] = Tr[M A(X)]` for every operator `X` when `A` is linear. Entry `(a, b)` is
`Tr[M A(|b⟩⟨a|)]`. -/
noncomputable def pullback {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (A : Matrix ι ι ℂ → Matrix κ κ ℂ) (M : Matrix κ κ ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun a b => (M * A (Matrix.single b a 1)).trace

/-- The real value `Tr[B(ρ − γσ)]` of a pair `(ρ, σ)` against a Hermitian operator `B`. -/
noncomputable def pairValue {ι : Type*} [Fintype ι] (B ρ σ : Matrix ι ι ℂ) (γ : ℝ) : ℝ :=
  (B * (ρ - (γ : ℂ) • σ)).trace.re

/-- §3.1 (printed p. 16 / PDF p. 17): the equal-marginal program
`L_{γ,i}(B) = max { Tr[B(ρ − γσ)] : ρ, σ ∈ D(ℂ² ⊗ R), Tr_i ρ = Tr_i σ }` for an operator `B`
on `ℂ² ⊗ R`, register `i` the first factor. The value is signed (it can be negative). It is
written as a supremum; the source notes that the feasible set is compact and nonempty, so it is
attained. -/
noncomputable def Lval {R : Type} [Fintype R] (γ : ℝ) (B : Matrix (Qubit × R) (Qubit × R) ℂ) : ℝ :=
  sSup {x | ∃ ρ σ : Matrix (Qubit × R) (Qubit × R) ℂ,
    IsDensityMatrix ρ ∧ IsDensityMatrix σ ∧ traceLeft ρ = traceLeft σ ∧ x = pairValue B ρ σ γ}

/-- §3.2 (printed p. 16 / PDF p. 17): the compressed pullback
`B_{M,S} = (I_i ⊗ V_S†) A†(M) (I_i ⊗ V_S)` on `ℂ² ⊗ ℂ^s`, where `V : ℂ^s → H_ī` is an isometry
(`V† V = I`) onto the subspace `S = range V` of the unchanged input. -/
noncomputable def compress {C K : Type} [Fintype C] [DecidableEq C] [Fintype K] {s : ℕ}
    (A : Matrix (Qubit × C) (Qubit × C) ℂ → Matrix K K ℂ) (M : Matrix K K ℂ)
    (V : Matrix C (Fin s) ℂ) : Matrix (Qubit × Fin s) (Qubit × Fin s) ℂ :=
  (Matrix.kronecker (1 : Matrix Qubit Qubit ℂ) V)ᴴ * pullback A M *
    Matrix.kronecker (1 : Matrix Qubit Qubit ℂ) V

/-- The inner optimization of Theorem 3.5 (printed p. 17 / PDF p. 18):
`max_{S ⊆ H_ī, 1 ≤ dim S ≤ 2} L_{γ,i}(B_{M,S})`, parametrized by the isometries
`V : ℂ^s → H_ī`, `s ∈ {1, 2}`, onto the subspaces `S` (every such `S` is the range of one, and
`L_{γ,i}(B_{M,S})` does not depend on which). Written as a supremum. -/
noncomputable def compressedValue {C K : Type} [Fintype C] [DecidableEq C] [Fintype K]
    (A : Matrix (Qubit × C) (Qubit × C) ℂ → Matrix K K ℂ) (M : Matrix K K ℂ) (γ : ℝ) : ℝ :=
  sSup {x | ∃ s : ℕ, 1 ≤ s ∧ s ≤ 2 ∧ ∃ V : Matrix C (Fin s) ℂ, Vᴴ * V = 1 ∧
    x = Lval γ (compress A M V)}

/-- Lemma 3.2 (printed p. 16 / PDF p. 17): an operator `X` on `H_i ⊗ C` is supported on
`H_i ⊗ S`, `S = range V` for an isometry `V`: `P X P = X` for the projection
`P = I_i ⊗ V V†` onto `H_i ⊗ S`. -/
def SupportedOn {I C : Type} [Fintype I] [DecidableEq I] [Fintype C] {s : ℕ}
    (V : Matrix C (Fin s) ℂ) (X : Matrix (I × C) (I × C) ℂ) : Prop :=
  Matrix.kronecker (1 : Matrix I I ℂ) (V * Vᴴ) * X * Matrix.kronecker (1 : Matrix I I ℂ) (V * Vᴴ) = X

/-! ### Sanity checks -/

/-- `id ⊗ id` is the identity. -/
example {I R : Type*} (X : Matrix (I × R) (I × R) ℂ) :
    applyFirst (fun Y : Matrix I I ℂ => Y) X = X := by
  ext p q; rfl

/-- The identity map is a channel, so every state is neighboring to itself: the neighbor pairs
(and hence the sets in the profiles) are nonempty whenever a state exists. -/
theorem neighborFirst_refl {I R : Type} [Fintype I] (ρ : Matrix (I × R) (I × R) ℂ) :
    NeighborFirst ρ ρ := by
  refine ⟨LinearMap.id, ⟨?_, fun X => rfl⟩, Or.inl ?_⟩
  · intro r X hX
    have h : idTensorSuperop (⇑(LinearMap.id : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ)) X = X := by
      ext p q; rfl
    rw [h]; exact hX
  · ext p q; rfl

end GuanQinQDP.Restricted


