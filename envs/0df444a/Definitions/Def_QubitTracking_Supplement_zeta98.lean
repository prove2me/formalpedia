-- Prove2me | Definitions.Def_QubitTracking_Supplement_zeta98
-- name    : QubitTracking_Supplement_zeta98
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:14:51.511225+00:00
-- url     : https://prove2.me/theorems/92c96708-de0e-4a6c-9a58-3f7aceaed03e
-- title:
--   The cloning parameter $\zeta$ of a state family and the $\zeta$-uniqueness experiment
-- statement:
--   **The uniqueness parameter.** For a family $\mathcal S=\{|\psi_i\rangle\}$ of $n$-qubit states (indexed as in Construction 9.8),
--   $$\zeta:=\sup_{\mathcal A}\ \mathbb E_{i}\big[\langle\psi_i|\langle\psi_i|\,\mathcal A(|\psi_i\rangle\langle\psi_i|)\,|\psi_i\rangle|\psi_i\rangle\big],$$
--   the supremum over all quantum channels $\mathcal A$ from $n$ to $2n$ qubits (of unbounded complexity), with $i$ uniform. It is the optimal cloning fidelity of $\mathcal S$.
--
--   **Two-region registers.** For a prover, a time $t'$ and two spatial regions $S_0,S_1\subseteq\mathbb R$, $\mathsf{register}[S_b@t']$ consists of the cells located in $S_b$ at time $t'$, excluding challenge cells not yet broadcast and response cells already received; a verifier's message is heard in $S_b@t'$ when it has reached some point of $S_b\cap[-1,1]$ by time $t'$. The joint reduced state on $\mathsf{register}[S_0@t']\otimes\mathsf{register}[S_1@t']$ traces out all other cells.
--
--   **The uniqueness experiment.** Two local adversaries $\mathcal A$ on $\mathsf{register}[S_0@t']$ and $\mathcal B$ on $\mathsf{register}[S_1@t']$, each a channel to $n$ qubits that may depend on the public oracle and on the messages heard in its own region, are applied to the joint state; the value of the experiment is the expected fidelity $\mathbb E[\langle\psi_i|\langle\psi_i|(\mathcal A\otimes\mathcal B)(\rho_{\mathbf A^*\mathbf B^*})|\psi_i\rangle|\psi_i\rangle]$ over all randomness of Construction 9.8.
--
--   **Formalization Note** Channels are finite Kraus families with $\sum_jK_j^\dagger K_j=1$ (the published `WildeQIT.QChannel`). The set inside the supremum is nonempty and bounded by $1$, so the real supremum is the true one.
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Theorem 9.9 (definition of ζ), p.70; Definition 9.7 (ζ-Uniqueness), p.69; Definition 3.2, pp.23–24

import Definitions.Def_QubitTracking_Supplement_accProb98
import Definitions.Def_WildeQIT_QChannel

set_option autoImplicit false

open Matrix

namespace QubitTracking.Supplement

/-! The uniqueness parameter `ζ` of Theorem 9.9 and the `ζ`-uniqueness experiment of
Definition 9.7.

Source: Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through Space and Time (Or:
Sailing in a Quantum Boat)*, arXiv:2605.30732 (held version, sha256 bf98e5b5…), Definition 3.2,
pp.23–24, Definition 9.7, p.69, Theorem 9.9, p.70. -/

/-- **The uniqueness parameter** (Theorem 9.9, p.70):
`ζ := sup_𝒜 𝔼[⟨ψ_i|⟨ψ_i| 𝒜(|ψ_i⟩⟨ψ_i|) |ψ_i⟩|ψ_i⟩ : |ψ_i⟩ ← 𝒮]`, the supremum over all channels
`𝒜` from `n` to `2n` qubits (of unbounded size; a channel is a finite Kraus family with
`∑_j K_j†K_j = 1`, the published `WildeQIT.QChannel`), with `|ψ_i⟩` uniform over the family as
indexed.

**Formalization Note** The set is nonempty (an isometry appending `n` qubits) and bounded by `1`,
so the real supremum is the true one. -/
noncomputable def zeta98 {n k : ℕ} (F : StateFam n k) : ℝ :=
  sSup {z : ℝ | ∃ N : WildeQIT.QChannel (Bits (Fin n)) (Bits (Fin n) × Bits (Fin n)),
      z = avg fun i : Fin k × Bits (Fin n) =>
        fidPure (fun p : Bits (Fin n) × Bits (Fin n) => psiFam F i p.1 * psiFam F i p.2)
          (N.apply (proj (psiFam F i)))}

/-- **The cells of `register[S @ t]`** for an arbitrary spatial region `S ⊆ ℝ` (Definition 3.2,
items 1–2): the cells located in `S` at time `t`, except challenge cells not yet broadcast and
response cells already received (as in `regionMem`, which is the case `S = [a, b]`). -/
def regionOn {σ : Sched} {lam inLen respLen : ℕ} {κ : Type} {inL outL : κ → ℕ}
    (P : Prover σ lam inLen respLen κ inL outL) (t : ℝ) (S : Set ℝ) (c : P.Cell) : Prop :=
  P.traj c t ∈ S ∧
  (¬ ∃ i j, c = P.chalL i j ∧ t < σ.sendL i) ∧
  (¬ ∃ i j, c = P.chalR i j ∧ t < σ.sendR i) ∧
  (¬ ∃ i j, c = P.respL i j ∧ σ.deadL i ≤ t) ∧
  (¬ ∃ i j, c = P.respR i j ∧ σ.deadR i ≤ t)

/-- `𝒱_L`'s round-`i` message is heard in `S @ t` (Definition 3.2, item 3): it reaches some point
`p ∈ S ∩ [−1, 1]` by time `t`, i.e. `p + 1 ≤ t − sendL i`. -/
def HeardLOn (σ : Sched) (t : ℝ) (S : Set ℝ) (i : Fin (σ.N + 1)) : Prop :=
  ∃ p ∈ S ∩ Set.Icc (-1 : ℝ) 1, p + 1 ≤ t - σ.sendL i

/-- `𝒱_R`'s round-`i` message is heard in `S @ t`: `1 − p ≤ t − sendR i` for some
`p ∈ S ∩ [−1, 1]`. -/
def HeardROn (σ : Sched) (t : ℝ) (S : Set ℝ) (i : Fin (σ.N + 1)) : Prop :=
  ∃ p ∈ S ∩ Set.Icc (-1 : ℝ) 1, 1 - p ≤ t - σ.sendR i

open Classical in
/-- **The reduced state on `register[S₀ @ t′] ⊗ register[S₁ @ t′]`** (Definition 3.2 with two
regions) of a global pure state `ψ` on the cells (no anchor, `Fin 0`): the partial trace over every
cell in neither region. -/
noncomputable def regState2 {σ : Sched} {lam inLen respLen : ℕ} {κ : Type} {inL outL : κ → ℕ}
    (P : Prover σ lam inLen respLen κ inL outL) (R₀ R₁ : P.Cell → Prop)
    (ψ : Bits (Fin 0 ⊕ P.Cell) → ℂ) :
    Matrix (Bits {c // R₀ c} × Bits {c // R₁ c}) (Bits {c // R₀ c} × Bits {c // R₁ c}) ℂ :=
  fun p q =>
    ∑ e : Bits {c // ¬ R₀ c ∧ ¬ R₁ c},
      ψ (Sum.elim (fun i => i.elim0) (fun c =>
          if h₀ : R₀ c then p.1 ⟨c, h₀⟩ else if h₁ : R₁ c then p.2 ⟨c, h₁⟩ else e ⟨c, h₀, h₁⟩)) *
        star (ψ (Sum.elim (fun i => i.elim0) (fun c =>
          if h₀ : R₀ c then q.1 ⟨c, h₀⟩ else if h₁ : R₁ c then q.2 ⟨c, h₁⟩ else e ⟨c, h₀, h₁⟩)))

/-- The product map `(𝒜 ⊗ ℬ)(ρ) = ∑_{j,k} (A_j ⊗ B_k) ρ (A_j ⊗ B_k)†` of two channels on the two
factors of a bipartite operator. -/
noncomputable def chanPair {α β γ δ : Type} [Fintype α] [Fintype β] [DecidableEq β] [Fintype γ]
    [Fintype δ] [DecidableEq δ] (A : WildeQIT.QChannel β α) (B : WildeQIT.QChannel δ γ)
    (ρ : Matrix (β × δ) (β × δ) ℂ) : Matrix (α × γ) (α × γ) ℂ :=
  fun p q => ∑ j, ∑ k, ∑ b, ∑ d, ∑ b', ∑ d',
    A.K j p.1 b * B.K k p.2 d * ρ (b, d) (b', d') * star (A.K j q.1 b') * star (B.K k q.2 d')

open Classical in
/-- **A local (potentially unbounded) adversary** on the region `R` of cells (Definition 9.7,
`ζ`-Uniqueness, p.69): for each value of `pp = 𝒪` and of the transcripts heard in its region, a
channel from the region's cells to `n` qubits. -/
def LocalAdv98 (n m lam : ℕ) {σ : Sched} (P : Prover98 n m lam σ) (R : P.Cell → Prop) : Type 1 :=
  PP98 n m lam → (Fin (σ.N + 1) → Option (Bits (Fin (lam + 1)))) →
    (Fin (σ.N + 1) → Option (Bits (Fin (lam + 1)))) →
      WildeQIT.QChannel (Bits {c // R c}) (Bits (Fin n))

open Classical in
/-- **The value of the `ζ`-uniqueness experiment** (Definition 9.7, p.69): the prover `P` runs
`Localize`; at time `t′` the registers `𝐀* = register[S₀ @ t′]` and `𝐁* = register[S₁ @ t′]` are
handed to the local adversaries `𝒜` and `ℬ` (each also sees `pp` and the transcripts heard in its
region); the result is `𝔼[⟨ψ_i|⟨ψ_i| (𝒜 ⊗ ℬ)(ρ_{𝐀*𝐁*}) |ψ_i⟩|ψ_i⟩]` over all randomness. -/
noncomputable def uniqVal98 {n m lam k : ℕ} {σ : Sched} (P : Prover98 n m lam σ)
    (F : StateFam n k) (S₀ S₁ : Set ℝ) (t' : ℝ)
    (A : LocalAdv98 n m lam P (regionOn P t' S₀)) (B : LocalAdv98 n m lam P (regionOn P t' S₁)) :
    ℝ :=
  avg fun ω : Omega98 n m lam σ.N k =>
    fidPure (fun p : Bits (Fin n) × Bits (Fin n) => psiFam F ω.2.2.2.1 p.1 * psiFam F ω.2.2.2.1 p.2)
      (chanPair
        (A (pp98 ω) (heardTranscript (HeardLOn σ t' S₀) (msgL98 ω))
          (heardTranscript (HeardROn σ t' S₀) (msgR98 ω)))
        (B (pp98 ω) (heardTranscript (HeardLOn σ t' S₁) (msgL98 ω))
          (heardTranscript (HeardROn σ t' S₁) (msgR98 ω)))
        (regState2 P (regionOn P t' S₀) (regionOn P t' S₁)
          (P.stateAt (Fin 0) (fun _ _ => orc98 ω) (initState98 P F ω) t')))

end QubitTracking.Supplement


