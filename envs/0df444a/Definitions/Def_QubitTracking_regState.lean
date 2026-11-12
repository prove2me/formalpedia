-- Prove2me | Definitions.Def_QubitTracking_regState
-- name    : QubitTracking_regState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:31:34.412147+00:00
-- url     : https://prove2.me/theorems/e7894dce-0b25-4c90-b072-d9fd82a1dbc3
-- title:
--   The register $\mathsf{register}[[a,b]@t]$: region cells, heard transcripts, reduced state
-- statement:
--   For a prover and a spatial interval $[a,b]$ at time $t$, the **region cells** are the cells located in $[a,b]$ at time $t$, except the challenge cells of rounds broadcast after $t$ (still the verifier's) and the response cells of rounds whose deadline is at or before $t$ (already the verifier's). A message of $\mathcal V_L$ sent at time $s$ is **heard** in $[a,b]@t$ if $t-s\ge\max(a,-1)+1$, and one of $\mathcal V_R$ if $t-s\ge 1-\min(b,1)$. The **heard transcript** of a verifier lists each round's challenge if heard and nothing otherwise.
--
--   For a global pure state $\psi$ on $\mathbf A\otimes(\text{cells})$, the reduced state on $\mathbf A\otimes(\text{region cells})$ is
--   $$\rho\big((x,r),(x',r')\big)=\sum_{e}\psi(x,r,e)\,\overline{\psi(x',r',e)},$$
--   $e$ ranging over the basis labels of the cells outside the region. A Kraus family acts on the second factor by $\rho\mapsto\sum_j(1\otimes K_j)\rho(1\otimes K_j)^\dagger$.
--
--   These objects make Definition 3.2 precise: items 1–2 are the region cells, item 3 the heard transcript.
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Definition 3.2, pp.23–24

import Definitions.Def_QubitTracking_Prover

set_option autoImplicit false

open Matrix

namespace QubitTracking

variable {σ : Sched} {lam inLen respLen : ℕ} {κ : Type} {inL outL : κ → ℕ}

/-- **The cells of `register[[a, b] @ t]`** (Definition 3.2, pp.23–24, items 1–2), for a prover `P`
and the spatial interval `[a, b]` at time `t`: the cells located in `[a, b]` at time `t`, except
* a challenge cell of a round whose broadcast time is after `t` (the message is still the
  verifier's), and
* a response cell of a round whose deadline is at or before `t` (the message has been received by
  the verifier).

Source: Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through Space and Time*,
arXiv:2605.30732 (held version, sha256 bf98e5b5…), Definition 3.2, pp.23–24: "1. All of `𝒫`'s
registers within region `R_i`. 2. All message registers currently inflight within region `R_i`." -/
def regionMem (P : Prover σ lam inLen respLen κ inL outL) (t a b : ℝ) (c : P.Cell) : Prop :=
  P.traj c t ∈ Set.Icc a b ∧
  (¬ ∃ i j, c = P.chalL i j ∧ t < σ.sendL i) ∧
  (¬ ∃ i j, c = P.chalR i j ∧ t < σ.sendR i) ∧
  (¬ ∃ i j, c = P.respL i j ∧ σ.deadL i ≤ t) ∧
  (¬ ∃ i j, c = P.respR i j ∧ σ.deadR i ≤ t)

/-- `𝒱_L`'s round-`i` message is **heard** in `[a, b] @ t` (Definition 3.2, item 3, p.24: "the
transcript of all classical messages sent by `𝒱` which causally precede any points in `R_i`"):
some point `p ∈ [a, b] ∩ [−1, 1]` satisfies `t − sendL i ≥ p + 1`, i.e.
`t − sendL i ≥ max(a, −1) + 1`. -/
def HeardL (σ : Sched) (t a : ℝ) (i : Fin (σ.N + 1)) : Prop :=
  max a (-1) + 1 ≤ t - σ.sendL i

/-- `𝒱_R`'s round-`i` message is heard in `[a, b] @ t`: `t − sendR i ≥ 1 − min(b, 1)`. -/
def HeardR (σ : Sched) (t b : ℝ) (i : Fin (σ.N + 1)) : Prop :=
  1 - min b 1 ≤ t - σ.sendR i

open Classical in
/-- The heard transcript of one verifier: the round-`i` challenge if it is heard, `none`
otherwise. -/
noncomputable def heardTranscript {N lam : ℕ} (heard : Fin (N + 1) → Prop)
    (x : Fin (N + 1) → Bits (Fin lam)) : Fin (N + 1) → Option (Bits (Fin lam)) :=
  fun i => if heard i then some (x i) else none

open Classical in
/-- **The reduced state on `𝐀 ⊗ register[[a, b] @ t]`**: for a global pure state `ψ` on
`A ⊗ (cells)` (`A` the anchor), the partial trace over every cell outside the region,
`ρ((x, r), (x′, r′)) = ∑_e ψ(x, r, e) · conj ψ(x′, r′, e)`, where `r, r′` range over the
computational-basis labels of the region cells and `e` over those of the remaining cells. -/
noncomputable def regState (P : Prover σ lam inLen respLen κ inL outL) {A : Type} [Fintype A]
    [DecidableEq A] (R : P.Cell → Prop) (ψ : Bits (A ⊕ P.Cell) → ℂ) :
    Matrix (Bits A × Bits {c // R c}) (Bits A × Bits {c // R c}) ℂ :=
  fun p q =>
    ∑ e : Bits {c // ¬ R c},
      ψ (Sum.elim p.1 (fun c => if h : R c then p.2 ⟨c, h⟩ else e ⟨c, h⟩)) *
        star (ψ (Sum.elim q.1 (fun c => if h : R c then q.2 ⟨c, h⟩ else e ⟨c, h⟩)))

/-- Apply the Kraus family `K_j : ℂ^{β} → ℂ^{γ}` to the second factor of an operator on
`ℂ^{α} ⊗ ℂ^{β}`: `∑_j (1 ⊗ K_j) ρ (1 ⊗ K_j)†`. -/
noncomputable def krausRight {α β γ : Type} [Fintype β] {r : ℕ} (K : Fin r → Matrix γ β ℂ)
    (ρ : Matrix (α × β) (α × β) ℂ) : Matrix (α × γ) (α × γ) ℂ :=
  fun p q => ∑ j, ∑ b, ∑ b', K j p.2 b * ρ (p.1, b) (q.1, b') * star (K j q.2 b')

end QubitTracking


