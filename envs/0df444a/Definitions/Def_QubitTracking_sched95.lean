-- Prove2me | Definitions.Def_QubitTracking_sched95
-- name    : QubitTracking_sched95
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:34:03.383296+00:00
-- url     : https://prove2.me/theorems/d3bebf8a-2b04-4ab6-beab-a28f8e7794c1
-- title:
--   Construction 9.5: schedule, oracles, acceptance probability, moving provers and extraction
-- statement:
--   Let $L$ be a claimed trajectory on $[0,\tau]$, $\Delta$ a localization parameter and $\gamma$ a repetition factor. Construction 9.5 uses $\delta=\Delta/(\gamma+2)$, $N=\lceil\tau/\delta\rceil+\gamma$ and $\tilde L_i=L(\min(i\delta,\tau))$. In round $i=0,\dots,N$, $\mathcal V_L$ broadcasts $x_{L,i}\in\mathbb F_2^\lambda$ at $i\delta-(\tilde L_i+1)$ and expects a response at $i\delta+(\tilde L_i+1)$; $\mathcal V_R$ broadcasts $x_{R,i}$ at $i\delta-(1-\tilde L_i)$ and expects a response at $i\delta+(1-\tilde L_i)$.
--
--   The setup samples the anchor state ($n_e=n_h=n_s=n$), a challenge oracle $\mathcal O_{\mathsf{Chal}}:\mathbb F_2^\lambda\to\mathbb F_2$ and a hidden random oracle $\mathcal O_{\mathsf{random}}:\mathbb F_2\times\mathbb F_2^\lambda\to\mathbb F_2^m$, and publishes $\mathsf{pp}=(\mathcal O_{\mathsf{Chal}},\mathcal O)$ with
--   $$\mathcal O(\theta,x,z)=\begin{cases}\mathcal O_{\mathsf{random}}(\theta,x)&\theta=0,\ z\in T+v\ \text{ or }\ \theta=1,\ z\in S^\perp+u,\\ \bot&\text{otherwise.}\end{cases}$$
--   The verifier accepts iff for every round, with $x_i=x_{L,i}\oplus x_{R,i}$, $\theta_i=\mathcal O_{\mathsf{Chal}}(x_i)$ and $w_i\in\{v,u\}$ according to $\theta_i$, both responses equal $\mathcal O(\theta_i,x_i,w_i)$. The acceptance probability $\eta$ averages over all randomness.
--
--   A prover family **moves along** $L$ if every gate is located on $\tilde L(s)=L(\min(\max(s,0),\tau))$ and the input cells follow $\tilde L$. A **local extractor at time $t$** maps, for each value of $\mathsf{pp}$ and the heard transcripts, the region cells of $[L(t)-\Delta,L(t)+\Delta]@t$ to $n$ qubits by a Kraus family. Extraction with probability $\eta$ and fidelity $\beta$ means that the extracted state $\hat\rho$ on $\mathbf A\mathbf B^*$ (averaged, unnormalized) has $\mathrm{Tr}\,\hat\rho\ge\eta$ and $\langle\mathrm{EPR}^{\otimes n}|\hat\rho|\mathrm{EPR}^{\otimes n}\rangle\ge\beta\,\mathrm{Tr}\,\hat\rho$.
--
--   The parameters satisfy $n,m\ge\lambda$ polynomially bounded, $0<\Delta\le1$, $\gamma\ge1$, and $1/\Delta$ and $\gamma$ polynomially bounded.
--
--   **Formalization Note** Every round $i\le N$ is sent and checked: the text's "for $i=0,1$" in $\mathcal V_R$'s line and in the test is a leftover from Construction 8.3, and the proof uses all checkpoints. Challenges are written into their cells at the start and responses measured at the end, which is equivalent because no gate touches them outside their windows. A missing response is any value that fails the test. The success event is the extractor's success branch averaged over all randomness (Definition 8.1, p.56; Theorem 7.9, p.55; proof of Theorem 9.6, pp.67–68). The polynomial bounds on $1/\Delta$ and $\gamma$ make the verifier polynomial time, as Definition 9.4 requires ("a PPT verifier", p.64).
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Definition 9.4 (pp.64–65), Construction 9.5 (pp.65–66)

import Definitions.Def_QubitTracking_regState
import Definitions.Def_QubitTracking_anchorVec

set_option autoImplicit false

open Matrix

namespace QubitTracking

/-! Construction 9.5 (trajectory verification), pinned down.

Source: Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through Space and Time (Or:
Sailing in a Quantum Boat)*, arXiv:2605.30732 (held version, sha256 bf98e5b5…), Definition 9.4
and Construction 9.5, pp.64–66. -/

/-- **Valid trajectory** (§3.2, p.23; Definition 9.4, p.64): a claimed trajectory `L : [0, τ] →
[−1, 1]` with `τ ≥ 0` that moves at most at the speed of light,
`|L(t₁) − L(t₀)| ≤ |t₁ − t₀|`. Only the values of `L` on `[0, τ]` matter. -/
def ValidTrajectory (L : ℝ → ℝ) (τ : ℝ) : Prop :=
  0 ≤ τ ∧ (∀ s ∈ Set.Icc 0 τ, L s ∈ Set.Icc (-1 : ℝ) 1) ∧ LipschitzOnWith 1 L (Set.Icc 0 τ)

/-- The trajectory extended to all times, `L̃(s) = L(min(max(s, 0), τ))`: the honest prover waits
at `L(0)` before time `0` and remains at `L(τ)` after `τ` (Construction 9.5, p.65,
`L̃(s) := L(min{s, τ})` for `s ≥ 0`, and p.66, "remaining at `L(τ)` for the final `γ`
checkpoints"). -/
noncomputable def extTraj (L : ℝ → ℝ) (τ : ℝ) (s : ℝ) : ℝ := L (min (max s 0) τ)

/-- **The schedule of Construction 9.5** (pp.65–66): `δ = Δ/(γ + 2)`, `N = ⌈τ/δ⌉ + γ`,
`L̃_i = L(min(iδ, τ))`; in round `i = 0, …, N`, `𝒱_L` broadcasts at `iδ − (L̃_i + 1)` and expects
its response at `iδ + (L̃_i + 1)`; `𝒱_R` broadcasts at `iδ − (1 − L̃_i)` and expects its response at
`iδ + (1 − L̃_i)`.

**Formalization Note** The construction's text says "for `i = 0, 1`" in `𝒱_R`'s line; every round
`i ≤ N` is sent, as in `𝒱_L`'s line and in the proof ("`∏_{i=0}^N q_i = η`", p.66). -/
noncomputable def sched95 (L : ℝ → ℝ) (τ Δ : ℝ) (γ : ℕ) : Sched where
  N := ⌈τ / (Δ / ((γ : ℝ) + 2))⌉₊ + γ
  sendL i := (i : ℝ) * (Δ / ((γ : ℝ) + 2)) - (L (min ((i : ℝ) * (Δ / ((γ : ℝ) + 2))) τ) + 1)
  sendR i := (i : ℝ) * (Δ / ((γ : ℝ) + 2)) - (1 - L (min ((i : ℝ) * (Δ / ((γ : ℝ) + 2))) τ))
  deadL i := (i : ℝ) * (Δ / ((γ : ℝ) + 2)) + (L (min ((i : ℝ) * (Δ / ((γ : ℝ) + 2))) τ) + 1)
  deadR i := (i : ℝ) * (Δ / ((γ : ℝ) + 2)) + (1 - L (min ((i : ℝ) * (Δ / ((γ : ℝ) + 2))) τ))

/-- The two public oracles of Construction 9.5: the challenge oracle `𝒪_Chal` and the oracle
`𝒪`. -/
inductive Orc95 : Type
  | chal
  | main
  deriving DecidableEq

/-- Input lengths: `𝒪_Chal : 𝔽₂^λ → {0,1}` takes `λ` qubits; `𝒪(θ, x, z)` takes `1 + λ + d` qubits
(`θ ∈ {0,1}`, `x ∈ 𝔽₂^λ`, `z ∈ 𝔽₂^d`, `d = 3n`). -/
def inLen95 (lam d : ℕ) : Orc95 → ℕ
  | .chal => lam
  | .main => 1 + lam + d

/-- Output lengths: `𝒪_Chal` answers in one qubit; `𝒪` answers in `m + 1` qubits (an element of
`𝔽₂^m ∪ {⊥}`). -/
def outLen95 (m : ℕ) : Orc95 → ℕ
  | .chal => 1
  | .main => m + 1

/-- The sample space of one run of Construction 9.5 for security parameter `λ` (all classical
randomness, sampled uniformly): `U_shift ∈ GL_{3n}(𝔽₂)`, `u′, v′ ∈ 𝔽₂^n` (Definition 4.2), the
challenge oracle `𝒪_Chal : 𝔽₂^λ → 𝔽₂`, the hidden random oracle `𝒪_random : 𝔽₂ × 𝔽₂^λ → 𝔽₂^m`,
and the challenges `x_{L,i}, x_{R,i} ∈ 𝔽₂^λ` for `i = 0, …, N`. -/
abbrev Omega95 (n m lam N : ℕ) : Type :=
  GL (Fin (3 * n)) (ZMod 2) × Bits (Fin n) × Bits (Fin n) × (Bits (Fin lam) → ZMod 2) ×
    (ZMod 2 → Bits (Fin lam) → Bits (Fin m)) × (Fin (N + 1) → Bits (Fin lam)) ×
    (Fin (N + 1) → Bits (Fin lam))

/-- The type of the public parameters `pp = (𝒪_Chal, 𝒪)`. -/
abbrev PP95 (n m lam : ℕ) : Type :=
  (Bits (Fin lam) → ZMod 2) × (ZMod 2 → Bits (Fin lam) → Bits (Fin (3 * n)) → Option (Bits (Fin m)))

open Classical in
/-- **The public oracle `𝒪`** (Construction 9.5, p.65):
`𝒪(θ, x, z) = 𝒪_random(θ, x)` if `θ = 0` and `z ∈ T + v`, or `θ = 1` and `z ∈ S^⊥ + u`; `⊥`
otherwise, for the anchor data `S, T, u, v` of `(U_shift, u′, v′)` with `n_e = n_h = n_s = n`. -/
noncomputable def oracleO {n m lam : ℕ} (U : GL (Fin (3 * n)) (ZMod 2)) (u' v' : Bits (Fin n))
    (ORand : ZMod 2 → Bits (Fin lam) → Bits (Fin m)) (θ : ZMod 2) (x : Bits (Fin lam))
    (z : Bits (Fin (3 * n))) : Option (Bits (Fin m)) :=
  if (θ = 0 ∧ z - anchorV n n n U v' ∈ anchorT n n U) ∨
      (θ = 1 ∧ z - anchorU n n n U u' ∈ perp (anchorS n U))
  then some (ORand θ x) else none

/-- The public parameters `pp = (𝒪_Chal, 𝒪)` of a sample. -/
noncomputable def pp95 {n m lam N : ℕ} (ω : Omega95 n m lam N) : PP95 n m lam :=
  (ω.2.2.2.1, oracleO ω.1 ω.2.1 ω.2.2.1 ω.2.2.2.2.1)

/-- The oracle assignment answering the prover's queries in a sample: `𝒪_Chal` and `𝒪`, the latter
with input `(θ, x, z)` read from the `1 + λ + 3n` input qubits and output encoded by `encOpt`. -/
noncomputable def orc95 {n m lam N : ℕ} (ω : Omega95 n m lam N) :
    OracleAssign Orc95 (inLen95 lam (3 * n)) (outLen95 m) :=
  fun k => match k with
    | .chal => fun q => fun _ => ω.2.2.2.1 q
    | .main => fun q =>
        encOpt ((pp95 ω).2 (q ⟨0, by simp only [inLen95]; omega⟩)
          (fun j => q ⟨1 + j, by simp only [inLen95]; omega⟩)
          (fun j => q ⟨1 + lam + j, by simp only [inLen95]; omega⟩))

/-- A prover for Construction 9.5 at security parameter `λ` with schedule `σ`: input `𝐁` of `3n`
qubits, challenges of `λ` bits, responses of `m + 1` qubits, oracles `𝒪_Chal` and `𝒪`. -/
abbrev Prover95 (n m lam : ℕ) (σ : Sched) : Type 1 :=
  Prover σ lam (3 * n) (m + 1) Orc95 (inLen95 lam (3 * n)) (outLen95 m)

open Classical in
/-- **The initial state of a sample** (Construction 9.5 with Definition 4.2): the anchor state
`|Ψ^{sk}⟩` on `𝐀 ⊗ (input cells)`, the challenge cells in the basis states `|x_{L,i}⟩`,
`|x_{R,i}⟩`, and every other cell in `|0⟩`.

**Formalization Note** The challenges are classical and no gate may touch a challenge cell before
its broadcast time, so writing them into their cells at the start is the same as sending them at
the broadcast time. -/
noncomputable def initState95 {n m lam : ℕ} {σ : Sched} (P : Prover95 n m lam σ)
    (ω : Omega95 n m lam σ.N) : Bits (Fin n ⊕ P.Cell) → ℂ :=
  fun f =>
    anchorVec n n n ω.1 ω.2.1 ω.2.2.1 (fun j => f (Sum.inl j), fun j => f (Sum.inr (P.input j))) *
      (if (∀ i j, f (Sum.inr (P.chalL i j)) = ω.2.2.2.2.2.1 i j) ∧
          (∀ i j, f (Sum.inr (P.chalR i j)) = ω.2.2.2.2.2.2 i j) ∧
          (∀ c, (∀ j, P.input j ≠ c) → (∀ i j, P.chalL i j ≠ c) → (∀ i j, P.chalR i j ≠ c) →
            f (Sum.inr c) = 0)
        then 1 else 0)

/-- **The acceptance test of Construction 9.5** (p.66) on the computational-basis outcome `f` of
the final state: for every round `i ≤ N`, with `x_i = x_{L,i} ⊕ x_{R,i}`, `θ_i = 𝒪_Chal(x_i)` and
`w_i = v` if `θ_i = 0`, `w_i = u` if `θ_i = 1`, both responses equal (the encoding of)
`𝒪(θ_i, x_i, w_i)`.

**Formalization Note** Responses are read by measuring the response cells in the computational
basis at the end of the run; no gate touches a response cell after its deadline, so this is the
same as measuring at the deadline. A "missing" response is any value that fails the test. -/
def Accepts95 {n m lam : ℕ} {σ : Sched} (P : Prover95 n m lam σ) (ω : Omega95 n m lam σ.N)
    (f : Bits (Fin n ⊕ P.Cell)) : Prop :=
  ∀ i : Fin (σ.N + 1),
    let x : Bits (Fin lam) := ω.2.2.2.2.2.1 i + ω.2.2.2.2.2.2 i
    let θ : ZMod 2 := ω.2.2.2.1 x
    let w : Bits (Fin (3 * n)) :=
      if θ = 0 then anchorV n n n ω.1 ω.2.2.1 else anchorU n n n ω.1 ω.2.1
    let e : Bits (Fin (m + 1)) := encOpt ((pp95 ω).2 θ x w)
    (fun j => f (Sum.inr (P.respL i j))) = e ∧ (fun j => f (Sum.inr (P.respR i j))) = e

open Classical in
/-- **The acceptance probability `η`** of a prover in Construction 9.5 (Definition 9.4, p.65):
`Pr[b = ⊤] = 𝔼_ω ∑_{f accepted} |Φ_ω(f)|²`, where `Φ_ω` is the final state of sample `ω`. -/
noncomputable def accProb95 {n m lam : ℕ} {σ : Sched} (P : Prover95 n m lam σ) : ℝ :=
  avg fun ω : Omega95 n m lam σ.N =>
    ∑ f : Bits (Fin n ⊕ P.Cell),
      if Accepts95 P ω f then
        Complex.normSq (P.finalState (Fin n) (fun _ _ => orc95 ω) (initState95 P ω) f)
      else 0

/-- **A prover family moving along `L`** (Definition 9.4, α-Completeness, p.65, and the honest
prover of Construction 9.5, p.66): every gate is located on the extended trajectory,
`pos = L̃(time)`, and the input cells (the register `𝐁`) follow `L̃` at all times. -/
def IsMovingAlong {n m : ℕ → ℕ} {σ : ℕ → Sched} (P : (l : ℕ) → Prover95 (n l) (m l) l (σ l))
    (L : ℝ → ℝ) (τ : ℝ) : Prop :=
  ∀ l, (∀ g ∈ (P l).gates, g.pos = extTraj L τ g.time) ∧
    ∀ j s, (P l).traj ((P l).input j) s = extTraj L τ s

open Classical in
/-- **A local extractor at time `t`** for the region `R` of cells (Definition 9.4, (β, β′, Δ)-
Extraction Soundness, p.65, and Remark 8.2, p.57): for each value of the public parameters `pp`
and of the heard transcripts of `𝒱_L` and `𝒱_R`, a finite Kraus family from the region's cells to
an `n`-qubit output register, with `∑_j K_j† K_j ≤ 1` (the success branch; it may be unbounded).
It never acts on the anchor `𝐀`. -/
structure Extractor95 (n m lam : ℕ) {σ : Sched} (P : Prover95 n m lam σ) (R : P.Cell → Prop) where
  r : ℕ
  K : PP95 n m lam → (Fin (σ.N + 1) → Option (Bits (Fin lam))) →
    (Fin (σ.N + 1) → Option (Bits (Fin lam))) → Fin r → Matrix (Bits (Fin n)) (Bits {c // R c}) ℂ
  kraus : ∀ pp hL hR, IsKrausFamily (K pp hL hR)

open Classical in
/-- **The extracted state `ρ̂` on `𝐀𝐁*`** at time `t` (Definition 9.4, p.65): for each sample `ω`,
the reduced state of `𝐀 ⊗ register[[L(t) − Δ, L(t) + Δ] @ t]` (`regionMem`, `regState`), mapped by
the extractor's success branch, which reads `pp` and the heard transcripts; then averaged
(unnormalized) over all samples. Its trace is the success probability. -/
noncomputable def rhoHat95 {n m lam : ℕ} {σ : Sched} (P : Prover95 n m lam σ) (L : ℝ → ℝ)
    (Δ t : ℝ) (E : Extractor95 n m lam P (regionMem P t (L t - Δ) (L t + Δ))) :
    Matrix (Bits (Fin n) × Bits (Fin n)) (Bits (Fin n) × Bits (Fin n)) ℂ :=
  avgMat fun ω : Omega95 n m lam σ.N =>
    krausRight
      (E.K (pp95 ω) (heardTranscript (HeardL σ t (L t - Δ)) ω.2.2.2.2.2.1)
        (heardTranscript (HeardR σ t (L t + Δ)) ω.2.2.2.2.2.2))
      (regState P (regionMem P t (L t - Δ) (L t + Δ))
        (P.stateAt (Fin n) (fun _ _ => orc95 ω) (initState95 P ω) t))

/-- **Successful extraction at time `t`** with fidelity `β` and probability `η` (Definition 9.4,
p.65, "the probability of extracting `σ` with fidelity at least `β(λ, η)` is at least
`β′(λ, η)`"): some local extractor has success probability `Tr ρ̂ ≥ η` and conditional fidelity
`⟨EPR^{⊗n}|ρ̂|EPR^{⊗n}⟩ ≥ β · Tr ρ̂` with `n` EPR pairs between the anchor `𝐀` and the output.

**Formalization Note** The success event is the extractor's success branch averaged over all
classical randomness; merging every outcome whose conditional fidelity is at least `β` into one
branch loses nothing. This matches Definition 8.1's expected fidelity (p.56), Theorem 7.9's
conditional expectation (p.55) and the conclusion of the proof of Theorem 9.6 (pp.67–68). -/
def ExtractsAt95 {n m lam : ℕ} {σ : Sched} (P : Prover95 n m lam σ) (L : ℝ → ℝ) (Δ t : ℝ)
    (η β : ℝ) : Prop :=
  ∃ E : Extractor95 n m lam P (regionMem P t (L t - Δ) (L t + Δ)),
    η ≤ (rhoHat95 P L Δ t E).trace.re ∧
      β * (rhoHat95 P L Δ t E).trace.re ≤ fidPure (eprVec n) (rhoHat95 P L Δ t E)

/-- **The parameters of Construction 9.5** (p.65; Definition 9.4, p.64): `n(λ), m(λ) ≥ λ`
polynomially bounded; localization parameter `0 < Δ(λ) ≤ 1`; repetition factor `γ(λ) ≥ 1`; and
`1/Δ` and `γ` polynomially bounded, so that the verifier, which sends `N + 1 = ⌈τ(γ+2)/Δ⌉ + γ + 1`
rounds, is polynomial time ("a PPT verifier", p.64). -/
def Params95 (n m : ℕ → ℕ) (Δ : ℕ → ℝ) (γ : ℕ → ℕ) : Prop :=
  PPADSIS.SubexpSIS.PolyBounded n ∧ PPADSIS.SubexpSIS.PolyBounded m ∧
    (∀ l, l ≤ n l ∧ l ≤ m l) ∧ (∀ l, 0 < Δ l ∧ Δ l ≤ 1) ∧ (∀ l, 1 ≤ γ l) ∧
    PPADSIS.SubexpSIS.PolyBounded (fun l => ⌈1 / Δ l⌉₊) ∧ PPADSIS.SubexpSIS.PolyBounded γ

end QubitTracking


