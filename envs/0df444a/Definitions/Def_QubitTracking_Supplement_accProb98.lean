-- Prove2me | Definitions.Def_QubitTracking_Supplement_accProb98
-- name    : QubitTracking_Supplement_accProb98
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:13:37.108444+00:00
-- url     : https://prove2.me/theorems/bf16c2cd-6221-4d6c-9d99-382eb466c0b0
-- title:
--   Construction 9.8: state localization for a union of orthonormal bases — encoding, protocol, acceptance, extraction and destruction
-- statement:
--   **The state family.** For $k\ge1$ unitaries $U_1,\dots,U_k$ on $n$ qubits, the family $\mathcal S=\bigcup_j\{U_j|x\rangle\}_{x\in\{0,1\}^n}$ is a union of $k$ orthonormal bases; its states $|\psi_{(j,x)}\rangle=U_j|x\rangle$ are indexed by $(j,x)$.
--
--   **Setup.** Sample $U_{\mathrm{shift}}\in GL_{3n}(\mathbb F_2)$ and $u',v'\in\mathbb F_2^n$ uniformly, giving $S$ (span of the first $n$ columns), $T$ (first $2n$ columns), $u$ and $v$ as in Definition 4.2. Sample the index $(j,x)$ uniformly and give the prover $\mathrm{Enc}_{S,T,u,v}|\psi_{(j,x)}\rangle$, where
--   $$\mathrm{Enc}_{S,T,u,v}|y\rangle=\frac1{\sqrt{2^n}}\sum_{s\in S}(-1)^{s\cdot u}\,|s+U_{\mathrm{shift}}(0^n\times y\times0^n)+v\rangle .$$
--   The public parameter is the oracle $\mathcal O(\theta,x,z)=\mathcal O_{\mathrm{random}}(\theta,x)$ if $\theta=0$ and $z\in T+v$, or $\theta=1$ and $z\in S^\perp+u$, and $\bot$ otherwise, for a hidden uniformly random $\mathcal O_{\mathrm{random}}:\{0,1\}\times\mathbb F_2^\lambda\to\mathbb F_2^m$.
--
--   **Localize.** On the schedule of Construction 9.2, for each checkpoint $i=0,\dots,\gamma$ the verifiers sample a basis bit $\theta_i$ and shares $x_{L,i},x_{R,i}\in\mathbb F_2^\lambda$; $\mathcal V_L$ broadcasts $(\theta_i,x_{L,i})$ and $\mathcal V_R$ broadcasts $x_{R,i}$. The verifier accepts iff for every $i$ both responses equal $\mathcal O(\theta_i,x_{L,i}\oplus x_{R,i},w_i)$ with $w_i=v$ if $\theta_i=0$ and $w_i=u$ if $\theta_i=1$. The **acceptance probability** $\eta$ of a prover is the probability of acceptance over all randomness.
--
--   **Extraction.** A local extractor at $(L,t)$ sees the public oracle $\mathcal O$, the verifiers' messages heard in $[L-\Delta,L+\Delta]$ at time $t$, and the reduced state of $\mathsf{register}[[L-\Delta,L+\Delta]@t]$, but neither the index $(j,x)$ nor the secret $(u,v)$. Its success branch is a trace-non-increasing completely positive map to $n$ qubits; with $\hat\rho_\omega$ its success-branch output in sample $\omega$, it extracts $|\psi_i\rangle$ with probability $\eta$ and fidelity $\beta$ when $\mathbb E_\omega\operatorname{Tr}\hat\rho_\omega\ge\eta$ and $\mathbb E_\omega\langle\psi_{i(\omega)}|\hat\rho_\omega|\psi_{i(\omega)}\rangle\ge\beta\,\mathbb E_\omega\operatorname{Tr}\hat\rho_\omega$.
--
--   **Destruction.** The expected destruction is $\mathbb E_\omega[\mathrm{TD}(\rho_{\mathbf B},\rho_{\mathbf B'})]$ with $\rho_{\mathbf B}=\mathrm{Enc}|\psi_i\rangle\langle\psi_i|\mathrm{Enc}^\dagger$ and $\rho_{\mathbf B'}$ the reduced state of the prover's input cells after $\mathsf{Localize}$.
--
--   **Formalization Note** The register model, the region and the heard transcripts are the published ones of the live mission. $\mathcal V_R$'s $\lambda$-bit message is padded with a leading $0$ bit so that both verifiers send $\lambda+1$ bits. There is no anchor register. Oracle answers in $\mathbb F_2^m\cup\{\bot\}$ are encoded in $m+1$ qubits.
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Definition 9.7, pp.68–69; Construction 9.8, pp.69–70; Theorem 9.9 and the rewriting 𝒮 = ⋃_{U∈𝒰}{U|x⟩}, p.70; footnotes 16–17, pp.69, 71

import Definitions.Def_QubitTracking_Supplement_ndDist95

set_option autoImplicit false

open Matrix

namespace QubitTracking.Supplement

/-! Construction 9.8 (non-destructive state localization), pinned down in the model of the base
mission (`Prover`, `regionMem`, `regState`, `heardTranscript`).

Source: Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through Space and Time (Or:
Sailing in a Quantum Boat)*, arXiv:2605.30732 (held version, sha256 bf98e5b5…), Definition 9.7,
pp.68–69, Construction 9.8, pp.69–70, Theorem 9.9 and the remark after it, pp.70–71. -/

/-- **A union of `k` orthonormal bases of `n` qubits** (Theorem 9.9, p.70: "`𝒮 = ⋃_j ℬ_j`, where
each `ℬ_j` consists of `2^n` orthonormal states"; p.70–71: "`𝒮 = ⋃_{U∈𝒰} {U|x⟩}_{x∈{0,1}^n}`"):
the basis `ℬ_j` is given by the unitary `U_j`, whose columns are its states. -/
abbrev StateFam (n k : ℕ) : Type := Fin k → Matrix.unitaryGroup (Bits (Fin n)) ℂ

/-- The state `|ψ_{(j,x)}⟩ = U_j|x⟩` of the family (footnote 17, p.71: "the family of states is
indexed by `U, x`"). -/
def psiFam {n k : ℕ} (F : StateFam n k) (i : Fin k × Bits (Fin n)) : Bits (Fin n) → ℂ :=
  fun y => (F i.1 : Matrix (Bits (Fin n)) (Bits (Fin n)) ℂ) y i.2

open Classical in
/-- **The isometry `Enc_{S,T,u,v}`** of Construction 9.8 (p.69), from `n` to `3n` qubits:
`Enc|x⟩ = 2^{-n/2} ∑_{s∈S} (−1)^{s·u} |s + U_shift(0^n × x × 0^n) + v⟩`, for the anchor data
`S, T, u, v` of `(U_shift, u′, v′)` (Definition 4.2). The entry at `(b, x)` is
`2^{-n/2}(−1)^{s·u}` if `s := b − U_shift(0^n × x × 0^n) − v ∈ S`, and `0` otherwise. -/
noncomputable def encMat (n : ℕ) (U : GL (Fin (3 * n)) (ZMod 2)) (u' v' : Bits (Fin n)) :
    Matrix (Bits (Fin (3 * n))) (Bits (Fin n)) ℂ :=
  fun b x =>
    let s : Bits (Fin (3 * n)) :=
      b - (U : Matrix (Fin (3 * n)) (Fin (3 * n)) (ZMod 2)) *ᵥ blk (nh := n) (ns := n) 0 x 0
        - anchorV n n n U v'
    if s ∈ anchorS n U then ((Real.sqrt 2 : ℂ) ^ n)⁻¹ * sgn (s ⬝ᵥ anchorU n n n U u') else 0

/-- The sample space of one run of Construction 9.8 at security parameter `λ` with checkpoints
`i = 0, …, N` and a family of `k` bases (all randomness uniform): `U_shift ∈ GL_{3n}(𝔽₂)`,
`u′, v′ ∈ 𝔽₂^n` (giving `S, T, u, v` as in `GenAnchorState`), the index `(j, x)` of the state,
the hidden random oracle `𝒪_random : 𝔽₂ × 𝔽₂^λ → 𝔽₂^m`, the bases `θ_i ∈ 𝔽₂`, and the shares
`x_{L,i}, x_{R,i} ∈ 𝔽₂^λ`. -/
abbrev Omega98 (n m lam N k : ℕ) : Type :=
  GL (Fin (3 * n)) (ZMod 2) × Bits (Fin n) × Bits (Fin n) × (Fin k × Bits (Fin n)) ×
    (ZMod 2 → Bits (Fin lam) → Bits (Fin m)) × (Fin (N + 1) → ZMod 2) ×
    (Fin (N + 1) → Bits (Fin lam)) × (Fin (N + 1) → Bits (Fin lam))

/-- The type of the public parameter `pp = 𝒪` of Construction 9.8. -/
abbrev PP98 (n m lam : ℕ) : Type :=
  ZMod 2 → Bits (Fin lam) → Bits (Fin (3 * n)) → Option (Bits (Fin m))

/-- The public parameter `pp = 𝒪` of a sample (`oracleO`, as in Construction 9.5). -/
noncomputable def pp98 {n m lam N k : ℕ} (ω : Omega98 n m lam N k) : PP98 n m lam :=
  oracleO ω.1 ω.2.1 ω.2.2.1 ω.2.2.2.2.1

/-- `𝒱_L`'s round-`i` message `(θ_i, x_{L,i})`, as `λ + 1` bits (bit `0` is `θ_i`). -/
def msgL98 {n m lam N k : ℕ} (ω : Omega98 n m lam N k) (i : Fin (N + 1)) : Bits (Fin (lam + 1)) :=
  Fin.cons (α := fun _ => ZMod 2) (ω.2.2.2.2.2.1 i) (ω.2.2.2.2.2.2.1 i)

/-- `𝒱_R`'s round-`i` message `x_{R,i}`, padded to `λ + 1` bits by a leading `0` bit. -/
def msgR98 {n m lam N k : ℕ} (ω : Omega98 n m lam N k) (i : Fin (N + 1)) : Bits (Fin (lam + 1)) :=
  Fin.cons (α := fun _ => ZMod 2) 0 (ω.2.2.2.2.2.2.2 i)

/-- The oracle assignment answering the prover's queries: the single public oracle `𝒪`, with input
`(θ, x, z)` read from `1 + λ + 3n` qubits and output encoded by `encOpt` in `m + 1` qubits. -/
noncomputable def orc98 {n m lam N k : ℕ} (ω : Omega98 n m lam N k) :
    OracleAssign Unit (fun _ => 1 + lam + 3 * n) (fun _ => m + 1) :=
  fun _ (q : Bits (Fin (1 + lam + 3 * n))) =>
    encOpt (pp98 ω (q ⟨0, by omega⟩) (fun j => q ⟨1 + j, by omega⟩)
      (fun j => q ⟨1 + lam + j, by omega⟩))

/-- A prover for Construction 9.8 at security parameter `λ` with schedule `σ`: input `𝐁` of `3n`
qubits, challenge messages of `λ + 1` bits, responses of `m + 1` qubits, one oracle `𝒪`. -/
abbrev Prover98 (n m lam : ℕ) (σ : Sched) : Type 1 :=
  Prover σ (lam + 1) (3 * n) (m + 1) Unit (fun _ => 1 + lam + 3 * n) (fun _ => m + 1)

open Classical in
/-- **The initial state of a sample** (Construction 9.8): `Enc_{S,T,u,v}|ψ_i⟩` on the input cells,
the challenge cells in the basis states of the messages `(θ_i, x_{L,i})` and `x_{R,i}`, every other
cell in `|0⟩`. There is no anchor register (`Fin 0`). -/
noncomputable def initState98 {n m lam k : ℕ} {σ : Sched} (P : Prover98 n m lam σ)
    (F : StateFam n k) (ω : Omega98 n m lam σ.N k) : Bits (Fin 0 ⊕ P.Cell) → ℂ :=
  fun f =>
    (encMat n ω.1 ω.2.1 ω.2.2.1 *ᵥ psiFam F ω.2.2.2.1) (fun j => f (Sum.inr (P.input j))) *
      (if (∀ i j, f (Sum.inr (P.chalL i j)) = msgL98 ω i j) ∧
          (∀ i j, f (Sum.inr (P.chalR i j)) = msgR98 ω i j) ∧
          (∀ c, (∀ j, P.input j ≠ c) → (∀ i j, P.chalL i j ≠ c) → (∀ i j, P.chalR i j ≠ c) →
            f (Sum.inr c) = 0)
        then 1 else 0)

/-- **The acceptance test of Construction 9.8** (p.70) on the computational-basis outcome `f` of
the final state: for every `i = 0, …, γ`, with `x_i = x_{L,i} ⊕ x_{R,i}` and `w_i = v` if
`θ_i = 0`, `w_i = u` if `θ_i = 1`, both responses equal (the encoding of) `𝒪(θ_i, x_i, w_i)`. -/
def Accepts98 {n m lam k : ℕ} {σ : Sched} (P : Prover98 n m lam σ) (ω : Omega98 n m lam σ.N k)
    (f : Bits (Fin 0 ⊕ P.Cell)) : Prop :=
  ∀ i : Fin (σ.N + 1),
    let x : Bits (Fin lam) := ω.2.2.2.2.2.2.1 i + ω.2.2.2.2.2.2.2 i
    let θ : ZMod 2 := ω.2.2.2.2.2.1 i
    let w : Bits (Fin (3 * n)) :=
      if θ = 0 then anchorV n n n ω.1 ω.2.2.1 else anchorU n n n ω.1 ω.2.1
    let e : Bits (Fin (m + 1)) := encOpt (pp98 ω θ x w)
    (fun j => f (Sum.inr (P.respL i j))) = e ∧ (fun j => f (Sum.inr (P.respR i j))) = e

open Classical in
/-- **The acceptance probability `η`** of a prover in Construction 9.8 (Definition 9.7, p.68):
`Pr[b = ⊤] = 𝔼_ω ∑_{f accepted} |Φ_ω(f)|²`, `Φ_ω` the final state of sample `ω`. -/
noncomputable def accProb98 {n m lam k : ℕ} {σ : Sched} (P : Prover98 n m lam σ)
    (F : StateFam n k) : ℝ :=
  avg fun ω : Omega98 n m lam σ.N k =>
    ∑ f : Bits (Fin 0 ⊕ P.Cell),
      if Accepts98 P ω f then
        Complex.normSq (P.finalState (Fin 0) (fun _ _ => orc98 ω) (initState98 P F ω) f)
      else 0

open Classical in
/-- **A local extractor at time `t`** for the region `R` of cells (Definition 9.7, p.69, with
Remark 8.2 and footnote 16): for each value of `pp = 𝒪` and of the heard transcripts of `𝒱_L` and
`𝒱_R`, a finite Kraus family from the region's cells to `n` qubits with `∑_j K_j†K_j ≤ 1` (the
success branch; it may be unbounded). It does not receive the index `i` or `sp`. -/
structure Extractor98 (n m lam : ℕ) {σ : Sched} (P : Prover98 n m lam σ) (R : P.Cell → Prop) where
  r : ℕ
  K : PP98 n m lam → (Fin (σ.N + 1) → Option (Bits (Fin (lam + 1)))) →
    (Fin (σ.N + 1) → Option (Bits (Fin (lam + 1)))) → Fin r →
      Matrix (Bits (Fin n)) (Bits {c // R c}) ℂ
  kraus : ∀ pp hL hR, IsKrausFamily (K pp hL hR)

open Classical in
/-- The extractor's (unnormalized) success-branch output on `𝐁*` in sample `ω`, from
`register[[L − Δ, L + Δ] @ t]` (`regionMem`, `regState`) and the heard transcripts. -/
noncomputable def outState98 {n m lam k : ℕ} {σ : Sched} (P : Prover98 n m lam σ)
    (F : StateFam n k) (L Δ t : ℝ) (E : Extractor98 n m lam P (regionMem P t (L - Δ) (L + Δ)))
    (ω : Omega98 n m lam σ.N k) :
    Matrix (Bits (Fin 0) × Bits (Fin n)) (Bits (Fin 0) × Bits (Fin n)) ℂ :=
  krausRight
    (E.K (pp98 ω) (heardTranscript (HeardL σ t (L - Δ)) (msgL98 ω))
      (heardTranscript (HeardR σ t (L + Δ)) (msgR98 ω)))
    (regState P (regionMem P t (L - Δ) (L + Δ))
      (P.stateAt (Fin 0) (fun _ _ => orc98 ω) (initState98 P F ω) t))

/-- **Successful extraction of `|ψ_i⟩` at `(L, t)`** with fidelity `β` and probability `η`
(Definition 9.7, p.69): some local extractor has success probability `𝔼_ω Tr ρ̂_ω ≥ η` and
`𝔼_ω ⟨ψ_{i(ω)}|ρ̂_ω|ψ_{i(ω)}⟩ ≥ β · 𝔼_ω Tr ρ̂_ω`, where `ρ̂_ω` is its success-branch output in
sample `ω` and `i(ω)` the sampled index (the reading of the base mission's `ExtractsAt95`). -/
def ExtractsAt98 {n m lam k : ℕ} {σ : Sched} (P : Prover98 n m lam σ) (F : StateFam n k)
    (L Δ t η β : ℝ) : Prop :=
  ∃ E : Extractor98 n m lam P (regionMem P t (L - Δ) (L + Δ)),
    η ≤ avg (fun ω : Omega98 n m lam σ.N k => (outState98 P F L Δ t E ω).trace.re) ∧
      β * avg (fun ω : Omega98 n m lam σ.N k => (outState98 P F L Δ t E ω).trace.re) ≤
        avg (fun ω : Omega98 n m lam σ.N k =>
          fidPure (fun p : Bits (Fin 0) × Bits (Fin n) => psiFam F ω.2.2.2.1 p.2)
            (outState98 P F L Δ t E ω))

/-- **The expected destruction `𝔼[TD(ρ_𝐁, ρ_{𝐁′})]`** in Construction 9.8 (Definition 9.7,
p.69): `ρ_𝐁 = Enc|ψ_i⟩⟨ψ_i|Enc†` after `Setup`, `ρ_{𝐁′}` the reduced state on the input cells of
the final state after `Localize`; per-sample trace distances averaged over all samples. -/
noncomputable def ndDist98 {n m lam k : ℕ} {σ : Sched} (P : Prover98 n m lam σ)
    (F : StateFam n k) : ℝ :=
  avg fun ω : Omega98 n m lam σ.N k =>
    TD (proj (fun p : Bits (Fin 0) × Bits (Fin (3 * n)) =>
          (encMat n ω.1 ω.2.1 ω.2.2.1 *ᵥ psiFam F ω.2.2.2.1) p.2))
      (inputState P (P.finalState (Fin 0) (fun _ _ => orc98 ω) (initState98 P F ω)))

end QubitTracking.Supplement


