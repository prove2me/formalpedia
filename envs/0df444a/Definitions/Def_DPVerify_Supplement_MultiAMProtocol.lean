-- Prove2me | Definitions.Def_DPVerify_Supplement_MultiAMProtocol
-- name    : DPVerify_Supplement_MultiAMProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:56:42.027513+00:00
-- url     : https://prove2.me/theorems/2b621e58-f121-4752-82d1-acc7b3959186
-- title:
--   Multi-round public-coin (AM) distribution tester, its transcript law, acceptance, communication and $(\varepsilon,\delta)$-DP
-- statement:
--   A **$k$-round public-coin (AM) distribution tester** $T$ with sample complexity $s$ on a measurable space $\mathcal X$ runs as follows. In round $i\in\{1,\dots,k\}$ the verifier sends $n_i$ uniformly random public bits $\rho_i\in\{0,1\}^{n_i}$, and the prover replies with $b_i$ from a finite set $B_i$. After all rounds the verifier, holding its sample $S\sim D^s$, accepts with probability $\mathrm{acc}(S,\rho,b)\in[0,1]$, a measurable function of $S$; the verifier's private coins in this last step are folded into $\mathrm{acc}$.
--
--   A deterministic prover strategy $g$ maps all public coins to all replies; it is **adaptive** if its round-$i$ reply depends only on $\rho_1,\dots,\rho_i$. Against $g$, the transcript $(\rho,b,d)$ (coins, replies, decision bit) has law
--   $$\Pr[(\rho,b,d)]=2^{-\sum_i n_i}\,\mathbf 1[g(\rho)=b]\cdot\begin{cases}\mathrm{acc}(S,\rho,b)&d=1,\\1-\mathrm{acc}(S,\rho,b)&d=0,\end{cases}$$
--   the acceptance probability on $S$ is $2^{-\sum_i n_i}\sum_\rho \mathrm{acc}(S,\rho,g(\rho))$, and under a distribution $D$ it is the expectation of this over $S\sim D^s$. The **communication complexity** is $\sum_i n_i+\sum_i\lceil\log_2|B_i|\rceil$.
--
--   $T$ is **$(\varepsilon,\delta)$-differentially private** (Definition 2.2) if for every prover strategy $g$, every pair of samples $S,S'$ that differ in exactly one entry, and every set $E$ of transcripts,
--   $$\Pr[\mathrm{Interact}(T,g,S)\in E]\le e^{\varepsilon}\Pr[\mathrm{Interact}(T,g,S')\in E]+\delta .$$
--   $\varepsilon$-DP means $\delta=0$.
--
--   This is the protocol model of §2 ("the only messages that the verifier is allowed to send to the prover are random bits, and the number of bits cannot depend on the dataset … we can assume that all interactions occur prior to the samples being drawn") with any number of rounds, as Theorem 6.2's proof needs ("In the $i$th round of interaction").
--
--   **Formalization Note** For $k=1$ this coincides with the published one-round `DPVerify.AMProtocol` (same coin law, acceptance and communication). Adjacency is the published `PrivLearn.Generic.Neighbors` (substitution of one entry of a fixed-size sample), as in the base mission. The privacy clause quantifies over every deterministic strategy, adaptive or not; randomized provers are mixtures.
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), §2, p.4 (PDF p.7), Definition 2.2 and AM protocols; Theorem 6.2 and its proof, p.32 (PDF p.35)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy

set_option autoImplicit false

open MeasureTheory

namespace DPVerify.Supplement

/-- A `k`-round public-coin (AM) distribution tester with sample complexity `s` (Du, Dwork,
Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819
(version of November 3, 2026, sha256 0146fa5f…), §2, p.4 = PDF p.7, and the proof of
Theorem 6.2, p.32 = PDF p.35): in round `i` the verifier sends `nbits i` uniformly random public
bits `ρ i`, and the prover replies with `b i ∈ B i`. After all rounds the verifier, holding its
sample `S ∼ D^s`, accepts with probability `acc S ρ b`.

**Formalization Note**
* "The only messages that the verifier is allowed to send to the prover are random bits, and the
  number of bits cannot depend on the dataset … we can assume that all interactions occur prior
  to the samples being drawn" (p.4): `k`, `nbits` and the reply types `B i` are fixed by the
  protocol, the public coins are uniform on `∏ᵢ {0,1}^{nbits i}` and independent of `S`, and only
  `acc` sees the sample.
* The verifier's private coins in the decision are folded into `acc S ρ b ∈ [0, 1]`, measurable
  in the sample. Replies range over finite types.
* For `k = 1` this is the published one-round `DPVerify.AMProtocol` (same coin law, same
  acceptance, same communication `nbits + ⌈log₂ |B|⌉`).
* The structure carries no privacy, completeness or soundness property. -/
structure MultiAMProtocol (X : Type) [MeasurableSpace X] (s : ℕ) where
  /-- number of rounds -/
  k : ℕ
  /-- number of public random bits sent in round `i` -/
  nbits : Fin k → ℕ
  /-- reply space of round `i` -/
  B : Fin k → Type
  [fintypeB : ∀ i, Fintype (B i)]
  [decEqB : ∀ i, DecidableEq (B i)]
  /-- the acceptance probability on sample `S`, public coins `ρ` and replies `b` -/
  acc : (Fin s → X) → (∀ i, Fin (nbits i) → Bool) → (∀ i, B i) → ℝ
  acc_nonneg : ∀ S ρ b, 0 ≤ acc S ρ b
  acc_le_one : ∀ S ρ b, acc S ρ b ≤ 1
  measurable_acc : ∀ ρ b, Measurable fun S => acc S ρ b

attribute [instance] MultiAMProtocol.fintypeB MultiAMProtocol.decEqB

namespace MultiAMProtocol

variable {X : Type} [MeasurableSpace X] {s : ℕ}

/-- A deterministic prover strategy `g` (all public coins ↦ all replies) is **adaptive** (causal)
if its round-`i` reply depends only on the coins `ρ 0, …, ρ i` sent so far. -/
def IsAdaptive (T : MultiAMProtocol X s) (g : (∀ i, Fin (T.nbits i) → Bool) → ∀ i, T.B i) :
    Prop :=
  ∀ ρ ρ' : (∀ i, Fin (T.nbits i) → Bool), ∀ i : Fin T.k,
    (∀ j : Fin T.k, j ≤ i → ρ j = ρ' j) → g ρ i = g ρ' i

/-- The law of the transcript `(ρ, b, d)` (public coins, replies, decision bit) on the sample `S`
against the prover strategy `g`, as a probability mass function. -/
noncomputable def transcript (T : MultiAMProtocol X s)
    (g : (∀ i, Fin (T.nbits i) → Bool) → ∀ i, T.B i) (S : Fin s → X) :
    (∀ i, Fin (T.nbits i) → Bool) × (∀ i, T.B i) × Bool → ℝ :=
  fun t => ((2 : ℝ) ^ (∑ i, T.nbits i))⁻¹ *
    (if g t.1 = t.2.1 then (if t.2.2 then T.acc S t.1 t.2.1 else 1 - T.acc S t.1 t.2.1) else 0)

/-- The acceptance probability on the sample `S` against the prover strategy `g`. -/
noncomputable def accProb (T : MultiAMProtocol X s)
    (g : (∀ i, Fin (T.nbits i) → Bool) → ∀ i, T.B i) (S : Fin s → X) : ℝ :=
  ((2 : ℝ) ^ (∑ i, T.nbits i))⁻¹ * ∑ ρ, T.acc S ρ (g ρ)

/-- The acceptance probability under the population distribution `D` (`S ∼ D^s`). -/
noncomputable def accept (T : MultiAMProtocol X s)
    (g : (∀ i, Fin (T.nbits i) → Bool) → ∀ i, T.B i) (D : ProbabilityMeasure X) : ℝ :=
  ∫ S, T.accProb g S ∂(Measure.pi fun _ : Fin s => (D : Measure X))

/-- Communication complexity: all public bits plus the bit lengths of all replies,
`∑ᵢ nbits i + ∑ᵢ ⌈log₂ |B i|⌉`. -/
def comm (T : MultiAMProtocol X s) : ℕ :=
  (∑ i, T.nbits i) + ∑ i, Nat.clog 2 (Fintype.card (T.B i))

/-- An `(ε, δ)`-differentially private `k`-round public-coin protocol (Definition 2.2, p.4 =
PDF p.7): for every prover strategy `g`, every pair of adjacent samples `S, S′` and every set `E`
of transcripts `(ρ, b, d)`, `Pr[Interact(T, g, S) ∈ E] ≤ e^ε · Pr[Interact(T, g, S′) ∈ E] + δ`.

**Formalization Note** Adjacency is the published `PrivLearn.Generic.Neighbors` (one entry of the
fixed-size sample substituted), as in `DPVerify.AMProtocol.IsDP`. The adversary ranges over every
deterministic strategy, adaptive or not (randomized provers are mixtures); `ε`-DP is `δ = 0`. -/
def IsDP (T : MultiAMProtocol X s) (ε δ : ℝ) : Prop :=
  ∀ g : (∀ i, Fin (T.nbits i) → Bool) → ∀ i, T.B i, ∀ S S' : Fin s → X,
    PrivLearn.Generic.Neighbors S S' →
    ∀ E : Finset ((∀ i, Fin (T.nbits i) → Bool) × (∀ i, T.B i) × Bool),
      ∑ t ∈ E, T.transcript g S t ≤ Real.exp ε * ∑ t ∈ E, T.transcript g S' t + δ

end MultiAMProtocol

end DPVerify.Supplement


