-- Prove2me | Definitions.Def_NoisyOWMPC_ChannelTest
-- name    : NoisyOWMPC_ChannelTest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:49:44.242208+00:00
-- url     : https://prove2.me/theorems/f0eb2984-b90b-4c2c-b03a-2ba05a1e4a13
-- title:
--   Recoverable channel tests, access tests and release tests
-- statement:
--   A **channel test** for receiver $i$ with channel-input length $n$, seed length $\kappa$ and observers $\mathcal R\subseteq[k]$ adds to the protocol half the proof-side algorithms $\mathrm{SampleSt}(1^\lambda)\to\mathrm{st}$ (with designated observation $\mathrm{obs}(\mathrm{st})\in\prod_{j\in\mathcal R}\mathcal Y_j^n$ and honest bit $H(\mathrm{st})$), $\mathrm{Recons}(\mathrm{st},\sigma)\to\omega$ and $\mathrm{Rec}(\mathrm{st},w)\to\mathcal L$. In the **seeded experiment** $\mathrm{st}\leftarrow\mathrm{SampleSt}$ and $\sigma\leftarrow\{0,1\}^\kappa$ independently. The test is **recoverable with observers $\mathcal R$ and error $\delta$** if
--   1. *sampling correctness* (5.1): $(\mathrm{Recons}(\mathrm{st},\sigma),\mathrm{obs}(\mathrm{st}))\overset d=(\omega,D_{\mathcal R})$;
--   2. *recoverability* (5.2): $\Pr_{\mathrm{st},\sigma}[H(\mathrm{st})=0\text{ and }\exists w:\mathrm{Test}_{\mathrm{Recons}(\mathrm{st},\sigma)}(w)=1\text{ and }\sigma\notin\mathrm{Rec}(\mathrm{st},w)]\le\delta$.
--
--   A **recoverable access test** with errors $(\alpha,\delta_{\mathrm{acc}})$ (Definition 5.2) needs $k>1$, observers $[k]\setminus\{i\}$, honest bit identically zero and completeness $\alpha$. A **recoverable release test** with errors $(\eta,\delta_{\mathrm{rel}})$ (Definition 5.3) has observers $[k]$, unbiasedness $\eta$ and the release invariant (5.4) $Q_{\mathrm{Recons}(\mathrm{st},\sigma')}(\mathrm{obs}(\mathrm{st})_i)=H(\mathrm{st})$ for every seed $\sigma'$.
--
--   **Formalization Note** Both kinds include efficiency: polynomial lengths, samplers implementable within $2^{-\lambda}$, injective encodings, and deterministic polynomial-time $\mathrm{Word}$, $\mathrm{Test}$, $\mathrm{obs}$, $H$, $\mathrm{Recons}$, $\mathrm{Rec}$ (§3, p.15; §5.1, p.21).
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Definitions 5.1–5.3, pp.21–23

import Mathlib
import Definitions.Def_NoisyOWMPC_Halves
import Definitions.Def_NoisyOWMPC_CoinAlg
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_NoisyOWMPC_symEnc

namespace NoisyOWMPC

open LaconicBarrier

/-- A **channel test** for receiver `i` with channel-input length `n`, seed length `κ` and observer
set `R ⊆ [k]` (Ishai, Lu, Zafar, STOC 2027 submission (manuscript sha256 3a9569fa…), Definition 5.1,
p.22): the protocol half (`Gen`, `Word`, `Test`) and the proof-side algorithms
* `SampleSt(1^λ) → st` (exact reference law `sampW λ` on `St λ`, encoding `encSt`), with the
  designated observation `obs(st) ∈ ∏_{j ∈ R} Y_jⁿ` ("one observation of the word for each receiver
  in `R`") and honest bit `H(st)`;
* `Recons(st, σ) → ω` for seeds `σ ∈ {0,1}^κ`;
* `Rec(st, w) → L`, a list of candidate seeds. -/
structure ChannelTest (k : ℕ) (X : Type) (Y : Fin k → Type) (i : Fin k) (n : ℕ → ℕ)
    (R : Finset (Fin k)) extends TestHalf X (Y i) n where
  /-- the seed length `κ` -/
  κ : ℕ → ℕ
  /-- the sampler states -/
  St : ℕ → Type
  [finSt : ∀ lam, Fintype (St lam)]
  /-- the law of `SampleSt(1^λ)` -/
  sampW : (lam : ℕ) → St lam → ℝ
  /-- the encoding of a sampler state -/
  encSt : (lam : ℕ) → St lam → List Bool
  /-- the designated observation `obs(st)` -/
  obs : (lam : ℕ) → St lam → (j : {j : Fin k // j ∈ R}) → Fin (n lam) → Y j
  /-- the honest bit `H(st)` -/
  H : (lam : ℕ) → St lam → Bool
  /-- `Recons(st, σ)` -/
  recons : (lam : ℕ) → St lam → (Fin (κ lam) → Bool) → Sec lam
  /-- `Rec(st, w)` -/
  recov : (lam : ℕ) → St lam → (Fin (n lam) → Y i) → List (Fin (κ lam) → Bool)

attribute [instance] ChannelTest.finSt

variable {k : ℕ} {X : Type} [Fintype X] {Y : Fin k → Type} [∀ i, Fintype (Y i)]
  {i : Fin k} {n : ℕ → ℕ} {R : Finset (Fin k)}

/-- The **seeded experiment** (Definition 5.1, p.21: "sample `st ← SampleSt(1^λ)` and an independent
uniform seed `σ ← {0,1}^κ`"): the weight of `(st, σ)`. -/
noncomputable def ChannelTest.seedW (T : ChannelTest k X Y i n R) (lam : ℕ)
    (z : T.St lam × (Fin (T.κ lam) → Bool)) : ℝ :=
  T.sampW lam z.1 * (1 / 2 : ℝ) ^ (T.κ lam)

/-- **Sampling correctness with observers `R`** (Definition 5.1, (5.1), p.22):
`(Recons(st, σ), obs(st)) =ᵈ (ω, D_R)`, the right side from the honest experiment. -/
def ChannelTest.SamplingCorrect (C : ∀ j, DMC X (Y j)) (T : ChannelTest k X Y i n R) : Prop :=
  ∀ lam (ω : T.Sec lam) (d : ∀ j : {j // j ∈ R}, Fin (n lam) → Y j),
    wprob (T.seedW lam) (fun z => T.recons lam z.1 z.2 = ω ∧ T.obs lam z.1 = d) =
      wprob (honestW C T.toTestHalf lam) (fun z => z.1 = ω ∧ (fun (j : {j // j ∈ R}) s => z.2 s j) = d)

/-- **Recoverability with error `δ`** (Definition 5.1, (5.2), p.22):
`Pr_{st,σ}[H(st) = 0 and ∃ w : Test_{Recons(st,σ)}(w) = 1 and σ ∉ Rec(st, w)] ≤ δ`. -/
def ChannelTest.Recoverable (T : ChannelTest k X Y i n R) (δ : ℕ → ℝ) : Prop :=
  ∀ lam, wprob (T.seedW lam) (fun z => T.H lam z.1 = false ∧
    ∃ w, T.test lam (T.recons lam z.1 z.2) w = true ∧ z.2 ∉ T.recov lam z.1 w) ≤ δ lam

/-- The algorithms of the test are **efficient** (Definition 5.1, p.22: "The two samplers `Gen` and
`SampleSt` are randomized; the others are deterministic"; §3, p.15: all algorithms polynomial time;
§5.1, p.21: "a deterministic recovery algorithm `Rec` returning a polynomial-size list"): `n` and
`κ` are polynomial, the two samplers' laws are probability distributions implementable within
`2^{−λ}`, the encodings are injective, and `Word`, `Test`, `obs`, `H`, `Recons` and `Rec` are
deterministic polynomial time on the encodings. -/
def ChannelTest.Efficient (T : ChannelTest k X Y i n R) : Prop :=
  PolyBounded n ∧ PolyBounded T.κ ∧ T.IsDist ∧
  (∀ lam, (∀ st, 0 ≤ T.sampW lam st) ∧ ∑ st, T.sampW lam st = 1) ∧
  (∀ lam, Function.Injective (T.enc lam)) ∧ (∀ lam, Function.Injective (T.encSt lam)) ∧
  Samplable (I := fun _ => Unit) (fun lam _ => T.genW lam) (fun lam _ => T.enc lam) (fun _ _ => []) ∧
  Samplable (I := fun _ => Unit) (fun lam _ => T.sampW lam) (fun lam _ => T.encSt lam)
    (fun _ _ => []) ∧
  PolyTimeOn (ι := (lam : ℕ) × T.Sec lam) (fun z => [unary z.1, T.enc z.1 z.2])
    (fun z => wordEnc X (T.word z.1 z.2)) ∧
  PolyTimeOn (ι := (lam : ℕ) × T.Sec lam × (Fin (n lam) → Y i))
    (fun z => [unary z.1, T.enc z.1 z.2.1, wordEnc (Y i) z.2.2]) (fun z => [T.test z.1 z.2.1 z.2.2]) ∧
  PolyTimeOn (ι := (lam : ℕ) × T.St lam) (fun z => [unary z.1, T.encSt z.1 z.2])
    (fun z => QAdvFew.PoQOracle.tup ([[T.H z.1 z.2]] ++
      (List.finRange k).filterMap fun j => if h : j ∈ R then
        some (wordEnc (Y j) (T.obs z.1 z.2 ⟨j, h⟩)) else none)) ∧
  PolyTimeOn (ι := (lam : ℕ) × T.St lam × (Fin (T.κ lam) → Bool))
    (fun z => [unary z.1, T.encSt z.1 z.2.1, bits z.2.2]) (fun z => T.enc z.1 (T.recons z.1 z.2.1 z.2.2)) ∧
  PolyTimeOn (ι := (lam : ℕ) × T.St lam × (Fin (n lam) → Y i))
    (fun z => [unary z.1, T.encSt z.1 z.2.1, wordEnc (Y i) z.2.2])
    (fun z => QAdvFew.PoQOracle.tup ((T.recov z.1 z.2.1 z.2.2).map bits))

/-- A **recoverable access test for receiver `i` with errors `(α, δ_acc)`** (Definition 5.2, p.22):
`k > 1`; a channel test recoverable with observers `[k] ∖ {i}` and error `δ_acc` (sampling
correctness and recoverability), whose honest bit is identically zero, and complete with error `α`. -/
def ChannelTest.IsRecAccess (C : ∀ j, DMC X (Y j)) (T : ChannelTest k X Y i n (Finset.univ.erase i))
    (α δacc : ℕ → ℝ) : Prop :=
  1 < k ∧ T.Efficient ∧ T.SamplingCorrect C ∧ T.Recoverable δacc ∧
    (∀ lam st, T.H lam st = false) ∧ T.toTestHalf.Complete C α

/-- A **recoverable release test for receiver `i` with errors `(η, δ_rel)`** (Definition 5.3,
pp.22–23): a channel test recoverable with observers `[k]` and error `δ_rel`, unbiased with error
`η`, with the release invariant (5.4): `Q_{Recons(st,σ′)}(obs(st)_i) = H(st)` for every seed `σ′`
(for every sampler state in the support). -/
def ChannelTest.IsRecRelease (C : ∀ j, DMC X (Y j)) (T : ChannelTest k X Y i n Finset.univ)
    (η δrel : ℕ → ℝ) : Prop :=
  T.Efficient ∧ T.SamplingCorrect C ∧ T.Recoverable δrel ∧ T.toTestHalf.Unbiased C η ∧
    ∀ lam st σ', T.sampW lam st ≠ 0 → T.test lam (T.recons lam st σ') (T.obs lam st ⟨i, Finset.mem_univ i⟩) = T.H lam st

end NoisyOWMPC


