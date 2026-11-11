-- Prove2me | Definitions.Def_QNatProofs_finPoissonSampler
-- name    : QNatProofs_finPoissonSampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:01:13.136204+00:00
-- url     : https://prove2.me/theorems/3ccfe309-b1bc-4015-b6f0-1548493e5397
-- title:
--   The finite Poisson sampler $\mathrm{Samp}_{\mathrm{fin}}$
-- statement:
--   Fix $K_{\max},q\in\mathbb N$ and integer thresholds $T_i$. Let $P_i=\Pr[K_{\mathrm{id}}<i]=e^{-\mu}\sum_{k<i}\mu^k/k!$ for $K_{\mathrm{id}}\sim\mathrm{Pois}(\mu)$. The thresholds are **admissible** (36) if $T_i\in\{0,\dots,2^q\}$, $|T_i/2^q-P_i|\le2^{-q}$ for every $i\in[K_{\max}]$, and they are nondecreasing in $i$.
--
--   The tape $\Omega\in\{0,1\}^R$, $R=(2K_{\max}+2)q$, is read as $q$-bit blocks
--   $$
--   \Omega=(Z,U^{\mathrm{fin}}_{1,0},U^{\mathrm{fin}}_{1,1},\dots,U^{\mathrm{fin}}_{K_{\max},0},U^{\mathrm{fin}}_{K_{\max},1},\Theta^{\mathrm{fin}}),\tag{35}
--   $$
--   with $Z\in\{0,\dots,2^q-1\}$ an integer and the others $q$-bit binary fractions. $K_{\mathrm{fin}}$ is the number of $i\in[K_{\max}]$ with $Z\ge T_i$, and
--   $$
--   R_{\mathrm{fin}}=\begin{cases}\min_{i\in[K_{\mathrm{fin}}]}\max\{U^{\mathrm{fin}}_{i,0},U^{\mathrm{fin}}_{i,1}\},&K_{\mathrm{fin}}>0,\\0,&K_{\mathrm{fin}}=0.\end{cases}\tag{37}
--   $$
--   $\mathrm{Samp}_{\mathrm{fin}}(\Omega)$ is the pair of $q$-bit encodings of $(R_{\mathrm{fin}},\Theta^{\mathrm{fin}})$, representing $V_{\mathrm{fin}}=R_{\mathrm{fin}}e^{2\pi i\Theta^{\mathrm{fin}}}$.
--
--   This is the comparison-only complex Gaussian sampler that the paper implements in $A_8CQ$.
--
--   **Formalization Note** The thresholds are a parameter, and one fixed admissible choice $T_i=\lfloor 2^qP_i\rfloor$ is provided. With nondecreasing thresholds the pairs with $Z\ge T_i$ are the first $K_{\mathrm{fin}}$ pairs, as in the paper. Blocks are most significant bit first.
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), §4.1.2, (35)–(37), p.20; Claim 4.2, p.23

import Mathlib
import Definitions.Def_QNatProofs_complexGaussian

set_option autoImplicit false

namespace QNatProofs

/-- `P_i = Pr[K_id < i] = e^{-µ} Σ_{k<i} µ^k/k!` for `K_id ∼ Pois(µ)` (Li, Parham, arXiv:2610.06826
(held copy sha256 b604fa11…), §4.1.2, p.20; Claim 4.2, p.23). -/
noncomputable def poissonCDF (mu : ℝ) (i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range i, Real.exp (-mu) * mu ^ k / (Nat.factorial k)

/-- **Admissible thresholds** (§4.1.2, (36), p.20): integers `T_i ∈ {0, …, 2^q}` with
`|T_i/2^q − P_i| ≤ 2^{-q}` for every `i ∈ [K_max] = {1, …, K_max}`, chosen nondecreasing in `i`
("The probabilities `P_i` are nondecreasing in `i`, so the thresholds `T_i` can be chosen
nondecreasing as well", p.20). -/
def AdmissibleThresholds (mu : ℝ) (Kmax q : ℕ) (thr : ℕ → ℕ) : Prop :=
  (∀ i, 1 ≤ i → i ≤ Kmax →
    thr i ≤ 2 ^ q ∧ |(thr i : ℝ) / 2 ^ q - poissonCDF mu i| ≤ (2 : ℝ)⁻¹ ^ q) ∧
  (∀ i j, 1 ≤ i → i ≤ j → j ≤ Kmax → thr i ≤ thr j)

/-- One fixed admissible choice of thresholds: `T_i = ⌊2^q P_i⌋`. -/
noncomputable def stdThresholds (mu : ℝ) (q : ℕ) (i : ℕ) : ℕ :=
  ⌊(2 : ℝ) ^ q * poissonCDF mu i⌋₊

/-- The integer `b₀ b₁ ⋯ b_{q−1}` written by a `q`-bit string, most significant bit first. -/
def natVal {q : ℕ} (b : Fin q → Bool) : ℕ :=
  ∑ t : Fin q, if b t then 2 ^ (q - 1 - t.val) else 0

/-- The `q`-bit string of `v mod 2^q`, most significant bit first. -/
def natBits (q v : ℕ) : Fin q → Bool :=
  fun t => Nat.testBit v (q - 1 - t.val)

/-- Block `b` (`q` consecutive bits, starting at bit `b q`) of a tape. -/
def tapeBlock {L : ℕ} (q : ℕ) (Ω : Fin L → Bool) (b : ℕ) : Fin q → Bool :=
  fun t => if h : b * q + t.val < L then Ω ⟨b * q + t.val, h⟩ else false

/-- The tape fields of (35), p.20: `Ω = (Z, U^fin_{1,0}, U^fin_{1,1}, …, U^fin_{K_max,0},
U^fin_{K_max,1}, Θ^fin)`, each a `q`-bit block. `tapeZ` is the integer `Z ∈ {0, …, 2^q − 1}`. -/
def tapeZ {L : ℕ} (q : ℕ) (Ω : Fin L → Bool) : ℕ := natVal (tapeBlock q Ω 0)

/-- `2^q U^fin_{i,a}`: the integer of the coordinate block `(i, a)`, `i ∈ [K_max]`, `a ∈ {0,1}`. -/
def tapeU {L : ℕ} (q : ℕ) (Ω : Fin L → Bool) (i a : ℕ) : ℕ :=
  natVal (tapeBlock q Ω (1 + 2 * (i - 1) + a))

/-- The phase block `Θ^fin`. -/
def tapeTheta {L : ℕ} (Kmax q : ℕ) (Ω : Fin L → Bool) : Fin q → Bool :=
  tapeBlock q Ω (2 * Kmax + 1)

/-- `K_fin`, the number of `i ∈ [K_max]` with `Z ≥ T_i` (p.20). -/
def kFin {L : ℕ} (Kmax q : ℕ) (thr : ℕ → ℕ) (Ω : Fin L → Bool) : ℕ :=
  ((Finset.Icc 1 Kmax).filter fun i => thr i ≤ tapeZ q Ω).card

/-- `2^q R_fin` ((37), p.20): `min_{i ∈ [K_fin]} max{U^fin_{i,0}, U^fin_{i,1}}` if `K_fin > 0`, and
`0` if `K_fin = 0`. -/
def rFin {L : ℕ} (Kmax q : ℕ) (thr : ℕ → ℕ) (Ω : Fin L → Bool) : ℕ :=
  if h : 0 < kFin Kmax q thr Ω then
    (Finset.Icc 1 (kFin Kmax q thr Ω)).inf' ⟨1, Finset.mem_Icc.2 ⟨le_refl 1, h⟩⟩
      fun i => max (tapeU q Ω i 0) (tapeU q Ω i 1)
  else 0

/-- **The finite Poisson sampler** `Samp_fin : {0,1}^R → {0,1}^{2q}`, `R = (2K_max + 2)q`
(Li, Parham, arXiv:2610.06826 (held copy sha256 b604fa11…), §4.1.2, (35)–(37), p.20): the tape
`Ω = (Z, U^fin_{1,0}, U^fin_{1,1}, …, U^fin_{K_max,0}, U^fin_{K_max,1}, Θ^fin)` consists of `q`-bit
blocks, read as an integer `Z ∈ {0, …, 2^q − 1}` and as binary fractions in `[0, 1)`; with
thresholds `T_i`, `K_fin` is the number of `i ∈ [K_max]` with `Z ≥ T_i`, and
`R_fin = min_{i ∈ [K_fin]} max{U^fin_{i,0}, U^fin_{i,1}}` (`0` if `K_fin = 0`). The output is the pair
of `q`-bit encodings of `(R_fin, Θ^fin)`, representing `V_fin = R_fin e^{2πiΘ_fin}`.

**Formalization Note** The thresholds are a parameter; the paper's sampler uses thresholds
satisfying `AdmissibleThresholds` (these are nondecreasing, so the `K_fin` pairs with `Z ≥ T_i` are
the first `K_fin` pairs). Blocks are most significant bit first. -/
def finPoissonSampler (Kmax q : ℕ) (thr : ℕ → ℕ) : Sampler ((2 * Kmax + 2) * q) q :=
  fun Ω => (natBits q (rFin Kmax q thr Ω), tapeTheta Kmax q Ω)

end QNatProofs


