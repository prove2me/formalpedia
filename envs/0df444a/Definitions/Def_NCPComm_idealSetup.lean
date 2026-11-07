-- Prove2me | Definitions.Def_NCPComm_idealSetup
-- name    : NCPComm_idealSetup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:01:56.184909+00:00
-- url     : https://prove2.me/theorems/0da83753-8e6a-4ac4-ad7e-f3091441290b
-- title:
--   The random setup $((\mathbf P^b_{\mathrm{light}},\mathbf P^b_{\mathrm{heavy}}),(\mathbf V^b_i)_i)(N,K,s)$ and its counts
-- statement:
--   The **setup** of an interactive proof for NCP consists of the prover's indicators $p_{\mathrm{light}},p_{\mathrm{heavy}}\in\{0,1\}^N$ and the verifier's multiplicity indicators $(v_i)_i$. In the **random setup** with parameter $b\in\{0,1\}$, the distribution $D$ is uniform on $\mathcal F_b(N,K)$ and the sample is Poissonized with mean $s$. Write $\mathbf H^b_i$ and $\mathbf L^b_i$ for the indicators of heavy and light elements occurring exactly $i$ times, so that $\mathbf H^b_i+\mathbf L^b_i=\mathbf V^b_i$.
--
--   The module also defines the counts $|\mathbf H_i|$, $|\mathbf L_i|$, the histograms $(|\mathbf H_i|)_{i\ge1}$, $(|\mathbf L_i|)_{i\ge1}$, the shift at the doubleton entry, Alice's canonical sample (a Poissonized sample from the canonical $D_0$), the mean and variance of a law on $\mathbb N$, the binomial point mass, and
--   $$
--   g:=\big\lfloor\mathbb E[|\mathbf L^1_2|]-\mathbb E[|\mathbf L^0_2|]+\tfrac12\big\rfloor.
--   $$
--
--   **Formalization Note** The family $(v_i)_i$ is encoded as a count function, with $v_i(x)=1\iff$ count at $x$ equals $i$, and $s'$ is the total of the counts. "$D$ uniform on $\mathcal F_b$" is implemented by a uniform permutation $\pi$ with $D=\pi(D_b)$; the orbit map pushes the uniform law forward to the uniform law on the orbit, and $\pi$ is what chooses "the heavy and light sets" (p.21). Outside $3\mid N$, $0<K<N/3$ the setup is a fixed point mass, and all theorems assume the valid range at least for large parameters.
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), Definitions 4.5 and 4.6, pp.20–21; Claims 4.11–4.13, pp.25–27; Figure 4.9.1, step 3a, p.23

import Mathlib
import Definitions.Def_NCPComm_family
import Definitions.Def_NCPComm_poissonSample
import Definitions.Def_OAI_Probability_ThreeState_Basic

open scoped NNReal ENNReal

namespace NCPComm

/-- The setup of an interactive proof for NCP (Definition 4.5, p.20, of Herman, The Communication
Complexity of Verifying Distribution Properties, STOC 2027 submission, manuscript sha256 714c0353…):
the prover's indicators `p_light`, `p_heavy` and the verifier's sample.

**Formalization Note** The multiplicity indicators `v_1, v_2, …` are encoded as the count function:
`v_i(x) = 1 ↔ counts x = i`. The sample size is `s′ = ∑ₓ counts x`, so no information is lost. -/
structure SetupOutcome (N : ℕ) where
  light : Fin N → Bool
  heavy : Fin N → Bool
  counts : Fin N → ℕ

/-- The setup for one choice of permutation `π`: the input distribution is `D = π(D_b)`, so `π` sends
the canonical heavy and light sets to the heavy and light sets of `D`. The sample is a Poissonized
sample of mean `s` from `D`. -/
noncomputable def setupGiven (b : Bool) (N K : ℕ) (s : ℝ≥0) (h : ValidParams N K)
    (π : Equiv.Perm (Fin N)) : PMF (SetupOutcome N) :=
  (poissonSample ((canonicalPMF b N K h).map π) s).map fun l =>
    { light := fun x => decide (K ≤ (π.symm x).val ∧ (b = false ∨ (π.symm x).val < N / 3))
      heavy := fun x => decide ((π.symm x).val < K)
      counts := countVec l }

/-- A random setup `((P^b_light, P^b_heavy), (V^b_i)_i)(N, K, s)` (Definition 4.6, pp.20–21): `D` is
uniform on `F_b(N, K)` and the sample is Poissonized with mean `s` (p.21).

**Formalization Note** "`D` uniform on `F_b`" is implemented by a uniform permutation `π` with
`D = π(D_b)`. The orbit map pushes the uniform law on permutations to the uniform law on the orbit,
and the page describes the randomness as "the choice of the distribution in the family (i.e. the
heavy and light sets)", which is what `π` chooses. Outside `ValidParams` the value is a fixed point
mass; every theorem of this mission assumes `ValidParams` at the relevant parameters, at least
eventually. -/
noncomputable def idealSetup (b : Bool) (N K : ℕ) (s : ℝ≥0) : PMF (SetupOutcome N) :=
  if h : ValidParams N K then
    (PMF.uniformOfFintype (Equiv.Perm (Fin N))).bind (setupGiven b N K s h)
  else PMF.pure ⟨fun _ => false, fun _ => false, fun _ => 0⟩

/-- Alice's canonical sample of Figure 4.9.1, step 3a, p.23: a Poissonized sample of mean `s` from
the canonical `D₀(N, K)`, together with its canonical heavy and light indicators. Outside
`ValidParams` it is the same fixed point mass as `idealSetup`. -/
noncomputable def canonicalSetup (N K : ℕ) (s : ℝ≥0) : PMF (SetupOutcome N) :=
  if h : ValidParams N K then setupGiven false N K s h 1
  else PMF.pure ⟨fun _ => false, fun _ => false, fun _ => 0⟩

/-- `|H_i|`: the number of heavy elements occurring exactly `i` times. -/
def heavyCount {N : ℕ} (o : SetupOutcome N) (i : ℕ) : ℕ :=
  (Finset.univ.filter fun x => o.heavy x = true ∧ o.counts x = i).card

/-- `|L_i|`: the number of light elements occurring exactly `i` times. -/
def lightCount {N : ℕ} (o : SetupOutcome N) (i : ℕ) : ℕ :=
  (Finset.univ.filter fun x => o.light x = true ∧ o.counts x = i).card

/-- The heavy part `(H_i)_{i ≥ 1}` of the sample, as a count function: the count on heavy elements
and `0` elsewhere. -/
def heavyPart {N : ℕ} (o : SetupOutcome N) : Fin N → ℕ :=
  fun x => if o.heavy x = true then o.counts x else 0

/-- `L_i` as a vector: the indicator of the light elements occurring exactly `i` times. -/
def lightIndicator {N : ℕ} (o : SetupOutcome N) (i : ℕ) : Fin N → Bool :=
  fun x => decide (o.light x = true ∧ o.counts x = i)

/-- The family `(L_i)_{i ≥ 3}`, as a count function: the count on light elements occurring at least
three times and `0` elsewhere. -/
def lightHigh {N : ℕ} (o : SetupOutcome N) : Fin N → ℕ :=
  fun x => if o.light x = true ∧ 3 ≤ o.counts x then o.counts x else 0

/-- The heavy histogram `(|H_i|)_{i ≥ 1}` with values in `ℤ`; the unused entry at `i = 0` is `0`. -/
def heavyHist {N : ℕ} (o : SetupOutcome N) : ℕ → ℤ :=
  fun i => if i = 0 then 0 else (heavyCount o i : ℤ)

/-- The light histogram `(|L_i|)_{i ≥ 1}` with values in `ℤ`; the unused entry at `i = 0` is `0`. -/
def lightHist {N : ℕ} (o : SetupOutcome N) : ℕ → ℤ :=
  fun i => if i = 0 then 0 else (lightCount o i : ℤ)

/-- The shift `(h_i + r·1_{i=2})_i` of a histogram at the doubleton entry (Claim 4.13, p.27). -/
def doubletonShift (r : ℤ) (h : ℕ → ℤ) : ℕ → ℤ := fun i => if i = 2 then h i + r else h i

/-- The mean of a law on `ℕ`, as a real. The laws of this mission are supported on `{0, …, N}`, so
the sum is finite. -/
noncomputable def pmfMean (P : PMF ℕ) : ℝ := (∑' k, P k * (k : ℝ≥0∞)).toReal

/-- The variance of a law on `ℕ`, as a real. -/
noncomputable def pmfVar (P : PMF ℕ) : ℝ :=
  (∑' k, P k * ENNReal.ofReal (((k : ℝ) - pmfMean P) ^ 2)).toReal

/-- The mass at `k` of the binomial law `Bin(n, q)`, for `0 ≤ q ≤ 1`. -/
noncomputable def binomialMass (n : ℕ) (q : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k))

/-- `g := ⌊E[|L¹₂|] - E[|L⁰₂|] + 1/2⌋` (Claim 4.12, p.26, and Claim 4.13, p.27), at parameters
`(N, K, s)`.

**Formalization Note** The floor is `Nat.floor`. In the regime of the claims the mean difference is
positive for all large `N` (Claim 4.11's formula), so the floor is the integer floor. -/
noncomputable def gapFromMeans (N K : ℕ) (s : ℝ≥0) : ℕ :=
  ⌊pmfMean ((idealSetup true N K s).map fun o => lightCount o 2)
    - pmfMean ((idealSetup false N K s).map fun o => lightCount o 2) + 1 / 2⌋₊

end NCPComm


