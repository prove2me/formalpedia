-- Prove2me | Definitions.Def_DQIShattered_Supplement_Framework
-- name    : DQIShattered_Supplement_Framework
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:33:43.816809+00:00
-- url     : https://prove2.me/theorems/c58f11bb-7434-43cf-ae19-b62576b58219
-- title:
--   Normalized Wasserstein stability, Gibbs shattering, Glauber mixing, and right-invertible exact sampling
-- statement:
--   This definition file supplies the objects used by the six supplement theorems.
--
--   For probability laws $\mu,\nu$ on $\{\pm1\}^N$, the normalized Wasserstein distance is
--   $$
--   W_1(\mu,\nu)=\frac1N\inf_{\pi\in\Pi(\mu,\nu)}\mathbb E_\pi\lVert X-Y\rVert_1
--   =\frac2N\inf_{\pi\in\Pi(\mu,\nu)}\mathbb E_\pi d_H(X,Y).
--   $$
--   A sampler family is $\iota$-stable when replacing one independently sampled clause changes its output law by expected $W_1$ at most $\iota$. Its sampling error is the ensemble-average $W_1$ distance from the Gibbs law.
--
--   An $\varepsilon$-shattering witness consists of a positive number of nonempty clusters and a constant $c>0$ independent of $N$: every cluster has mass at most $e^{-cN}$ and Hamming diameter at most $\varepsilon N$, distinct clusters are separated by at least $\varepsilon^3N$, and their union has mass at least $1-e^{-cN}$. The framework distinguishes the paper's high-probability definition from the exponentially-good estimate proved for random Max-$k$-XORSAT.
--
--   The Glauber chain is the random-scan single-site heat-bath chain. A lower bound $t_{\mathrm{mix}}\ge T$ means that at every integer time $t<T$ some initial state remains at total variation distance greater than $1/4$ from the Gibbs law.
--
--   Finally, the Gibbs family is extended to $\beta=\infty$ by the uniform law on satisfying assignments. For a right-invertible incidence matrix, the file gives the exact classical syndrome-and-kernel sampler and the ideal DQI/Regev output law, together with cubic field/gate-operation bounds.
--
--   **Formalization Note** Spins and couplings use the published $\mathbb F_2$ encodings. The $N=0$ branch of normalized Wasserstein is explicitly $0$, but every supplement theorem has $N\to\infty$ with $N\ge k\ge2$. Glauber mixing is expressed as a lower-bound predicate rather than a natural-number infimum, avoiding a default value for a chain that never mixes.
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), eqs. (4.2)–(4.4), pp.17–18; Definition 4.4, p.19; Theorem 4.10, pp.21–22; Appendix A, pp.35–36

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_DQIShattered_Ensemble
import Definitions.Def_DQIShattered_Gibbs
import Definitions.Def_DQIShattered_Decoding
import Definitions.Def_DQIShattered_DQI
import Definitions.Def_DQIShattered_Efficient

namespace DQIShattered

namespace Supplement

open Finset Filter Topology

abbrev Spin (N : ℕ) := Fin N → ZMod 2

abbrev Law (N : ℕ) := Spin N → ℝ

/-- A probability mass function on a finite type. -/
def IsLaw {X : Type*} [Fintype X] (p : X → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

/-- Hamming distance on the spin cube, using the bijection between F₂ bits and {±1} spins. -/
def hamming {N : ℕ} (x y : Spin N) : ℕ :=
  (univ.filter fun i => x i ≠ y i).card

/-- A coupling of two finite probability laws. -/
def IsCoupling {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X → ℝ) (q : Y → ℝ) (π : X × Y → ℝ) : Prop :=
  (∀ z, 0 ≤ π z) ∧
    (∀ x, ∑ y, π (x, y) = p x) ∧
    (∀ y, ∑ x, π (x, y) = q y)

/-- The normalized Wasserstein distance of (4.2),
'W₁(μ,ν) = N⁻¹ inf E‖X−Y‖₁ = (2/N) inf E d_H(X,Y)'.

Zhou, Shutty, Sellke, Jordan, arXiv:2609.40345, held version sha256 0c7f6fdf…,
Eq. (4.2), pp.17–18. The statements using this definition have 'N ≥ k ≥ 3'; the explicit
'N = 0' branch merely gives the total Lean function a harmless boundary value. -/
noncomputable def normalizedW1 (N : ℕ) (p q : Law N) : ℝ :=
  if N = 0 then 0 else
    sInf {r : ℝ | ∃ π : Spin N × Spin N → ℝ, IsCoupling p q π ∧
      r = (2 / (N : ℝ)) * ∑ z : Spin N × Spin N, π z * hamming z.1 z.2}

/-- Expectation of a real observable under '(B,J) ∼ 𝔾_ER(N,k,D)'. -/
noncomputable def erExpectation (N k : ℕ) (D : ℝ)
    (F : Matrix (Fin (Mrows N k D)) (Fin N) (ZMod 2) →
      (Fin (Mrows N k D) → ZMod 2) → ℝ) : ℝ :=
  (∑ E : Fin (Mrows N k D) → KSet N k,
      ∑ v : Fin (Mrows N k D) → ZMod 2, F (incidence E) v) /
    ((Fintype.card (Fin (Mrows N k D) → KSet N k) : ℝ) * 2 ^ Mrows N k D)

/-- A distribution-valued sampler family for the Erdős–Rényi ensemble. -/
abbrev SamplerFamily (k : ℕ) (D : ℝ) :=
  (N : ℕ) → Matrix (Fin (Mrows N k D)) (Fin N) (ZMod 2) →
    (Fin (Mrows N k D) → ZMod 2) → Law N

/-- Every output of a distribution-valued sampler is a probability law. -/
def IsSamplerFamily {k : ℕ} {D : ℝ} (A : SamplerFamily k D) : Prop :=
  ∀ N B v, IsLaw (A N B v)

/-- The inverse-temperature interval (2.8)/(4.4). -/
def InHardRange (k : ℕ) (D ε β : ℝ) : Prop :=
  (1 + ε) * Real.sqrt (2 * Real.log k / D) ≤ β ∧
    β ≤ Real.sqrt (k / (2 * D))

/-- The ensemble-average normalized-Wasserstein error in (4.3). -/
noncomputable def samplingError {k : ℕ} {D β : ℝ} (A : SamplerFamily k D) (N : ℕ) : ℝ :=
  erExpectation N k D fun B v => normalizedW1 N (gibbs B v β) (A N B v)

/-- The expected normalized-Wasserstein change when the last of the 'M' iid clauses is replaced
by an independent clause, exactly the coupling of Definition 4.2 and Theorem 4.7 (pp.18–19).
When 'M = 0' the value is '0'; every theorem using it has 'N ≥ k ≥ 3' and 'D ≥ k', hence 'M > 0'. -/
noncomputable def oneClauseChange {k : ℕ} {D : ℝ} (A : SamplerFamily k D) (N : ℕ) : ℝ :=
  if hM : 0 < Mrows N k D then
    let i : Fin (Mrows N k D) := ⟨Mrows N k D - 1, by omega⟩
    (∑ E : Fin (Mrows N k D) → KSet N k,
      ∑ v : Fin (Mrows N k D) → ZMod 2,
        ∑ e' : KSet N k, ∑ j' : ZMod 2,
          normalizedW1 N (A N (incidence E) v)
            (A N (incidence (Function.update E i e')) (Function.update v i j'))) /
      ((Fintype.card (Fin (Mrows N k D) → KSet N k) : ℝ) *
        2 ^ Mrows N k D * Fintype.card (KSet N k) * 2)
  else 0

/-- The quantitative conclusion of Theorem 4.3: one fixed positive 'ιstar', independent of 'N',
obstructs every family which is 'ι'-stable for a fixed 'ι ∈ (0,ιstar]'. -/
def StableObstruction (k : ℕ) (D β : ℝ) : Prop :=
  ∃ ιstar : ℝ, 0 < ιstar ∧ ∀ ι : ℝ, 0 < ι → ι ≤ ιstar →
    ∀ A : SamplerFamily k D, IsSamplerFamily A →
      (∀ N, k ≤ N → oneClauseChange A N ≤ ι) →
      0 < liminf (fun N => samplingError (D := D) (β := β) A N) atTop

/-- A cluster decomposition satisfying all four clauses S1–S4 of Definition 4.4 (p.19).
The exponent 'c > 0' is independent of 'N'. -/
def ClusterWitness (N : ℕ) (p : Law N) (ε c : ℝ) : Prop :=
  ∃ K : ℕ, 0 < K ∧ ∃ C : Fin K → Finset (Spin N),
    (∀ i, (C i).Nonempty) ∧
    (∀ i, ∑ x ∈ C i, p x ≤ Real.exp (-c * N)) ∧
    (∀ i, ∀ x ∈ C i, ∀ y ∈ C i, (hamming x y : ℝ) ≤ ε * N) ∧
    (∀ i j, i ≠ j → ∀ x ∈ C i, ∀ y ∈ C j, ε ^ 3 * N ≤ (hamming x y : ℝ)) ∧
    1 - Real.exp (-c * N) ≤ ∑ x ∈ univ.filter (fun x => ∃ i, x ∈ C i), p x

/-- Definition 4.4: with probability tending to one there is a cluster decomposition with a
single positive exponential constant independent of 'N'. -/
def IsShatteredLaw (k : ℕ) (D : ℝ)
    (p : (N : ℕ) → Matrix (Fin (Mrows N k D)) (Fin N) (ZMod 2) →
      (Fin (Mrows N k D) → ZMod 2) → Law N) (ε : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ Tendsto
    (fun N => erProb N k D fun B v => ClusterWitness N (p N B v) ε c) atTop (𝓝 1)

/-- The exponentially-good version supplied by the proof of Theorem 4.6. -/
def IsExponentiallyShatteredLaw (k : ℕ) (D : ℝ)
    (p : (N : ℕ) → Matrix (Fin (Mrows N k D)) (Fin N) (ZMod 2) →
      (Fin (Mrows N k D) → ZMod 2) → Law N) (ε : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
    1 - Real.exp (-c * N) ≤
      erProb N k D fun B v => ClusterWitness N (p N B v) ε c

/-- Shattering of the finite-temperature Gibbs laws of the Max-'k'-XORSAT ensemble. -/
def IsShattered (k : ℕ) (D β ε : ℝ) : Prop :=
  IsShatteredLaw k D (fun _ B v => gibbs B v β) ε

/-- Exponentially-good shattering of the finite-temperature Gibbs laws. -/
def IsExponentiallyShattered (k : ℕ) (D β ε : ℝ) : Prop :=
  IsExponentiallyShatteredLaw k D (fun _ B v => gibbs B v β) ε

/-- One random-scan heat-bath step: select a uniform coordinate and resample it from the
conditional law of 'p', as recalled before Theorem 4.10 (p.21). -/
noncomputable def glauberStep (N : ℕ) (p : Law N) (x y : Spin N) : ℝ :=
  if N = 0 then 0 else
    (1 / (N : ℝ)) * ∑ i,
      if ∀ j, j ≠ i → y j = x j then
        p y / ∑ b : ZMod 2, p (Function.update x i b)
      else 0

/-- A sampler family is asymptotically non-stable when its expected normalized-Wasserstein
change under one independently resampled clause does not vanish as `N → ∞`. This is the
asymptotic meaning of "non-stable" used for the classical sampler in Theorem A.1 (p.35),
consistent with the paper's explanation after Theorem 2.6 that stability means a vanishing
change under one clause resampling. -/
def IsAsymptoticallyNonStable {k : ℕ} {D : ℝ} (A : SamplerFamily k D) : Prop :=
  ¬Tendsto (fun N => oneClauseChange A N) atTop (𝓝 0)

/-- Law after 't' single-site Glauber steps from a fixed starting spin. -/
noncomputable def glauberLaw (N : ℕ) (p : Law N) : ℕ → Spin N → Law N
  | 0, x, y => if y = x then 1 else 0
  | t + 1, x, y => ∑ z, glauberLaw N p t x z * glauberStep N p z y

/-- The usual worst-start total-variation mixing time is at least 'T': at every integer time
't < T', some starting state remains farther than '1/4' from stationarity. This formulation
avoids assigning a junk natural value if a generic chain never mixes. -/
def MixingTimeAtLeast (N : ℕ) (p : Law N) (T : ℝ) : Prop :=
  ∀ t : ℕ, (t : ℝ) < T → ∃ x : Spin N,
    1 / 4 < IsingLTL.BeliefProp.tvDist (glauberLaw N p t x) p

/-- With high probability, the Glauber mixing time is at least 'exp(aN)' for one fixed 'a > 0'. -/
def ExponentialGlauberMixing (k : ℕ) (D β : ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ Tendsto
    (fun N => erProb N k D fun B v =>
      MixingTimeAtLeast N (gibbs B v β) (Real.exp (a * N))) atTop (𝓝 1)

/-- Gibbs laws extended to 'β = ∞': the endpoint is the uniform law on the satisfying
assignments 'Bx = v', exactly Appendix A, pp.35–36. -/
noncomputable def gibbsExtended {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2))
    (v : Fin M → ZMod 2) (β : WithTop ℝ) : Law N :=
  if hβ : β = ⊤ then fun x =>
    if B.mulVec x = v then ((univ.filter fun y : Spin N => B.mulVec y = v).card : ℝ)⁻¹ else 0
  else gibbs B v (β.untop hβ)

/-- The syndrome law used by the explicit classical sampler in Lemma A.3. -/
noncomputable def syndromeLaw {M : ℕ} (v : Fin M → ZMod 2) (β : WithTop ℝ) : Reg M → ℝ :=
  if hβ : β = ⊤ then fun y => if y = v then 1 else 0
  else fun y =>
    Real.exp ((β.untop hβ) * ∑ i, if y i = v i then (1 : ℝ) else -1) /
      ∑ y' : Reg M, Real.exp ((β.untop hβ) * ∑ i, if y' i = v i then (1 : ℝ) else -1)

/-- Output law of Appendix A's classical Gaussian-elimination sampler: draw a syndrome with
the Gibbs weight and then draw uniformly from its affine solution fiber. -/
noncomputable def classicalRightInverseLaw {M N : ℕ}
    (B : Matrix (Fin M) (Fin N) (ZMod 2)) (v : Fin M → ZMod 2) (β : WithTop ℝ) : Law N :=
  fun x => syndromeLaw v β (B.mulVec x) /
    (univ.filter fun y : Spin N => B.mulVec y = B.mulVec x).card

/-- Output law of the ideal DQI/Regev preparation in Appendix A. At finite temperature this is
the published target distribution followed by 'K_B'; at 'β = ∞' it is its uniform satisfying-state
endpoint. -/
noncomputable def dqiRightInverseLaw {M N : ℕ}
    (B : Matrix (Fin M) (Fin N) (ZMod 2)) (v : Fin M → ZMod 2) (β : WithTop ℝ) : Law N :=
  if hβ : β = ⊤ then gibbsExtended B v β
  else postProcess B 0 (Dtarget B v (β.untop hβ))

/-- Field-operation count of the displayed right-inverse/kernel-basis sampler: elimination plus
one affine solve and one kernel sample. -/
def classicalRightInverseWork (M N : ℕ) : ℕ := M ^ 3 + N * M + M + N

/-- Gate/field-operation count of the right-invertible DQI/Regev preparation: elimination and
the syndrome/state-preparation steps. -/
def dqiRightInverseWork (M N : ℕ) : ℕ := M ^ 3 + 2 * N * M + 2 * M + N

/-- The exact efficient-sampling conclusion of Lemma A.3 and the proof of Theorem A.1:
'B' is right-invertible (with a displayed right inverse), and both the explicit classical
Gaussian-elimination law and the DQI/Regev law equal the Gibbs law at every
'β ∈ [0,∞]', including '⊤'.

**Formalization Note** Gaussian elimination over F₂, formation of a kernel basis, and the
right-inverse matrix use polynomially many field operations; the two laws above are the exact
three-step sampler and ideal DQI preparation described on pp.35–36, rather than unconstrained
existential algorithms. -/
def ExactEfficientSampling {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2))
    (v : Fin M → ZMod 2) : Prop :=
  (∃ Bplus : Matrix (Fin N) (Fin M) (ZMod 2), B * Bplus = 1) ∧
    FullRowRankOn B univ ∧
    classicalRightInverseWork M N ≤ 6 * (N + 1) ^ 3 ∧
    dqiRightInverseWork M N ≤ 6 * (N + 1) ^ 3 ∧
    (∀ β : WithTop ℝ, 0 ≤ β → classicalRightInverseLaw B v β = gibbsExtended B v β) ∧
    (∀ β : WithTop ℝ, 0 ≤ β → dqiRightInverseLaw B v β = gibbsExtended B v β)

end Supplement

end DQIShattered


