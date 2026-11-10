-- Prove2me | Definitions.Def_AdaptiveRLDC_LowerBound_Construction
-- name    : AdaptiveRLDC_LowerBound_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:58:45.968207+00:00
-- url     : https://prove2.me/theorems/2b77985d-750a-4345-9b9e-ea55811b2bd5
-- title:
--   Algorithm 1 from sampled views
-- statement:
--   For a guessed heavy set $H$, assignment $\kappa:H\to\{0,1\}$ and output bit $b$, form $y=c_{H\leftarrow\kappa}$ and the actual weights
--   $$\rho_{H,\kappa,b}(S)=\Pr_{T\sim\tau}[T(y)=b\ \land\ Q_T(y)\setminus H=S].$$
--   The test statistic is its capped estimator at $1_W$ with cap $2m/(pr)$. A fixed input-independent finite enumeration visits every scale, heavy set of the prescribed size, assignment and bit; it returns the first bit with statistic at least $\theta$, or zero. The observable implementation uses the sampled view completed by zero; Claim 5.8 supplies its invariance to that completion. In the full-sampling branch the decoder chooses a preimage of the fully observed valid codeword. Both branches are defined without any assumed success certificate. No efficiency claim is imposed.
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), Construction 5.7; Algorithm 1; Remark 5.5, printed p.30, PDF p.31; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance. Exact per-concept locations: Remark 5.5 printed p.28/PDF p.29; Construction 5.7 printed p.30/PDF p.31; Algorithm 1 printed p.31/PDF p.32.

import Mathlib
import Definitions.Def_AdaptiveRLDC_LowerBound_AdaptiveDecoder
import Definitions.Def_AdaptiveRLDC_LowerBound_SampleDecoder
import Definitions.Def_AdaptiveRLDC_LowerBound_CappedEstimator
import Definitions.Def_AdaptiveRLDC_LowerBound_ConstructionParameters

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

open Classical

/-- The guessed corruption, with the assignment defined only on H. -/
def overwrite {n : ℕ} (c : Cube n) (H : Sets n) (κ : H → Bool) : Cube n :=
  fun i => if h : i ∈ H then κ ⟨i,h⟩ else c i

/-- Algorithm 1(i): the actual output-and-query-set subdistribution, not an assumed certificate. -/
def guessedWeights {n : ℕ} (τ : PMF (DecodeTree n)) (c : Cube n)
    (H : Sets n) (κ : H → Bool) (b : Bool) : Sets n → ℝ :=
  fun S => treeProb τ (fun T => T.eval (overwrite c H κ) = some b ∧
    queriedSet T (overwrite c H κ) \ H = S)

def guessedEstimate {n : ℕ} (τ : PMF (DecodeTree n)) (c : Cube n)
    (m p r : ℝ) (H : Sets n) (κ : H → Bool) (b : Bool) (W : Sets n) : ℝ :=
  cht (guessedWeights τ c H κ b) p (2*m/(p*r)) (indicator W)

/-- A finite, input-independent enumeration of all scales, heavy sets, assignments and bits. -/
abbrev Guess (n d : ℕ) := Σ _j : Fin d, Σ H : Sets n, (H → Bool) × Bool

def guessOrder (n d : ℕ) : List (Guess n d) := (Finset.univ : Finset (Guess n d)).toList

/-- Algorithm 1: the first successful test in a fixed enumeration, or zero. -/
def algorithmBit {n : ℕ} (τ : PMF (DecodeTree n)) (c : Cube n) (W : Sets n)
    (q d : ℕ) (p r θ : ℝ) : Bool :=
  let success := (guessOrder n d).find? (fun g => decide
    (g.2.1.card = ⌊(q : ℝ) / scaleMass n q d (g.1.val+1)⌋₊ ∧
      θ ≤ guessedEstimate τ c (scaleMass n q d (g.1.val+1)) p r g.2.1 g.2.2.1 g.2.2.2 W))
  match success with
  | none => false
  | some g => g.2.2.2

/-- Observable implementation: complete the view by zeros, then run the actual tests. -/
def algorithmDecoder {k n : ℕ} (τ : Fin k → PMF (DecodeTree n)) (q d : ℕ)
    (p r θ : ℝ) : SampleDecoder k n :=
  fun v i => algorithmBit (τ i) (completeView v) v.1 q d p r θ

/-- Remark 5.5: read the full sampled word and choose its preimage; no preimage gives zero.
On valid words of an injective RLDC the preimage is unique. -/
def fullReadDecoder {k n : ℕ} (C : Cube k → Cube n) : SampleDecoder k n :=
  fun v => if h : ∃ x, C x = completeView v then Classical.choose h else fun _ => false

/-- Both branches of the construction; success is a theorem target, never a field. -/
def constructedDecoder {k n : ℕ} (C : Cube k → Cube n) (τ : Fin k → PMF (DecodeTree n))
    (D ε α β : ℝ) (q : ℕ) : SampleDecoder k n :=
  let p := samplingRate D ε α β n q
  let d := constructionD ε α β q
  if p = 1 then fullReadDecoder C else
    algorithmDecoder τ q d p (spreadRate n d) (threshold α β q d)

end AdaptiveRLDC.LowerBound


