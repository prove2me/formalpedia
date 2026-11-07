-- Prove2me | Definitions.Def_ModFormPIR_Scheme
-- name    : ModFormPIR_Scheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:58:27.802902+00:00
-- url     : https://prove2.me/theorems/605fcfbd-7c02-4f24-bc9d-867a0102a823
-- title:
--   $s$-server doubly-efficient PIR schemes with exponent $\rho$
-- statement:
--   An **$s$-server PIR scheme on the machine** consists of three finite programs (a sampler of public parameters, a preprocessor, an answerer) and the user's functions $\mathrm{Query}$ and $\mathrm{Reconstruct}$. The sampler does not probe; the preprocessor neither probes nor flips coins; the answerer flips no coins.
--
--   The scheme has **exponent $\rho$** when there are constants $b,C,K$ and a function $g$ with $g(n)\to0$ such that, for all $n\ge1$ and word widths $W\ge b(\lfloor\log_2 n\rfloor+1)$, with $L=\lfloor\log_2(n+2)\rfloor+1$:
--
--   1. the sampler's accept time is measurable and has expectation at most $CL^K$;
--   2. for every parameter list the sampler can output, and every database $\mathrm{DB}\in\{0,1\}^n$:
--      - the law of the message to server $k$ does not depend on the index (information-theoretic privacy);
--      - each server's table is exactly $n+1$ bits, computed in at most $CnL^K$ steps;
--      - for every index and every outcome of $\mathrm{Query}$: each server gets at most $CL^2$ bits; its answer run accepts within $(n+1)^{\rho+g(n)}$ steps and reads at most that many bits; and $\mathrm{Reconstruct}$ applied to the bits read returns $\mathrm{DB}_i$.
--
--   This is Definition 5.1, the object all the main theorems of the paper construct.
--
--   **Formalization Note** A server's answer is the trace of bits it probed, and its memory holds only $n$, its index, the parameters and the message, so it can learn the database only through probes. The sampler is Las Vegas: every accepting run must give good parameters. $\mathrm{Query}$ and $\mathrm{Reconstruct}$ are free functions because Definition 5.1 bounds no user time. $n+1$ in the base of the exponent avoids $1^x=1$ at $n=1$ and changes no exponent.
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), §4.1, pp.18–19, and Definition 5.1, p.21

import Mathlib
import Definitions.Def_ModFormPIR_Machine

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace ModFormPIR

/-!
# Doubly-efficient PIR schemes

Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027
submission (manuscript sha256 2442f3db…), §4.1, pp.18–19, and Definition 5.1, p.21.

**Formalization Note.**
* *Public parameters.* The sampler is Las Vegas: its accept time has finite expectation `≤ C·L^K`,
  with `⊤` on a tape with no accepting run, and **every** accepting run gives good parameters. So
  correctness, privacy and all time bounds hold for every output, not on average.
* *Answer.* A server's answer is the trace of bits it probed; `ans` sees only `n`, `j`, the parameters and
  the message in its memory, never the database, so it can learn the database only by probing.
* *User side.* `query` and `reconstruct` are free functions, since Definition 5.1 bounds no user time.
* *Asymptotics.* `n^{ρ+o(1)}` is `(n+1)^{ρ+g n}` with one `g → 0` per scheme, and `polylog(n)` is `C·L^K`
  with `L = ⌊log₂(n+2)⌋ + 1`. Using `n+1` avoids the bound `1^x = 1` at `n = 1` and changes no exponent.
* *Server time.* The paper sums over the `s` servers; for fixed `s` this is the per-server bound up to a
  factor `s`, which `g` absorbs.
-/

/-- The polylog base `L = ⌊log₂(n+2)⌋ + 1`. -/
def polyL (n : ℕ) : ℕ := Nat.log2 (n + 2) + 1

/-- The database bits as cell values. -/
def dbCells {n : ℕ} (DB : Fin n → Bool) : List ℤ :=
  List.ofFn fun i => if DB i then 1 else 0

/-- The sampler's input: cell 0 holds `n`. -/
def samplerInput (n : ℕ) : List ℤ := [(n : ℤ)]

/-- The sampler's output: cell `-1` holds `ℓ`, cells `-2, …, -1-ℓ` hold the parameter words as naturals. -/
def readParams {W : ℕ} (st : State W) : List ℕ :=
  (List.range (st.mem (-1)).toNat).map fun i => (st.mem (-2 - (i : ℤ))).toNat

/-- `params` is the output of some accepting run of the sampler `P` on input size `n`. -/
def IsSamplerOutput (P : Program) (W n : ℕ) (params : List ℕ) : Prop :=
  ∃ (τ : ℕ → Bool) (t : ℕ) (st : State W), Accepts P [] τ (samplerInput n) t st ∧ params = readParams st

/-- The preprocessor's input: `n`, `j`, `ℓ`, the `ℓ` parameters, then the database, one bit per cell. -/
def prepInput {n : ℕ} (j : ℕ) (params : List ℕ) (DB : Fin n → Bool) : List ℤ :=
  (n : ℤ) :: (j : ℤ) :: (params.length : ℤ) :: params.map (fun x => (x : ℤ)) ++ dbCells DB

/-- The answerer's input: `n`, `j`, `ℓ`, the `ℓ` parameters, the message length, then the message, one
bit per cell. The database is not there. -/
def ansInput (n j : ℕ) (params : List ℕ) (msg : List Bool) : List ℤ :=
  (n : ℤ) :: (j : ℤ) :: (params.length : ℤ) :: params.map (fun x => (x : ℤ)) ++
    (msg.length : ℤ) :: msg.map (fun b => if b then 1 else 0)

/-- An `s`-server PIR scheme on the machine (§4.1, p.18): one finite sampler, preprocessor and answerer
for all `n`, and the user's `Query` and `Reconstruct`. `query n params i` gives the secret state and one
message per server. Admissibility: the sampler does not probe, the preprocessor neither probes nor flips
coins, the answerer flips no coins. -/
structure Scheme (s : ℕ) where
  sampler : Program
  prep : Program
  ans : Program
  query : (n : ℕ) → List ℕ → Fin n → PMF (List ℕ × (Fin s → List Bool))
  reconstruct : (n : ℕ) → List ℕ → List ℕ → (Fin s → List Bool) → Bool
  sampler_noProbe : NoProbe sampler
  prep_noProbe : NoProbe prep
  prep_noCoin : NoCoin prep
  ans_noCoin : NoCoin ans

/-- `S` is a scheme of the shape of Definition 5.1 at database size `n` and word width `W`, with constants
`C, K` and answer budget `U` (a bound on server steps and on bits read and sent):
1. the sampler's accept time is measurable with expectation at most `C·L^K`;
2. for every parameter list it can output:
   * privacy: the law of each server's message does not depend on the index;
   * for every database, each server's table is exactly `n+1` bits, computed in at most `C·n·L^K` steps;
   * for every index and every `(st, msg)` in the support of `Query`: at most `C·L²` bits go up to each
     server; each server's answer run accepts within `U` steps and reads at most `U` bits; and
     `Reconstruct` returns the record. -/
def Scheme.Realizes {s : ℕ} (S : Scheme s) (n C K : ℕ) (U : ℝ) (W : ℕ) : Prop :=
  Measurable (acceptCost S.sampler W (samplerInput n)) ∧
  ∫⁻ τ, acceptCost S.sampler W (samplerInput n) τ ∂coinMeasure ≤ ((C * polyL n ^ K : ℕ) : ℝ≥0∞) ∧
  ∀ params : List ℕ, IsSamplerOutput S.sampler W n params →
    (∀ (k : Fin s) (i i' : Fin n),
      (S.query n params i).map (fun x => x.2 k) = (S.query n params i').map (fun x => x.2 k)) ∧
    ∀ DB : Fin n → Bool, ∃ tables : Fin s → List Bool,
      (∀ j : Fin s, ∃ (t : ℕ) (st : State W), t ≤ C * n * polyL n ^ K ∧
        Accepts S.prep [] zeroTape (prepInput (j : ℕ) params DB) t st ∧
        BitCellsOK st (-1) (n + 1) ∧ tables j = readBits st (-1) (n + 1)) ∧
      ∀ i : Fin n, ∀ x ∈ (S.query n params i).support,
        (∀ j : Fin s, (x.2 j).length ≤ C * polyL n ^ 2) ∧
        ∃ tr : Fin s → List Bool,
          (∀ j : Fin s, ∃ (t : ℕ) (st : State W), (t : ℝ) ≤ U ∧
            Accepts S.ans (tables j) zeroTape (ansInput n (j : ℕ) params (x.2 j)) t st ∧
            tr j = st.trace ∧ ((tr j).length : ℝ) ≤ U) ∧
          S.reconstruct n params x.1 tr = DB i

/-- Definition 5.1, p.21: an `s`-server doubly-efficient PIR scheme with exponent `ρ` exists. One finite
program triple and one `g → 0` serve all `n ≥ 1` and all word widths `W ≥ b(⌊log₂ n⌋ + 1)`. -/
def HasScheme (s : ℕ) (ρ : ℝ) : Prop :=
  ∃ (S : Scheme s) (b C K : ℕ) (g : ℕ → ℝ), Tendsto g atTop (𝓝 0) ∧
    ∀ n ≥ 1, ∀ W ≥ b * (Nat.log2 n + 1),
      S.Realizes n C K (((n : ℝ) + 1) ^ (ρ + g n)) W

end ModFormPIR


