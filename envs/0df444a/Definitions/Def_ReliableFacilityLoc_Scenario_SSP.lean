-- Prove2me | Definitions.Def_ReliableFacilityLoc_Scenario_SSP
-- name    : ReliableFacilityLoc_Scenario_SSP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:09:19.079977+00:00
-- url     : https://prove2.me/theorems/db3467e0-9269-4f15-a4db-5f53d02bcc19
-- title:
--   The scenario-based stochastic program (SSP) (17a)–(17d), scenario probabilities and nearest-server assignment
-- statement:
--   Fix the data of the reliable facility location model (customers $i$ with $\lambda_i \ge 0$, regular sites $j = 0,\dots,J-1$ with $f_j$, $0 \le q_j < 1$, unit costs $d_{ij}$, emergency facility $J$ with $d_{iJ} = \phi_i$, $q_J = 0$).
--
--   **Scenarios.** $\Omega = \{0,1\}^J$. In scenario $\omega$, $\delta_{j\omega} = 1$ if regular facility $j$ operates and $0$ if it has failed; by convention $\delta_{J\omega} = 1$ for every $\omega$. Since failures are independent, the probability of $\omega$ is
--   $$p_\omega = \prod_{j=0}^{J-1} (1-q_j)^{\delta_{j\omega}}\, q_j^{\,1-\delta_{j\omega}}.$$
--
--   **(SSP).** With $X_j \in \{0,1\}$ (site $j$ open) and $Y_{ij\omega} \in \{0,1\}$ (customer $i$ served by facility $j$ in scenario $\omega$, $0 \le j \le J$), minimize
--   $$\Psi(X,Y) = \sum_{j=0}^{J-1} f_j X_j + \sum_{i=0}^{I-1}\sum_{j=0}^{J}\sum_{\omega\in\Omega} \lambda_i d_{ij} p_\omega Y_{ij\omega} \qquad (17a)$$
--   subject to
--   1. $\sum_{j=0}^{J} Y_{ij\omega} = 1$ for every $i$ and $\omega$ (17b);
--   2. $Y_{ij\omega} \le \delta_{j\omega} X_j$ for every $i$, every $0 \le j \le J-1$ and every $\omega$ (17c);
--   3. $X_j, Y_{ij\omega} \in \{0,1\}$ (17d).
--
--   Feasible and optimal solutions are defined as for (RUFL).
--
--   **Nearest server.** With the convention $X_J = 1$, call facility $k$ *operating and open* in $\omega$ if $\delta_{k\omega} X_k = 1$. Facility $k$ is the **nearest server** of customer $i$ in scenario $\omega$ if
--   $$k = \min\{0 \le k \le J : \delta_{k\omega}X_k = 1,\ d_{ik} \le d_{ik'}\ \forall k' \ne k \text{ with } \delta_{k'\omega}X_{k'} = 1\},$$
--   that is, $k$ is the closest operating open facility, ties broken by the lowest index.
--
--   (SSP) is the exponential-size formulation that enumerates all failure scenarios; Proposition 1 shows that it has the same optimal value as the compact (RUFL) when $R = J$.
--
--   **Formalization Note** The page prints (17c) as $\sum_{i=0}^{I-1} Y_{ij\omega} \le \delta_{j\omega} X_j$. With binary $X$ this lets each facility serve at most one customer per scenario, a capacity of one in an uncapacitated model, under which Proposition 1 is false (two customers next to one open site). It is stated per customer, as the proof in A.1 uses it. The paper defines $p_\omega$ only as "the probability that scenario $\omega$ will occur"; the product form is what independence of failures (p. 8) gives. A scenario is a function from the $J$ regular sites to Booleans.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), Appendix A.1, pp. 32–33 (PDF 34–35), (SSP) (17a)–(17d), conventions δ_Jω = 1, X_J = 1 and the nearest-server rule on p. 33; (17c) corrected

import Definitions.Def_ReliableFacilityLoc_Scenario_Instance

open Finset

namespace ReliableFacilityLoc.Scenario

/-- A failure scenario `ω ∈ Ω = {0,1}^J` (Cui–Ouyang–Shen, UCTC-FR-2010-02 (Feb. 2010), A.1,
p. 32, PDF 34): `ω j = true` iff regular facility `j` is operational in `ω`. -/
abbrev FailureScenario (J : ℕ) := Fin J → Bool

/-- The indicator `δ_jω` that facility `j` operates in scenario `ω` (A.1, p. 32), extended to the
emergency facility `J = Fin.last J` by the paper's convention `δ_Jω = 1` for all `ω` (p. 33). -/
def delta {J : ℕ} (ω : FailureScenario J) : Fin (J + 1) → Bool :=
  Fin.lastCases true ω

/-- The location vector extended to the emergency facility by the paper's convention `X_J = 1`
(A.1, p. 33). -/
def XExt {J : ℕ} (X : Fin J → ℝ) : Fin (J + 1) → ℝ :=
  Fin.lastCases 1 X

/-- Facility `k` (regular or emergency) is open and operating in scenario `ω`: `δ_kω X_k = 1`,
with the conventions `δ_Jω = 1` and `X_J = 1` (A.1, p. 33). -/
def IsOperatingOpen {J : ℕ} (X : Fin J → ℝ) (ω : FailureScenario J) (k : Fin (J + 1)) : Prop :=
  delta ω k = true ∧ XExt X k = 1

namespace Instance

variable {I J R : ℕ} (D : Instance I J R)

/-- The probability `p_ω` of the failure scenario `ω` (A.1, p. 32):
`p_ω = Π_{j=0}^{J-1} (1 - q_j)^{δ_jω} q_j^{1 - δ_jω}`.

Formalization Note: the paper defines `p_ω` only as "the probability that scenario ω will occur";
the product is what the independence of facility failures (p. 8) gives. It is written as a product
of `1 - q_j` over the operating facilities and `q_j` over the failed ones. -/
def scenarioProb (ω : FailureScenario J) : ℝ :=
  ∏ j : Fin J, if ω j then 1 - D.q j else D.q j

/-- The objective (17a) of the scenario-based stochastic program (SSP), A.1, p. 32 (PDF 34):
`Ψ(X, Y) = Σ_{j=0}^{J-1} f_j X_j + Σ_{i=0}^{I-1} Σ_{j=0}^{J} Σ_{ω ∈ Ω} λ_i d_ij p_ω Y_ijω`.

Formalization Note: `Y` is indexed by customer, facility in `Fin (J+1)` (the last index is the
emergency facility, with `d_iJ = φ_i`) and scenario. -/
def sspObjective (X : Fin J → ℝ) (Y : Fin I → Fin (J + 1) → FailureScenario J → ℝ) : ℝ :=
  ∑ j, D.f j * X j + ∑ i, ∑ j, ∑ ω, D.lam i * D.dExt i j * D.scenarioProb ω * Y i j ω

/-- Feasibility for (SSP), constraints (17b)–(17d), A.1, p. 32 (PDF 34).

Formalization Note: (17c) is printed as `Σ_{i=0}^{I-1} Y_ijω ≤ δ_jω X_j` for `0 ≤ j ≤ J-1`. With
binary `X` this lets each regular facility serve at most one customer per scenario, a capacity of
one in an uncapacitated model, under which Proposition 1 fails (two customers next to one open
facility). It is stated here as `Y_ijω ≤ δ_jω X_j` for every customer `i` and every regular `j`,
which is what the proof in A.1 uses ("each customer is always served by her closest open
facility", p. 33). There is no (17c) for the emergency facility `J`. (17d) keeps `X`, `Y`
real-valued and requires each entry to be `0` or `1`. The instance `D` is a parameter only so that
the constraints are read for the instance's index sets; they do not use its data. -/
@[nolint unusedArguments]
structure IsSSPFeasible (_D : Instance I J R) (X : Fin J → ℝ)
    (Y : Fin I → Fin (J + 1) → FailureScenario J → ℝ) : Prop where
  /-- (17b): `Σ_{j=0}^{J} Y_ijω = 1` -/
  serve_one : ∀ i ω, ∑ j, Y i j ω = 1
  /-- (17c), corrected: `Y_ijω ≤ δ_jω X_j` for every customer `i` and regular `j` -/
  open_operating : ∀ i (j : Fin J) ω, Y i j.castSucc ω ≤ (if ω j then (1 : ℝ) else 0) * X j
  /-- (17d): `X_j ∈ {0, 1}` -/
  X_binary : ∀ j, X j = 0 ∨ X j = 1
  /-- (17d): `Y_ijω ∈ {0, 1}` -/
  Y_binary : ∀ i j ω, Y i j ω = 0 ∨ Y i j ω = 1

/-- An optimal solution of (SSP): a feasible `(X, Y)` whose objective (17a) is at most that of
every feasible solution. -/
def IsSSPOptimal (X : Fin J → ℝ) (Y : Fin I → Fin (J + 1) → FailureScenario J → ℝ) : Prop :=
  D.IsSSPFeasible X Y ∧
    ∀ X' Y', D.IsSSPFeasible X' Y' → D.sspObjective X Y ≤ D.sspObjective X' Y'

/-- Facility `k` is the server of customer `i` in scenario `ω` prescribed on p. 33 (A.1):
`k = min{0 ≤ k ≤ J : δ_kω X_k = 1, d_ik ≤ d_ik' ∀ k' ≠ k s.t. δ_k'ω X_k' = 1}`, i.e. the closest
operating open facility (the emergency facility included), ties broken by the lowest index.

Formalization Note: the three clauses say that `k` is operating and open, that no operating open
facility is closer to `i`, and that every operating open facility exactly as close as `k` has an
index at least `k`. -/
def IsNearestServer (X : Fin J → ℝ) (i : Fin I) (ω : FailureScenario J) (k : Fin (J + 1)) :
    Prop :=
  IsOperatingOpen X ω k ∧
    (∀ k', IsOperatingOpen X ω k' → D.dExt i k ≤ D.dExt i k') ∧
    ∀ k', IsOperatingOpen X ω k' → D.dExt i k' ≤ D.dExt i k → k ≤ k'

end Instance

end ReliableFacilityLoc.Scenario


