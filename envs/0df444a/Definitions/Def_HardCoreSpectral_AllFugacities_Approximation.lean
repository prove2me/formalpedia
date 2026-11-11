-- Prove2me | Definitions.Def_HardCoreSpectral_AllFugacities_Approximation
-- name    : HardCoreSpectral_AllFugacities_Approximation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:35:43.921204+00:00
-- url     : https://prove2.me/theorems/b9c8c93b-cc03-4675-b952-4cb4d034138a
-- title:
--   Spectral bipartite class, hard-core model, and FPRAS / FPTAS / approximate-sampler predicates
-- statement:
--   Let $n\ge 0$ and let $M\in\{0,1\}^{n\times n}$ be the biadjacency matrix of a bipartite graph $G$ on $L\sqcup R$ with $L=R=\{0,\dots,n-1\}$: the left vertex $i$ and the right vertex $j$ are adjacent iff $M_{ij}=1$. An independent set is a vertex set with no two adjacent vertices; $\mathcal I(G)$ contains $\emptyset$. For a fugacity $\lambda$,
--
--   $$
--   Z_G(\lambda)=\sum_{I\in\mathcal I(G)}\lambda^{|I|},\qquad \mu_{G,\lambda}(I)=\frac{\lambda^{|I|}}{Z_G(\lambda)}\ (I\in\mathcal I(G)),\quad \mu_{G,\lambda}(S)=0 \text{ otherwise}.
--   $$
--
--   $G$ is $\Delta$-regular when every row and every column of $M$ has exactly $\Delta$ ones. With $\Pi_\perp x=x-\bar x\mathbf 1$ the projection away from the constant vector, $\sigma_2(M)\le\sigma$ means $\|\Pi_\perp M\Pi_\perp x\|_2\le\sigma\|x\|_2$ for all $x\in\mathbb R^n$ (the identity $\sigma_2(M)=\|\Pi_\perp M\Pi_\perp\|_{op}$ of p. 6). The class $\mathcal G^\sigma_{\Delta,\Delta}$ consists of the $\Delta$-regular such $M$ with $\sigma_2(M)\le\sigma$, for $\sigma\ge 0$.
--
--   A graph is given to a register-machine program as its $2n\times 2n$ adjacency matrix (left vertex $i$ at index $i$, right vertex $j$ at index $n+j$) together with a list of real parameters, the first of which is the accuracy $\varepsilon$, followed by the fixed real parameters of the theorem. The random tape is an i.i.d. sequence of uniform $[0,1]$ variables. A run's scalar output is register $0$; its set output is the set of vertices whose memory cell at the vertex's index is nonzero. With work budget $B=C(2n+\lceil 1/\varepsilon\rceil)^d$:
--
--   - **FPRAS**: one program and one pair $(C,d)$ such that for every $G\in\mathcal G^\sigma_{\Delta,\Delta}$ and every $\varepsilon\in(0,1)$ every run halts without fault within $B$ steps and $\Pr[(1-\varepsilon)Z_G(\lambda)\le \hat Z\le(1+\varepsilon)Z_G(\lambda)]\ge 3/4$.
--   - **FPTAS**: the same with a program that has no uniform-draw instruction and the approximation holding on every run.
--   - **Efficient approximate sampler**: one program and $(C,d)$ such that every run halts within $B$ and outputs an independent set, and the output law $\hat\mu$ satisfies $\mathrm{TV}(\hat\mu,\mu_{G,\lambda})=\tfrac12\sum_S|\hat\mu(S)-\mu_{G,\lambda}(S)|<\varepsilon$.
--
--   These are the definitions of p. 2 of the paper read in the mission's real-register computational model; the class is (1.1) on p. 3 with the conventions of §2.1, p. 6.
-- source:
--   Ijay Narang, Will Perkins, STOC 2027 submission #294 (October 2026), p. 2 (hard-core model, FPTAS, FPRAS, efficient approximate sampler), p. 3 (class (1.1)), p. 6 (§2.1, σ₂(M) = ‖Π⊥MΠ⊥‖_op).

import Mathlib
import Definitions.Def_HardCoreSpectral_AllFugacities_RegisterMachine

set_option autoImplicit false

namespace HardCoreSpectral.AllFugacities

open MeasureTheory

/-- Vertices of a bipartite graph with sides `L = Fin n` (`Sum.inl`) and `R = Fin n`
(`Sum.inr`). -/
abbrev Vertex (n : ℕ) := Fin n ⊕ Fin n

/-- Adjacency of the bipartite graph whose biadjacency matrix is `M`
(`M i j = true` iff the left vertex `i` and the right vertex `j` are joined). -/
def bipAdj {n : ℕ} (M : Matrix (Fin n) (Fin n) Bool) : Vertex n → Vertex n → Bool
  | .inl i, .inr j => M i j
  | .inr j, .inl i => M i j
  | _, _ => false

/-- `I` is an independent set: no two of its vertices are adjacent. -/
def IsIndependent {n : ℕ} (M : Matrix (Fin n) (Fin n) Bool) (I : Finset (Vertex n)) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, bipAdj M u v = false

/-- Hard-core partition function `Z_G(λ) = ∑_{I ∈ 𝓘(G)} λ^{|I|}` (p. 2); the empty set is
included. -/
noncomputable def partitionFunction {n : ℕ} (M : Matrix (Fin n) (Fin n) Bool) (lam : ℝ) : ℝ := by
  classical
  exact ∑ I ∈ (Finset.univ : Finset (Finset (Vertex n))).filter (IsIndependent M),
    lam ^ I.card

/-- Hard-core measure `μ_{G,λ}(I) = λ^{|I|} / Z_G(λ)` on independent sets, and `0` on
vertex sets that are not independent (p. 2). -/
noncomputable def hardCoreLaw {n : ℕ} (M : Matrix (Fin n) (Fin n) Bool) (lam : ℝ)
    (I : Finset (Vertex n)) : ℝ := by
  classical
  exact if IsIndependent M I then lam ^ I.card / partitionFunction M lam else 0

/-- Every left and every right vertex has degree exactly `Δ`. -/
def IsBiregular {n : ℕ} (Δ : ℕ) (M : Matrix (Fin n) (Fin n) Bool) : Prop :=
  (∀ i, (Finset.univ.filter fun j => M i j = true).card = Δ) ∧
  (∀ j, (Finset.univ.filter fun i => M i j = true).card = Δ)

/-- `Π⊥ x = x − (mean x) 𝟙`, the orthogonal projection away from the constant vector. -/
noncomputable def projPerp {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i - (∑ j, x j) / n

/-- The real biadjacency matrix acting on a vector indexed by `R`. -/
noncomputable def biadjMulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) Bool) (x : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => ∑ j, (if M i j = true then (1 : ℝ) else 0) * x j

/-- `σ₂(M_G) = ‖Π⊥ M Π⊥‖_op ≤ σ` (p. 6), written with squared Euclidean norms; for `σ ≥ 0`
this is exactly the operator-norm bound. -/
def SecondSingularValueLE {n : ℕ} (M : Matrix (Fin n) (Fin n) Bool) (σ : ℝ) : Prop :=
  ∀ x : Fin n → ℝ,
    ∑ i, (projPerp (biadjMulVec M (projPerp x)) i) ^ 2 ≤ σ ^ 2 * ∑ i, (x i) ^ 2

/-- The class `𝒢^σ_{Δ,Δ}` of (1.1): `Δ`-regular bipartite graphs on `L ⊔ R`, `|L| = |R| = n`,
with `σ₂(M_G) ≤ σ`, for a certificate `σ ≥ 0` (§2.1). -/
def InSpectralClass {n : ℕ} (Δ : ℕ) (σ : ℝ) (M : Matrix (Fin n) (Fin n) Bool) : Prop :=
  0 ≤ σ ∧ IsBiregular Δ M ∧ SecondSingularValueLE M σ

/-- Machine input: the `2n × 2n` adjacency matrix of `G`, left vertex `i` stored as index `i`,
right vertex `j` as index `n + j`, followed by the real scalar parameters. -/
def graphInput {n : ℕ} (M : Matrix (Fin n) (Fin n) Bool) (params : List ℝ) : RegisterInput where
  vertexCount := n + n
  adjacency a b := bipAdj M (finSumFinEquiv.symm a) (finSumFinEquiv.symm b)
  parameters := params

/-- The random tape: an i.i.d. sequence of uniform `[0,1]` draws (countable product of the
Lebesgue probability measure on `[0,1]`). -/
noncomputable def tapeMeasure : Measure (ℕ → Set.Icc (0 : ℝ) 1) :=
  Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval))

/-- Scalar output of a run: register `0` of the configuration after `B` transitions. -/
noncomputable def scalarOutput (P : RegisterProgram) (input : RegisterInput) (B : ℕ)
    (tape : ℕ → Set.Icc (0 : ℝ) 1) : ℝ :=
  (registerRun P input tape B).registers 0

/-- Set output of a run on a graph input: the vertices whose memory cell (at the vertex's input
index) is nonzero after `B` transitions. -/
noncomputable def setOutput {n : ℕ} (P : RegisterProgram) (input : RegisterInput) (B : ℕ)
    (tape : ℕ → Set.Icc (0 : ℝ) 1) : Finset (Vertex n) := by
  classical
  exact Finset.univ.filter fun v : Vertex n =>
    (registerRun P input tape B).memory (finSumFinEquiv v).val ≠ 0

/-- Polynomial work budget `C (|V(G)| + ⌈1/ε⌉)^d`. -/
noncomputable def polyBudget (C d n : ℕ) (ε : ℝ) : ℕ := C * (n + n + ⌈ε⁻¹⌉₊) ^ d

/-- The event that the scalar output is a `(1 ± ε)` approximation of `Z_G(λ)`. -/
def accurateEvent {n : ℕ} (P : RegisterProgram) (M : Matrix (Fin n) (Fin n) Bool)
    (params : List ℝ) (B : ℕ) (lam ε : ℝ) : Set (ℕ → Set.Icc (0 : ℝ) 1) :=
  {tape | (1 - ε) * partitionFunction M lam ≤ scalarOutput P (graphInput M params) B tape ∧
    scalarOutput P (graphInput M params) B tape ≤ (1 + ε) * partitionFunction M lam}

/-- Output law of the set produced by the run (probability of each vertex set). -/
noncomputable def outputLaw {n : ℕ} (P : RegisterProgram) (M : Matrix (Fin n) (Fin n) Bool)
    (params : List ℝ) (B : ℕ) (S : Finset (Vertex n)) : ℝ :=
  (tapeMeasure {tape | setOutput (n := n) P (graphInput M params) B tape = S}).toReal

/-- Total variation distance `TV(μ̂, μ_{G,λ}) = ½ ∑_S |μ̂(S) − μ_{G,λ}(S)|`. -/
noncomputable def tvToHardCore {n : ℕ} (P : RegisterProgram) (M : Matrix (Fin n) (Fin n) Bool)
    (params : List ℝ) (B : ℕ) (lam : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ S : Finset (Vertex n), |outputLaw P M params B S - hardCoreLaw M lam S|

/-- A program is deterministic when it contains no uniform-draw instruction. -/
def IsDeterministic (P : RegisterProgram) : Prop :=
  ∀ ins ∈ P, ∀ dst : ℕ, ins ≠ RegisterInstruction.uniform dst

/-- FPRAS for `Z_G(λ)` on `𝒢^σ_{Δ,Δ}` (p. 2). One finite program and one polynomial
(coefficient `C`, degree `d`) are fixed before every graph and accuracy; the program reads `G`,
`ε` and the fixed real parameters `fixedParams`. On every input it halts without fault within the
budget, and the `(1 ± ε)` event has probability at least `3/4` under the uniform tape. -/
def IsFPRAS (Δ : ℕ) (σ lam : ℝ) (fixedParams : List ℝ) : Prop :=
  ∃ P : RegisterProgram, ∃ C d : ℕ,
    ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) Bool), InSpectralClass Δ σ M →
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      RegisterTerminatesWithin P (graphInput M (ε :: fixedParams)) (polyBudget C d n ε) ∧
      MeasurableSet (accurateEvent P M (ε :: fixedParams) (polyBudget C d n ε) lam ε) ∧
      (3 / 4 : ENNReal) ≤
        tapeMeasure (accurateEvent P M (ε :: fixedParams) (polyBudget C d n ε) lam ε)

/-- FPTAS for `Z_G(λ)` on `𝒢^σ_{Δ,Δ}` (p. 2): a deterministic program (no uniform draws)
that halts within a polynomial budget with a `(1 ± ε)` approximation. -/
def IsFPTAS (Δ : ℕ) (σ lam : ℝ) (fixedParams : List ℝ) : Prop :=
  ∃ P : RegisterProgram, IsDeterministic P ∧ ∃ C d : ℕ,
    ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) Bool), InSpectralClass Δ σ M →
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      RegisterTerminatesWithin P (graphInput M (ε :: fixedParams)) (polyBudget C d n ε) ∧
      ∀ tape, tape ∈ accurateEvent P M (ε :: fixedParams) (polyBudget C d n ε) lam ε

/-- Efficient approximate sampler for `μ_{G,λ}` on `𝒢^σ_{Δ,Δ}` (p. 2): one program and one
polynomial before every graph and accuracy; every run halts without fault within budget and
outputs an independent set, and the unconditional output law is at total variation distance
strictly less than `ε` from `μ_{G,λ}`. -/
def IsEfficientSampler (Δ : ℕ) (σ lam : ℝ) (fixedParams : List ℝ) : Prop :=
  ∃ P : RegisterProgram, ∃ C d : ℕ,
    ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) Bool), InSpectralClass Δ σ M →
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      RegisterTerminatesWithin P (graphInput M (ε :: fixedParams)) (polyBudget C d n ε) ∧
      (∀ tape, IsIndependent M
        (setOutput (n := n) P (graphInput M (ε :: fixedParams)) (polyBudget C d n ε) tape)) ∧
      (∀ S : Finset (Vertex n), MeasurableSet
        {tape | setOutput (n := n) P (graphInput M (ε :: fixedParams))
          (polyBudget C d n ε) tape = S}) ∧
      tvToHardCore P M (ε :: fixedParams) (polyBudget C d n ε) lam < ε

end HardCoreSpectral.AllFugacities


