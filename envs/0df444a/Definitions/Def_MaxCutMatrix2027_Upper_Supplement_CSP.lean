-- Prove2me | Definitions.Def_MaxCutMatrix2027_Upper_Supplement_CSP
-- name    : MaxCutMatrix2027_Upper_Supplement_CSP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:08:13.576142+00:00
-- url     : https://prove2.me/theorems/1e1671fa-523b-4169-b28f-a9b3a852e463
-- title:
--   MAX-2CSP instances, pair oracle, spectral objects and RAM extension
-- statement:
--   This definition file fixes the MAX-2CSP objects of §3 (p.14) and Appendix A (pp.42–45).
--
--   1. **Instances.** An instance on variables $[n]$ is a set of distinct triples $(f,u,v)$ with $u<v$ and $f:\{0,1\}^2\to\{0,1\}$ any of the 16 truth tables; a pair may carry several different predicates. $\mathrm{OPT}(F)$ is the maximum over all $2^n$ assignments of the number of satisfied constraints, and $F[Q]$ keeps the constraints with both variables in $Q$.
--   2. **Pair oracle.** The answer to the pair query $(u,v)$ is the full set of predicates on that pair, encoded as the 16-bit mask $\sum 2^{\mathrm{code}(f)}$ with $\mathrm{code}(f)=\sum_{a,b}f(a,b)2^{2a+b}$.
--   3. **Matrix and spectral split (pp.42–43).** $A^{(a,b)}_{ij}$ counts constraints stored on $(i,j)$ satisfied at $x_i=a,x_j=b$; $M_{(i,a),(j,b)}=(A^{(a,b)}_{ij}+A^{(b,a)}_{ji})/2$ for $i\neq j$, and the same-variable blocks are zero. With eigenpairs $(\theta_j,u_j)$ of $M$, $L=\sum_{|\theta_j|>\tau n}\theta_ju_ju_j^T$ and $R=M-L$.
--   4. **Fractional set and sampling.** $\mathcal X=\{z\in[0,1]^{[n]\times\{0,1\}}:z_{i,0}+z_{i,1}=1\}$; $P$ repeats the selector $\xi_i$ on both labels of variable $i$. For vectors $y_{i,a}$, $K=\{n^{-1}\sum_{i,a}z_{i,a}y_{i,a}:z\in\mathcal X\}$, $K_Q=\{s^{-1}\sum_{i\in Q,a}z_{i,a}y_{i,a}:z\in\mathcal X\}$, $\Delta=d_H(K_Q,K)$ and $t_y=n^{-1}\sum_{i,a}\|y_{i,a}\|^2$.
--   5. **RAM extension.** The published unit-cost RAM is reused for every instruction except the query, which places the full truth-table mask of the queried pair in a register; time is the number of transitions.
--
--   Supremum and maximum over $\mathcal X$ are taken as `sSup` of the image of the compact nonempty set $\mathcal X$, hence attained.
--
--   **Formalization Note** Variable values are Booleans ($\mathtt{false}=0$). Scaling and the cutoff use $n$, not $2n$, as on p.43. The only proof in this file is the structural symmetry of $M$.
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), §3 p.14, Algorithm 2 p.42, Appendix A pp.42–45, p.42 (PDF p.42); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Mathlib
import Definitions.Def_MaxCutMatrix2027_Upper_RAM

set_option autoImplicit false
open scoped BigOperators

namespace MaxCutMatrix2027.Upper.Supplement

/-! MAX-2CSP (§3, p.14; Appendix A, pp.42–45). Variables are `Fin n`, Boolean values
`false = 0`, `true = 1`. -/

/-- A binary Boolean predicate `f : {0,1}² → {0,1}`; all 16 truth tables are allowed. -/
abbrev Pred := Bool → Bool → Bool

/-- A MAX-2CSP instance (§3, p.14): a set (so no repetitions) of distinct triples `(f, u, v)`
with `u < v`. Several different predicates may share a pair; at most 16 do. -/
structure CSPInstance (n : ℕ) where
  constraints : Finset (Pred × Fin n × Fin n)
  ordered : ∀ c ∈ constraints, c.2.1 < c.2.2

namespace CSPInstance

variable {n : ℕ}

/-- The number of constraints satisfied by the assignment `x`. -/
def satisfied (F : CSPInstance n) (x : Fin n → Bool) : ℕ :=
  (F.constraints.filter (fun c => c.1 (x c.2.1) (x c.2.2) = true)).card

/-- `OPT(F)` (§3, p.14): the maximum over all `2^n` assignments of the number of satisfied
constraints. -/
def opt (F : CSPInstance n) : ℕ := Finset.univ.sup F.satisfied

/-- `OPT(F)` as a real number. -/
noncomputable def optR (F : CSPInstance n) : ℝ := (F.opt : ℝ)

/-- `F[Q]` (§3, p.14): the constraints whose two variables both lie in `Q`. -/
def induced (F : CSPInstance n) (Q : Finset (Fin n)) : CSPInstance n where
  constraints := F.constraints.filter (fun c => c.2.1 ∈ Q ∧ c.2.2 ∈ Q)
  ordered := fun c hc => F.ordered c (Finset.mem_filter.mp hc).1

end CSPInstance

/-- The code `∑_{a,b} f(a,b) 2^{2a+b} ∈ {0,…,15}` of a truth table. -/
def predCode (f : Pred) : ℕ :=
  (if f false false then 1 else 0) + (if f false true then 2 else 0) +
  (if f true false then 4 else 0) + (if f true true then 8 else 0)

/-- The complete answer to the pair query `(u, v)` (§3, p.14: "reveals all constraints between
`x_u` and `x_v`"): the 16-bit membership mask `∑_{(f,u,v) ∈ F} 2^{code f}` of the set of
predicates on the ordered pair `u < v`. Arguments that are not a pair `u < v < n` give `0`. -/
noncomputable def pairMask {n : ℕ} (F : CSPInstance n) (u v : ℕ) : ℕ := by
  classical
  exact ∑ c ∈ F.constraints.filter (fun c => c.2.1.val = u ∧ c.2.2.val = v), 2 ^ predCode c.1

/-! Appendix A, p.42–45: the matrix `M`, its spectral split, and the fractional set `X`. -/

/-- `A^{(a,b)}_{ij}` (p.42): the number of constraints assigned to the ordered pair `(i, j)`
(stored as `(f, i, j)` with `i < j`) that are satisfied at `x_i = a`, `x_j = b`. -/
noncomputable def pairCount {n : ℕ} (F : CSPInstance n) (a b : Bool) (i j : Fin n) : ℝ := by
  classical
  exact ((F.constraints.filter (fun c => c.2.1 = i ∧ c.2.2 = j ∧ c.1 a b = true)).card : ℝ)

/-- The symmetric `2n × 2n` matrix `M` indexed by `(i, a)` (p.42):
`M_{(i,a),(j,b)} = (A^{(a,b)}_{ij} + A^{(b,a)}_{ji})/2` for `i ≠ j`, and the whole same-variable
block is zero. -/
noncomputable def cspMatrix {n : ℕ} (F : CSPInstance n) :
    Matrix (Fin n × Bool) (Fin n × Bool) ℝ := by
  classical
  exact fun α γ => if α.1 = γ.1 then 0 else (pairCount F α.2 γ.2 α.1 γ.1 + pairCount F γ.2 α.2 γ.1 α.1) / 2

/-- Structural symmetry of `M` (no analytic content). -/
theorem cspMatrix_hermitian {n : ℕ} (F : CSPInstance n) : (cspMatrix F).IsHermitian := by
  classical
  ext α γ
  simp only [cspMatrix, Matrix.conjTranspose_apply, star_trivial]
  by_cases h : α.1 = γ.1
  · simp [h]
  · have h' : ¬ γ.1 = α.1 := fun e => h e.symm
    simp [h, h', add_comm]

/-- The eigenvalues `θ` of `M` (Mathlib's spectral decomposition). -/
noncomputable def cspEigenvalue {n : ℕ} (F : CSPInstance n) : Fin n × Bool → ℝ :=
  (cspMatrix_hermitian F).eigenvalues

/-- Orthonormal eigenvectors `u` of `M`. -/
noncomputable def cspEigenvector {n : ℕ} (F : CSPInstance n) :
    OrthonormalBasis (Fin n × Bool) ℝ (EuclideanSpace ℝ (Fin n × Bool)) :=
  (cspMatrix_hermitian F).eigenvectorBasis

/-- `L = ∑_{|θ_j| > τ n} θ_j u_j u_jᵀ` (p.43), both eigenvalue signs, cutoff `τ n` (not `2τn`). -/
noncomputable def cspRetained {n : ℕ} (F : CSPInstance n) (τ : ℝ) :
    Matrix (Fin n × Bool) (Fin n × Bool) ℝ := by
  classical
  exact fun α γ => ∑ j, if τ * n < |cspEigenvalue F j| then
    cspEigenvalue F j * cspEigenvector F j α * cspEigenvector F j γ else 0

/-- `R = M − L` (p.43). -/
noncomputable def cspResidual {n : ℕ} (F : CSPInstance n) (τ : ℝ) :
    Matrix (Fin n × Bool) (Fin n × Bool) ℝ := cspMatrix F - cspRetained F τ

/-- `X = {z ∈ [0,1]^{[n]×{0,1}} : z_{i,0} + z_{i,1} = 1}` (p.42). -/
def fracAssignments (n : ℕ) : Set (Fin n × Bool → ℝ) :=
  {z | ∀ i, 0 ≤ z (i, false) ∧ 0 ≤ z (i, true) ∧ z (i, false) + z (i, true) = 1}

/-- The quadratic form `zᵀ B z`. -/
def cspQuad {n : ℕ} (B : Matrix (Fin n × Bool) (Fin n × Bool) ℝ) (z : Fin n × Bool → ℝ) : ℝ :=
  ∑ α, ∑ γ, z α * B α γ * z γ

/-- `P B P` for `P = diag(ξ)` with the same selector `ξ_i` on both label coordinates of variable
`i` (p.43); `Q = {i : ξ_i = 1}`. -/
noncomputable def cspRestrict {n : ℕ} (Q : Finset (Fin n))
    (B : Matrix (Fin n × Bool) (Fin n × Bool) ℝ) : Matrix (Fin n × Bool) (Fin n × Bool) ℝ := by
  classical
  exact fun α γ => if α.1 ∈ Q ∧ γ.1 ∈ Q then B α γ else 0

/-- `sup_{z ∈ X} |zᵀ B z|` (attained: `X` is compact and nonempty). -/
noncomputable def cspAbsSup {n : ℕ} (B : Matrix (Fin n × Bool) (Fin n × Bool) ℝ) : ℝ :=
  sSup ((fun z => |cspQuad B z|) '' fracAssignments n)

/-- `max_{z ∈ X} zᵀ B z` over the full fractional set (attained: `X` is compact and nonempty). -/
noncomputable def cspMax {n : ℕ} (B : Matrix (Fin n × Bool) (Fin n × Bool) ℝ) : ℝ :=
  sSup (cspQuad B '' fracAssignments n)

/-- `K = {n⁻¹ ∑_{i,a} z_{i,a} y_{i,a} : z ∈ X}` (p.45), for arbitrary vectors `y_{i,a}`. -/
def cspPopulationSet {n d : ℕ} (y : Fin n × Bool → EuclideanSpace ℝ (Fin d)) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {w | ∃ z ∈ fracAssignments n, w = (n : ℝ)⁻¹ • ∑ α, z α • y α}

/-- `K_Q = {s⁻¹ ∑_{i,a} ξ_i z_{i,a} y_{i,a} : z ∈ X}` (p.45). -/
noncomputable def cspSampledSet {n d : ℕ} (y : Fin n × Bool → EuclideanSpace ℝ (Fin d)) (s : ℝ)
    (Q : Finset (Fin n)) : Set (EuclideanSpace ℝ (Fin d)) := by
  classical
  exact {w | ∃ z ∈ fracAssignments n, w = s⁻¹ • ∑ α ∈ Finset.univ.filter (fun α => α.1 ∈ Q), z α • y α}

/-- `Δ = d_H(K_Q, K)` (p.45), Euclidean Hausdorff distance. -/
noncomputable def cspSampleDistance {n d : ℕ} (y : Fin n × Bool → EuclideanSpace ℝ (Fin d)) (s : ℝ)
    (Q : Finset (Fin n)) : ℝ :=
  Metric.hausdorffDist (cspSampledSet y s Q) (cspPopulationSet y)

/-- `t_y = n⁻¹ ∑_{i,a} ‖y_{i,a}‖²` (p.45): summed over both labels, divided by `n`. -/
noncomputable def cspEnergy {n d : ℕ} (y : Fin n × Bool → EuclideanSpace ℝ (Fin d)) : ℝ :=
  (∑ α, ‖y α‖ ^ 2) / n

/-! Operational RAM extension for Algorithm 2 (p.42; RAM convention of p.28). The published
`Command`/`RAMState`/`ramStep` are reused unchanged for every non-query instruction; only the
query instruction is reinterpreted: one oracle call writes the full truth-table membership mask
of the queried pair into a natural-number register. -/

/-- One charged RAM transition with a MAX-2CSP pair oracle. -/
noncomputable def cspStep {L : ℕ} (oracle : ℕ → ℕ → ℕ) (ω : RandomTape L) (st : RAMState) :
    RAMState :=
  match st.output, st.control with
  | none, Command.query dst u v :: tail =>
    { st with control := tail,
              natReg := Function.update st.natReg dst (oracle (st.natReg u) (st.natReg v)),
              queries := (st.natReg u, st.natReg v) :: st.queries }
  | _, _ => ramStep (fun _ _ => false) ω st

/-- `t` executed transitions (time is the number of transitions). -/
noncomputable def cspRun {L : ℕ} (oracle : ℕ → ℕ → ℕ) (ω : RandomTape L) (initial : RAMState) :
    ℕ → RAMState
  | 0 => initial
  | t + 1 => cspStep oracle ω (cspRun oracle ω initial t)

/-- Initial state of a program: natural register 0 holds `n`, real register 0 holds `ε`;
everything else, including memory, is zero, and no query has been made. -/
noncomputable def cspInitial (prog : List Command) (n : ℕ) (ε : ℝ) : RAMState where
  control := prog
  natReg := fun r => if r = 0 then n else 0
  realReg := fun r => if r = 0 then ε else 0
  memory := fun _ _ => 0
  randomCursor := 0
  randomParameters := []
  queries := []
  output := none

end MaxCutMatrix2027.Upper.Supplement


