-- Prove2me | Definitions.Def_NetUnrelDesign_Main_Interfaces
-- name    : NetUnrelDesign_Main_Interfaces
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:09:30.838237+00:00
-- url     : https://prove2.me/theorems/18d71ea4-dbc9-4dc6-bfac-8d0c6f0671bb
-- title:
--   Oracle interfaces of the paper, their validity and cost hypotheses, and input layouts
-- statement:
--   - **Unreliability oracle** $U(H;s,\beta)$ (§1.1). A query is a graph $H$ (vertex count, edge count, endpoints, failure probabilities) together with $s$ and $\beta$. The oracle is **valid** on a class of queries when, at each such well-formed query with probabilities in $[0,1]$, its answer lies within a factor $1\pm s$ of $u_H$ except on a tape set of measure at most $\beta$; at $u_H=0$ the answer must then be exactly $0$. Its **cost bound** $T$ on a class of queries says that every such call has expected cost at most $T$. The primitive accuracy is $\alpha=1/(8\sqrt n)$.
--   - **Marked source** (3.1). A query is a design $x$. The answer is a weight $Z$ and block labels whose kernel is the returned partition $\Pi$. Validity at $x$ means: $Z\ge0$ on every tape; $\mathbb E[Z\varphi(\Pi)]=\mathbb E_x[1_{K\ge2}\varphi(\Pi_x)]$ for every bounded $\varphi$ on partitions; and $\mathbb E Z^2\le C_Z u(x)^2$. A valid marked source is measurable and valid at every design $x\ge0$.
--   - **Separation oracle** for $K\subseteq\mathbb R^d$. At $y\in K$ it answers "member". At $y\notin K$ it returns $g\ne0$ with $\langle g,z\rangle\le\langle g,y\rangle$ for all $z\in K$.
--   - **Value/supergradient oracle** for $(P_0,\psi)$. At $y\notin P_0$ it returns a feasibility separator. At $y\in P_0$ it returns the exact value $\psi(y)$ and a supergradient $g$, that is, $\psi(z)\le\psi(y)+\langle g,z-y\rangle$ on $P_0$.
--   - **Candidate and value routines** (Lemma H.1). A candidate call returns a point or FAIL. A value call at a point $x$ (given by its address) returns a real number.
--   - Euclidean balls $\{y:\|y-c\|_2\le\rho\}$ and ellipsoids $c+\rho JB_2=\{c+Jv:\|v\|_2\le\rho\}$.
--   - **Input layouts.** An instance is written as the integer cells $n,m,k$ and the two endpoints of each edge, then the real cells $q^0$, $A$ (row-major) and $b$. Each theorem prepends its own parameters.
--
--   **Formalization Note.** A scalar query is the raw tuple $(n_H,m_H,\text{endpoints},\text{probabilities},s,\beta)$. Entries beyond $m_H$ are normalized to $0$, and a query with an endpoint out of range is malformed: the instruction then makes no call. Probabilities are "except on a set of measure at most $\beta$", which is the paper's "with probability at least $1-\beta$". Answers are written back into memory at the query's base address; the exact cells are listed in the module docstring.
-- source:
--   Sun 2026, Fast Approximation Algorithms for Minimizing Network Unreliability, doi:10.5281/zenodo.23914978 (PDF sha256 1120f100…), §1.1 (p. 2, PDF 3: U(H; s, β), T_U); (3.1) (p. 9, PDF 10); Theorem 5.2 and Lemma 5.3 (p. 17, PDF 18); Lemma H.1 (p. 55, PDF 56); App. A.1 (p. 21, PDF 22: α = 1/(8√n))

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelDesign_Main_Machine

open scoped BigOperators ENNReal Classical

noncomputable section

namespace NetUnrelDesign.Main

/-!
# The oracle interfaces of the paper, their validity and cost hypotheses, and the input layouts

Mu-Xia Sun, *Fast Approximation Algorithms for Minimizing Network Unreliability* (2026),
doi:10.5281/zenodo.23914978: the unreliability oracle `U(H; s, β)` and `T_U` (§1.1, p. 2, PDF 3),
marked estimates (3.1) (§3.1, p. 9, PDF 10), separation and value/supergradient queries
(Theorem 5.2, Lemma 5.3, p. 17, PDF 18), candidate and value routines (Lemma H.1, p. 55, PDF 56).

**Scalar unreliability oracle.** A query is the raw tuple `(n_H, m_H, endpoints, probabilities, s, β)`
(`ScalarQuery`); it is well formed when every endpoint of an edge `i < m_H` is `< n_H`, and then
`ScalarQuery.graph` is its multigraph on `Fin n_H` and `ScalarQuery.target` its unreliability `u_H`.
In memory at base address `b`: integer cells `b` (`n_H`), `b+1` (`m_H`), `b+2+2i`, `b+3+2i` (the
endpoints of edge `i`); real cells `b` (`s`), `b+1` (`β`), `b+2+i` (the failure probability of edge
`i`). A query with a negative count or an endpoint out of range is malformed. Entries beyond `m_H` are
normalized to `0`. The answer is written to real cell `b`.
`ScalarValidOn good O`: at every well-formed query with probabilities in `[0,1]` that satisfies
`good`, the answer is within a factor `1 ± s` of `u_H` except on a tape set of measure at most `β`
(at `u_H = 0` the answer must be exactly `0`). `ScalarCostOn good T O`: the expected cost at every
such query is at most `T`.

**Marked source** for a network `(G, q⁰)` with `n` vertices and `m` edges. A query is a design
`x ∈ ℝ^m` at real cells `b, …, b+m−1`. The answer is a weight `Z` (real cell `b`) and integer block
labels `ℓ_v` of the vertices (integer cells `b+v`); the returned partition `Π` is the kernel of the
labelling (`Setoid.ker`). `MarkedValidAt CZ O x` is (3.1) at the design `x`: `Z ≥ 0` on every tape,
`E[Zφ(Π)] = E_x[1_{K≥2} φ(Π_x)]` for every bounded `φ` on partitions, and `E Z² ≤ C_Z u(x)²`.

**Separation and value/supergradient oracles** in `ℝ^d`: a query is a point `y` (real cells
`b, …, b+d−1`). A separation answer is a flag (integer cell `b`: `1` = `y ∈ K`) and a vector `g`
(real cells `b, …`) with `g ≠ 0` and `⟨g, z⟩ ≤ ⟨g, y⟩` for all `z ∈ K` when `y ∉ K`. A
value/supergradient answer is a flag (`1` = feasible), a value (real cell `b + d`) and a vector:
for `y ∉ P₀` a feasibility separator; for `y ∈ P₀` the exact value `ψ(y)` and a supergradient
`g` (`ψ(z) ≤ ψ(y) + ⟨g, z − y⟩` for all `z ∈ P₀`).

**Candidate and value routines** of Lemma H.1 for points of `ℝ^m`. Query `(false, 0)` is a candidate
call (integer cell `b` = `0`); query `(true, x)` is a value call at the point `x` stored at real cells
`p, …, p+m−1` where `p` is integer cell `b+1` (integer cell `b` = `1`). The answer is a flag
(integer cell `b`: `1` = a point was returned, `0` = FAIL), a point (real cells `b, …, b+m−1`) and a
value (real cell `b+m`).

**Input layouts.** An instance is written as integer cells `[n, m, k, u₀, v₀, u₁, v₁, …]` (the
endpoints of each edge) and real cells `q⁰` (m cells), `A` row-major (`k·m` cells), `b` (`k` cells).
Each theorem prepends its own parameters as described at its layout definition.
-/

/-! ## Scalar unreliability oracle -/

/-- A raw scalar query `(n_H, m_H, endpoints, failure probabilities, s, β)`. -/
abbrev ScalarQuery := ℕ × ℕ × (ℕ → ℕ × ℕ) × (ℕ → ℝ) × ℝ × ℝ

/-- Number of vertices of the query graph. -/
def ScalarQuery.nV (q : ScalarQuery) : ℕ := q.1
/-- Number of edges of the query graph. -/
def ScalarQuery.nE (q : ScalarQuery) : ℕ := q.2.1
/-- Raw endpoints. -/
def ScalarQuery.endsRaw (q : ScalarQuery) : ℕ → ℕ × ℕ := q.2.2.1
/-- Raw failure probabilities. -/
def ScalarQuery.probs (q : ScalarQuery) : ℕ → ℝ := q.2.2.2.1
/-- Requested relative accuracy `s`. -/
def ScalarQuery.acc (q : ScalarQuery) : ℝ := q.2.2.2.2.1
/-- Requested failure probability `β`. -/
def ScalarQuery.fail (q : ScalarQuery) : ℝ := q.2.2.2.2.2

/-- Every endpoint of every edge is a vertex. -/
def ScalarQuery.WellFormed (q : ScalarQuery) : Prop :=
  ∀ i < q.nE, (q.endsRaw i).1 < q.nV ∧ (q.endsRaw i).2 < q.nV

/-- The multigraph of a well-formed query. -/
def ScalarQuery.graph (q : ScalarQuery) (h : q.WellFormed) : Ends q.nV q.nE :=
  fun i => (⟨(q.endsRaw i).1, (h i i.2).1⟩, ⟨(q.endsRaw i).2, (h i i.2).2⟩)

/-- The failure probabilities of the query graph. -/
def ScalarQuery.probVec (q : ScalarQuery) : Fin q.nE → ℝ := fun i => q.probs i

/-- The probabilities are in `[0,1]`. -/
def ScalarQuery.ProbsOK (q : ScalarQuery) : Prop := ∀ i < q.nE, 0 ≤ q.probs i ∧ q.probs i ≤ 1

/-- The unreliability `u_H` of a well-formed query graph. -/
def ScalarQuery.target (q : ScalarQuery) (h : q.WellFormed) : ℝ := unrel (q.graph h) q.probVec

/-- Read a scalar query at base address `b`. -/
def decodeScalar (mem : ℤ → ℝ) (ints : ℤ → ℤ) (b : ℤ) : Option ScalarQuery :=
  if 0 ≤ ints b ∧ 0 ≤ ints (b + 1) ∧ ∀ i : ℕ, i < (ints (b + 1)).toNat →
      0 ≤ ints (b + 2 + 2 * i) ∧ ints (b + 2 + 2 * i) < ints b ∧
      0 ≤ ints (b + 3 + 2 * i) ∧ ints (b + 3 + 2 * i) < ints b then
    some ((ints b).toNat, (ints (b + 1)).toNat,
      (fun i => if i < (ints (b + 1)).toNat then
        ((ints (b + 2 + 2 * i)).toNat, (ints (b + 3 + 2 * i)).toNat) else (0, 0)),
      (fun i => if i < (ints (b + 1)).toNat then mem (b + 2 + i) else 0), mem b, mem (b + 1))
  else none

/-- The scalar unreliability oracle interface. -/
abbrev scalarSpec : OracleSpec where
  Query := ScalarQuery
  Answer := ℝ
  measQ := inferInstance
  measA := inferInstance
  decode := decodeScalar
  encode := fun a mem ints b => (Function.update mem b a, ints)

/-- Validity on the queries satisfying `good`: measurable, and within a factor `1 ± s` of `u_H`
except with probability at most `β`. -/
def ScalarValidOn (good : ScalarQuery → Prop) (O : Oracle scalarSpec) : Prop :=
  OracleMeasurable scalarSpec O ∧
  ∀ (q : ScalarQuery) (h : q.WellFormed), q.ProbsOK → good q →
    uniformTape {ω' | ¬ |(O q ω').1 - q.target h| ≤ q.acc * q.target h} ≤ ENNReal.ofReal q.fail

/-- The expected cost of every call satisfying `good` is at most `T`. -/
def ScalarCostOn (good : ScalarQuery → Prop) (T : ℝ) (O : Oracle scalarSpec) : Prop :=
  ∀ q : ScalarQuery, q.WellFormed → q.ProbsOK → good q →
    ∫⁻ ω', ((O q ω').2 : ℝ≥0∞) ∂uniformTape ≤ ENNReal.ofReal T

/-- The query is at relative accuracy `s` and failure probability `β`. -/
def ScalarQuery.AtParams (s β : ℝ) (q : ScalarQuery) : Prop := q.acc = s ∧ q.fail = β

/-- The query graph has at most `m` edges and at most `n` vertices. -/
def ScalarQuery.Small (n m : ℕ) (q : ScalarQuery) : Prop := q.nV ≤ n ∧ q.nE ≤ m

/-- The query graph, with its probabilities, is an iterated deletion/contraction minor of
`(ends, q)` with inherited failure probabilities. -/
def ScalarQuery.MinorOf {n m : ℕ} (ends : Ends n m) (prob : Fin m → ℝ) (q : ScalarQuery) : Prop :=
  ∃ h : q.WellFormed, IsMinor ends prob (q.graph h) q.probVec

/-- The primitive accuracy `α = 1/(8√n)`. -/
def primAcc (n : ℕ) : ℝ := 1 / (8 * Real.sqrt n)

/-! ## Marked source -/

/-- Write the block labels at integer cells `b, …, b+n−1`. -/
def writeLabels {n : ℕ} (l : Fin n → ℤ) (ints : ℤ → ℤ) (b : ℤ) : ℤ → ℤ :=
  fun z => if h : b ≤ z ∧ z < b + n then l ⟨(z - b).toNat, by omega⟩ else ints z

/-- The marked-source interface for a graph with `n` vertices and `m` edges. -/
abbrev markedSpec (n m : ℕ) : OracleSpec where
  Query := Fin m → ℝ
  Answer := ℝ × (Fin n → ℤ)
  measQ := inferInstance
  measA := inferInstance
  decode := fun mem _ b => some fun e => mem (b + (e : ℕ))
  encode := fun a mem ints b => (Function.update mem b a.1, writeLabels a.2 ints b)

/-- The partition with the given block labels. -/
def partitionOfLabels {n : ℕ} (l : Fin n → ℤ) : Setoid (Fin n) := Setoid.ker l

/-- `φ` is bounded on partitions. -/
def BoundedFn {n : ℕ} (φ : Setoid (Fin n) → ℝ) : Prop := ∃ B : ℝ, ∀ π, |φ π| ≤ B

/-- (3.1) at the design `x` with constant `C_Z`. -/
def MarkedValidAt {n m : ℕ} (ends : Ends n m) (q0 : Fin m → ℝ) (CZ : ℝ)
    (O : Oracle (markedSpec n m)) (x : Fin m → ℝ) : Prop :=
  (∀ ω', 0 ≤ (O x ω').1.1) ∧
  (∀ φ : Setoid (Fin n) → ℝ, BoundedFn φ →
    ∫ ω', (O x ω').1.1 * φ (partitionOfLabels (O x ω').1.2) ∂uniformTape =
      expect (failProbAt q0 x) fun F => if Disconnected ends F then φ (partitionOf ends F) else 0) ∧
  ∫⁻ ω', ENNReal.ofReal ((O x ω').1.1 ^ 2) ∂uniformTape ≤
    ENNReal.ofReal (CZ * risk ends q0 x ^ 2)

/-- A valid marked source: measurable, and (3.1) with constant `C_Z` at every design `x ≥ 0`. -/
def MarkedValid {n m : ℕ} (ends : Ends n m) (q0 : Fin m → ℝ) (CZ : ℝ)
    (O : Oracle (markedSpec n m)) : Prop :=
  OracleMeasurable (markedSpec n m) O ∧ ∀ x : Fin m → ℝ, (∀ e, 0 ≤ x e) → MarkedValidAt ends q0 CZ O x

/-- The expected cost of a marked estimate at `x` is at most `Q`. -/
def MarkedCostAt {n m : ℕ} (Q : ℝ) (O : Oracle (markedSpec n m)) (x : Fin m → ℝ) : Prop :=
  ∫⁻ ω', ((O x ω').2 : ℝ≥0∞) ∂uniformTape ≤ ENNReal.ofReal Q

/-! ## Separation and value/supergradient oracles -/

/-- Read a point of `ℝ^d` at real cells `b, …, b+d−1`. -/
def readVec (d : ℕ) (mem : ℤ → ℝ) (b : ℤ) : Fin d → ℝ := fun i => mem (b + (i : ℕ))

/-- Write a vector of `ℝ^d` at real cells `b + off, …`. -/
def writeVec {d : ℕ} (v : Fin d → ℝ) (mem : ℤ → ℝ) (b : ℤ) : ℤ → ℝ :=
  fun z => if h : b ≤ z ∧ z < b + d then v ⟨(z - b).toNat, by omega⟩ else mem z

/-- Euclidean inner product on `ℝ^d`. -/
def dot {d : ℕ} (g y : Fin d → ℝ) : ℝ := ∑ i, g i * y i

/-- The separation interface in `ℝ^d`. -/
abbrev sepSpec (d : ℕ) : OracleSpec where
  Query := Fin d → ℝ
  Answer := Bool × (Fin d → ℝ)
  measQ := inferInstance
  measA := inferInstance
  decode := fun mem _ b => some (readVec d mem b)
  encode := fun a mem ints b => (writeVec a.2 mem b, Function.update ints b (if a.1 then 1 else 0))

/-- Every answer is a correct separation answer for `K`. -/
def SeparationValid {d : ℕ} (K : Set (Fin d → ℝ)) (O : Oracle (sepSpec d)) : Prop :=
  ∀ y ω', (y ∈ K → (O y ω').1.1 = true) ∧
    (y ∉ K → (O y ω').1.1 = false ∧ (O y ω').1.2 ≠ 0 ∧
      ∀ z ∈ K, dot (O y ω').1.2 z ≤ dot (O y ω').1.2 y)

/-- The value/supergradient interface in `ℝ^d`. -/
abbrev valSpec (d : ℕ) : OracleSpec where
  Query := Fin d → ℝ
  Answer := Bool × ℝ × (Fin d → ℝ)
  measQ := inferInstance
  measA := inferInstance
  decode := fun mem _ b => some (readVec d mem b)
  encode := fun a mem ints b =>
    (Function.update (writeVec a.2.2 mem b) (b + d) a.2.1,
      Function.update ints b (if a.1 then 1 else 0))

/-- Every answer is a feasibility separator off `P₀`, and the exact value with a supergradient
on `P₀`. -/
def ValueOracleValid {d : ℕ} (P0 : Set (Fin d → ℝ)) (ψ : (Fin d → ℝ) → ℝ)
    (O : Oracle (valSpec d)) : Prop :=
  ∀ y ω', (y ∉ P0 → (O y ω').1.1 = false ∧ (O y ω').1.2.2 ≠ 0 ∧
      ∀ z ∈ P0, dot (O y ω').1.2.2 z ≤ dot (O y ω').1.2.2 y) ∧
    (y ∈ P0 → (O y ω').1.1 = true ∧ (O y ω').1.2.1 = ψ y ∧
      ∀ z ∈ P0, ψ z ≤ ψ y + dot (O y ω').1.2.2 (z - y))

/-- Every call costs at most `S`. -/
def CostAtMost {I : OracleSpec} (S : ℝ) (O : Oracle I) : Prop := ∀ q ω', ((O q ω').2 : ℝ) ≤ S

/-- Closed Euclidean ball `{y : ‖y − c‖₂ ≤ ρ}`. -/
def eBall {d : ℕ} (c : Fin d → ℝ) (ρ : ℝ) : Set (Fin d → ℝ) := {y | ∑ i, (y i - c i) ^ 2 ≤ ρ ^ 2}

/-- The ellipsoid `c + ρ J B₂ = {c + Jv : ‖v‖₂ ≤ ρ}`. -/
def ellipsoid {d : ℕ} (c : Fin d → ℝ) (J : Matrix (Fin d) (Fin d) ℝ) (ρ : ℝ) : Set (Fin d → ℝ) :=
  {x | ∃ v : Fin d → ℝ, ∑ i, v i ^ 2 ≤ ρ ^ 2 ∧ x = c + J.mulVec v}

/-! ## Candidate and value routines (Lemma H.1) -/

/-- The routine interface for points of `ℝ^m`. -/
abbrev routineSpec (m : ℕ) : OracleSpec where
  Query := Bool × (Fin m → ℝ)
  Answer := Bool × (Fin m → ℝ) × ℝ
  measQ := inferInstance
  measA := inferInstance
  decode := fun mem ints b =>
    if ints b = 0 then some (false, fun _ => 0)
    else if ints b = 1 then some (true, readVec m mem (ints (b + 1))) else none
  encode := fun a mem ints b =>
    (Function.update (writeVec a.2.1 mem b) (b + m) a.2.2,
      Function.update ints b (if a.1 then 1 else 0))

/-- The candidate-call query. -/
def candQuery (m : ℕ) : Bool × (Fin m → ℝ) := (false, fun _ => 0)

/-! ## Input layouts -/

/-- Integer cells of an instance: `n, m, k`, then the endpoints of each edge. -/
def instInts {n m k : ℕ} (I : Instance n m k) : List ℤ :=
  [(n : ℤ), (m : ℤ), (k : ℤ)] ++
    (List.ofFn fun e : Fin m => [((I.ends e).1 : ℤ), ((I.ends e).2 : ℤ)]).flatten

/-- Real cells of an instance: `q⁰`, `A` row-major, `b`. -/
def instReals {n m k : ℕ} (I : Instance n m k) : List ℝ :=
  vecList I.q0 ++ matList I.A ++ vecList I.b

/-- Integer cells of a network: `n, m`, then the endpoints of each edge. -/
def graphInts {n m : ℕ} (ends : Ends n m) : List ℤ :=
  [(n : ℤ), (m : ℤ)] ++ (List.ofFn fun e : Fin m => [((ends e).1 : ℤ), ((ends e).2 : ℤ)]).flatten

end NetUnrelDesign.Main


