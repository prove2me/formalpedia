-- Prove2me | Definitions.Def_DiagLinesLDT_Supplement_TotalDegreeStrategy
-- name    : DiagLinesLDT_Supplement_TotalDegreeStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:21:16.175195+00:00
-- url     : https://prove2.me/theorems/a49805f6-a60b-492c-9442-40507a022ad1
-- title:
--   Total-degree diagonal line-versus-point test, projective strategies, and polynomial decoders (Definitions 9.1–9.2)
-- statement:
--   Let $\mathbb F_q$ be a finite field and let $m\ge1$ and $d\ge0$. For a coordinate $i\in\{1,\ldots,m\}$, set
--
--   $$
--   V_i=\{v\in\mathbb F_q^m:v_{i+1}=\cdots=v_m=0\}.
--   $$
--
--   The **literal diagonal/general-line sampler** chooses $u\in\mathbb F_q^m$, $i\in\{1,\ldots,m\}$, and $v\in V_i$ independently and uniformly, and asks the affine line $\ell=\{u+tv:t\in\mathbb F_q\}$. The event $v=0$ is retained, producing the singleton $\ell=\{u\}$.
--
--   A legal answer on $\ell$ is a function $h:\ell\to\mathbb F_q$ induced by a univariate polynomial of degree at most $d$; every function on a singleton is legal. A projective strategy consists of a normalized bipartite state, projective point measurements for both provers, and fresh projective measurements indexed by these general-line answers.
--
--   The degree-$d$ **total-degree diagonal line-versus-point test** chooses, with probability $1/3$ each: Alice-point/Bob-line consistency, Alice-line/Bob-point consistency, or point self-consistency. Its acceptance probability is the corresponding average of the three acceptance indicators.
--
--   A function $g:\mathbb F_q^m\to\mathbb F_q$ is in $\operatorname{TotPoly}(m,q,d)$ when its unique reduced polynomial representative has total degree at most $d$. A total-degree polynomial measurement is a projective measurement indexed by these functions. For measurements $M^x,N^x$ on opposite subsystems, the probability-style inconsistency is the averaged disagreement mass
--
--   $$
--   \mathbb E_x\sum_{a\ne b}\langle\psi|M^x_a\otimes N^x_b|\psi\rangle.
--   $$
--
--   These definitions give the exact strategy, test, outcome class, point-value coarse-graining, and error convention used by Theorem 10.1.
--
--   **Formalization Note** Hilbert spaces are finite coordinate spaces over $\mathbb C$, operators are matrices, and Alice's tensor factor is on the left. Lines are point sets, not sampled tuples. A function is placed in $\operatorname{TotPoly}$ by exhibiting any representative of total degree at most $d$; reduction modulo $X_i^q-X_i$ cannot increase total degree, so this is equivalent to the paper's unique-reduced-representative definition. Projective measurements use the published `MIPRE.IsPVM`, which allows zero projections. The helper definitions are total at $m=0$, but every source-facing use, including Theorem 10.1, carries the paper's hypothesis $m\ge1$.
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), §9 and Definitions 9.1–9.2, pp.25–26

import Mathlib
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_DiagLinesLDT_reducedAcc

open Polynomial
open scoped Kronecker

namespace DiagLinesLDT.Supplement

set_option autoImplicit false

/-- The directions `V_i = {v : v_{i+1} = ... = v_m = 0}` of the literal diagonal sampler.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), §9, p.25.

**Formalization Note** Paper coordinates start at one, while `Fin m` starts at zero. Thus the paper's
condition `v_{i+1} = ... = v_m = 0` is `v j = 0` for every Lean index `j > i`. The zero direction is
retained. -/
def DiagDirection (F : Type*) [Field F] (m : ℕ) (i : Fin m) : Type _ :=
  {v : Fin m → F // ∀ j, i < j → v j = 0}

noncomputable instance diagDirectionFintype (F : Type*) [Field F] [Fintype F]
    (m : ℕ) (i : Fin m) : Fintype (DiagDirection F m i) :=
  have : Finite (Fin m → F) := inferInstance
  have : Finite (DiagDirection F m i) := Subtype.finite
  Fintype.ofFinite _

/-- The affine line `{u + t v : t ∈ F}`, allowing `v = 0` and hence singleton lines. -/
def generalLineThrough {F : Type*} [Field F] {m : ℕ} (u v : Fin m → F) : Set (Fin m → F) :=
  Set.range fun t : F => u + t • v

variable (F : Type*) [Field F] (m : ℕ) in
/-- A diagonal/general line question, represented by its set of points. Degenerate singleton lines
are included.

Source: Zhao, Fu, Yu, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), §9, p.25, and
Definition 9.1, p.26.

**Formalization Note** The question is the point set, not the sampled tuple `(u,i,v)`, so the prover
does not learn a distinguished point. -/
def GeneralLine : Type _ :=
  {ell : Set (Fin m → F) // ∃ u v, ell = generalLineThrough u v}

/-- The general line sampled from base point `u` and direction `v`. -/
def generalLineOf {F : Type*} [Field F] {m : ℕ} (u v : Fin m → F) : GeneralLine F m :=
  ⟨generalLineThrough u v, u, v, rfl⟩

/-- The sampled base point lies on its general line. -/
theorem self_mem_generalLineThrough {F : Type*} [Field F] {m : ℕ}
    (u v : Fin m → F) : u ∈ generalLineThrough u v :=
  ⟨0, by simp⟩

/-- A line answer is legal when it is induced by a univariate polynomial of degree at most `d`.

Source: Zhao, Fu, Yu, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), Definition 9.1,
p.26.

**Formalization Note** The existential parametrization makes legality independent of how the point
set was sampled. If the line is a singleton, taking `v = 0` and a constant polynomial makes every
function on it legal, exactly as stipulated in Definition 9.1. -/
def IsLegalGeneralAnswer {F : Type*} [Field F] {m : ℕ} (d : ℕ) (ell : GeneralLine F m)
    (h : ell.1 → F) : Prop :=
  ∃ (u v : Fin m → F), ell.1 = generalLineThrough u v ∧
    ∃ p : F[X], p.natDegree ≤ d ∧
      ∀ (t : F) (x : ell.1), (x : Fin m → F) = u + t • v → h x = p.eval t

/-- The finite outcome type of legal degree-at-most-`d` answers on a general line. -/
def GeneralAnswer {F : Type*} [Field F] {m : ℕ} (d : ℕ) (ell : GeneralLine F m) : Type _ :=
  {h : ell.1 → F // IsLegalGeneralAnswer d ell h}

noncomputable instance generalAnswerFintype {F : Type*} [Field F] [Fintype F] {m : ℕ}
    (d : ℕ) (ell : GeneralLine F m) : Fintype (GeneralAnswer d ell) :=
  have : Finite (ell.1 → F) := inferInstance
  have : Finite (GeneralAnswer d ell) := Subtype.finite
  Fintype.ofFinite _

/-- A function `F^m → F` has reduced total degree at most `d` when it is represented by a
multivariate polynomial of total degree at most `d`.

Source: Zhao, Fu, Yu, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), §9, p.25.

**Formalization Note** The paper phrases this using the unique representative whose degree in every
variable is at most `q-1`. Existence of an arbitrary representative of total degree at most `d` is
equivalent: reducing modulo `X_i^q-X_i` preserves the represented function and cannot increase total
degree. -/
def IsTotalDegreeFunction {F : Type*} [Field F] {m : ℕ} (d : ℕ) (g : (Fin m → F) → F) : Prop :=
  ∃ p : MvPolynomial (Fin m) F, p.totalDegree ≤ d ∧ ∀ u, MvPolynomial.eval u p = g u

/-- `TotPoly(m,q,d)`: functions represented by reduced polynomials of total degree at most `d`. -/
def TotalDegreeFunction (F : Type*) [Field F] (m d : ℕ) : Type _ :=
  {g : (Fin m → F) → F // IsTotalDegreeFunction d g}

noncomputable instance totalDegreeFunctionFintype (F : Type*) [Field F] [Fintype F]
    (m d : ℕ) : Fintype (TotalDegreeFunction F m d) :=
  have : Finite ((Fin m → F) → F) := inferInstance
  have : Finite (TotalDegreeFunction F m d) := Subtype.finite
  Fintype.ofFinite _

noncomputable instance totalDegreeFunctionDecidableEq (F : Type*) [Field F] [Fintype F]
    (m d : ℕ) : DecidableEq (TotalDegreeFunction F m d) :=
  Classical.decEq _

/-- A projective strategy for the total-degree diagonal line-versus-point test.

Source: Zhao, Fu, Yu, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), Definition 9.1,
p.26.

**Formalization Note** The finite-dimensional Hilbert spaces are `C^iotaA` and `C^iotaB`, operators
are matrices, and Alice's tensor factor is on the left. General-line measurements are fresh and are
indexed by line point sets, rather than reusing the base mission's axis-parallel strategy. -/
structure TotalDegreeStrategy (F : Type*) [Field F] (m d : ℕ) (iotaA iotaB : Type*) where
  state : iotaA × iotaB → ℂ
  pointA : (Fin m → F) → F → Matrix iotaA iotaA ℂ
  lineA : (ell : GeneralLine F m) → GeneralAnswer d ell → Matrix iotaA iotaA ℂ
  pointB : (Fin m → F) → F → Matrix iotaB iotaB ℂ
  lineB : (ell : GeneralLine F m) → GeneralAnswer d ell → Matrix iotaB iotaB ℂ

/-- Normalization and projectivity of a total-degree test strategy. Zero projections are permitted. -/
structure TotalDegreeStrategy.IsProjective {F : Type*} [Field F] [Fintype F] {m d : ℕ}
    {iotaA iotaB : Type*} [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    (S : TotalDegreeStrategy F m d iotaA iotaB) : Prop where
  state_norm : ∑ x, ‖S.state x‖ ^ 2 = 1
  pointA_pvm : ∀ u, MIPRE.IsPVM (S.pointA u)
  lineA_pvm : ∀ ell, MIPRE.IsPVM (S.lineA ell)
  pointB_pvm : ∀ u, MIPRE.IsPVM (S.pointB u)
  lineB_pvm : ∀ ell, MIPRE.IsPVM (S.lineB ell)

/-- Probability-style disagreement mass for measurements on the two respective subsystems. -/
noncomputable def inconsistency {Ans iotaA iotaB : Type*}
    [Fintype Ans] [DecidableEq Ans] [Fintype iotaA] [Fintype iotaB]
    (psi : iotaA × iotaB → ℂ) (M : Ans → Matrix iotaA iotaA ℂ)
    (N : Ans → Matrix iotaB iotaB ℂ) : ℝ :=
  ∑ a, ∑ b, if a ≠ b then DiagLinesLDT.expect psi (M a) (N b) else 0

/-- The literal diagonal/general-line acceptance term with Alice asked the point and Bob the line. -/
noncomputable def diagPointLineAcc {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {m d : ℕ} {iotaA iotaB : Type*} [Fintype iotaA] [Fintype iotaB]
    (S : TotalDegreeStrategy F m d iotaA iotaB) : ℝ :=
  DiagLinesLDT.uniformAvg fun u : Fin m → F =>
    DiagLinesLDT.uniformAvg fun i : Fin m =>
      DiagLinesLDT.uniformAvg fun v : DiagDirection F m i =>
        let ell := generalLineOf u v.1
        ∑ h : GeneralAnswer d ell, ∑ a : F,
          if h.1 ⟨u, self_mem_generalLineThrough u v.1⟩ = a then
            DiagLinesLDT.expect S.state (S.pointA u a) (S.lineB ell h)
          else 0

/-- The literal diagonal/general-line acceptance term with Alice asked the line and Bob the point. -/
noncomputable def diagLinePointAcc {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {m d : ℕ} {iotaA iotaB : Type*} [Fintype iotaA] [Fintype iotaB]
    (S : TotalDegreeStrategy F m d iotaA iotaB) : ℝ :=
  DiagLinesLDT.uniformAvg fun u : Fin m → F =>
    DiagLinesLDT.uniformAvg fun i : Fin m =>
      DiagLinesLDT.uniformAvg fun v : DiagDirection F m i =>
        let ell := generalLineOf u v.1
        ∑ h : GeneralAnswer d ell, ∑ a : F,
          if h.1 ⟨u, self_mem_generalLineThrough u v.1⟩ = a then
            DiagLinesLDT.expect S.state (S.lineA ell h) (S.pointB u a)
          else 0

/-- Acceptance probability of the point self-consistency subtest. -/
noncomputable def totalDegreeSelfAcc {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {m d : ℕ} {iotaA iotaB : Type*} [Fintype iotaA] [Fintype iotaB]
    (S : TotalDegreeStrategy F m d iotaA iotaB) : ℝ :=
  DiagLinesLDT.uniformAvg fun u : Fin m → F =>
    ∑ a : F, ∑ b : F,
      if a = b then DiagLinesLDT.expect S.state (S.pointA u a) (S.pointB u b) else 0

/-- Acceptance probability of Definition 9.1: each of the two point-line orientations and point
self-consistency is chosen with probability `1/3`. -/
noncomputable def totalDegreeAcc {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {m d : ℕ} {iotaA iotaB : Type*} [Fintype iotaA] [Fintype iotaB]
    (S : TotalDegreeStrategy F m d iotaA iotaB) : ℝ :=
  (1 / 3) * diagPointLineAcc S + (1 / 3) * diagLinePointAcc S +
    (1 / 3) * totalDegreeSelfAcc S

/-- The point-value coarse-graining `G_[g(u)=a]`. -/
noncomputable def pointValue {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {m d : ℕ} {iota : Type*} [Fintype iota]
    (G : TotalDegreeFunction F m d → Matrix iota iota ℂ) (u : Fin m → F) (a : F) :
    Matrix iota iota ℂ :=
  ∑ g with g.1 u = a, G g

/-- The exponent `c0 = 1/40000` in Theorem 10.1. -/
noncomputable def c0 : ℝ := 1 / 40000

/-- The explicit error envelope in Theorem 10.1, with the proof's witness `C0 = 2000000`. -/
noncomputable def soundnessError (q m d : ℕ) (epsilon k : ℝ) : ℝ :=
  2000000 * (k + 1) ^ (2 : ℕ) * (m : ℝ) ^ (4 : ℕ) *
    (epsilon ^ c0 + ((d : ℝ) / (q : ℝ)) ^ c0 +
      Real.exp (-k / (2560000 * (m : ℝ) ^ (2 : ℕ))))

end DiagLinesLDT.Supplement


