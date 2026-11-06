-- Prove2me | Definitions.Def_IntConeFPT_Problem
-- name    : IntConeFPT_Problem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:23.777703+00:00
-- url     : https://prove2.me/theorems/130ad9c5-a833-446d-984a-40076e4e9776
-- title:
--   The problem (♣): generators $(x,u)\in\mathbb Z^d\times\mathbb R^k$, feasibility, cost, unboundedness, discrete Jensen, certificates and correct outputs
-- statement:
--   A **generator** is a pair $(x,u)\in\mathbb Z^d\times\mathbb R^k$, and $S^{(t)}=P^{(t)}\cap(\mathbb Z^d\times\mathbb R^k)$, $X^{(t)}=P^{(t)}_x\cap\mathbb Z^d$. **Multiplicities** are finitely supported functions $\lambda^{(t)}:\mathbb Z^d\times\mathbb R^k\to\mathbb Z_{\ge0}$, one per type, supported in $S^{(t)}$. They define
--   $$
--   (y^{(t)},v^{(t)})=\sum_{(x,u)}\lambda^{(t)}_{(x,u)}(x,u),\qquad N^{(t)}=\sum_{(x,u)}\lambda^{(t)}_{(x,u)},\qquad
--   \mathrm{cost}(\lambda)=\sum_{t=1}^{\tau}\sum_{(x,u)}\lambda^{(t)}_{(x,u)}f^{(t)}(x).
--   $$
--   Then $\lambda$ is **feasible** for (♣) when $\sum_t(y^{(t)},v^{(t)})\in Q$ and $((y^{(t)},v^{(t)},N^{(t)}))_t\in\mathcal A$, and feasible subject to (1.1) when moreover $\sum_tN^{(t)}\le N_{\max}$. The instance is **unbounded below** when for every real $B$ some feasible $\lambda$ has cost below $B$.
--
--   A function $f$ on $X\subseteq\mathbb Z^d$ satisfies the **discrete Jensen inequality** (Assumption 3.1) when $f(x)\le\sum_i\theta_if(x_i)$ whenever $x\in X$ is a convex combination $x=\sum_i\theta_ix_i$ of points $x_i\in X$.
--
--   A **certificate** lists, for each type, entries $(x,u,\mu)$ with $x\in\mathbb Z^d$, $u\in\mathbb Q^k$, $\mu\in\mathbb N$. It is **well formed** when each type has at most $2^{2d+1}$ entries with pairwise distinct generators $(x,u)\in S^{(t)}$ and $\mu\ge1$. An **output** is *infeasible*, *unbounded*, or *optimal* $(y,v,\text{certificate})$. It is **correct** when, respectively, no feasible $\lambda$ exists; the instance is unbounded below; or the certificate is well formed, its multiplicities are feasible with total aggregate $(y,v)$, and its cost is at most that of every feasible $\lambda$. The variant relative to (1.1) uses feasibility subject to (1.1) and never accepts *unbounded*.
--
--   **Formalization Note** The continuous coordinates $u$ of generators are real: feasibility, optimality and unboundedness range over all real generators, while certificates are rational. Outputs are encoded with a tag symbol followed by the binary data.
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), §1 pp.2–4 ((♣), (1.1), Theorem 1), Assumption 3 p.6

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Instance

namespace IntConeFPT

open OnlineCRS.Combine

/-- **Generators `(x, u) ∈ Z^d × R^k`.**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), §1, p.2: "Write a generator as (x, u), where x ∈ Z^d
records integer choices and u ∈ R^k records fractional allocations."

**Formalization Note.** The continuous coordinates `u` are **real**: feasibility, optimality and
unboundedness of (♣) range over all real generators; only the returned certificate is rational. -/
abbrev Gen (d k : ℕ) : Type := (Fin d → ℤ) × (Fin k → ℝ)

/-- The generator `(x, u)` as a point of `R^d × R^k`. -/
def Gen.toReal {d k : ℕ} (g : Gen d k) : (Fin d → ℝ) × (Fin k → ℝ) :=
  (fun i => (g.1 i : ℝ), g.2)

/-- **`S = P ∩ (Z^d × R^k)`**, the generators of a set `P ⊆ R^{d+k}` (§1, p.2; Lemma 7, p.10). -/
def genSet {d k : ℕ} (P : Set ((Fin d → ℝ) × (Fin k → ℝ))) : Set (Gen d k) :=
  {g | g.toReal ∈ P}

/-- **The aggregate `Σ λ_(x,u) (x, u)`** of finitely supported nonnegative integer multiplicities
(§1, p.3, "(y^(t), v^(t)) := Σ λ^(t)_(x,u) (x, u)"). -/
def aggr {d k : ℕ} (μ : Gen d k →₀ ℕ) : (Fin d → ℝ) × (Fin k → ℝ) :=
  μ.sum fun g n => (n : ℝ) • g.toReal

/-- **The generator count `N = Σ λ_(x,u)`** (§1, p.3). -/
def count {d k : ℕ} (μ : Gen d k →₀ ℕ) : ℕ :=
  μ.sum fun _ n => n

/-- **The cost `Σ λ_(x,u) f(x)`** of multiplicities `μ` under a cost `f` of the integer block
(§1, p.3: "the cost of (x, u) is f^(t)(x)"). -/
def costOf {d k : ℕ} (f : (Fin d → ℝ) → ℝ) (μ : Gen d k →₀ ℕ) : ℝ :=
  μ.sum fun g n => (n : ℝ) * f (fun i => (g.1 i : ℝ))

/-- **Discrete Jensen inequality on `X ⊆ Z^d`** (Assumption 3.1, p.6): "For every x ∈ X^(t) and
every convex combination x = Σ_{i=1}^m θ_i x_i of points x_i ∈ X^(t), we have
f^(t)(x) ≤ Σ_{i=1}^m θ_i f^(t)(x_i)." -/
def DiscreteJensen {d : ℕ} (X : Set (Fin d → ℤ)) (f : (Fin d → ℤ) → ℝ) : Prop :=
  ∀ x ∈ X, ∀ (m : ℕ) (θ : Fin m → ℝ) (xs : Fin m → Fin d → ℤ),
    (∀ i, xs i ∈ X) → (∀ i, 0 ≤ θ i) → ∑ i, θ i = 1 →
    (fun j => (x j : ℝ)) = ∑ i, θ i • (fun j => (xs i j : ℝ)) →
    f x ≤ ∑ i, θ i * f (xs i)

/-- **Multiplicities of (♣)**: one finitely supported `λ^(t) : Z^d × R^k → Z≥0` per type. -/
abbrev Mult (I : Instance) : Type := (t : Fin I.τ) → Gen I.d I.k →₀ ℕ

namespace Instance

/-- **`S^(t) := P^(t) ∩ (Z^d × R^k)`** (§1, p.2). -/
def S (I : Instance) (t : Fin I.τ) : Set (Gen I.d I.k) := genSet (I.P t)

/-- **`X^(t) := P_x^(t) ∩ Z^d`** (§1, p.2). -/
def X (I : Instance) (t : Fin I.τ) : Set (Fin I.d → ℤ) :=
  {x | (fun i => (x i : ℝ)) ∈ I.Px t}

/-- `λ^(t)` is supported in `S^(t)` for every type. -/
def Supported (I : Instance) (μ : Mult I) : Prop :=
  ∀ t, (↑(μ t).support : Set (Gen I.d I.k)) ⊆ I.S t

/-- **The typewise aggregate and count `(y^(t), v^(t), N^(t))`** (§1, p.3). -/
def typeAgg (I : Instance) (μ : Mult I) (t : Fin I.τ) : (Fin I.d → ℝ) × (Fin I.k → ℝ) × ℝ :=
  ((aggr (μ t)).1, (aggr (μ t)).2, (count (μ t) : ℝ))

/-- **The total aggregate `Σ_t (y^(t), v^(t))`** (§1, p.3). -/
def totalAgg (I : Instance) (μ : Mult I) : (Fin I.d → ℝ) × (Fin I.k → ℝ) :=
  ∑ t, aggr (μ t)

/-- **The total count `Σ_t N^(t)`** ((1.1), p.4). -/
def totalCount (I : Instance) (μ : Mult I) : ℕ :=
  ∑ t, count (μ t)

/-- **The objective of (♣)**: `Σ_t Σ_{(x,u)∈S^(t)} λ^(t)_(x,u) f^(t)(x)` (p.3). -/
def cost (I : Instance) (μ : Mult I) : ℝ :=
  ∑ t, costOf (I.f t) (μ t)

/-- **Feasible multiplicities of (♣)** (p.3): supported in the `S^(t)`, with
`Σ_t (y^(t), v^(t)) ∈ Q` and `((y^(t), v^(t), N^(t)))_t ∈ A`. -/
def Feasible (I : Instance) (μ : Mult I) : Prop :=
  I.Supported μ ∧ I.totalAgg μ ∈ I.Q ∧ (fun t => I.typeAgg μ t) ∈ I.A

/-- **Feasible for (♣) subject to (1.1)**: feasible and `Σ_t N^(t) ≤ N_max` (p.4). -/
def FeasibleN (I : Instance) (Nmax : ℕ) (μ : Mult I) : Prop :=
  I.Feasible μ ∧ I.totalCount μ ≤ Nmax

/-- **(♣) is unbounded below**: for every real `B` some feasible `λ` has cost `< B`. In
particular an unbounded instance is feasible. -/
def Unbounded (I : Instance) : Prop :=
  ∀ B : ℝ, ∃ μ : Mult I, I.Feasible μ ∧ I.cost μ < B

end Instance

/-- **A certificate**: for each type a list of rational generators with multiplicities,
entries `(x, u, μ)` with `x ∈ Z^d`, `u ∈ Q^k`, `μ ∈ N` (Theorem 1, p.4: "a certificate consisting
of rational generators and integer multiplicities"). -/
abbrev Cert (I : Instance) : Type := Fin I.τ → List ((Fin I.d → ℤ) × (Fin I.k → ℚ) × ℕ)

/-- The generator `(x, u)` of a certificate entry, with `u` cast to `R^k`. -/
def certGen {d k : ℕ} (c : (Fin d → ℤ) × (Fin k → ℚ) × ℕ) : Gen d k :=
  (c.1, fun j => (c.2.1 j : ℝ))

/-- The multiplicities `λ` that a certificate describes. -/
noncomputable def certMult (I : Instance) (cert : Cert I) : Mult I :=
  fun t => ((cert t).map fun c => Finsupp.single (certGen c) c.2.2).sum

/-- **Well-formed certificate**: for each type at most `2^{2d+1}` entries, with pairwise distinct
generators `(x, u)`, positive multiplicities, and generators in `S^(t)` (Theorem 1, p.4: "with at
most 2^{2d+1} distinct generators per type"). -/
def CertOK (I : Instance) (cert : Cert I) : Prop :=
  ∀ t, (cert t).length ≤ 2 ^ (2 * I.d + 1) ∧
    ((cert t).map fun c => (c.1, c.2.1)).Nodup ∧
    ∀ c ∈ cert t, 1 ≤ c.2.2 ∧ certGen c ∈ I.S t

/-- **The three-way output of the algorithm of Theorem 1** (p.4): infeasible, unbounded below, or
an optimal aggregate `(y, v)` with a certificate. -/
inductive Output (I : Instance) where
  | infeasible
  | unbounded
  | optimal (y : Fin I.d → ℚ) (v : Fin I.k → ℚ) (cert : Cert I)

namespace Output

/-- **Correct output for (♣)** (Theorem 1, p.4).
1. `infeasible`: no feasible multiplicities exist;
2. `unbounded`: (♣) is unbounded below;
3. `optimal y v cert`: the certificate is well formed (`CertOK`), the multiplicities it describes
   are feasible, their aggregate `Σ_t (y^(t), v^(t))` equals `(y, v)`, and their cost is at most
   the cost of **every** feasible `λ` (real generators, no multiplicity bound). -/
def Correct {I : Instance} : Output I → Prop
  | infeasible => ¬ ∃ μ, I.Feasible μ
  | unbounded => I.Unbounded
  | optimal y v cert =>
      CertOK I cert ∧ I.Feasible (certMult I cert) ∧
      I.totalAgg (certMult I cert) = ((fun i => (y i : ℝ)), fun j => (v j : ℝ)) ∧
      ∀ μ, I.Feasible μ → I.cost (certMult I cert) ≤ I.cost μ

/-- **Correct output for (♣) subject to (1.1)** (Proposition 14, p.16): `infeasible` iff no
`λ` is feasible with `Σ_t N^(t) ≤ N_max`; `optimal` as in `Correct` but relative to (1.1);
`unbounded` is never correct. -/
def CorrectN {I : Instance} (Nmax : ℕ) : Output I → Prop
  | infeasible => ¬ ∃ μ, I.FeasibleN Nmax μ
  | unbounded => False
  | optimal y v cert =>
      CertOK I cert ∧ I.FeasibleN Nmax (certMult I cert) ∧
      I.totalAgg (certMult I cert) = ((fun i => (y i : ℝ)), fun j => (v j : ℝ)) ∧
      ∀ μ, I.FeasibleN Nmax μ → I.cost (certMult I cert) ≤ I.cost μ

end Output

/-- Binary encoding of an integer vector: each entry by `encInt`, followed by `3`. -/
def encIntVec {d : ℕ} (x : Fin d → ℤ) : List Sym :=
  (List.finRange d).flatMap fun i => encInt (x i) ++ [3]

/-- Binary encoding of a list of certificate entries `(x, u, μ)`: its length, then each entry
(`x` by `encIntVec`, `u` by `encVec`, `μ` by `encNat`), each followed by `3`. -/
def encCert {d k : ℕ} (c : List ((Fin d → ℤ) × (Fin k → ℚ) × ℕ)) : List Sym :=
  encNat c.length ++ [3] ++ c.flatMap fun e => encIntVec e.1 ++ encVec e.2.1 ++ encNat e.2.2 ++ [3]

/-- **Binary encoding of an output**: a tag (`0` infeasible, `1` unbounded, `2` optimal), then for
`optimal` the aggregate `(y, v)` and, type by type, the certificate. -/
def encOutput {I : Instance} : Output I → List Sym
  | .infeasible => [0]
  | .unbounded => [1]
  | .optimal y v cert => [2] ++ encVec y ++ encVec v ++ (List.finRange I.τ).flatMap fun t => encCert (cert t)

end IntConeFPT


