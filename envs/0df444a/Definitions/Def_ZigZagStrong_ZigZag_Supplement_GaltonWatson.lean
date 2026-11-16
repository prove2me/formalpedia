-- Prove2me | Definitions.Def_ZigZagStrong_ZigZag_Supplement_GaltonWatson
-- name    : ZigZagStrong_ZigZag_Supplement_GaltonWatson
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:14:04.028272+00:00
-- url     : https://prove2.me/theorems/592966de-ecac-4cfd-ba4e-25e3d7e9221a
-- title:
--   Unimodular Galton–Watson tree, return probabilities, limit laws and the support edge
-- statement:
--   Let $D$ be a probability law on the nonnegative integers, with **minimum degree** $\delta=\min\{d:P(D=d)>0\}$ and mean $\mu=\mathbb E D$. The **size-biased law** is
--   $$P(D^*=c)=\frac{c\,P(D=c)}{\mu}.$$
--   The **unimodular Galton–Watson tree** $T_D$ has a root with $D$ children, and every other vertex independently has $D^*-1$ children. It is coded by its child counts at every Ulam–Harris address (the list of child indices from the root), all independent.
--
--   For simple random walk $X$ on $T_D$ started at the root $r$ (each step to a uniformly chosen neighbour), $p_k(T_D,r)=P[X_k=r\mid X_0=r]$. A measure $\nu$ is a **limit law for $D$** when it is a probability measure on $[-1,1]$ with
--   $$\int x^k\,d\nu(x)=\mathbb E\,[p_k(T_D,r)]\qquad(k\ge0).$$
--   For a measure $\nu$, $\rho(\nu)=\max\{|x|:x\in\operatorname{supp}\nu\}$, and $b(x)=2\sqrt{x-1}/x$, so that $\rho_\delta=b(\delta)$ and the Cohen–Maor value is $b(\bar d)$. The file also defines the radius-$R$ neighbourhood of the root of $T_D$, the average degree $\bar d_n=N_n/n$, and the standing assumptions of §4 on a sequence of degree sequences $d(n)$: positive degrees, even total degree, a uniform degree bound $\Delta$, empirical degree distribution converging to $D$, and $\delta\ge2$.
--
--   These are the limiting objects of local convergence and of the limiting spectral law in §4.
--
--   **Formalization Note** The size-biased law is defined by normalizing $c\,P(D=c)$; its fallback branch is reached only when $\mu\in\{0,\infty\}$, which the standing assumptions exclude. Convergence of the empirical degree distribution is written as pointwise convergence of the frequencies $\#\{i:d_i=k\}/n\to P(D=k)$, which is convergence in distribution for laws on $\mathbb N$.
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), §4, pp. 15–16 (standing assumptions, $\mu$, $\delta$, $\bar d_n$), p. 17 Eq. (12) ($D^*$, $T_D$), p. 18 ($p_k$, Eq. (13), $\rho(\nu)$), p. 19 Eq. (14) ($\rho_\delta$).

import Definitions.Def_ZigZagStrong_ZigZag_Supplement_Configuration

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag.Supplement
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal

/-- `δ := min{d : P(D = d) > 0}`, the least degree charged by the law `D`. -/
def minDegree (D : PMF ℕ) : ℕ := sInf {d | D d ≠ 0}

/-- `μ := E D`, in `ℝ≥0∞`. -/
def meanDegree (D : PMF ℕ) : ℝ≥0∞ := ∑' c : ℕ, (c : ℝ≥0∞) * D c

open Classical in
/-- Eq. (12): the size-biased law `P(D* = c) = c P(D = c) / μ`. The `else` branch is reached only
when `μ ∈ {0, ∞}`, which the standing assumptions exclude. -/
def sizeBiased (D : PMF ℕ) : PMF ℕ :=
  if h : meanDegree D ≠ 0 ∧ meanDegree D ≠ ∞ then
    PMF.normalize (fun c : ℕ => (c : ℝ≥0∞) * D c) h.1 h.2
  else D

/-- Ulam–Harris coding of the unimodular Galton–Watson tree `T_D`: a configuration
`c : List ℕ → ℕ` gives the number of children of every potential vertex (an address, the list of
child indices along the path from the root `[]`). The coordinates are independent; the root has
`D` children and every other address has `D* - 1` children. -/
def gwLaw (D : PMF ℕ) : Measure (List ℕ → ℕ) :=
  Measure.infinitePi (fun a : List ℕ =>
    (if a = [] then D else (sizeBiased D).map (fun k => k - 1)).toMeasure)

/-- An address is a vertex of the tree coded by `c` when each child index along it is less than
the number of children of the corresponding ancestor. -/
def IsVertex (c : List ℕ → ℕ) (a : List ℕ) : Prop :=
  ∀ k (hk : k < a.length), a[k] < c (a.take k)

/-- Degree of a vertex in the tree: its children plus its parent (the root has no parent). -/
def treeDeg (c : List ℕ → ℕ) (a : List ℕ) : ℝ :=
  (c a : ℝ) + if a = [] then 0 else 1

/-- `walkMass c k a`: the probability that simple random walk on the tree coded by `c`, started
at the root, is at the address `a` at time `k` (each step uniform among the neighbours). -/
def walkMass (c : List ℕ → ℕ) : ℕ → List ℕ → ℝ
  | 0, a => if a = [] then 1 else 0
  | k + 1, a =>
      (match a.getLast? with
        | none => 0
        | some j => if j < c a.dropLast then walkMass c k a.dropLast / treeDeg c a.dropLast else 0) +
      ∑ i ∈ Finset.range (c a), walkMass c k (a ++ [i]) / treeDeg c (a ++ [i])

/-- `p_k(T, r) = P[X_k = r | X_0 = r]`. -/
def returnProb (c : List ℕ → ℕ) (k : ℕ) : ℝ := walkMass c k []

/-- Eq. (13): `ν` is a probability measure on `[-1, 1]` whose `k`-th moment is
`E[p_k(T_D, r)]` for every `k ≥ 0`. -/
def IsLimitLaw (D : PMF ℕ) (ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ ν (Set.Icc (-1 : ℝ) 1)ᶜ = 0 ∧
    ∀ k : ℕ, ∫ x, x ^ k ∂ν = ∫ c, returnProb c k ∂(gwLaw D)

/-- `b(x) := 2√(x - 1)/x`; `ρ_δ = b(δ)` (Eqs. (5), (14)) and the Cohen–Maor value is `b(d̄)`. -/
def edgeValue (x : ℝ) : ℝ := 2 * Real.sqrt (x - 1) / x

/-- `ρ(ν) := max{|x| : x ∈ supp ν}` (p. 18), as a supremum. -/
def supportEdge (ν : Measure ℝ) : ℝ := sSup ((fun x => |x|) '' ν.support)

/-- The tree's vertices at depth at most `R`, i.e. at distance at most `R` from the root. -/
def treeBall (c : List ℕ → ℕ) (R : ℕ) : Set (List ℕ) := {a | IsVertex c a ∧ a.length ≤ R}

open Classical in
/-- Tree adjacency: parent and child are joined by one edge. -/
def treeAdj (a b : List ℕ) : ℕ :=
  if (∃ i, b = a ++ [i]) ∨ (∃ i, a = b ++ [i]) then 1 else 0

/-- The radius-`R` neighbourhood of the root of the tree coded by `c`, rooted at the root. -/
def treeNbhd (c : List ℕ → ℕ) (R : ℕ) : RootedMultigraph where
  V := treeBall c R
  adj u w := treeAdj u.1 w.1
  root := ⟨[], fun k hk => absurd hk (Nat.not_lt_zero k), Nat.zero_le R⟩

/-- Average degree `d̄_n = N_n / n`. -/
def avgDegree {n : ℕ} (deg : Fin n → ℕ) : ℝ := (∑ i, (deg i : ℝ)) / (n : ℝ)

/-- The standing assumptions of §4 (pp. 15–16): positive degrees, even total degree for every
`n`, a uniform degree bound `Δ`, empirical degree distribution converging to `D` (pointwise, which
for laws on `ℕ` is convergence in distribution), and `δ ≥ 2`. -/
structure DegreeRegime (deg : ∀ n : ℕ, Fin n → ℕ) (D : PMF ℕ) : Prop where
  pos : ∀ n i, 0 < deg n i
  even : ∀ n, Even (∑ i, deg n i)
  bounded : ∃ Δ : ℕ, ∀ n i, deg n i ≤ Δ
  empirical : ∀ k : ℕ,
    Tendsto (fun n => (Nat.card {i : Fin n // deg n i = k} : ℝ) / (n : ℝ)) atTop (𝓝 (D k).toReal)
  min_deg : 2 ≤ minDegree D

end ZigZagStrong.ZigZag.Supplement


