-- Prove2me | Definitions.Def_MaoLowDegree_Counterexample_rankTest
-- name    : MaoLowDegree_Counterexample_rankTest
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:07.168564+00:00
-- url     : https://prove2.me/theorems/9e7941d7-e53a-4b8c-bea9-4f8235cbec90
-- title:
--   Monomial lift, random puncturing, entropy conditions, and Algorithm 1
-- statement:
--   For $y\in\mathbb F_2^T$, the degree-$s$ monomial lift has coordinates $\Psi_s(y)_S=\prod_{i\in S}y_i$ for all $S\subseteq[T]$ with $|S|\le s$, including the empty product. A random puncturing is a uniform subset of the entire binary cube of the prescribed size. An impossible finite size has the explicit convention of a point mass at the empty set; the sizes in Lemma 3.1 are feasible.
--
--   Fix rational $a,\sigma>0$, set $T=\lfloor a\ell_n\rfloor$, $s=\lfloor\sigma\ell_n\rfloor$, and $N_0=\lfloor\sqrt n\rfloor$. The columns of $M_s(Y)$ are the lifts of the anchor-edge vectors to the next $N_0$ vertices. Algorithm 1 returns Null if $T+N_0>n$; otherwise it returns Planted exactly when
--   $$\operatorname{rank}_{\mathbb F_2}M_s(Y)<N_0.$$
--
--   The rank is the dimension of the actual binary column span. This mathematical rule does not supply a unit-cost rank instruction. Binary entropy is $h_2(u)=-u\log_2u-(1-u)\log_2(1-u)$ with $0\log_2 0=0$. The noise parameters are $\lambda=-\log_2(1-\varepsilon)$ and $\mu_n=N_0(1-\varepsilon)^T$. The condition predicates spell out all inequalities in Lemmas 3.3–3.5. `Puncturing` names the full arbitrary-degree-sequence probability limit of Lemma 3.1.
-- source:
--   Songtao Mao, STOC 2027 submission #509 (October 2026), §3.1–3.4, pp.11–14

import Definitions.Def_MaoLowDegree_Counterexample_construction

open Classical Filter
open scoped Topology
noncomputable section
set_option autoImplicit false

namespace MaoLowDegree.Counterexample

/-- Degree-s monomial lift, indexed by every allowed subset, including ∅. -/
def lift {T : ℕ} (s : ℕ) (y : Vec T) : Monomials T s → F₂ :=
  fun S => monomial S.val y

/-- Uniform subsets of prescribed size. The infeasible-size convention is the point mass
at ∅; for δ ∈ (0,1) and binomLE T s this branch is never needed. -/
def uniformSubset (T k : ℕ) : PMF (Finset (Vec T)) :=
  if h : k ≤ Fintype.card (Vec T) then
    PMF.uniformOfFinset ((Finset.univ : Finset (Vec T)).powersetCard k)
      (by simpa using (Finset.powersetCard_nonempty.mpr h))
  else PMF.pure ∅

def Puncturing (γ₀ : ℝ) : Prop :=
  ∀ s : ℕ → ℕ, Tendsto s atTop atTop →
    (∀ᶠ T : ℕ in atTop, (s T : ℝ) < γ₀ * T) →
    ∀ δ : ℝ, 0 < δ → δ < 1 →
      Tendsto (fun T => prob (uniformSubset T ⌊(1 - δ) * binomLE T (s T)⌋₊)
        (fun Z => LinearIndependent F₂ (fun z : Z => lift (s T) z.val))) atTop (nhds 1)

def binaryEntropy (u : ℝ) : ℝ := -u * log₂ u - (1 - u) * log₂ (1 - u)
def anchors (a : ℚ) (n : ℕ) : ℕ := ⌊(a : ℝ) * ell n⌋₊
def liftDegree (σ : ℚ) (n : ℕ) : ℕ := ⌊(σ : ℝ) * ell n⌋₊
def columns (n : ℕ) : ℕ := Nat.sqrt n

/-- Total adjacency lookup; out-of-range entries and diagonal entries are false. -/
def edgeAt {n : ℕ} (Y : Graph n) (i j : ℕ) : Bool :=
  if hi : i < n then
    if hj : j < n then
      if h : i ≠ j then Y (orderedEdge ⟨i,hi⟩ ⟨j,hj⟩ (by simpa using h)) else false
    else false
  else false

def liftedColumn {n : ℕ} (a σ : ℚ) (Y : Graph n) (j : Fin (columns n)) :
    Monomials (anchors a n) (liftDegree σ n) → F₂ :=
  lift (liftDegree σ n) (fun i => if edgeAt Y i.val (anchors a n + j.val) then 1 else 0)

/-- F₂ column rank, as the dimension of the actual column span. -/
def liftedRank {n : ℕ} (a σ : ℚ) (Y : Graph n) : ℕ :=
  Module.finrank F₂ (Submodule.span F₂ (Set.range (liftedColumn a σ Y)))

/-- Mathematical decision rule of Algorithm 1. Its machine realization remains a theorem
obligation: this definition does not declare rank to be one computational instruction. -/
def rankTest {n : ℕ} (a σ : ℚ) (Y : Graph n) : Bool :=
  if anchors a n + columns n > n then false else decide (liftedRank a σ Y < columns n)

def noiseExponent (ε : Rate) : ℝ := -log₂ (1 - ε.val)
def cleanMean (a : ℚ) (ε : Rate) (n : ℕ) : ℝ := columns n * (1 - ε.val) ^ anchors a n

def NullConditions (γ₀ : ℝ) (a σ : ℚ) : Prop :=
  0 < a ∧ 0 < σ ∧ 2 < (a : ℝ) ∧
    (σ : ℝ) / a < min γ₀ (1/2) ∧ (1/2 : ℝ) < a * binaryEntropy ((σ : ℝ) / a)

def PlantedConditions (r : ℕ) (b : ℝ) (a σ : ℚ) (ε : Rate) : Prop :=
  (r : ℝ) * σ / b < 1/2 ∧
    b * binaryEntropy ((r : ℝ) * σ / b) < 1/2 - a * noiseExponent ε

end MaoLowDegree.Counterexample


