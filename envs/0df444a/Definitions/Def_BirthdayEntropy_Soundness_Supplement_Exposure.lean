-- Prove2me | Definitions.Def_BirthdayEntropy_Soundness_Supplement_Exposure
-- name    : BirthdayEntropy_Soundness_Supplement_Exposure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:19:07.002451+00:00
-- url     : https://prove2.me/theorems/3f60c582-d908-4423-8171-67f04f16aa0a
-- title:
--   Disjoint violated families and oriented two-view exposure
-- statement:
--   Let $\Phi$ be an indexed Boolean exact-ternary CSP. A disjoint violated family for $g$ is a set $J$ of constraint indices such that $g$ violates each constraint and their three-variable scopes are pairwise disjoint. The promise is
--
--   $$\forall g\;\exists J:\quad |J|\ge\gamma n\quad\text{and }J\text{ is a disjoint violated family for }g.$$
--
--   Orient each selected scope as $(a_j,b_j,c_j)$ by an arbitrary permutation. For independent uniform views $S,T$, define
--
--   $$\alpha=\frac{\ell(\ell-1)}{n(n-1)},\quad\Lambda=|J|\alpha,\quad p_0=\frac\ell n\Lambda,\quad X=\sum_{j\in J}\mathbf1\{c_j\in S,\ a_j,b_j\in T\},\quad Y=X\mathbf1\{S,T\notin B\}.$$
--
--   Expectations and probabilities are finite sums over all ordered view pairs, divided by $\binom n\ell^2$. The bad-view set $B$ is arbitrary. Also define the selected distinct-nonedge probability by counting ordered distinct nonadjacent pairs divided by $|H|^2$; the diagonal contributes zero. These computed quantities support the additive soundness branch without changing the published graph or imposing a degree or nonisolation condition. Their theorem domains ensure positive denominators; outside those domains the raw normalized sums use Lean's total division convention.
-- source:
--   Alexandru Popa, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, Appendix B.1–B.3, PDF pp22–25 / printed pp21–24

import Mathlib
import Definitions.Def_BirthdayEntropy_Soundness_Graph

noncomputable section
open scoped Classical

namespace BirthdayEntropy.Soundness.Supplement

/-- Appendix B.1, PDF p22 / printed p21. The indexed violated family may depend on g. -/
def DisjointViolations {n m : ℕ} (φ : CSP n m) (g : Fin n → Bool)
    (J : Finset (Fin m)) : Prop :=
  (∀ j ∈ J, φ.f j (g ∘ φ.H.M j) = false) ∧
    ∀ j ∈ J, ∀ k ∈ J, j ≠ k → Disjoint (φ.H.verts j) (φ.H.verts k)

def DisjointViolationPromise {n m : ℕ} (φ : CSP n m) (γ : ℝ) : Prop :=
  ∀ g : Fin n → Bool, ∃ J : Finset (Fin m),
    DisjointViolations φ g J ∧ γ * n ≤ (J.card : ℝ)

/-- Every ordering of a scope is admitted, independently for each indexed constraint. -/
def oriented {n m : ℕ} (φ : CSP n m) (o : Fin m → Equiv.Perm (Fin 3))
    (j : Fin m) (r : Fin 3) : Fin n := φ.H.M j (o j r)

/-- Equation (28), PDF p22 / printed p21; real subtraction in both factors. -/
def alpha (n ℓ : ℕ) : ℝ :=
  ((ℓ : ℝ) * ((ℓ : ℝ) - 1)) / ((n : ℝ) * ((n : ℝ) - 1))

def exposureLambda {m : ℕ} (n ℓ : ℕ) (J : Finset (Fin m)) : ℝ :=
  J.card * alpha n ℓ

def exposureP0 {m : ℕ} (n ℓ : ℕ) (J : Finset (Fin m)) : ℝ :=
  ratio n ℓ * exposureLambda n ℓ J

def exposureX {n m ℓ : ℕ} (φ : CSP n m) (J : Finset (Fin m))
    (o : Fin m → Equiv.Perm (Fin 3)) (S T : View n ℓ) : ℝ :=
  (J.filter (fun j => oriented φ o j 2 ∈ S.val ∧
    oriented φ o j 0 ∈ T.val ∧ oriented φ o j 1 ∈ T.val)).card

/-- Equation (29): an adversarial bad-view set, without an independence assumption. -/
def exposureY {n m ℓ : ℕ} (φ : CSP n m) (J : Finset (Fin m))
    (o : Fin m → Equiv.Perm (Fin 3)) (B : Finset (View n ℓ))
    (S T : View n ℓ) : ℝ :=
  if S ∉ B ∧ T ∉ B then exposureX φ J o S T else 0

/-- Independent uniform draws from ALL views; used only where 2≤ell and ell²≤n. -/
def viewPairMean {n ℓ : ℕ} (F : View n ℓ → View n ℓ → ℝ) : ℝ :=
  (∑ S : View n ℓ, ∑ T : View n ℓ, F S T) / (Nat.choose n ℓ : ℝ)^2

def viewPairProb {n ℓ : ℕ} (P : View n ℓ → View n ℓ → Prop) : ℝ :=
  viewPairMean (fun S T => if P S T then 1 else 0)

/-- Distinct ordered nonedges only; the diagonal contributes zero. -/
def qbad {n m ℓ : ℕ} (φ : CSP n m) (H : Finset (Vertex n ℓ)) : ℝ :=
  ((H ×ˢ H).filter (fun vw => vw.1 ≠ vw.2 ∧ ¬ (graph φ).Adj vw.1 vw.2)).card /
    (H.card : ℝ)^2

end BirthdayEntropy.Soundness.Supplement


