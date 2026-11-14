-- Prove2me | Definitions.Def_KSATSingleFlip_Connect_Reconstruction
-- name    : KSATSingleFlip_Connect_Reconstruction
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T07:09:45.093101+00:00
-- url     : https://prove2.me/theorems/f9168f66-3be5-4925-aeb0-538f3128c1fe
-- title:
--   Random k-SAT exterior reconstruction observables
-- statement:
--   For a Boolean CNF formula, form the graph in which distinct variables are adjacent when they occur in a common clause. The exterior $B_r(v)$ consists of variables at distance at least $r$ from $v$, including disconnected variables. Let $p_v$ be the uniform-solution marginal at $v$ and let $q_{v,r}$ be the marginal after conditioning on the sampled exterior. These definitions give $p_v$, $q_{v,r}$, the expectation of $|q_{v,r}-p_v|$, the Bayes prediction error $\min(q_{v,r},1-q_{v,r})$, and the fixed-$r$ limit superior as the variable count tends to infinity. Formula, variable and solution are sampled as in Theorem 1.2; unsatisfiable formulas contribute zero.
-- source:
--   Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, paragraph preceding Theorem 1.2, printed p. 3 (PDF p. 5), STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_Model

noncomputable section
open scoped Classical BigOperators
open Filter
namespace KSATSingleFlip.Connect
open OAI.FixedClauseThreshold

/-- Variables are adjacent if they occur together in a clause. -/
def variableGraph {n : ℕ} (Φ : GFormula (Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => ∃ C ∈ Φ, u ∈ vbl C ∧ v ∈ vbl C

/-- Variables at graph distance at least r from v. Disconnected variables
have infinite distance and are included at every finite radius. -/
def exterior {n : ℕ} (Φ : GFormula (Fin n)) (v : Fin n) (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => ¬ (variableGraph Φ).Reachable v u ∨ r ≤ (variableGraph Φ).dist v u

/-- The uniform-solution marginal at v, with value 0 when the formula is unsatisfiable. -/
def vertexMarginal {n : ℕ} (Φ : GFormula (Fin n)) (v : Fin n) : ℝ :=
  (((sols Φ).filter fun x => x v = true).card : ℝ) / (numSols Φ : ℝ)

/-- Satisfying assignments agreeing with x on the exterior of the radius-r ball. -/
def exteriorFiber {n : ℕ} (Φ : GFormula (Fin n)) (v : Fin n) (r : ℕ)
    (x : Fin n → Bool) : Finset (Fin n → Bool) :=
  (sols Φ).filter fun y => ∀ u ∈ exterior Φ v r, y u = x u

/-- Conditional solution marginal after revealing the exterior, with zero
for an empty conditional fiber. -/
def exteriorPosterior {n : ℕ} (Φ : GFormula (Fin n)) (v : Fin n) (r : ℕ)
    (x : Fin n → Bool) : ℝ :=
  (((exteriorFiber Φ v r x).filter fun y => y v = true).card : ℝ) /
    ((exteriorFiber Φ v r x).card : ℝ)

/-- Average reconstruction signal over a uniform variable and uniform solution.
On an unsatisfiable formula, the empty uniform average is zero. -/
def reconstructionSignal {n : ℕ} (Φ : GFormula (Fin n)) (r : ℕ) : ℝ :=
  uexp fun v : Fin n => uexp fun x : {x // x ∈ sols Φ} =>
    |exteriorPosterior Φ v r x.1 - vertexMarginal Φ v|

/-- Average optimal 0–1 prediction error given the revealed exterior. -/
def reconstructionError {n : ℕ} (Φ : GFormula (Fin n)) (r : ℕ) : ℝ :=
  uexp fun v : Fin n => uexp fun x : {x // x ∈ sols Φ} =>
    min (exteriorPosterior Φ v r x.1) (1 - exteriorPosterior Φ v r x.1)

/-- Average signal at fixed k,n,α,r over the fixed-clause random k-SAT law. -/
def expectedReconstructionSignal (k n : ℕ) (α : ℝ) (r : ℕ) : ℝ :=
  uexp fun F : Formula n k ⌊α * n⌋₊ => reconstructionSignal (ofFormula F) r

/-- Average Bayes prediction error in the same model. -/
def expectedReconstructionError (k n : ℕ) (α : ℝ) (r : ℕ) : ℝ :=
  uexp fun F : Formula n k ⌊α * n⌋₊ => reconstructionError (ofFormula F) r

/-- The inner limit superior, first n→∞ with k, α, r fixed. -/
def reconstructionProfile (k : ℕ) (α : ℝ) (r : ℕ) : ℝ :=
  Filter.limsup (fun n => expectedReconstructionSignal k n α r) atTop

end KSATSingleFlip.Connect


