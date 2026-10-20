-- Prove2me | Definitions.Def_ShapleyAttribution_UniqueUniform_Model
-- name    : ShapleyAttribution_UniqueUniform_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:43.897864+00:00
-- url     : https://prove2.me/theorems/fdb8a3e9-dd10-4154-8d59-91ebf612a217
-- title:
--   §2.1, §4.2–4.3, Proposition 1 — attribution model and its coalition, counterfactual, and path values
-- statement:
--   The attribution model equips the finite action-dependent chain with a designated no-ad action, denoted $1$ in the paper. Players are state-action pairs $\mathbb P=\mathbb S\times\mathbb A$. For a coalition $X\subseteq\mathbb P$, a pair in $X$ keeps its action; all other action mass takes the zero-value action and quits. For a set $Y$ of counterfactual players, its mass instead uses the no-ad transition row. The coalition value is the conversion probability
--
--   $$v(X,Y)=\lambda^\top(I-P^{X,Y})^{-1}p_c^{X,Y},\qquad v(X)=v(X,\varnothing).$$
--
--   A counterfactual model $\mathcal M_r$ changes player $r=(s,a)$ to the no-ad transition row while retaining its action frequency and identity. The Shapley value uses the published general Shapley definition and its coefficient $|X|!(mn-|X|-1)!/(mn)!$. CASV is the sum in display (5), replacing the absent-coalition value by $v(X,\{r\})$.
--
--   A converting path is a finite sequence of state-action pairs followed by conversion. Its probability includes the initial-state probability, each action frequency, intermediate transition probabilities, and the final conversion probability. Its unique-uniform weight is $1/u(\mathcal P)$ if $r$ appears, where $u$ counts distinct players; otherwise it is zero. Path expectation sums this weight against probabilities of all finite converting paths. These definitions connect the coalition game and the Markov path model.
--
--   **Formalization Note** `noAd` is a field rather than a fixed Lean index. The zero-value action is an exit rule, not a player. For $\mathcal M_r$, the relabelled row reading follows Appendix B, p. 46: the player retains its identity so its Shapley marginal is the counterfactual marginal. An ordinary inverse at a singular matrix has a junk value; theorem statements using $v$ carry the paper's absorption assumption. All values and path sums are real.
-- source:
--   Singal, Besbes, Desir, Goyal & Iyengar, Shapley Meets Uniform: An Axiomatic Framework for Attribution in Online Advertising, SSRN 3392721 (version of August 21, 2021), pp. 6–9, 12, 14–16, 20–22, 46, §2.1, §2.3, §3.3, §4.2–4.3, Assumption 1, displays (3)–(5), Proposition 1, Appendix B

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_ShapleyAttribution_UniqueUniform_ActionChain

namespace ShapleyAttribution.UniqueUniform

open Matrix Finset Filter Topology

/-- The paper's Markov attribution model adds a specified no-ad action to an
action-dependent finite chain. -/
structure Model (m n : ℕ) where
  chain : ActionChain m n
  noAd : Fin n

def Model.Valid {m n : ℕ} (M : Model m n) : Prop := M.chain.Valid
def Model.Pβ {m n : ℕ} (M : Model m n) : Matrix (Fin m) (Fin m) ℝ := M.chain.Pβ
def Model.Absorbing {m n : ℕ} (M : Model m n) : Prop := M.chain.Absorbing

/-- The transient matrix for a coalition: active players in `X` take their own
action, counterfactual players in `Y` take the no-ad row, and all other mass quits. -/
def Model.coalP {m n : ℕ} (M : Model m n)
    (X Y : Finset (Fin m × Fin n)) : Matrix (Fin m) (Fin m) ℝ :=
  fun s s' => ∑ a, ((if (s, a) ∈ X then M.chain.β s a * M.chain.P a s s' else 0) +
    (if (s, a) ∈ Y then M.chain.β s a * M.chain.P M.noAd s s' else 0))

/-- The conversion vector for a coalition. -/
def Model.coalPc {m n : ℕ} (M : Model m n)
    (X Y : Finset (Fin m × Fin n)) : Fin m → ℝ :=
  fun s => ∑ a, ((if (s, a) ∈ X then M.chain.β s a * M.chain.pc a s else 0) +
    (if (s, a) ∈ Y then M.chain.β s a * M.chain.pc M.noAd s else 0))

/-- Coalition conversion probability, with conversion worth one unit. -/
noncomputable def Model.val {m n : ℕ} (M : Model m n)
    (X Y : Finset (Fin m × Fin n)) : ℝ :=
  M.chain.lam ⬝ᵥ ((1 - M.coalP X Y)⁻¹ *ᵥ M.coalPc X Y)

/-- The counterfactual retains the player's action frequency and identity but
substitutes the no-ad transition row for that player's row. -/
def Model.cfModel {m n : ℕ} (M : Model m n) (r : Fin m × Fin n) : Model m n :=
  { chain := { M.chain with
      P := fun a s s' => if (s, a) = r then M.chain.P M.noAd s s' else M.chain.P a s s'
      pc := fun a s => if (s, a) = r then M.chain.pc M.noAd s else M.chain.pc a s
      pq := fun a s => if (s, a) = r then M.chain.pq M.noAd s else M.chain.pq a s }
    noAd := M.noAd }

/-- The Shapley coefficient in display (4), with `N` players and coalition size `k`. -/
noncomputable def weight (N k : ℕ) : ℝ :=
  (k.factorial * (N - k - 1).factorial : ℝ) / N.factorial

/-- Shapley value of the coalition conversion game, using the published general
Shapley value and the product-to-`Fin (m*n)` equivalence. -/
noncomputable def Model.shap {m n : ℕ} (M : Model m n)
    (r : Fin m × Fin n) : ℝ :=
  Supermodularity.Cooperative.ShapleyValue
    (fun Z : Finset (Fin (m * n)) => M.val (Z.map finProdFinEquiv.symm.toEmbedding) ∅)
    (finProdFinEquiv r)

/-- Counterfactual adjusted Shapley value, display (5). -/
noncomputable def Model.casv {m n : ℕ} (M : Model m n)
    (r : Fin m × Fin n) : ℝ :=
  ∑ X ∈ (univ.erase r).powerset,
    weight (m * n) X.card * (M.val (insert r X) ∅ - M.val X {r})

/-- Probability of conversion after the listed actions, conditional on the
first state, including all action choices and transitions. -/
def Model.convTail {m n : ℕ} (M : Model m n) : List (Fin m × Fin n) → ℝ
  | [] => 0
  | [(s, a)] => M.chain.β s a * M.chain.pc a s
  | (s, a) :: (s', a') :: rest =>
      M.chain.β s a * M.chain.P a s s' * M.convTail ((s', a') :: rest)

/-- Probability of the finite path and immediate conversion thereafter. -/
def Model.convProb {m n : ℕ} (M : Model m n) : List (Fin m × Fin n) → ℝ
  | [] => 0
  | (s, a) :: rest => M.chain.lam s * M.convTail ((s, a) :: rest)

/-- Number of distinct state-action pairs on a path. -/
def uniq {m n : ℕ} (path : List (Fin m × Fin n)) : ℕ := path.toFinset.card

/-- Unique-uniform weight on a converting path. Nonconverting paths are
excluded by `convProb` in the expectation. -/
noncomputable def wUU {m n : ℕ} (r : Fin m × Fin n)
    (path : List (Fin m × Fin n)) : ℝ :=
  if r ∈ path then 1 / (uniq path : ℝ) else 0

/-- Expectation of a path functional supported on converting paths. -/
noncomputable def Model.pathExp {m n : ℕ} (M : Model m n)
    (f : List (Fin m × Fin n) → ℝ) : ℝ :=
  ∑' path : List (Fin m × Fin n), M.convProb path * f path

end ShapleyAttribution.UniqueUniform


