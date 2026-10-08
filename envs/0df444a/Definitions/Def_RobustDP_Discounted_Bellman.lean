-- Prove2me | Definitions.Def_RobustDP_Discounted_Bellman
-- name    : RobustDP_Discounted_Bellman
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T08:44:25.579573+00:00
-- url     : https://prove2.me/theorems/a72b8904-db46-47e1-bcbb-6bab1454dd71
-- title:
--   Bounded functions, the L∞ norm, and the robust Bellman operators L_D of (22) and of (30)
-- statement:
--   Fix a discounted ambiguous MDP $(\mathcal S,\mathcal A,\mathcal P,r,\lambda)$. Let $\mathbf V$ be the set of bounded functions $V:\mathcal S\to\mathbb R$, with the norm $\|V\|=\sup_{s\in\mathcal S}|V(s)|$.
--
--   For $V:\mathcal S\to\mathbb R$, a state $s$ and an action $a$, the robust one-step value is
--   $$Q_V(s,a)=\inf_{p\in\mathcal P(s,a)}\mathbf E^p\big[r(s,a,s')+\lambda V(s')\big].$$
--   For a set $\mathcal D$ of deterministic Markov decision rules, the **robust Bellman operator** (22) is
--   $$\mathcal L_{\mathcal D}V(s)=\sup_{d\in\mathcal D}\ \inf_{p\in\mathcal P(s,d(s))}\mathbf E^p\big[r(s,d(s),s')+\lambda V(s')\big],\qquad s\in\mathcal S.$$
--   For state-wise sets $\mathcal D(s)\subseteq\mathcal A(s)$, the **product set** $\prod_{s\in\mathcal S}\mathcal D(s)$ consists of all rules $d$ with $d(s)\in\mathcal D(s)$ for every $s$. Finally, the operator of the optimality equation (30) is
--   $$\mathcal T V(s)=\sup_{a\in\mathcal A(s)}\ \inf_{p\in\mathcal P(s,a)}\mathbf E^p\big[r(s,a,s')+\lambda V(s')\big],$$
--   which is $\mathcal L_{\mathcal D}$ for $\mathcal D=\prod_s\mathcal A(s)$.
--
--   These are the operators of Theorem 5, Corollary 2 and Lemma 1.
--
--   **Formalization Note** The page writes $\|V\|=\max_{s}|V(s)|$; for a countable state space it is a supremum. The operators are defined on all functions $\mathcal S\to\mathbb R$, and every statement applies them to bounded functions, where every infimum and supremum is over a nonempty bounded family (for $\mathcal L_{\mathcal D}$, when $\mathcal D$ is nonempty). Boundedness is a predicate, not a subtype.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 9, the space V, the norm ‖·‖ and (22); p. 11, (30) and D = ∏_{s∈S} A(s)

import Mathlib
import Definitions.Def_RobustDP_Discounted_Model

namespace RobustDP.Discounted

variable {S A : Type*} [Countable S] [Countable A]

/-- `V ∈ 𝐕`: the function `V : S → ℝ` is bounded. -/
def IsBounded (V : S → ℝ) : Prop :=
  ∃ C : ℝ, ∀ s, |V s| ≤ C

/-- The `L∞` norm `‖V‖ = sup_{s ∈ S} |V(s)|` (written `max` on p. 9); meaningful for bounded `V`. -/
noncomputable def supNorm (V : S → ℝ) : ℝ :=
  ⨆ s, |V s|

/-- The robust one-step value of action `a` in state `s` against `V`:
`inf_{p ∈ P(s, a)} E^p[r(s, a, s') + λ V(s')]`. -/
noncomputable def Q (M : Model S A) (V : S → ℝ) (s : S) (a : A) : ℝ :=
  ⨅ p : M.P s a, RobustDP.FiniteHorizon.expect p.1 (fun s' => M.r s a s' + M.lam * V s')

/-- The robust Bellman operator (22) of a set `D` of deterministic Markov decision rules:
`L_D V(s) = sup_{d ∈ D} inf_{p ∈ P(s, d(s))} E^p[r(s, d(s), s') + λ V(s')]`. -/
noncomputable def L (M : Model S A) (D : Set (DecisionRule M)) (V : S → ℝ) (s : S) : ℝ :=
  ⨆ d : D, Q M V s (d.1.1 s)

/-- The product set `D = ∏_{s ∈ S} D(s)` of deterministic Markov decision rules: all `d` with
`d(s) ∈ D(s)` for every state `s`. -/
def productRules (M : Model S A) (Dset : S → Set A) : Set (DecisionRule M) :=
  {d | ∀ s, d.1 s ∈ Dset s}

/-- The right-hand side of the robust optimality equation (30):
`sup_{a ∈ A(s)} inf_{p ∈ P(s, a)} E^p[r(s, a, s') + λ V(s')]`. -/
noncomputable def T (M : Model S A) (V : S → ℝ) (s : S) : ℝ :=
  ⨆ a : M.Aset s, Q M V s a

end RobustDP.Discounted


