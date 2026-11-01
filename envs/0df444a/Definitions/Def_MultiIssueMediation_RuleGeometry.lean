-- Prove2me | Definitions.Def_MultiIssueMediation_RuleGeometry
-- name    : MultiIssueMediation_RuleGeometry
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:54.718495+00:00
-- url     : https://prove2.me/theorems/6b535a93-978e-4b4f-a193-7bc15ac74b63
-- title:
--   Value regions, diagonals, cell adjacency and the constructed relation $\triangleright_f$
-- statement:
--   Four devices of the proof of Theorem 1.
--
--   1. The **value region** of $f_{k,k}$ is the block of rows $\{k,\dots,m\}$ and columns $\{1,\dots,k\}$ (p.29).
--   2. The **$t$-th diagonal** is the set of cells with $\ell=j+t-1$; the main diagonal is $t=1$ (p.32).
--   3. **Adjacency at a cell** is $f_{\ell,j}\in\{f_{\ell-1,j},f_{\ell,j+1}\}\subset\mathbf B$.
--   4. For bundles $a,b\in\mathbf B$, $a\triangleright_f b$ means that $a\ne b$ and some cell with $\ell>j$ has neighbours $\{f_{\ell-1,j},f_{\ell,j+1}\}=\{a,b\}$ and value $f_{\ell,j}=a$ (Step 2, p.35).
--
--   These objects are used by the milestones and do not occur in Theorem 1.
--
--   **Formalization Note** The diagonal equation is written $\ell+1=j+t$ to avoid natural subtraction. The page omits $a\ne b$ in Step 2. Without it, equal neighbours give $a\triangleright a$ and Lemma 4 fails, and the proof of Lemma 4 speaks of diagonally adjacent, hence distinct, bundles.
-- source:
--   Kesten, Özyurt, Efficient and Incentive Compatible Mediation: An Ordinal Market Design Approach, working paper, 4 October 2018, p.29 (value region), p.32 (diagonals), Lemmas 2–3, pp.32–33, Step 2, pp.34–35

import Mathlib
import Definitions.Def_MultiIssueMediation_AdjacentRule

namespace MultiIssueMediation

/-- The cells of the value region `V(a)` of the bundle `a = f_{k,k}` (working paper of 4 October
2018, p.29): rows `M^k = {k, …, m}` and columns `M_k = {1, …, k}`. A cell is (row, column). -/
def valueRegion {m : ℕ} (k : Fin m) : Set (Fin m × Fin m) :=
  {c | k ≤ c.1 ∧ c.2 ≤ k}

/-- The cell `(ℓ, j)` lies on the `t`-th diagonal `{f_{t,1}, f_{t+1,2}, …, f_{m,m−t+1}}` (working
paper of 4 October 2018, p.32), that is `ℓ = j + t − 1`; the main diagonal is `t = 1`.

**Formalization Note.** The equation is written `ℓ + 1 = j + t` to avoid natural subtraction, and
holds with `Fin` values as well as with paper indices. -/
def OnDiagonal {m : ℕ} (t : ℕ) (ℓ j : Fin m) : Prop :=
  ℓ.val + 1 = j.val + t

/-- Adjacency at a cell: `f_{ℓ,j} ∈ {f_{ℓ−1,j}, f_{ℓ,j+1}} ⊂ B` (working paper of 4 October 2018,
Lemma 2, p.32, Lemma 3, p.33), where `p` is row `ℓ−1` and `q` is column `j+1`. -/
def AdjacentCell {m : ℕ} (f : MediationRule m) (ℓ j p q : Fin m) : Prop :=
  f p j ∈ logrollBundles m ∧ f ℓ q ∈ logrollBundles m ∧ (f ℓ j = f p j ∨ f ℓ j = f ℓ q)

/-- The relation `▷_f` constructed from a rule in Step 2 (working paper of 4 October 2018, p.35):
"`f_{ℓ−1,j} ▷ f_{ℓ,j+1}` whenever `f_{ℓ,j} = f_{ℓ−1,j}` and `f_{ℓ,j+1} ▷ f_{ℓ−1,j}` whenever
`f_{ℓ,j} = f_{ℓ,j+1}`": `a ▷_f b` iff `a ≠ b` and some cell with `ℓ > j` has the neighbours
`{f_{ℓ−1,j}, f_{ℓ,j+1}} = {a, b}` and value `f_{ℓ,j} = a`.

**Formalization Note.** The page omits `a ≠ b`. Without it the relation is reflexive at a bundle
whose two neighbours coincide, and Lemma 4 fails; the proof of Lemma 4 speaks of diagonally
adjacent bundles, so the two are distinct. The name keeps this relation apart from the order `▷`
of Theorem 1. -/
def derivedPrec {m : ℕ} (f : MediationRule m) (a b : logrollBundles m) : Prop :=
  a ≠ b ∧ ∃ ℓ j p q : Fin m, j < ℓ ∧ p.val + 1 = ℓ.val ∧ q.val = j.val + 1 ∧
    ((f p j = a ∧ f ℓ q = b) ∨ (f p j = b ∧ f ℓ q = a)) ∧ f ℓ j = a

end MultiIssueMediation


