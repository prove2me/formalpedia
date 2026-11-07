-- Prove2me | Definitions.Def_ContinualCounting_InTs
-- name    : ContinualCounting_InTs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:57.262828+00:00
-- url     : https://prove2.me/theorems/bdb40fd2-3a01-47b8-9d9e-5f06256054c0
-- title:
--   The subtree $\mathcal T^s$, the values $\sigma_{u,\tilde s_{d+1}}$ and the selections $\mathcal J,\{J_d\}$
-- statement:
--   Let $h$ be even and $s\in\{\ell,r\}^{h/2}$. $\mathcal T^s$ is the set of nodes $u$ of $\mathcal T$ whose path from the root descends, at every odd depth $2j-1$, to the left child if $s_j=\ell$ and to the right child if $s_j=r$; at even depths it may descend into both children. $\mathcal L(\mathcal T^s)$ is its leaf set. For a letter $a$, $\tilde a$ is the opposite letter, so that for $u$ at depth $2d$ the value $\sigma_{u,\tilde s_{d+1}}$ is $\sigma_{u,\ell}$ if $s_{d+1}=r$ and $\sigma_{u,r}$ if $s_{d+1}=\ell$.
--
--   A **selection** is a set $\mathcal J\subseteq\{0,\dots,h/2-1\}$ with $|\mathcal J|=h/4$, together with, for each $d\in\mathcal J$ with $d>0$, a set $J_d$ of $2^{d-1}$ of the $2^d$ nodes of $\mathcal T^s$ at depth $2d$, and $J_0=\{\rho\}$ if $0\in\mathcal J$.
--
--   These objects localize the weighted sum of residual noises to one large term.
--
--   **Formalization Note** $s$ is `Fin (h / 2) → Bool` with `true` for $r$; indices are $0$-based, so the step from depth $2j+1$ to $2j+2$ is `s j`, and `letter s d` is $s_{d+1}$.
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), §5, pp.22–23 (PDF pp.23–24)

import Mathlib
import Definitions.Def_ContinualCounting_Node
import Definitions.Def_ContinualCounting_sigmaL

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ContinualCounting

/-- **The subtree `T^s`.** Bairaktari, Dahl, Larsen, arXiv:2607.00876 (sha256 986e6426…), §5, p.22: "For a
string s ∈ {ℓ, r}^{h/2}, let T^s be the subset of T containing all nodes u for which the path from the
root to u satisfies that in every odd depth 2j − 1, the path to u descends to the left child if
s_j = ℓ and to the right child if s_j = r. For even levels, we allow descending into both children."

**Formalization Note.** `s : Fin (h / 2) → Bool`, with `true` for `r` and `false` for `ℓ`, and `0`-based
`j`: the step from depth `2j + 1` to depth `2j + 2` is `s j`. The bit of the path of `u = (D, k)` into
depth `D′` is `(k / 2^{D−D′}) % 2`, `1` meaning right. -/
def InTs (h : ℕ) (s : Fin (h / 2) → Bool) (u : Node) : Prop :=
  IsNode h u ∧ ∀ j : Fin (h / 2), 2 * j.val + 2 ≤ u.1 →
    (u.2 / 2 ^ (u.1 - (2 * j.val + 2))) % 2 = (if s j then 1 else 0)

instance (h : ℕ) (s : Fin (h / 2) → Bool) : DecidablePred (InTs h s) := fun u => by
  unfold InTs; infer_instance

/-- `{u ∈ T^s : d(u) = 2d}`. -/
def evenLevel (h : ℕ) (s : Fin (h / 2) → Bool) (d : ℕ) : Finset Node :=
  (nodes h).filter fun u => InTs h s u ∧ u.1 = 2 * d

/-- `L(T^s)`, the leaf indices of `T^s`. -/
def leavesTs (h : ℕ) (s : Fin (h / 2) → Bool) : Finset (Fin (2 ^ h)) :=
  Finset.univ.filter fun i => InTs h s (h, i.val)

/-- The letter `s_{d+1}` for `0`-based `d`, `true` meaning `r`. It is only read at `d < h / 2`. -/
def letter {h : ℕ} (s : Fin (h / 2) → Bool) (d : ℕ) : Bool :=
  if hd : d < h / 2 then s ⟨d, hd⟩ else false

/-- `σ_{u, s̃_{d+1}}` for `u` at depth `2d`: the opposite letter `ã` of `a` (p.22) gives `σ_{u,ℓ}` when
`s_{d+1} = r` and `σ_{u,r}` when `s_{d+1} = ℓ`. -/
noncomputable def sigmaTilde {h : ℕ} (ν : Measure (Fin (2 ^ h) → ℝ)) (s : Fin (h / 2) → Bool)
    (u : Node) : ℝ≥0∞ :=
  if letter s (u.1 / 2) then sigmaL ν u else sigmaR ν u

/-- **The selections `J`, `{J_d}`.** Bairaktari, Dahl, Larsen, arXiv:2607.00876 (sha256 986e6426…), §5,
pp.22–23: "consider choosing J ⊆ {0, . . . , h/2 − 1} as a subset of h/4 out of the h/2 choices for d …
for each d ∈ J with d > 0, choose a subset J_d of 2^{d−1} out of the 2^d nodes u ∈ T^s with d(u) = 2d.
If d = 0 is in J, then that corresponds to the root and we choose J_0 = {ρ}".

**Formalization Note.** `d = 0` is its own clause, so `2^{d−1}` is only read with `d > 0`. -/
def Admissible (h : ℕ) (s : Fin (h / 2) → Bool) (J : Finset ℕ) (Js : ℕ → Finset Node) : Prop :=
  J ⊆ Finset.range (h / 2) ∧ J.card = h / 4 ∧
    ∀ d ∈ J, Js d ⊆ evenLevel h s d ∧ (d = 0 → Js d = {root}) ∧
      (0 < d → (Js d).card = 2 ^ (d - 1))

end ContinualCounting


