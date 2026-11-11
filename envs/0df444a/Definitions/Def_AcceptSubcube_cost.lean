-- Prove2me | Definitions.Def_AcceptSubcube_cost
-- name    : AcceptSubcube_cost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:32.097947+00:00
-- url     : https://prove2.me/theorems/4de0d3a6-f26a-43aa-a743-c11adfd6c27f
-- title:
--   Cost $C_{\mathcal I}(x)$, optimum, Hamming distance, ball optimum $\mathrm{OPT}_{\tau,r}$, induced cost, $D_j(n)$
-- statement:
--   For an instance $\mathcal I$ on $n$ variables and an assignment $x\in\{0,1\}^n$, the **cost** is the number of violated constraints,
--   $$C_{\mathcal I}(x)=\sum_E \mathbf 1[P_E(x_E)=0],$$
--   counted with multiplicity when scopes repeat. The **optimum** is $B=\mathrm{OPT}(\mathcal I)=\min_x C_{\mathcal I}(x)$. $\mathrm{dist}$ is Hamming distance, and for a center $\tau$ and radius $r$ the **ball optimum** is
--   $$\mathrm{OPT}_{\tau,r}=\min\{C_{\mathcal I}(x):\mathrm{dist}(x,\tau)\le r\}.$$
--   For a set $T$ of variables, the **induced cost** of an assignment on $T$ is the number of constraints whose scope lies inside $T$ and which it violates (§3.1). Finally $D_j(n)=\binom{n-j}{k-j}$ is the number of $k$-scopes containing a fixed $j$-set.
--
--   These quantities appear in every statement of the mission.
--
--   **Formalization Note** Both minima are over nonempty finite sets (all assignments; the ball contains $\tau$), so no junk value arises. $D_j(n)$ uses natural subtraction; it is used only for $j\le k$, and $n<j$ occurs only when there is no $k$-scope.
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), §2, p.9 (C_I, B = OPT, OPT_{τ,r}, dist, D_j(n)); §3.1, p.11 (induced cost)

import Mathlib
import Definitions.Def_AcceptSubcube_GInst

namespace AcceptSubcube

/-- **Cost** `C_I(x)`: the number of constraints violated by `x`.

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), §2, p.9: "C_I(x) = Σ_E 1[P_E(x_E) = 0]".

**Formalization Note.** Repeated scopes (allowed in Lemma 3.6) are counted with multiplicity. -/
def cost (I : GInst) (x : Fin I.n → Bool) : ℕ :=
  I.cons.countP (fun c => !evalTab c (extA x))

/-- **Optimum** `OPT(I) = B = min_x C_I(x)` (p.9). The minimum over the nonempty finite set of
assignments (nonempty also for `n = 0`). -/
def OPT (I : GInst) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (cost I)

/-- **Hamming distance** of two assignments (p.9). -/
def hdist {n : ℕ} (x y : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ y i)).card

/-- **Ball optimum** `OPT_{τ,r} = min{C_I(x) : dist(x, τ) ≤ r}` (p.9). The ball contains `τ`, so
the minimum is over a nonempty set. -/
def OPTball (I : GInst) (τ : Fin I.n → Bool) (r : ℕ) : ℕ :=
  (Finset.univ.filter (fun x => hdist x τ ≤ r)).inf' ⟨τ, by simp [hdist]⟩ (cost I)

/-- **Induced cost** on a variable set `T` (§3.1, p.11): "the number of constraints inside T that
it violates". `x` is read only on `T`. -/
def indCost (I : GInst) (T : Finset ℕ) (x : ℕ → Bool) : ℕ :=
  I.cons.countP (fun c => decide (c.1.toFinset ⊆ T) && !evalTab c x)

/-- `D_j(n) = (n − j choose k − j)` (p.9), the number of `k`-scopes containing a fixed `j`-set.

**Formalization Note.** Natural subtraction; it is used only for `j ≤ k`, and `n < j` happens only
when there is no `k`-scope at all (then every bound using it is trivially true). -/
def Dj (k j n : ℕ) : ℕ := (n - j).choose (k - j)

end AcceptSubcube


