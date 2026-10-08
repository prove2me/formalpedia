-- Prove2me | Definitions.Def_SelfScaledLongStep_AffinePot_Defs
-- name    : SelfScaledLongStep_AffinePot_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:39.175875+00:00
-- url     : https://prove2.me/theorems/1ac50ea2-01d4-469a-85ca-40f3676a98dd
-- title:
--   (6.4), (7.1), (7.15)–(7.17), §7.2 pp. 29–31 — projection into ker A, potential Φ(x; ζ), λ(ζ), s̃(λ), updated lower bound ζ⁺, direction p, K̄ and F̲
-- statement:
--   These definitions fix the objects of the affine potential-reduction method of Nesterov and Todd (§7.2), for the conic problem
--   $$\min\ \langle c, x\rangle \quad\text{s.t.}\quad Ax = b,\ x \in K,\qquad\qquad (P)$$
--   where $K \subseteq E$ is a self-scaled cone with $\nu$-self-scaled barrier $F$, $A : E \to Y^*$ is linear and surjective, and $(D)$ is the conic dual $\max\{\langle b, y\rangle : A^*y + s = c,\ s \in K^*\}$.
--
--   1. **Projection (6.4).** For $w \in \operatorname{int} K$ and $u \in E^*$, a pair $(y, p)$ is a projection pair of $u$ if
--   $$Ap = 0,\qquad A^*y + F''(w)p = u;$$
--   $p = p(u)$ is the projection of $u$ into $\ker A$ with respect to the positive definite operator $F''(w)$.
--   2. **Optimal value.** $\zeta^* = \inf\{\langle c, x\rangle : Ax = b,\ x \in K\}$.
--   3. **Primal potential (7.1).** For $\mu > 0$ and $\zeta \le \zeta^*$,
--   $$\Phi(x; \zeta) = \mu \ln(\langle c, x\rangle - \zeta) + F(x).$$
--   4. **Scaling (7.15).** At the current iterate $\hat x \in S^0(P)$, $\lambda(\zeta) = (\langle c, \hat x\rangle - \zeta)/\mu$.
--   5. **Dual slack (7.16).** With $p(c)$ and $p(d)$ the projections (7.12) of $c$ and of $d = F'(\hat x)$ at $w = \hat x$,
--   $$\tilde s(\lambda) = F''(\hat x)\big(p(c) + \lambda p(d)\big) - \lambda F'(\hat x),\qquad \lambda \in \mathbb R.$$
--   6. **Lower bound update (7.17).** The set of lower bounds $\{\langle c, \hat x\rangle - \langle \tilde s(\lambda), \hat x\rangle : \lambda \in \mathbb R,\ \tilde s(\lambda) \in K^*\}$, and
--   $$\zeta^+ = \max\Big(\hat\zeta,\ \sup_{\lambda:\ \tilde s(\lambda) \in K^*} \big(\langle c, \hat x\rangle - \langle \tilde s(\lambda), \hat x\rangle\big)\Big),$$
--   with $\zeta^+ = \hat\zeta$ when no $\lambda$ gives $\tilde s(\lambda) \in K^*$.
--   7. **Search direction.** $\lambda^+ = \lambda(\zeta^+)$ and $p = p(c) + \lambda^+ p(d)$.
--   8. **The set $\bar K$ and $\underline F$ (p. 29).** $\bar K = \{x \in K : Ax = b\tau,\ 0 \le \tau \le 1,\ \langle c, x\rangle \le \gamma_0\}$ with $\gamma_0 = \max(\langle c, x_0\rangle, 0) + 1$, and $\underline F$ the minimum of $F$ on $\bar K$.
--
--   These are the data of Theorems 7.3 and 7.4 and of Lemma 7.2.
--
--   **Formalization Note** $E$ and $E^*$ are both $\mathbb R^n$ (`EuclideanSpace ℝ (Fin n)`), identified through the inner product, and $Y^* = \mathbb R^m$. The paper takes $\hat\lambda$ as the minimal $\lambda$ with $\tilde s(\lambda) \in K^*$ and uses the value at $\hat\lambda$; since the gap $\langle \tilde s(\lambda), \hat x\rangle$ is nondecreasing in $\lambda$ (p. 31), that value is the supremum used here, which is also how the proof of Lemma 7.2 reads $\zeta^+$ ("the best lower bound that can be deduced from an $s$ of this form"). The supremum is genuine because each such value is the objective of a feasible dual point, hence at most $\zeta^*$; the empty case is the paper's "$-\infty$". $\underline F$ is the infimum of $F$ over $\bar K \cap \operatorname{int} K$, the set where the barrier is finite. $\zeta^*$ is an infimum of reals and is used only under (6.2)–(6.3), where it is finite.
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, pp. 22–23 (P), (6.4); p. 25 (7.1); pp. 29–31 K̄, F̲, (7.12)–(7.17)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_PrimalDual_Defs

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.AffinePot

/-- Optimal value `ζ*` of (P) `min {⟨c, x⟩ : A x = b, x ∈ K}` (§6, p. 22), as the infimum of the
objective over the feasible set. It is a genuine (finite, attained) value under (6.2)–(6.3);
every statement using it carries (6.3). -/
noncomputable def zetaStar {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (c : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sInf ((fun x => ⟪c, x⟫_ℝ) '' {x | x ∈ K ∧ A x = b})

/-- Primal potential (7.1), p. 25: `Φ(x; ζ) = µ ln(⟨c, x⟩ − ζ) + F(x)`. -/
noncomputable def affPotential {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (μ : ℝ)
    (c : EuclideanSpace ℝ (Fin n)) (ζ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  μ * Real.log (⟪c, x⟫_ℝ - ζ) + F x

/-- (7.15), p. 30: `λ(ζ) = (⟨c, x̂⟩ − ζ) / µ`. -/
noncomputable def lam {n : ℕ} (μ : ℝ) (c xh : EuclideanSpace ℝ (Fin n)) (ζ : ℝ) : ℝ :=
  (⟪c, xh⟫_ℝ - ζ) / μ

/-- (7.16), p. 30: `s̃(λ) = F''(x̂)(p(c) + λ p(d)) − λ F'(x̂)`, where `pc = p(c)` and
`pd = p(d)` are the projections (7.12) of `c` and of `d = F'(x̂)`. -/
noncomputable def sTilde {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (xh pc pd : EuclideanSpace ℝ (Fin n)) (t : ℝ) : EuclideanSpace ℝ (Fin n) :=
  hess F xh (pc + t • pd) - t • gradient F xh

/-- The lower bounds on `ζ*` obtainable from (7.16), p. 31: the values `⟨c, x̂⟩ − ⟨s̃(λ), x̂⟩`
over all real `λ` with `s̃(λ) ∈ K*`. -/
def dualBounds {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (c xh pc pd : EuclideanSpace ℝ (Fin n)) : Set ℝ :=
  {z | ∃ t : ℝ, sTilde F xh pc pd t ∈ ConvexOptimization.dualCone K ∧
    z = ⟪c, xh⟫_ℝ - ⟪sTilde F xh pc pd t, xh⟫_ℝ}

open Classical in
/-- Updated lower bound (7.17), p. 31: `ζ⁺ = max(ζ̂, ⟨c, x̂⟩ − ⟨s̃(λ̂), x̂⟩)`, with the second
argument `−∞` when no `λ` gives `s̃(λ) ∈ K*`. Written in best-lower-bound form: the second
argument is the supremum of `dualBounds`, which equals the value at the minimal `λ̂` because
the gap `⟨s̃(λ), x̂⟩` is nondecreasing in `λ` (p. 31). -/
noncomputable def zetaPlus {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (c xh pc pd : EuclideanSpace ℝ (Fin n)) (ζh : ℝ) : ℝ :=
  if (dualBounds K F c xh pc pd).Nonempty then max ζh (sSup (dualBounds K F c xh pc pd))
  else ζh

/-- Search direction of §7.2, p. 31: `p = p(c) + λ⁺ p(d)` with `λ⁺ = λ(ζ⁺)`. -/
noncomputable def affDir {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (μ : ℝ) (c xh pc pd : EuclideanSpace ℝ (Fin n))
    (ζh : ℝ) : EuclideanSpace ℝ (Fin n) :=
  pc + lam μ c xh (zetaPlus K F c xh pc pd ζh) • pd

/-- `K̄ = {x ∈ K : Ax = bτ, 0 ≤ τ ≤ 1, ⟨c, x⟩ ≤ γ₀ := max(⟨c, x₀⟩, 0) + 1}` (§7.2, p. 29). -/
def Kbar {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (c x0 : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | x ∈ K ∧ (∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ 1 ∧ A x = τ • b) ∧ ⟪c, x⟫_ℝ ≤ max ⟪c, x0⟫_ℝ 0 + 1}

/-- `F̲` (§7.2, p. 29): the minimum of the barrier `F` on `K̄`, taken over `K̄ ∩ int K`
(where `F` is finite). -/
noncomputable def FLow {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (c x0 : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sInf (F '' (Kbar K A b c x0 ∩ interior K))

end SelfScaledLongStep.AffinePot


