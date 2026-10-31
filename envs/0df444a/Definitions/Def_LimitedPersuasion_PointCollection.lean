-- Prove2me | Definitions.Def_LimitedPersuasion_PointCollection
-- name    : LimitedPersuasion_PointCollection
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:24:43.086206+00:00
-- url     : https://prove2.me/theorems/61648e9b-d327-4a00-874b-c917707ccad8
-- title:
--   Recommendation points, point collections, Pareto frontier, slope correspondence and $s$-Pareto collections (Definition 1)
-- statement:
--   This module defines the geometric objects of §3.1 of the paper, for an instance with $n$ actions and $k\le n$ signals.
--
--   1. **Types of the first $k$ actions** (p.6). For a state $\boldsymbol\theta$, $C(\boldsymbol\theta)=\bigcup_{i\in[k]}\{\theta_i\}$, and for a finite set $C$ of types
--   $$q_C=\Pr\Big[\bigcup_{i\in[k]}\{\theta_i\}=C\Big].$$
--   2. **Points of $C$.** Type $t$ is the point $(\varrho(t),\xi(t))$ of the plane (receiver coordinate first).
--   3. **Recommendation point** (p.6). For a direct scheme $\varphi$ in which signal $j$ recommends action $j\in[k]$, and $q_C>0$, the recommendation point of $C$ is $(\mathbb E[u_R(\varphi)\mid C],\mathbb E[u_S(\varphi)\mid C])$, the conditional expected utilities when the receiver follows the recommendation:
--   $$p(C)=\frac1{q_C}\sum_{\boldsymbol\theta:\,C(\boldsymbol\theta)=C}q_{\boldsymbol\theta}\sum_{j\in[k]}\varphi(\boldsymbol\theta,j)\,\big(\varrho(\theta_j),\xi(\theta_j)\big).$$
--   4. **Point collection** (p.6). A map $C\mapsto p(C)=(p_R(C),p_S(C))$ with $p(C)$ in the convex hull of the points of $C$, with utilities
--   $$u_S(\mathcal P)=\sum_C q_C\,p_S(C),\qquad u_R(\mathcal P)=\sum_C q_C\,p_R(C).$$
--   5. **Pareto frontier** (p.6). A point $p$ is on the Pareto frontier of $C$ if it lies in the convex hull of $C$ and no point of the hull is strictly larger in both coordinates. So the frontier starts at a type with largest sender utility with a horizontal segment (possibly of length 0) and ends at a type with largest receiver utility with a vertical segment (possibly of length 0).
--   6. **Slope** (p.6). A point $p$ of the hull corresponds to slope $s$ if the line of slope $s$ through $p$ lies tangent to the frontier, i.e. $x_S-s\,x_R\le p_S-s\,p_R$ for every point $x$ of the hull.
--   7. **$s$-Pareto (Definition 1, p.6).** For $s\le0$, a point collection $\mathcal P$ is $s$-Pareto if (1) for every $C$, $p(C)$ is on the Pareto frontier of $C$ and corresponds to slope $s$, and (2) $u_R(\mathcal P)\ge\varrho_E$.
--
--   Theorem 1 characterizes an optimal scheme through these collections.
--
--   **Formalization Note** Sets of types are finite sets `Finset T`; a point collection is any map from them to $\mathbb R^2$, and the hull, frontier and slope conditions are required for the sets $C$ with $q_C\neq0$ (the sets that occur). The recommendation point is used only where $q_C\ne0$. "Tangent with slope $s$" is formalized as the supporting-line inequality over the whole hull, which for $s\le0$ is the same as tangency to the Pareto frontier; for $s=0$ every point of the top edge of the hull corresponds to the slope, as in the paper's picture. Slope $-\infty$ is not part of Definition 1 ("For $s\le0$") and is not formalized; §3.2 works with slopes in $[0,-\infty)$.
-- source:
--   Gradwohl–Hahn–Hoefer–Smorodinsky, Algorithms for Persuasion with Limited Communication, arXiv:2007.12489v2, §3.1, p.6 (q_C, recommendation points, point collections, u_S(P), u_R(P), Pareto frontier, slopes, Definition 1)

import Mathlib
import Definitions.Def_LimitedPersuasion_Model

namespace LimitedPersuasion

variable {T : Type*} [Fintype T] [DecidableEq T] {n k : ℕ}

/-- The set `C = ⋃_{i ∈ [k]} {θᵢ}` of types of the first `k` actions in state `θ`,
arXiv:2007.12489v2, §3.1, p.6.

**Formalization Note.** The first `k` actions are `Fin.castLE hkn j`, `j : Fin k`. -/
def typesK (hkn : k ≤ n) (θ : Fin n → T) : Finset T :=
  Finset.univ.image fun j : Fin k => θ (Fin.castLE hkn j)

/-- **`q_C`**, arXiv:2007.12489v2, §3.1, p.6: the probability `Pr[⋃_{i ∈ [k]} {θᵢ} = C]` that
the first `k` actions have type set `C`. -/
noncomputable def Instance.qC (I : Instance T n) (hkn : k ≤ n) (C : Finset T) : ℝ :=
  ∑ θ ∈ Finset.univ.filter (fun θ : Fin n → T => typesK hkn θ = C), I.q θ

/-- The points of `C`: `{(ϱ(c), ξ(c)) : c ∈ C} ⊆ ℝ × ℝ`, arXiv:2007.12489v2, §3.1, p.6 ("Type
`θᵢ` corresponds to point `(ϱ(θᵢ), ξ(θᵢ))`").

**Formalization Note.** The receiver coordinate comes first, as in `p(C) = (p_R(C), p_S(C))`. -/
def Instance.pts (I : Instance T n) (C : Finset T) : Set (ℝ × ℝ) :=
  (fun t => (I.ρ t, I.ξ t)) '' (C : Set T)

/-- **Recommendation point for `C`** of a direct scheme `φ` that recommends action `j ∈ [k]` with
signal `j`, arXiv:2007.12489v2, §3.1, p.6: `(E[u_R(φ) | C], E[u_S(φ) | C])`, the expected
utilities of receiver and sender (who follow the recommendation) conditioned on the set `C` of
types of the first `k` actions.

**Formalization Note.** Computed as
`q_C⁻¹ · ∑_{θ : typesK θ = C} q_θ ∑_j φ(θ, j) (ϱ(θ_j), ξ(θ_j))`. The conditional expectation is
meaningful only when `q_C ≠ 0`; every statement about recommendation points is guarded by
`q_C ≠ 0` (at `q_C = 0` Lean's `0⁻¹ = 0` gives `(0, 0)`, which is never used). -/
noncomputable def Instance.recPt (I : Instance T n) (hkn : k ≤ n)
    (φ : (Fin n → T) → Fin k → ℝ) (C : Finset T) : ℝ × ℝ :=
  (I.qC hkn C)⁻¹ • ∑ θ ∈ Finset.univ.filter (fun θ : Fin n → T => typesK hkn θ = C),
    I.q θ • ∑ j : Fin k, φ θ j • (I.ρ (θ (Fin.castLE hkn j)), I.ξ (θ (Fin.castLE hkn j)))

/-- **Point collection**, arXiv:2007.12489v2, §3.1, p.6: for each set `C` of action types for the
first `k` actions a point `p(C) = (p_R(C), p_S(C))` inside the convex hull of (the points of) `C`.

**Formalization Note.** A collection is any map `P : Finset T → ℝ × ℝ`; the hull condition is
required for the sets `C` that occur, i.e. with `q_C ≠ 0`. -/
def Instance.IsPointCollection (I : Instance T n) (hkn : k ≤ n) (P : Finset T → ℝ × ℝ) : Prop :=
  ∀ C : Finset T, I.qC hkn C ≠ 0 → P C ∈ convexHull ℝ (I.pts C)

/-- **Sender utility of a point collection**, arXiv:2007.12489v2, §3.1, p.6:
`u_S(P) = ∑_C q_C · p_S(C)`. -/
noncomputable def Instance.uSP (I : Instance T n) (hkn : k ≤ n) (P : Finset T → ℝ × ℝ) : ℝ :=
  ∑ C : Finset T, I.qC hkn C * (P C).2

/-- **Receiver utility of a point collection**, arXiv:2007.12489v2, §3.1, p.6:
`u_R(P) = ∑_C q_C · p_R(C)`. -/
noncomputable def Instance.uRP (I : Instance T n) (hkn : k ≤ n) (P : Finset T → ℝ × ℝ) : ℝ :=
  ∑ C : Finset T, I.qC hkn C * (P C).1

/-- **`p` lies on the Pareto frontier of `C`**, arXiv:2007.12489v2, §3.1, p.6: the frontier starts
from a type with largest sender utility with a horizontal line (possibly of length 0) and ends at a
type with largest receiver utility with a vertical line (possibly of length 0). So `p` is in the
convex hull of the points of `C` and no point of the hull is strictly larger in both coordinates
(receiver and sender).

**Formalization Note.** Strict inequality in both coordinates keeps the paper's horizontal and
vertical end segments on the frontier: a point of a top edge of positive length is on the frontier
even though the right end of the edge weakly dominates it. Every other boundary point of the hull
(slope `> 0`) and every interior point has a hull point strictly above and to its right. -/
def Instance.OnFrontier (I : Instance T n) (C : Finset T) (p : ℝ × ℝ) : Prop :=
  p ∈ convexHull ℝ (I.pts C) ∧ ∀ x ∈ convexHull ℝ (I.pts C), ¬(p.1 < x.1 ∧ p.2 < x.2)

/-- **`p` corresponds to slope `s`** for `C`, arXiv:2007.12489v2, §3.1, p.6: the line of slope `s`
through `p` lies tangent to the Pareto frontier of `C` in `p`.

**Formalization Note.** In coordinates `(receiver, sender)`, the line of slope `s` through `p`
supports the convex hull of `C` from above: `x_S − s·x_R ≤ p_S − s·p_R` for every `x` in the hull.
For `s ≤ 0` this is equivalent to tangency to the Pareto frontier, since every hull point is
weakly dominated by a frontier point. For `s = 0` every point of the top edge corresponds to the
slope, as on p.6 (the horizontal line of slope 0). -/
def Instance.CorrSlope (I : Instance T n) (C : Finset T) (s : ℝ) (p : ℝ × ℝ) : Prop :=
  p ∈ convexHull ℝ (I.pts C) ∧ ∀ x ∈ convexHull ℝ (I.pts C), x.2 - s * x.1 ≤ p.2 - s * p.1

/-- **`s`-Pareto point collection (Definition 1)**, arXiv:2007.12489v2, §3.1, p.6: for `s ≤ 0`,
a point collection `P` is `s`-Pareto if (1) for every subset `C`, `p(C)` is on the Pareto frontier
of `C` and corresponds to slope `s`, and (2) `u_R(P) ≥ ϱ_E`.

**Formalization Note.** Condition (1) (and the point-collection condition) is required for every
`C` with `q_C ≠ 0`, the sets of types that occur. `s` is a real number: slope `−∞` is not part of
Definition 1 (§3.2, p.8, works with slopes in `[0, −∞)`). -/
def Instance.IsSPareto [NeZero n] (I : Instance T n) (hkn : k ≤ n) (s : ℝ)
    (P : Finset T → ℝ × ℝ) : Prop :=
  s ≤ 0 ∧ I.IsPointCollection hkn P ∧
  (∀ C : Finset T, I.qC hkn C ≠ 0 → I.OnFrontier C (P C) ∧ I.CorrSlope C s (P C)) ∧
  I.rhoE ≤ I.uRP hkn P

end LimitedPersuasion


