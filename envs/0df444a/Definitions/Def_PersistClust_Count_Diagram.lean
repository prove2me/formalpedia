-- Prove2me | Definitions.Def_PersistClust_Count_Diagram
-- name    : PersistClust_Count_Diagram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:02.187332+00:00
-- url     : https://prove2.me/theorems/ad412d6f-b8dc-40cb-928f-9d4ce90e5783
-- title:
--   §2.2 and pp. 18–21 — 0-dimensional persistence diagrams from rank functions, tameness, the extended plane, multi-bijections, (d₁, d₂)-separation
-- statement:
--   The persistence layer of the paper, for 0-dimensional homology (path components).
--
--   1. **Rank function.** A filtration is a family of stages $\{S_t\}_{t\in\mathbb R}$, decreasing in $t$ (time runs from $+\infty$ to $-\infty$), together with the relation "$x,y$ lie in the same path component of $S_t$". For $t\le s$, $r(s,t)$ is the number of path components of $S_t$ that meet $S_s$: the rank of $H_0(S_s)\to H_0(S_t)$.
--   2. **Diagram.** The $0$-th persistence diagram is a multiset in the extended plane $\overline{\mathbb R}^2$, a point $(b,d)$ having birth $b$ and death $d\le b$. For $b,d$ real with $d<b$,
--   $$\mu(b,d)=\min_{0<\varepsilon<(b-d)/2}\Big(\big[r(b-\varepsilon,d+\varepsilon)-r(b+\varepsilon,d+\varepsilon)\big]-\big[r(b-\varepsilon,d-\varepsilon)-r(b+\varepsilon,d-\varepsilon)\big]\Big),$$
--   the number of classes born in $[b-\varepsilon,b+\varepsilon)$ and dying in $[d-\varepsilon,d+\varepsilon)$ for small $\varepsilon$. For $b$ real, the point $(b,-\infty)$ (classes that never die) has multiplicity $\inf_{\varepsilon>0}\inf_{t\le b-\varepsilon}\big(r(b-\varepsilon,t)-r(b+\varepsilon,t)\big)$. All other off-diagonal points have multiplicity $0$; the diagonal $\Delta=\{(x,x):x\in\overline{\mathbb R}\}$ has infinite multiplicity.
--   3. **Superlevel-set diagram.** For $f:\mathbb X\to\mathbb R$ continuous on a topological space, $D_0f$ is the diagram of the filtration $\{\mathbb F^t\}$ with path components in $\mathbb F^t$. $f$ is **tame** if every $\mathbb F^t$ has finitely many path components, there is a finite set $T$ such that $\mathbb F^s\subseteq\mathbb F^t$ induces a bijection of path components whenever $t\le s$ and $[t,s]\cap T=\emptyset$, and $\mathbb F^s=\emptyset$ for all large $s$.
--   4. **Regions.** With $\alpha,d\in\mathbb R$: the quadrants $Q^{NE}_\alpha=(\alpha,+\infty]^2$, $Q^{SE}_\alpha=(\alpha,+\infty]\times[-\infty,\alpha]$, $Q^{SW}_\alpha=[-\infty,\alpha]^2$, $Q^{NW}_\alpha=[-\infty,\alpha]\times(\alpha,+\infty]$; the half-planes $\Delta^S_d=\{y\le x-d\}$ (closed), $\Delta^N_d=\{y>x-d\}$ (open), $\Lambda^W_d=\{x\le d\}$, $\Lambda^E_d=\{x>d\}$, $\Lambda^S_d=\{y\le d\}$, $\Lambda^N_d=\{y>d\}$.
--   5. **Multi-bijections.** A diagram $D$ is given by its multiplicities off the diagonal. Its *copies* are the pairs $(p,k)$ with $k<D(p)$, together with countably many copies $(x,k)$, $k\in\mathbb N$, of every diagonal point $(x,x)$. A multi-bijection between $D$ and $D'$ is a bijection between their copies. It satisfies **assertions (i)–(iv)** with threshold $\alpha$ and radius $r$ if (i) every copy of a point $p\in Q^{NE}_\alpha$ is sent within $\ell_\infty$-distance $r$; (ii) the same holds for $\gamma^{-1}$ on copies of points of $Q^{NE}_\alpha$; (iii) every copy of $p\in Q^{SE}_\alpha$ is sent to a point whose abscissa is within $r$ of $p_x$; (iv) the same holds for $\gamma^{-1}$. Distances between extended reals take $\pm\infty$ to be close only to themselves.
--   6. **Separation (Definitions 4.2, 4.7).** For $d_2>d_1\ge0$, $D$ is $(d_1,d_2)$-separated if every off-diagonal point of positive multiplicity lies in $\Delta^N_{d_1}$ or in $\Delta^S_{d_2}\cap\Lambda^E_{d_2}$.
--   7. **Prominent peaks.** The number of peaks of prominence at least $d$ is the total multiplicity of $D$ in $\Delta^S_d$ (points with $p_x-p_y\ge d$, essential classes included).
--
--   **Formalization Note** The truncated subtraction of $\mathbb N\cup\{\infty\}$ is exact in the multiplicity formulas because the rank function is monotone. Tameness is pinned in the 0-dimensional form above ("of the same finite type as in Eq. (1)", p. 9). Separation is imposed on off-diagonal points only: with $d_1=0$ no diagonal point lies in $\Delta^N_0\cup\Delta^S_{d_2}$, and the literal reading would make the definition unsatisfiable.
-- source:
--   Chazal, Guibas, Oudot, Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA RR-6968 (HAL inria-00389390v1, 2009), pp. 8–9 (§2.2, Eq. (1), tameness), p. 14 (Definition 4.2), pp. 18–19 (multi-bijections, quadrants), p. 21 (half-planes, Definition 4.7)

import Mathlib
import Definitions.Def_PersistClust_Count_Setting

namespace PersistClust.Count

noncomputable section

/-! ### 0-dimensional persistence of a decreasing family of stages (§2.2, pp. 8–9) -/

/-- The rank function of 0-dimensional persistence. `stage t` is the space at time `t` (time runs
from `+∞` to `-∞`, so `stage s ⊆ stage t` for `t ≤ s`), and `J t x y` says that `x` and `y` lie in
the same path component of `stage t`. For `t ≤ s`, `rankFn stage J s t` is the number of path
components of `stage t` that meet `stage s`, i.e. the rank of `H₀(stage s) → H₀(stage t)`. -/
def rankFn {α : Type*} (stage : ℝ → Set α) (J : ℝ → α → α → Prop) (s t : ℝ) : ℕ∞ :=
  ((fun x => {y | J t x y}) '' stage s).encard

/-- The multiplicity of a point `(b, d)` of the extended plane in the 0-th persistence diagram of
the rank function `r` (birth `b` ≥ death `d`):
* for `b, d` real with `d < b`: the number of bars born in `[b - ε, b + ε)` and dying in
  `[d - ε, d + ε)`, minimized over `0 < ε < (b - d)/2`;
* for `b` real and `d = -∞` (classes that never die): the number of such classes born in
  `[b - ε, b + ε)`, minimized over `ε > 0`;
* `0` everywhere else, in particular on the diagonal (whose infinite multiplicity is handled by
  `Copies`). -/
def mult (r : ℝ → ℝ → ℕ∞) (p : EReal × EReal) : ℕ∞ :=
  if p.1 ≠ ⊥ ∧ p.1 ≠ ⊤ then
    if p.2 = ⊥ then
      ⨅ (ε : ℝ) (_ : 0 < ε), ⨅ (t : ℝ) (_ : t ≤ p.1.toReal - ε),
        (r (p.1.toReal - ε) t - r (p.1.toReal + ε) t)
    else if p.2 < p.1 then
      ⨅ (ε : ℝ) (_ : ε ∈ Set.Ioo 0 ((p.1.toReal - p.2.toReal) / 2)),
        ((r (p.1.toReal - ε) (p.2.toReal + ε) - r (p.1.toReal + ε) (p.2.toReal + ε)) -
          (r (p.1.toReal - ε) (p.2.toReal - ε) - r (p.1.toReal + ε) (p.2.toReal - ε)))
    else 0
  else 0

variable {X : Type*} [TopologicalSpace X]

/-- The rank function of the superlevel-set filtration `{𝔽^α}` of `f`. -/
def superRank (f : X → ℝ) : ℝ → ℝ → ℕ∞ :=
  rankFn (superlevel f) (fun t => JoinedIn (superlevel f t))

/-- Tameness of the superlevel-set filtration of `f` in 0-dimensional homology ("of the same finite
type as in Eq. (1)", p. 9):
1. every superlevel set has finitely many path components;
2. there is a finite set `T` of critical values such that, whenever `t ≤ s` and `[t, s]` avoids `T`,
   the inclusion `𝔽^s ⊆ 𝔽^t` induces a bijection of path components;
3. `𝔽^s` is empty for all large `s`. -/
def IsTame0 (f : X → ℝ) : Prop :=
  (∀ t : ℝ, {C : Set X | ∃ x ∈ superlevel f t, C = pathComponentIn (superlevel f t) x}.Finite) ∧
  (∃ T : Finset ℝ, ∀ t s : ℝ, t ≤ s → (∀ u ∈ T, u < t ∨ s < u) →
    (∀ x ∈ superlevel f t, ∃ y ∈ superlevel f s, JoinedIn (superlevel f t) x y) ∧
    (∀ y ∈ superlevel f s, ∀ y' ∈ superlevel f s,
      JoinedIn (superlevel f t) y y' → JoinedIn (superlevel f s) y y')) ∧
  (∃ s₀ : ℝ, ∀ s ≥ s₀, superlevel f s = ∅)

/-- The 0-th persistence diagram `D₀f` of the superlevel-set filtration of `f` (off the diagonal). -/
def diagram0 (f : X → ℝ) : EReal × EReal → ℕ∞ :=
  mult (superRank f)

/-! ### The extended plane (pp. 18–21) -/

/-- `|a - b| ≤ r` for extended reals, with `±∞` close only to itself. -/
def closeE (a b : EReal) (r : ℝ) : Prop :=
  a ≤ b + (r : EReal) ∧ b ≤ a + (r : EReal)

/-- `Q^NE_α = (α, +∞] × (α, +∞]`. -/
def QNE (α : ℝ) : Set (EReal × EReal) := {p | (α : EReal) < p.1 ∧ (α : EReal) < p.2}
/-- `Q^SE_α = (α, +∞] × [-∞, α]`. -/
def QSE (α : ℝ) : Set (EReal × EReal) := {p | (α : EReal) < p.1 ∧ p.2 ≤ (α : EReal)}
/-- `Q^SW_α = [-∞, α] × [-∞, α]`. -/
def QSW (α : ℝ) : Set (EReal × EReal) := {p | p.1 ≤ (α : EReal) ∧ p.2 ≤ (α : EReal)}
/-- `Q^NW_α = [-∞, α] × (α, +∞]`. -/
def QNW (α : ℝ) : Set (EReal × EReal) := {p | p.1 ≤ (α : EReal) ∧ (α : EReal) < p.2}

/-- `Δ^S_d`: the closed half-plane below the line `y = x - d`. -/
def DeltaS (d : ℝ) : Set (EReal × EReal) := {p | p.2 ≤ p.1 - (d : EReal)}
/-- `Δ^N_d`: the open half-plane above the line `y = x - d`. -/
def DeltaN (d : ℝ) : Set (EReal × EReal) := {p | p.1 - (d : EReal) < p.2}
/-- `Λ^W_d`: the closed half-plane left of `x = d`. -/
def LamW (d : ℝ) : Set (EReal × EReal) := {p | p.1 ≤ (d : EReal)}
/-- `Λ^E_d`: the open half-plane right of `x = d`. -/
def LamE (d : ℝ) : Set (EReal × EReal) := {p | (d : EReal) < p.1}
/-- `Λ^S_d`: the closed half-plane below `y = d`. -/
def LamS (d : ℝ) : Set (EReal × EReal) := {p | p.2 ≤ (d : EReal)}
/-- `Λ^N_d`: the open half-plane above `y = d`. -/
def LamN (d : ℝ) : Set (EReal × EReal) := {p | (d : EReal) < p.2}

/-! ### Multi-bijections (p. 18) -/

/-- The copies of the points of a diagram `D`: `D p` copies `(p, k)`, `k < D p`, of each
off-diagonal point, and countably many copies `(x, k)` of each diagonal point `(x, x)`,
`x ∈ [-∞, +∞]` (the diagonal has infinite multiplicity). -/
abbrev Copies (D : EReal × EReal → ℕ∞) : Type :=
  {q : (EReal × EReal) × ℕ // (q.2 : ℕ∞) < D q.1} ⊕ (EReal × ℕ)

/-- The point of the extended plane a copy stands for. -/
def pt {D : EReal × EReal → ℕ∞} : Copies D → EReal × EReal
  | Sum.inl q => q.1.1
  | Sum.inr x => (x.1, x.1)

/-- `D` is a diagram off the diagonal: every point of positive multiplicity has death < birth. -/
def IsDiagramLike (D : EReal × EReal → ℕ∞) : Prop :=
  ∀ p, D p ≠ 0 → p.2 < p.1

/-- Assertions (i)–(iv) of Theorem 4.5 for a multi-bijection `γ` (a bijection of copies), with
threshold `α` and radius `r`. -/
def SatisfiesIIV {D D' : EReal × EReal → ℕ∞} (γ : Copies D ≃ Copies D') (α r : ℝ) : Prop :=
  (∀ a, pt a ∈ QNE α → closeE (pt a).1 (pt (γ a)).1 r ∧ closeE (pt a).2 (pt (γ a)).2 r) ∧
  (∀ b, pt b ∈ QNE α → closeE (pt (γ.symm b)).1 (pt b).1 r ∧ closeE (pt (γ.symm b)).2 (pt b).2 r) ∧
  (∀ a, pt a ∈ QSE α → closeE (pt a).1 (pt (γ a)).1 r) ∧
  (∀ b, pt b ∈ QSE α → closeE (pt (γ.symm b)).1 (pt b).1 r)

/-- Definitions 4.2 / 4.7: `D` is `(d₁, d₂)`-separated if every off-diagonal point lies in
`Δ^N_{d₁}` or in `Δ^S_{d₂} ∩ Λ^E_{d₂}`. -/
def IsSeparated (D : EReal × EReal → ℕ∞) (d₁ d₂ : ℝ) : Prop :=
  ∀ p, D p ≠ 0 → p ∈ DeltaN d₁ ∨ (p ∈ DeltaS d₂ ∧ p ∈ LamE d₂)

/-- The total multiplicity of `D` in `Δ^S_d`: the number of peaks of prominence at least `d`. -/
def prominentCount (D : EReal × EReal → ℕ∞) (d : ℝ) : ℕ∞ :=
  {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < D q.1 ∧ q.1.2 ≤ q.1.1 - (d : EReal)}.encard

end

end PersistClust.Count


