-- Prove2me | Definitions.Def_ApproachRegret_ToApproach_Setup
-- name    : ApproachRegret_ToApproach_Setup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T15:11:06.936004+00:00
-- url     : https://prove2.me/theorems/b8f29642-f7a9-4c61-8191-3471898ac5ad
-- title:
--   Blackwell instances, valid halfspace oracles, cones, polar cones, the lift κ ⊕ x, regret and the run of Algorithm 2 (Defs. 4, 9, 11; pp. 31–39)
-- statement:
--   This file sets up the objects of Abernethy, Bartlett and Hazan's reduction from online linear optimization to Blackwell approachability. Throughout, $\mathbb R^d$ is Euclidean space with the Euclidean norm $\|\cdot\|$ and inner product $\langle\cdot,\cdot\rangle$, and $B_2(r)$ is the closed Euclidean ball of radius $r$ about the origin.
--
--   1. **Lift.** For $a\in\mathbb R$ and $x\in\mathbb R^d$, the concatenation $a\oplus x\in\mathbb R^{d+1}$ has first coordinate $a$ followed by the coordinates of $x$, so that $\|a\oplus x\|^2=a^2+\|x\|^2$.
--   2. **Cones (Definition 11).** A set $X\subseteq\mathbb R^d$ is a *cone* if $\alpha z\in X$ for all $z\in X$ and $\alpha\ge0$, and a *convex cone* if it is moreover closed under addition. For $K\subseteq\mathbb R^d$ the conic hull is $\mathtt{cone}(K)=\{\alpha x:\alpha\ge0,\ x\in K\}$, and the polar cone of $C$ is
--   $$C^0=\{\theta\in\mathbb R^d:\ \langle\theta,x\rangle\le0\ \text{for all }x\in C\}.$$
--   3. **Biaffine maps.** $u:\mathbb R^n\times\mathbb R^m\to\mathbb R^d$ is biaffine on $\mathcal X\times\mathcal Y$ if $u(\alpha x+(1-\alpha)x',y)=\alpha u(x,y)+(1-\alpha)u(x',y)$ for all $x,x'\in\mathcal X$, $y\in\mathcal Y$, $\alpha\in[0,1]$, and symmetrically in the second argument.
--   4. **Blackwell instance (Definition 4).** A tuple $(\mathcal X,\mathcal Y,u,S)$ with $\mathcal X\subseteq\mathbb R^n$ and $\mathcal Y\subseteq\mathbb R^m$ compact and convex, $u$ biaffine on $\mathcal X\times\mathcal Y$, and $S\subseteq\mathbb R^d$ convex and closed.
--   5. **Valid halfspace oracle (p. 32).** A map $\mathcal O$ sending each halfspace $H=\{z:\langle a,z\rangle\le c\}$ to a point of $\mathbb R^n$; it is *valid* if for every halfspace $H\supseteq S$ one has $\mathcal O(H)\in\mathcal X$ and $u(\mathcal O(H),y)\in H$ for all $y\in\mathcal Y$.
--   6. **Regret (Definition 9).** For a decision set $\mathcal K$, plays $\theta_1,\dots,\theta_T$ and loss vectors $f_1,\dots,f_T$,
--   $$\mathrm{Regret}_T=\sum_{t=1}^T\langle f_t,\theta_t\rangle-\min_{\theta\in\mathcal K}\sum_{t=1}^T\langle f_t,\theta\rangle .$$
--   7. **Average payoff (p. 31).** $\frac1T\sum_{t=1}^T u(x_t,y_t)$; its distance to $S$ is the approachability rate $D_T(\mathcal A)$ of p. 37.
--   8. **Run of Algorithm 2 (p. 38).** Given an OLO algorithm $\mathcal L$ (a map from the history of past loss vectors to a point), a halfspace oracle $\mathcal O$ and an adversary sequence $y$, the sequences $(\theta_t,x_t,f_t)_{t=1}^T$ form a run if for each round $t=1,\dots,T$: $\theta_t=\mathcal L(f_1,\dots,f_{t-1})$, $x_t=\mathcal O(H_{\theta_t})$ with $H_\theta=\{z:\langle\theta,z\rangle\le0\}$, and $f_t=-u(x_t,y_t)$. Such a run exists and is unique, by recursion on $t$.
--   9. **Lifted instance (p. 39).** With $\kappa=\max_{s\in S}\|s\|$ (the "norm" of $S$, p. 37), the lifted payoff is $u'(x,y)=\kappa\oplus u(x,y)\in\mathbb R^{d+1}$ and the lifted target set is $S'=\mathtt{cone}(\{\kappa\}\times S)$.
--
--   These are the objects in which Lemma 13, Lemma 14, Theorem 17 and Corollary 18 are stated.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`, and the lift is built in `EuclideanSpace ℝ (Fin (d+1))` (coordinate 0 is $a$), so it carries the Euclidean norm, not the sup norm of a product. The polar cone uses the paper's sign ($\le 0$), the negative of Mathlib's `innerDual`. A halfspace is encoded by its pair $(a,c)$; $a=0$ is allowed (then $H$ is empty or everything), and Algorithm 2 queries $(\theta_t,0)$. Rounds are numbered $t=1,\dots,T$; the OLO algorithm at round $t$ receives $(f_1,\dots,f_{t-1})$ as a function on `Fin (t-1)`. The minimum in the regret and the maximum $\kappa$ are written as `sInf` / `sSup` of images; they are attained (and so equal the paper's min / max) when the set is nonempty and compact, which every theorem of the mission ensures.
-- source:
--   Abernethy, Bartlett, Hazan (COLT 2011, JMLR W&CP 19), Definition 4, p. 31; halfspace oracle, p. 32; Definition 9, p. 33; Definition 11, p. 34; D_T and κ, p. 37; Algorithm 2, p. 38; lifted instance, p. 39

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_Cones

open scoped RealInnerProductSpace

namespace ApproachRegret.ToApproach

/-- Definition 11, p. 34: `X` is a cone if it is closed under multiplication by nonnegative
scalars. -/
def IsCone {d : ℕ} (X : Set (ApproachRegret.ToOLO.E d)) : Prop :=
  ∀ α : ℝ, 0 ≤ α → ∀ z ∈ X, α • z ∈ X

/-- Definition 11, p. 34: `X` is a convex cone if it is a cone closed under element addition. -/
def IsConvexCone {d : ℕ} (X : Set (ApproachRegret.ToOLO.E d)) : Prop :=
  IsCone X ∧ ∀ z ∈ X, ∀ w ∈ X, z + w ∈ X

/-- pp. 29–30: `u` is biaffine on `X × Y`: affine in each argument along convex combinations
of points of `X` (resp. `Y`), the other argument ranging over `Y` (resp. `X`). -/
def IsBiaffine {n m d : ℕ} (X : Set (ApproachRegret.ToOLO.E n)) (Y : Set (ApproachRegret.ToOLO.E m)) (u : ApproachRegret.ToOLO.E n → ApproachRegret.ToOLO.E m → ApproachRegret.ToOLO.E d) : Prop :=
  (∀ x ∈ X, ∀ x' ∈ X, ∀ y ∈ Y, ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      u (α • x + (1 - α) • x') y = α • u x y + (1 - α) • u x' y) ∧
  (∀ x ∈ X, ∀ y ∈ Y, ∀ y' ∈ Y, ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      u x (α • y + (1 - α) • y') = α • u x y + (1 - α) • u x y')

/-- Definition 4, p. 31: `(X, Y, u, S)` is a Blackwell instance: `X ⊂ ℝⁿ`, `Y ⊂ ℝᵐ` compact and
convex, `u` biaffine on `X × Y`, and `S ⊂ ℝᵈ` convex and closed. -/
def IsBlackwellInstance {n m d : ℕ} (X : Set (ApproachRegret.ToOLO.E n)) (Y : Set (ApproachRegret.ToOLO.E m)) (u : ApproachRegret.ToOLO.E n → ApproachRegret.ToOLO.E m → ApproachRegret.ToOLO.E d)
    (S : Set (ApproachRegret.ToOLO.E d)) : Prop :=
  IsCompact X ∧ Convex ℝ X ∧ IsCompact Y ∧ Convex ℝ Y ∧ IsBiaffine X Y u ∧
    Convex ℝ S ∧ IsClosed S

/-- The halfspace `{z : ⟨a, z⟩ ≤ c}`. -/
def halfspace {d : ℕ} (a : ApproachRegret.ToOLO.E d) (c : ℝ) : Set (ApproachRegret.ToOLO.E d) :=
  {z | ⟪a, z⟫ ≤ c}

/-- p. 32: a halfspace oracle `O` (the halfspace `H = {z : ⟨a, z⟩ ≤ c}` is passed as `(a, c)`)
is valid if, for each halfspace `H ⊇ S`, `O(H) ∈ X` and `u(O(H), y) ∈ H` for every `y ∈ Y`. -/
def IsValidOracle {n m d : ℕ} (X : Set (ApproachRegret.ToOLO.E n)) (Y : Set (ApproachRegret.ToOLO.E m)) (u : ApproachRegret.ToOLO.E n → ApproachRegret.ToOLO.E m → ApproachRegret.ToOLO.E d)
    (S : Set (ApproachRegret.ToOLO.E d)) (O : ApproachRegret.ToOLO.E d → ℝ → ApproachRegret.ToOLO.E n) : Prop :=
  ∀ a c, S ⊆ halfspace a c → O a c ∈ X ∧ ∀ y ∈ Y, u (O a c) y ∈ halfspace a c

/-- Definition 9, p. 33: `Regret(L; f_{1:T}) = Σ_{t=1}^T ⟨f_t, θ_t⟩ − min_{θ ∈ K} Σ_{t=1}^T ⟨f_t, θ⟩`.
The minimum is written as the infimum of the image of `K`; it is attained when `K` is nonempty
and compact. -/
noncomputable def regret {D : ℕ} (K : Set (ApproachRegret.ToOLO.E D)) (θ f : ℕ → ApproachRegret.ToOLO.E D) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.Icc 1 T, ⟪f t, θ t⟫) -
    sInf ((fun φ : ApproachRegret.ToOLO.E D => ∑ t ∈ Finset.Icc 1 T, ⟪f t, φ⟫) '' K)

/-- p. 31: the average payoff `(1/T) Σ_{t=1}^T u(x_t, y_t)`. -/
noncomputable def avgPayoff {n m d : ℕ} (u : ApproachRegret.ToOLO.E n → ApproachRegret.ToOLO.E m → ApproachRegret.ToOLO.E d) (x : ℕ → ApproachRegret.ToOLO.E n) (y : ℕ → ApproachRegret.ToOLO.E m)
    (T : ℕ) : ApproachRegret.ToOLO.E d :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.Icc 1 T, u (x t) (y t)

/-- Algorithm 2, p. 38: `(θ, x, f)` is the run of Algorithm 2 for rounds `t = 1, …, T`, with OLO
algorithm `L`, halfspace oracle `O`, payoff `u` and adversary sequence `y`:
`θ_t = L(f_1, …, f_{t-1})`, `x_t = O(H_{θ_t})` with `H_θ = {z : ⟨θ, z⟩ ≤ 0}`, `f_t = −u(x_t, y_t)`.
The OLO algorithm `L t` receives the history `(f_1, …, f_t)` as a function on `Fin t`. -/
def IsAlg2Run {n m D : ℕ} (u : ApproachRegret.ToOLO.E n → ApproachRegret.ToOLO.E m → ApproachRegret.ToOLO.E D) (O : ApproachRegret.ToOLO.E D → ℝ → ApproachRegret.ToOLO.E n)
    (L : (t : ℕ) → (Fin t → ApproachRegret.ToOLO.E D) → ApproachRegret.ToOLO.E D) (y : ℕ → ApproachRegret.ToOLO.E m) (T : ℕ)
    (θ : ℕ → ApproachRegret.ToOLO.E D) (x : ℕ → ApproachRegret.ToOLO.E n) (f : ℕ → ApproachRegret.ToOLO.E D) : Prop :=
  ∀ t, 1 ≤ t → t ≤ T →
    θ t = L (t - 1) (fun s => f (s.val + 1)) ∧ x t = O (θ t) 0 ∧ f t = -u (x t) (y t)

/-- p. 37: `κ := max_{x ∈ K} ‖x‖`, the "norm" of the set `K` (written as a supremum; it is a
maximum when `K` is nonempty and compact). -/
noncomputable def setNorm {d : ℕ} (K : Set (ApproachRegret.ToOLO.E d)) : ℝ :=
  sSup ((fun x : ApproachRegret.ToOLO.E d => ‖x‖) '' K)

/-- p. 39: the lifted payoff `u'(x, y) := κ ⊕ u(x, y)`. -/
noncomputable def liftedPayoff {n m d : ℕ} (κ : ℝ) (u : ApproachRegret.ToOLO.E n → ApproachRegret.ToOLO.E m → ApproachRegret.ToOLO.E d) :
    ApproachRegret.ToOLO.E n → ApproachRegret.ToOLO.E m → ApproachRegret.ToOLO.E (d + 1) :=
  fun x y => ApproachRegret.ToOLO.lift κ (u x y)

/-- p. 39: the lifted target set `S' := cone({κ} × S)` with `κ = max_{s ∈ S} ‖s‖`. -/
noncomputable def liftedSet {d : ℕ} (S : Set (ApproachRegret.ToOLO.E d)) : Set (ApproachRegret.ToOLO.E (d + 1)) :=
  ApproachRegret.ToOLO.cone (ApproachRegret.ToOLO.lift (setNorm S) '' S)

end ApproachRegret.ToApproach


