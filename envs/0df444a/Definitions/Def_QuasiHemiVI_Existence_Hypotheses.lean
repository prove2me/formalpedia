-- Prove2me | Definitions.Def_QuasiHemiVI_Existence_Hypotheses
-- name    : QuasiHemiVI_Existence_Hypotheses
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T16:34:15.31722+00:00
-- url     : https://prove2.me/theorems/e5cc45cb-1594-436e-8042-58392b38198a
-- title:
--   Hypotheses (HC), (HT), (Hφ), (HK), (HC0), coercivity (3.2) and condition (3.19)
-- statement:
--   Let $V$, $X$, $Y$ be real normed spaces and let $C$, $K$, $T$, $\varphi$, $J$, $h$, $\gamma$, $\pi$, $f$ be as in Problem 1.1. The hypotheses of Section 3 are the following predicates.
--
--   1. **(HC)** $C$ is nonempty, closed and convex.
--   2. **(HT)(i)** For $u\in C$, $T(u)$ is nonempty, compact and convex in $V^*$, and $T$ is upper semicontinuous on $C$ (norm topologies of $V$ and $V^*$).
--   3. **(HT)(ii)** $u\mapsto T(u)+\gamma^*\partial J(\gamma u)$ is $(\varphi,h)$-**stably pseudomonotone** with respect to $\{\pi^*f\}$: for all $u,v\in C$, if some $u^*\in T(u)$ and $\eta_u\in\partial J(\gamma u)$ satisfy $\langle u^*+\gamma^*\eta_u-\pi^*f,v-u\rangle+\varphi(v,u)\ge0$, then
--   $$\langle v^*+\gamma^*\eta_v-\pi^*f,v-u\rangle+\varphi(v,u)\ge h(v-u)\quad\text{for all }v^*\in T(v),\ \eta_v\in\partial J(\gamma v);$$
--   and $h$ satisfies $\limsup_{t\to0^+}h(tu)/t\ge0$ for all $u\in V$ and, for $v_n\rightharpoonup v$, $h(v)\le\limsup_n h(v_n)$ (3.1).
--   4. **(Hφ)** $v\mapsto\varphi(v,u)$ is convex and lower semicontinuous, $u\mapsto\varphi(v,u)$ is concave and upper semicontinuous, and $\varphi(v,v)=0$.
--   5. **(HK)** For $u\in C$, $K(u)\subseteq C$ is nonempty, closed and convex; (i) if $x_n\in C$, $x_n\rightharpoonup x$ and $y\in K(x)$, there are $y_n\in K(x_n)$ with $y_n\to y$ in norm; (ii) if $x_n,y_n\in C$, $y_n\in K(x_n)$, $x_n\rightharpoonup x$ and $y_n\rightharpoonup y$, then $y\in K(x)$.
--   6. **Coercivity (3.2)** at $v_0$:
--   $$\lim_{u\in C,\ \|u\|_V\to\infty}\frac{\inf_{u^*\in T(u)}\langle u^*,u-v_0\rangle+\inf_{\eta_u\in\partial J(\gamma u)}\langle\eta_u,\gamma(u-v_0)\rangle_{X^*\times X}-\varphi(v_0,u)}{\|u\|_V}=+\infty.$$
--   7. **(HC0)** There is a bounded $C_0\subseteq V$ with $K(u)\cap C_0\neq\emptyset$ for every $u\in C$, and, if $C$ is unbounded, (3.2) holds for every $v_0\in C_0$. **(HC0) uniform** (used for Theorem 3.8 (ii) and the boundedness of $S(C)$): the same, with (3.2) holding uniformly in $v_0\in C_0$, i.e. one $R$ for each $M$ serves every $v_0\in C_0$. For Theorem 3.4, which assumes (3.2) without $K$, the companion condition is: $C_0$ is bounded, $C_0\cap C\neq\emptyset$, and (3.2) holds for every $v_0\in C_0$ if $C$ is unbounded.
--   8. **(3.19)** For $v_n,u_n\in C$ with $v_n\to v$ in norm and $u_n\rightharpoonup u$, $u,v\in C$: $\limsup_n\varphi(v_n,u_n)\le\varphi(v,u)$.
--
--   (HJ), (Hγ) and (H0) are carried by the types: $J$ is locally Lipschitz, and $\gamma$, $\pi$ are bounded linear operators.
--
--   **Formalization Note** No real $\limsup$, $\inf$ or limit is used, so no default value can make a condition vacuous or false. $\limsup_{t\to0^+}h(tu)/t\ge0$ is stated as: for all $\varepsilon,\delta>0$ some $t\in(0,\delta)$ has $h(tu)/t>-\varepsilon$; (3.1) as: for every $\varepsilon>0$, $h(v_n)>h(v)-\varepsilon$ for infinitely many $n$; (3.19) as: for every $\varepsilon>0$, eventually $\varphi(v_n,u_n)<\varphi(v,u)+\varepsilon$; (3.2) as: for every $M$ there is $R$ such that $\langle u^*,u-v_0\rangle+\langle\eta,\gamma(u-v_0)\rangle-\varphi(v_0,u)\ge M\|u\|$ for all $u\in C$ with $\|u\|\ge R$, $u^*\in T(u)$, $\eta\in\partial J(\gamma u)$ — equivalent to the printed limit because $T(u)$ and $\partial J(\gamma u)$ are nonempty. Three repairs relative to the page: the pairing in (3.2) is with $\gamma(u-v_0)$ (the page prints $u-v_0$, which does not typecheck; the proof, (3.15)–(3.16), uses $\gamma(u_n-v_0)$); $T(u)\neq\emptyset$ is added to (HT)(i); and Theorem 3.4's "(3.2)" comes with a bounded $C_0$ meeting $C$, which its proof uses ((3.15), p. 1256). A fourth repair concerns (HC0) in Theorem 3.8 (ii) only: the proof that $S(C)$ is bounded (pp. 1260–1261) applies (3.2) with one rate $r$ at test points $v_n\in C_0\cap K(w_n)$ that vary with $n$, so it needs (3.2) uniformly in $v_0\in C_0$; with (3.2) only at each fixed $v_0$, as printed, $\Gamma(f)$ can be unbounded (example in the note of Theorem 3.8 (ii)). In (HK) the weak limit $x$ is required to lie in $C$, which is automatic since a closed convex set is weakly sequentially closed.
-- source:
--   Zeng, Migórski & Khan, Nonlinear Quasi-hemivariational Inequalities: Existence and Optimal Control, SIAM J. Control Optim. 59(2) (2021) 1246–1274, doi:10.1137/19M1282210, p. 1250, hypotheses (HC), (HJ), (Hγ), (H0), (HT), (3.1), (Hφ), (HK), (HC0), (3.2); p. 1259, condition (3.19) in Theorem 3.8

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_ClarkeDeriv
import Definitions.Def_QuasiHemiVI_Existence_WeakConv
import Definitions.Def_QuasiHemiVI_Existence_SetValued

namespace QuasiHemiVI.Existence

open Filter Topology

/-- (HC), p. 1250: `C` is a nonempty, closed and convex subset of `V`. -/
def HC {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (C : Set V) : Prop :=
  C.Nonempty ∧ IsClosed C ∧ Convex ℝ C

/-- (HT)(i), p. 1250, plus nonemptiness of the values: `T : C → 2^{V*}` has nonempty, (norm)
compact and convex values and is upper semicontinuous on `C` for the norm topologies of `V`
and `V*`. -/
def HTi {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (C : Set V) (T : V → Set (V →L[ℝ] ℝ)) : Prop :=
  (∀ u ∈ C, (T u).Nonempty ∧ IsCompact (T u) ∧ Convex ℝ (T u)) ∧ IsUSCOn T C

/-- (HT)(ii), p. 1250: `C ∋ u ↦ T(u) + γ*∂J(γu)` is `(φ, h)`-stably pseudomonotone with respect
to `{π*f}`: for all `u, v ∈ C`, if some `u* ∈ T(u)` and `η_u ∈ ∂J(γu)` satisfy
`⟨u* + γ*η_u - π*f, v - u⟩ + φ(v, u) ≥ 0`, then
`⟨v* + γ*η_v - π*f, v - u⟩ + φ(v, u) ≥ h(v - u)` for all `v* ∈ T(v)` and `η_v ∈ ∂J(γv)`.
Adjoints are composition: `⟨γ*η, w⟩ = η (γ w)`, `⟨π*f, w⟩ = f (π w)`. -/
def StablyPseudomonotone {V X Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (C : Set V) (T : V → Set (V →L[ℝ] ℝ)) (φ : V → V → ℝ) (J : X → ℝ)
    (γ : V →L[ℝ] X) (π : V →L[ℝ] Y) (f : Y →L[ℝ] ℝ) (h : V → ℝ) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C,
    (∃ us ∈ T u, ∃ η ∈ clarkeGrad J (γ u),
      0 ≤ us (v - u) + η (γ (v - u)) - f (π (v - u)) + φ v u) →
    ∀ vs ∈ T v, ∀ η ∈ clarkeGrad J (γ v),
      h (v - u) ≤ vs (v - u) + η (γ (v - u)) - f (π (v - u)) + φ v u

/-- The two conditions on `h : V → ℝ` in (HT)(ii), p. 1250:
1. `limsup_{t → 0+} h(t u) / t ≥ 0` for all `u ∈ V`, stated without a real `limsup`: for every
   `ε > 0` and `δ > 0` some `t ∈ (0, δ)` has `h(t u) / t > -ε`;
2. (3.1): `h(v) ≤ limsup_{n→∞} h(v n)` whenever `v n ⇀ v`, stated as: for every `ε > 0`,
   `h(v n) > h(v) - ε` for infinitely many `n`. -/
def HhCond {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (h : V → ℝ) : Prop :=
  (∀ u : V, ∀ ε > 0, ∀ δ > 0, ∃ t ∈ Set.Ioo (0 : ℝ) δ, -ε < h (t • u) / t) ∧
  (∀ (v : ℕ → V) (v₀ : V), WeakConv v v₀ → ∀ ε > 0, ∃ᶠ n in atTop, h v₀ - ε < h (v n))

/-- Hypothesis (HT), p. 1250: (HT)(i) (with nonempty values), the `(φ, h)`-stable
pseudomonotonicity (HT)(ii), and the conditions on `h` in (HT)(ii). -/
def HT {V X Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (C : Set V) (T : V → Set (V →L[ℝ] ℝ)) (φ : V → V → ℝ) (J : X → ℝ)
    (γ : V →L[ℝ] X) (π : V →L[ℝ] Y) (f : Y →L[ℝ] ℝ) (h : V → ℝ) : Prop :=
  HTi C T ∧ StablyPseudomonotone C T φ J γ π f h ∧ HhCond h

/-- Hypothesis (Hφ), p. 1250, for `φ : V × V → ℝ` (written curried, `φ v u = φ(v, u)`):
(i) `v ↦ φ(v, u)` is convex and lower semicontinuous for each `u`; (ii) `u ↦ φ(v, u)` is concave
and upper semicontinuous for each `v`; (iii) `φ(v, v) = 0`. -/
def Hphi {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (φ : V → V → ℝ) : Prop :=
  (∀ u : V, ConvexOn ℝ Set.univ (fun v => φ v u) ∧ LowerSemicontinuous (fun v => φ v u)) ∧
  (∀ v : V, ConcaveOn ℝ Set.univ (fun u => φ v u) ∧ UpperSemicontinuous (fun u => φ v u)) ∧
  (∀ v : V, φ v v = 0)

/-- Hypothesis (HK), p. 1250: for `u ∈ C` the set `K(u) ⊆ C` is nonempty, closed and convex, and
(i) for every sequence `x n ∈ C` with `x n ⇀ x ∈ C` and every `y ∈ K(x)` there are
`y n ∈ K(x n)` (in `C`) with `y n → y` in norm;
(ii) for sequences `x n, y n ∈ C` with `y n ∈ K(x n)`, `x n ⇀ x ∈ C` and `y n ⇀ y` imply
`y ∈ K(x)`. -/
def HK {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (C : Set V) (K : V → Set V) : Prop :=
  (∀ u ∈ C, K u ⊆ C ∧ (K u).Nonempty ∧ IsClosed (K u) ∧ Convex ℝ (K u)) ∧
  (∀ (x : ℕ → V) (x₀ : V), (∀ n, x n ∈ C) → x₀ ∈ C → WeakConv x x₀ →
    ∀ y₀ ∈ K x₀, ∃ y : ℕ → V, (∀ n, y n ∈ C) ∧ (∀ n, y n ∈ K (x n)) ∧
      Tendsto y atTop (𝓝 y₀)) ∧
  (∀ (x y : ℕ → V) (x₀ y₀ : V), (∀ n, x n ∈ C) → (∀ n, y n ∈ C) → (∀ n, y n ∈ K (x n)) →
    x₀ ∈ C → WeakConv x x₀ → WeakConv y y₀ → y₀ ∈ K x₀)

/-- The coercivity condition (3.2), p. 1250, at a point `v₀`:
`lim_{u ∈ C, ‖u‖ → ∞} [inf_{u* ∈ T(u)} ⟨u*, u - v₀⟩ + inf_{η ∈ ∂J(γu)} ⟨η, γ(u - v₀)⟩
  - φ(v₀, u)] / ‖u‖ = +∞`,
stated without infima or limits: for every `M` there is `R` such that every `u ∈ C` with
`‖u‖ ≥ R`, every `u* ∈ T(u)` and every `η ∈ ∂J(γu)` satisfy
`⟨u*, u - v₀⟩ + ⟨η, γ(u - v₀)⟩ - φ(v₀, u) ≥ M ‖u‖`.
The pairing of `η ∈ X*` is with `γ(u - v₀)`, as in (3.15)–(3.16) (the page prints `u - v₀`). -/
def Coercive {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set V) (T : V → Set (V →L[ℝ] ℝ)) (φ : V → V → ℝ) (J : X → ℝ)
    (γ : V →L[ℝ] X) (v₀ : V) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, ∀ u ∈ C, R ≤ ‖u‖ → ∀ us ∈ T u, ∀ η ∈ clarkeGrad J (γ u),
    M * ‖u‖ ≤ us (u - v₀) + η (γ (u - v₀)) - φ v₀ u

/-- Hypothesis (HC0), p. 1250: a bounded `C₀ ⊆ V` meets `K(u)` for every `u ∈ C`, and, if `C` is
unbounded, (3.2) holds at every `v₀ ∈ C₀`. -/
def HC0 {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set V) (K : V → Set V) (T : V → Set (V →L[ℝ] ℝ)) (φ : V → V → ℝ) (J : X → ℝ)
    (γ : V →L[ℝ] X) (C₀ : Set V) : Prop :=
  Bornology.IsBounded C₀ ∧ (∀ u ∈ C, (K u ∩ C₀).Nonempty) ∧
  (¬ Bornology.IsBounded C → ∀ v₀ ∈ C₀, Coercive C T φ J γ v₀)

/-- The coercivity condition (3.2), p. 1250, uniformly in `v₀ ∈ C₀`: for every `M` there is one
`R` such that every `v₀ ∈ C₀`, every `u ∈ C` with `‖u‖ ≥ R`, every `u* ∈ T(u)` and every
`η ∈ ∂J(γu)` satisfy `⟨u*, u - v₀⟩ + ⟨η, γ(u - v₀)⟩ - φ(v₀, u) ≥ M ‖u‖`. This is the form the
proof that `S(C)` is bounded uses (pp. 1260–1261: one function `r` with `r(s) → +∞` for test
points `v_n ∈ C₀ ∩ K(w_n)` that vary with `n`); (3.2) at each fixed `v₀ ∈ C₀` does not suffice
there. -/
def CoerciveUnif {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set V) (T : V → Set (V →L[ℝ] ℝ)) (φ : V → V → ℝ) (J : X → ℝ)
    (γ : V →L[ℝ] X) (C₀ : Set V) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, ∀ v₀ ∈ C₀, ∀ u ∈ C, R ≤ ‖u‖ → ∀ us ∈ T u, ∀ η ∈ clarkeGrad J (γ u),
    M * ‖u‖ ≤ us (u - v₀) + η (γ (u - v₀)) - φ v₀ u

/-- Hypothesis (HC0), p. 1250, with (3.2) required uniformly in `v₀ ∈ C₀` (`CoerciveUnif`): a
bounded `C₀ ⊆ V` meets `K(u)` for every `u ∈ C`, and, if `C` is unbounded, (3.2) holds uniformly
over `v₀ ∈ C₀`. This is the repaired hypothesis under which Theorem 3.8 (ii) and the boundedness
of `S(C)` are stated: with (3.2) only at each fixed `v₀ ∈ C₀` (`HC0`) both are false
(`V = ℓ²`, `φ(v, u) = ψ(v) - ψ(u)` with `ψ` convex, continuous and unbounded on the unit ball). -/
def HC0Unif {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set V) (K : V → Set V) (T : V → Set (V →L[ℝ] ℝ)) (φ : V → V → ℝ) (J : X → ℝ)
    (γ : V →L[ℝ] X) (C₀ : Set V) : Prop :=
  Bornology.IsBounded C₀ ∧ (∀ u ∈ C, (K u ∩ C₀).Nonempty) ∧
  (¬ Bornology.IsBounded C → CoerciveUnif C T φ J γ C₀)

/-- Condition (3.2) as assumed in Theorem 3.4 (p. 1251), with the set `C₀` it refers to: `C₀` is
bounded and meets `C`, and, if `C` is unbounded, (3.2) holds at every `v₀ ∈ C₀`. (The page
assumes "(3.2)" without (HC0); that `C₀` meets `C` is what the proof uses, (3.15) p. 1256.) -/
def Coercive32 {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set V) (T : V → Set (V →L[ℝ] ℝ)) (φ : V → V → ℝ) (J : X → ℝ)
    (γ : V →L[ℝ] X) (C₀ : Set V) : Prop :=
  Bornology.IsBounded C₀ ∧ (C ∩ C₀).Nonempty ∧
  (¬ Bornology.IsBounded C → ∀ v₀ ∈ C₀, Coercive C T φ J γ v₀)

/-- Condition (3.19), p. 1259: for sequences `v n, u n ∈ C` with `v n → v` (norm) and `u n ⇀ u`
(weakly), `u, v ∈ C`, `limsup_{n→∞} φ(v n, u n) ≤ φ(v, u)`; stated without a real `limsup`: for
every `ε > 0`, eventually `φ(v n, u n) < φ(v, u) + ε`. -/
def Cond319 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (C : Set V) (φ : V → V → ℝ) : Prop :=
  ∀ (v u : ℕ → V) (v₀ u₀ : V), (∀ n, v n ∈ C) → (∀ n, u n ∈ C) → v₀ ∈ C → u₀ ∈ C →
    Tendsto v atTop (𝓝 v₀) → WeakConv u u₀ →
    ∀ ε > 0, ∀ᶠ n in atTop, φ (v n) (u n) < φ v₀ u₀ + ε

end QuasiHemiVI.Existence


