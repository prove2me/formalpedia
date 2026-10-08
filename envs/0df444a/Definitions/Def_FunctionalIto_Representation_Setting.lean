-- Prove2me | Definitions.Def_FunctionalIto_Representation_Setting
-- name    : FunctionalIto_Representation_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:37.19698+00:00
-- url     : https://prove2.me/theorems/51c5eb07-fd7c-4cc4-941b-0a48128cb712
-- title:
--   §2–§3.1, pp. 3–9 — paths, d∞, nonanticipative functionals, (10), ℂ_l^{0,0}, 𝔹, ℂ_b^{1,2} with derivative witnesses; the semimartingale setting; the cylindrical functional of Lemma 5.7
-- statement:
--   This file sets up the path-space calculus of Cont and Fournié for paths with values in $\mathbb R^d$ and in the cone $S_d^+$ of positive semidefinite $d\times d$ matrices, on a time horizon $T$.
--
--   **Paths.** A path is a map $x:[0,\infty)\to\mathbb R^d$ (or into matrices). It is *cadlag on $[0,t]$* if it is right-continuous on $[0,t]$ and has left limits on $(0,t]$; a pair $(x,v)$ belongs to $D([0,t],\mathbb R^d)\times\mathcal S_t$ if both are cadlag on $[0,t]$ and $v(u)\in S_d^+$ for $u\le t$. The *stopped path* is $x_t(u)=x(u\wedge t)$; it also plays the role of the horizontal extension $x_{t,h}$ of (4). The *vertical perturbation* (5) is
--   $$x_t^e(u)=x(u)\ (u<t),\qquad x_t^e(u)=x(t)+e\ (u\ge t),$$
--   and $v_{t-}$ equals $v$ on $[0,t)$ and the left limit $v(t-)$ from $t$ on (with $v(0-)=v(0)$).
--
--   **Distance (9).** $d_\infty((t,x,v),(t',x',v'))=|t-t'|+\sup_{u\in[0,T]}\max\big(|x_t(u)-x'_{t'}(u)|,\ |v_t(u)-v'_{t'}(u)|\big)$, with the sup norm on $\mathbb R^d$ and the entrywise sup norm on matrices.
--
--   **Functionals.** A functional $F_t(x,v)$ is *nonanticipative* if $F_t(x,v)=F_t(x_t,v_t)$, and has *predictable dependence on $v$* (10) if $F_t(x,v)=F_t(x,v_{t-})$ for all $t\le T$ and all $(x,v)\in D([0,t],\mathbb R^d)\times\mathcal S_t$.
--
--   **Classes.**
--   1. *Continuity at fixed times* (Def. 2.2, (11)): for $t<T$, $F_t$ is continuous for $d_\infty$ on $D([0,t],\mathbb R^d)\times\mathcal S_t$.
--   2. *Left-continuity* $\mathbb C_l^{0,0}([0,T))$ (Def. 2.4, (13)): for $t<T$, $\varepsilon>0$ and $(x,v)$ there is $\eta>0$ with $|F_t(x,v)-F_s(x',v')|<\varepsilon$ whenever $s\le t$, $(x',v')\in D([0,s],\mathbb R^d)\times\mathcal S_s$ and $d_\infty((t,x,v),(s,x',v'))<\eta$.
--   3. *Boundedness preservation* $\mathbb B([0,T))$ (Def. 2.5, (14)): for every compact $K\subset\mathbb R^d$, $R>0$ and $t_0<T$ there is $C>0$ with $|F_t(x,v)|<C$ whenever $t\le t_0$, $x([0,t])\subset K$ and $\sup_{s\le t}|v(s)|<R$.
--   4. *Horizontal derivative* (Def. 3.1, (17)): $\mathcal DF_t(x,v)$ is the right derivative at $h=0$ of $h\mapsto F_{t+h}(x_{t,h},v_{t,h})$.
--   5. *Vertical derivative* (Def. 3.2, (19)): $\nabla_xF_t(x,v)$ is the gradient at $e=0$ of $e\mapsto F_t(x_t^e,v_t)$, which is required to be differentiable at $0$.
--   6. $\mathbb C_b^{1,2}([0,T))$ (Def. 3.6): $F$ nonanticipative and left-continuous, horizontally differentiable with $\mathcal DF$ continuous at fixed times, twice vertically differentiable with $\nabla_xF$ and $\nabla_x^2F$ left-continuous, and $\mathcal DF,\nabla_xF,\nabla_x^2F\in\mathbb B([0,T))$.
--
--   **The continuous semimartingale setting (§2, p. 3).** $(\Omega,\mathcal F,\mathcal F_t,\mathbb P)$ satisfies the usual hypotheses; $X=X(0)+V+M$ with $V$ continuous, adapted, of bounded variation, $V(0)=0$, $M$ continuous with local-martingale components, $M(0)=0$; $A$ is an adapted cadlag process with values in $S_d^+$ and
--   $$[X^i,X^j](t)=\int_0^tA_{ij}(s)\,ds .$$
--
--   **The cylindrical functional (proof of Lemma 5.7, p. 18).** For times $t_1<\dots<t_n$ and $f:(\mathbb R^d)^n\to\mathbb R^d$,
--   $$F_t(x_t,v_t)=f\big(x(t_1-),\dots,x(t_n-)\big)\cdot\big(x(t)-x(t_n)\big)\,1_{t>t_n},\qquad \nabla_xF_t(x_t,v_t)=f\big(x(t_1-),\dots,x(t_n-)\big)\,1_{t>t_n}.$$
--
--   These are the objects in which every statement of the mission is written.
--
--   **Formalization Note.** Time is $\mathbb R_{\ge0}$ and functionals are defined on all paths; every quantifier over $D([0,t],\mathbb R^d)\times\mathcal S_t$ is restricted to cadlag pairs. The derivatives $\mathcal DF,\nabla_xF,\nabla_x^2F$ are explicit witnesses tied to $F$ by `HasDerivWithinAt` (on $[0,\infty)$) and `HasFDerivAt`, so no junk value arises. The measurability of Def. 2.1 is not part of the class: Theorem 2.7 derives it. Condition (11) is read with "for all $(x',v')$" (the page prints a slip). In (14), "$\sup_{s\le t}|v(s)|<R$" is encoded as $|v(s)|\le R'$ for some $R'<R$. In the semimartingale setting, $X$, $V$, $M$ have continuous paths and $A$ has cadlag paths for every $\omega$; the null sets of $\mathbb P$ lie in $\mathcal F_0$, and $A$ is assumed locally integrable along paths so that $\int_0^tA$ is a genuine Lebesgue integral. For $d>1$ the product in the cylindrical functional is the dot product, and $x(0-)=x(0)$.
-- source:
--   Cont and Fournié, Functional Itô calculus and stochastic integral representation of martingales, arXiv:1002.2446v5, pp. 3–9, §2–§3.1, (3)–(5), (9)–(11), (13), (14), (17), (19), Definitions 2.1–2.5, 3.1, 3.2, 3.6; p. 18, proof of Lemma 5.7 (cylindrical functional)

import Mathlib
import Definitions.Def_auto_M05_f3f59_EthierKurtz_HasCrossVariation
import Definitions.Def_FunctionalIto_Formula_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators Matrix

namespace FunctionalIto.Representation

/-! ## Paths (Cont–Fournié §2.1, pp. 3–4)

A path is a function on `ℝ≥0`; a path "in `D([0,t], E)`" is one that is cadlag on `[0,t]`.
The stopped path `stop t x` is `x_t`, and also the horizontal extension `x_{t,h}` of (4) viewed at
horizon `t + h`. -/

/-- The vertical perturbation `x_t^e` of (5): equal to `x` on `[0,t)` and to `x t + e` from `t` on. -/
noncomputable def bump {d : ℕ} (t : ℝ≥0) (x : ℝ≥0 → (Fin d → ℝ)) (e : Fin d → ℝ) : ℝ≥0 → (Fin d → ℝ) :=
  fun u => if u < t then x u else x t + e

/-- The path `v_{t−}` of p. 5: equal to `v` on `[0,t)` and to the left limit `v(t−)` from `t` on
(for `t = 0`, `Function.leftLim v 0 = v 0`). -/
noncomputable def vLeft {E : Type*} [TopologicalSpace E] (t : ℝ≥0) (v : ℝ≥0 → E) : ℝ≥0 → E :=
  fun u => if u < t then v u else Function.leftLim v t

/-- `(x, v) ∈ D([0,t], ℝ^d) × 𝒮_t`, with `𝒮_t = D([0,t], S_d^+)`: both paths cadlag on `[0,t]`,
`v` valued in positive semidefinite matrices on `[0,t]`. -/
def IsPathPair {d : ℕ} (t : ℝ≥0) (x : ℝ≥0 → (Fin d → ℝ))
    (v : ℝ≥0 → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  FunctionalIto.Formula.CadlagOn t x ∧ FunctionalIto.Formula.CadlagOn t v ∧ ∀ u ≤ t, (v u).PosSemidef

/-- The entrywise sup norm of a matrix (the norm on `S_d^+` used in `d_∞` and in (14)). -/
noncomputable def matNorm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ‖Matrix.of.symm M‖

/-- `d_∞((t,x,v),(t',x',v')) < η`, the distance (9) on stopped paths, with the max norm on
`ℝ^d × S_d^+` (sup norm on `ℝ^d`, entrywise sup norm on matrices), the supremum taken over
`u ∈ [0,T]` of the stopped paths. Encoded with an explicit bound `c` on the supremum. -/
def DistLt {d : ℕ} (T η : ℝ) (t : ℝ≥0) (x : ℝ≥0 → (Fin d → ℝ))
    (v : ℝ≥0 → Matrix (Fin d) (Fin d) ℝ) (t' : ℝ≥0) (x' : ℝ≥0 → (Fin d → ℝ))
    (v' : ℝ≥0 → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∃ c : ℝ, |(t : ℝ) - (t' : ℝ)| + c < η ∧
    ∀ u : ℝ≥0, (u : ℝ) ≤ T →
      max ‖FunctionalIto.Formula.stop t x u - FunctionalIto.Formula.stop t' x' u‖ (matNorm (FunctionalIto.Formula.stop t v u - FunctionalIto.Formula.stop t' v' u)) ≤ c

/-! ## Nonanticipative functionals (Def. 2.1, (10)) -/

/-- The type of (real-valued) functionals `F_t(x, v)` on paths. -/
abbrev Functional (d : ℕ) (β : Type*) :=
  ℝ≥0 → (ℝ≥0 → (Fin d → ℝ)) → (ℝ≥0 → Matrix (Fin d) (Fin d) ℝ) → β

/-- Nonanticipative: `F_t(x, v)` depends only on the stopped paths `x_t`, `v_t`. -/
def IsNonanticipative {d : ℕ} {β : Type*} (F : Functional d β) : Prop :=
  ∀ t x v, F t x v = F t (FunctionalIto.Formula.stop t x) (FunctionalIto.Formula.stop t v)

/-- Condition (10), "predictable" dependence on the second argument:
`F_t(x_t, v_t) = F_t(x_t, v_{t−})` for `t ∈ [0,T]` and `(x, v) ∈ D([0,t],ℝ^d) × 𝒮_t`. -/
def PredictableInV {d : ℕ} (T : ℝ≥0) (F : Functional d ℝ) : Prop :=
  ∀ t ≤ T, ∀ x v, IsPathPair t x v → F t x v = F t x (vLeft t v)

/-! ## Continuity and boundedness classes (Defs. 2.2, 2.4, 2.5) -/

/-- Def. 2.2, (11) (read with `∀ (x', v')`): continuity at fixed times for `d_∞`, `t ∈ [0,T)`. -/
def ContinuousAtFixedTimes {d : ℕ} (T : ℝ≥0) (F : Functional d ℝ) : Prop :=
  ∀ t < T, ∀ ε > (0 : ℝ), ∀ x v, IsPathPair t x v → ∃ η > (0 : ℝ), ∀ x' v',
    IsPathPair t x' v' → DistLt T η t x v t x' v' → |F t x v - F t x' v'| < ε

/-- Def. 2.4, (13): left-continuous functionals `ℂ_l^{0,0}([0,T))`. The comparison time is
`s = t − h ∈ [0,t]`; `h = 0` gives continuity of `F_t` in the sup norm. -/
def LeftContinuous {d : ℕ} (T : ℝ≥0) (F : Functional d ℝ) : Prop :=
  ∀ t < T, ∀ ε > (0 : ℝ), ∀ x v, IsPathPair t x v → ∃ η > (0 : ℝ), ∀ s ≤ t, ∀ x' v',
    IsPathPair s x' v' → DistLt T η t x v s x' v' → |F t x v - F s x' v'| < ε

/-- Def. 2.5, (14): boundedness-preserving functionals `𝔹([0,T))`. "`sup_{s∈[0,t]} |v(s)| < R`" is
`∃ R' < R, ∀ s ≤ t, |v(s)| ≤ R'`. -/
def BoundednessPreserving {d : ℕ} (T : ℝ≥0) (F : Functional d ℝ) : Prop :=
  ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ R > (0 : ℝ), ∀ t₀ < T, ∃ C > (0 : ℝ),
    ∀ t ≤ t₀, ∀ x v, IsPathPair t x v → (∀ u ≤ t, x u ∈ K) →
      (∃ R' < R, ∀ s ≤ t, matNorm (v s) ≤ R') → |F t x v| < C

/-! ## Horizontal and vertical derivatives (Defs. 3.1, 3.2), as witnesses tied to `F` -/

/-- Def. 3.1, (17): `DF` is the horizontal derivative of `F` on `[0,T)`: for every
`(x,v) ∈ D([0,t],ℝ^d) × 𝒮_t`, `h ↦ F_{t+h}(x_{t,h}, v_{t,h})` has right derivative `DF t x v` at
`h = 0`. -/
def IsHorizDeriv {d : ℕ} (T : ℝ≥0) (F DF : Functional d ℝ) : Prop :=
  ∀ t < T, ∀ x v, IsPathPair t x v →
    HasDerivWithinAt (fun h : ℝ => F (t + h.toNNReal) (FunctionalIto.Formula.stop t x) (FunctionalIto.Formula.stop t v)) (DF t x v)
      (Set.Ici 0) 0

/-- Def. 3.2, (19): `G` is vertically differentiable on `[0,T)` with vertical gradient `∇G`:
`e ↦ G_t(x_t^e, v_t)` is (Fréchet) differentiable at `0` with gradient `∇G t x v`. -/
def IsVertGrad {d : ℕ} (T : ℝ≥0) (G : Functional d ℝ) (gradG : Functional d (Fin d → ℝ)) :
    Prop :=
  ∀ t < T, ∀ x v, IsPathPair t x v →
    HasFDerivAt (fun e : Fin d → ℝ => G t (bump t x e) v)
      (∑ i, gradG t x v i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) 0

/-- Def. 3.6 with `k = 2`: `F ∈ ℂ_b^{1,2}([0,T))` with horizontal derivative `DF`, vertical
derivative `gradF` and second vertical derivative `hessF` (`hessF t x v i` is the vertical gradient
of the `i`-th component of `gradF`). `F` is nonanticipative and left-continuous, `DF` is continuous
at fixed times, `∇F` and `∇²F` are left-continuous componentwise, and `DF`, `∇F`, `∇²F` are
boundedness preserving. -/
def IsC12b {d : ℕ} (T : ℝ≥0) (F DF : Functional d ℝ) (gradF : Functional d (Fin d → ℝ))
    (hessF : Functional d (Matrix (Fin d) (Fin d) ℝ)) : Prop :=
  IsNonanticipative F ∧ LeftContinuous T F ∧
  IsHorizDeriv T F DF ∧ ContinuousAtFixedTimes T DF ∧
  IsVertGrad T F gradF ∧ (∀ i, LeftContinuous T (fun t x v => gradF t x v i)) ∧
  (∀ i, IsVertGrad T (fun t x v => gradF t x v i) (fun t x v => hessF t x v i)) ∧
  (∀ i j, LeftContinuous T (fun t x v => hessF t x v i j)) ∧
  BoundednessPreserving T DF ∧ (∀ i, BoundednessPreserving T (fun t x v => gradF t x v i)) ∧
  (∀ i j, BoundednessPreserving T (fun t x v => hessF t x v i j))

/-! ## The continuous semimartingale setting of §2 (p. 3) -/

/-- The standing setting of §2: `(Ω, 𝓕, 𝓕_t, ℙ)` satisfies the usual hypotheses (complete,
null sets in `𝓕_0`, right-continuous); `X = X(0) + V + M` is a continuous `ℝ^d`-valued
semimartingale (`V` continuous adapted of bounded variation with `V 0 = 0`, `M` continuous adapted
with local-martingale components and `M 0 = 0`, `X 0` `𝓕_0`-measurable); `A` is an adapted process
with cadlag paths valued in positive semidefinite matrices, locally integrable along paths, and
`[X^i, X^j](t) = ∫_0^t A_{ij}(s) ds` (3). -/
def IsContSemimartingaleSetting {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (X V M : ℝ≥0 → Ω → (Fin d → ℝ))
    (A : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  P.IsComplete ∧ (∀ s : Set Ω, P s = 0 → MeasurableSet[ℱ 0] s) ∧
  (∀ t, ℱ t = ⨅ s, ⨅ (_ : t < s), ℱ s) ∧
  (∀ t ω, X t ω = X 0 ω + V t ω + M t ω) ∧
  StronglyMeasurable[ℱ 0] (X 0) ∧
  Adapted ℱ V ∧ (∀ ω, Continuous (fun t => V t ω)) ∧ (∀ ω, V 0 ω = 0) ∧
  (∀ ω (s : ℝ≥0) i, BoundedVariationOn (fun t => V t ω i) (Set.Icc 0 s)) ∧
  Adapted ℱ M ∧ (∀ ω, Continuous (fun t => M t ω)) ∧ (∀ ω, M 0 ω = 0) ∧
  (∀ i, EthierKurtz.IsSourceLocalMartingale P ℱ (fun t ω => M t ω i)) ∧
  (∀ t i j, StronglyMeasurable[ℱ t] (fun ω => A t ω i j)) ∧ (∀ t ω, (A t ω).PosSemidef) ∧
  (∀ ω t, ContinuousWithinAt (fun s => A s ω) (Set.Ici t) t) ∧
  (∀ ω t, 0 < t → ∃ l, Tendsto (fun s => A s ω) (𝓝[<] t) (𝓝 l)) ∧
  (∀ ω (t : ℝ) i j, IntervalIntegrable (fun s : ℝ => A s.toNNReal ω i j) MeasureTheory.volume 0 t) ∧
  (∀ i j, EthierKurtz.HasCrossVariation P (fun t ω => X t ω i) (fun t ω => X t ω j)
    (fun t ω => ∫ s in (0 : ℝ)..(t : ℝ), A s.toNNReal ω i j))

/-! ## The cylindrical functional of the proof of Lemma 5.7 (p. 18) -/

/-- The cylindrical functional `F_t(x_t, v_t) = f(x(t_1−), …, x(t_n−)) · (x(t) − x(t_n)) 1_{t > t_n}`
of the proof of Lemma 5.7, with `n + 1` times `ts 0, …, ts (Fin.last n)` (so `t_n = ts (Fin.last n)`),
`f` valued in `ℝ^d` and `·` the dot product (for `d = 1` it is the product of the page);
`x(t_i−)` is `Function.leftLim x (ts i)` (which is `x 0` at `ts i = 0`). -/
noncomputable def cylindricalF {d n : ℕ} (ts : Fin (n + 1) → ℝ≥0)
    (f : (Fin (n + 1) → Fin d → ℝ) → (Fin d → ℝ)) : Functional d ℝ :=
  fun t x _ => if ts (Fin.last n) < t then
    f (fun i => Function.leftLim x (ts i)) ⬝ᵥ (x t - x (ts (Fin.last n))) else 0

/-- Its vertical derivative as stated on p. 18: `∇_x F_t(x_t, v_t) = f(x(t_1−), …, x(t_n−)) 1_{t > t_n}`. -/
noncomputable def cylindricalGradF {d n : ℕ} (ts : Fin (n + 1) → ℝ≥0)
    (f : (Fin (n + 1) → Fin d → ℝ) → (Fin d → ℝ)) : Functional d (Fin d → ℝ) :=
  fun t x _ => if ts (Fin.last n) < t then f (fun i => Function.leftLim x (ts i)) else 0

end FunctionalIto.Representation


