-- Prove2me | Definitions.Def_ZhangBSDE_Scheme_Setting
-- name    : ZhangBSDE_Scheme_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:13.670984+00:00
-- url     : https://prove2.me/theorems/4e2a55c5-87d3-4a98-b722-f2cf0d6e10a0
-- title:
--   §2, pp. 461–462, 465, 479 — partitions and mesh, càdlàg paths, L∞- and L¹-Lipschitz functionals (Definition 2.1), Assumption 2.3, K-uniform partitions (Definition 5.2)
-- statement:
--   This module fixes the deterministic objects of Zhang (2004). Throughout, $T>0$ is a terminal time, $d\ge 1$ is the dimension of the forward state, and $|\cdot|$ is the Euclidean norm on $\mathbb R^d$.
--
--   1. **Partitions.** A partition $\pi: 0=t_0<t_1<\dots<t_n=T$ of $[0,T]$ with $n\ge1$. For $i=1,\dots,n$ put $\Delta t_i = t_i-t_{i-1}$, and let the *partition size* be
--   $$|\pi| = \max_{1\le i\le n}\Delta t_i .$$
--   For a grid index $k>n$ the grid point $t_k$ is read as $t_n=T$ (the convention $t_{n+1}=t_n$ of Lemma 3.3). For $s\ge0$ the *grid index* of $s$ is the largest $k\le n$ with $t_k\le s$; it equals $i-1$ for $s\in[t_{i-1},t_i)$, so $t_{k}$ is the paper's $\pi(s)$, and it equals $n$ for $s\ge T$.
--   2. **$\kappa$-uniform partitions** (Definition 5.2). Given $\kappa>0$, $\pi$ is $\kappa$-uniform if $\Delta t_i\ge |\pi|/\kappa$ for $i=1,\dots,n$.
--   3. **Càdlàg paths.** A path $x:[0,\infty)\to E$ is càdlàg on $[0,T]$ (an element of the paper's space $\mathbb D$) if it is right-continuous at every $t\in[0,T)$ and has a left limit at every $t\in(0,T]$.
--   4. **Lipschitz functionals** (Definition 2.1). A functional $\Phi$ on $\mathbb R^d$-valued paths is $L^\infty$-Lipschitz with constant $K$ if
--   $$|\Phi(x_1)-\Phi(x_2)|\le K\sup_{0\le t\le T}|x_1(t)-x_2(t)|$$
--   for all càdlàg $x_1,x_2$, and $L^1$-Lipschitz with constant $K$ if $|\Phi(x_1)-\Phi(x_2)|\le K\int_0^T|x_1(t)-x_2(t)|\,dt$ for all càdlàg $x_1,x_2$. $\Phi$ is *Markovian* if $\Phi(x)=g(x(T))$ for some $g:\mathbb R^d\to\mathbb R$ and all càdlàg $x$.
--   5. **The class $C^{1/2,1}$ with constant $K$.** A function $\varphi(t,v)$ is continuous on $[0,T]\times V$, satisfies $|\varphi(t,v)-\varphi(s,v)|\le K|t-s|^{1/2}$ and $|\varphi(t,v)-\varphi(t,v')|\le K|v-v'|$ for $s,t\in[0,T]$. For the driver $f(t,x,y,z)$ the spatial Lipschitz condition reads $|f(t,x,y,z)-f(t,x',y',z')|\le K(|x-x'|+|y-y'|+|z-z'|)$.
--   6. **Assumption 2.3.** The drift $b:[0,T]\times\mathbb R^d\to\mathbb R^d$, the diffusion coefficient $\sigma:[0,T]\times\mathbb R^d\to\mathbb R^d$ (a vector, the Brownian motion being one-dimensional) and the driver $f:[0,T]\times\mathbb R^d\times\mathbb R\times\mathbb R\to\mathbb R$ lie in $C^{1/2,1}$, $\Phi$ is $L^\infty$-Lipschitz, all with one constant $K>0$, and
--   $$\sup_{0\le t\le T}\{|b(t,0)|+|\sigma(t,0)|+|f(t,0,0,0)|\}+|\Phi(0)|\le K,$$
--   where $0$ is the zero path. The "conditions on $b$ and $\sigma$ in Assumption 2.3" used by Lemma 4.1 and Theorem 4.2 are the $b,\sigma$ part alone. Finally, $f$ is *independent of $z$* if $f(t,x,y,z)=f(t,x,y,z')$ for all arguments.
--
--   These are the standing objects of every statement of the mission.
--
--   **Formalization Note** Time is $[0,\infty)$ (`ℝ≥0`) and only $[0,T]$ matters. The supremum in (2.2) is written as "for every bound $M$ of $|x_1(t)-x_2(t)|$ on $[0,T]$, $|\Phi(x_1)-\Phi(x_2)|\le KM$", which is equivalent because a càdlàg path is bounded on $[0,T]$; the integral in (2.3) is a lower Lebesgue integral in $[0,\infty]$. The paper names the uniformity constant of Definition 5.2 $K$, the letter of the Lipschitz constant; here it is $\kappa$. The Hölder constant in $t$ is taken equal to $K$, reading "a common constant $K$ to denote all the Lipschitz constants" as covering it.
-- source:
--   Zhang (2004), Ann. Appl. Probab. 14, §2, pp. 461–462 (spaces, (2.1), Definition 2.1 (2.2)–(2.3), Assumption 2.3); §3, p. 465 (partitions, |π|); Definition 5.2, p. 479

import Mathlib
import Definitions.Def_ReflectedBSDE_Existence_Setting

namespace ZhangBSDE.Scheme

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- A partition `π : 0 = t₀ < t₁ < ⋯ < tₙ = T` of `[0, T]` with `n ≥ 1` intervals
(Zhang 2004, §3, p. 465). -/
structure Partition (T : ℝ≥0) where
  n : ℕ
  pos : 0 < n
  t : Fin (n + 1) → ℝ≥0
  mono : StrictMono t
  start : t 0 = 0
  finish : t (Fin.last n) = T

namespace Partition

variable {T : ℝ≥0} (π : Partition T)

/-- The grid point `t_k` for `k ≤ n`, indexed by a natural number; for `k > n` it is `t_n = T`
(this realizes the convention `t_{n+1} ≜ t_n` of Lemma 3.3). -/
def tt (k : ℕ) : ℝ≥0 :=
  π.t ⟨min k π.n, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- `Δt_i = t_i − t_{i−1}` (real subtraction), meaningful for `i = 1, …, n`. -/
noncomputable def Δt (i : ℕ) : ℝ := (π.tt i : ℝ) - (π.tt (i - 1) : ℝ)

/-- The partition size `|π| = max_{1 ≤ i ≤ n} Δt_i`. -/
noncomputable def mesh : ℝ :=
  (Finset.range π.n).sup' (Finset.nonempty_range_iff.mpr π.pos.ne') (fun i => π.Δt (i + 1))

/-- Definition 5.2 (p. 479): `π` is `κ`-uniform if `Δt_i ≥ |π| / κ` for `i = 1, …, n`.
(The paper names this constant `K`; it is renamed `κ` to keep it apart from the Lipschitz
constant `K` of Assumption 2.3.) -/
def IsUniform (κ : ℝ) : Prop :=
  ∀ i ∈ Finset.Icc 1 π.n, π.mesh / κ ≤ π.Δt i

open Classical in
/-- The index of the grid interval containing `s`: the largest `k ≤ n` with `t_k ≤ s`.
For `s ∈ [t_{i−1}, t_i)` it equals `i − 1` (so `t_{gridIndex s}` is the paper's `π(s)`), and for
`s ≥ T` it equals `n`. -/
noncomputable def gridIndex (s : ℝ≥0) : ℕ :=
  Nat.findGreatest (fun k => π.tt k ≤ s) π.n

end Partition

/-- The path `x` is càdlàg on `[0, T]` (an element of the paper's `𝔻`, p. 461): right-continuous
at every `t ∈ [0, T)` and with a finite left limit at every `t ∈ (0, T]`. -/
def IsCadlagOn {F : Type*} [TopologicalSpace F] (T : ℝ≥0) (x : ℝ≥0 → F) : Prop :=
  (∀ t < T, ContinuousWithinAt x (Ici t) t) ∧
    ∀ t ∈ Ioc 0 T, ∃ l : F, Tendsto x (𝓝[<] t) (𝓝 l)

/-- (2.2), Definition 2.1 (p. 462): `Φ` is `L^∞`-Lipschitz with constant `K`:
`|Φ(x₁) − Φ(x₂)| ≤ K sup_{0≤t≤T} |x₁(t) − x₂(t)|` for càdlàg `x₁, x₂`. It is written with an
arbitrary bound `M` of `|x₁(t) − x₂(t)|` on `[0, T]`; a càdlàg path on `[0, T]` is bounded, so this
is equivalent to (2.2). -/
def IsLinfLipschitz {d : ℕ} (T : ℝ≥0) (K : ℝ) (Φ : (ℝ≥0 → EuclideanSpace ℝ (Fin d)) → ℝ) :
    Prop :=
  ∀ x₁ x₂ : ℝ≥0 → EuclideanSpace ℝ (Fin d), IsCadlagOn T x₁ → IsCadlagOn T x₂ →
    ∀ M : ℝ, (∀ t ≤ T, ‖x₁ t - x₂ t‖ ≤ M) → |Φ x₁ - Φ x₂| ≤ K * M

/-- (2.3), Definition 2.1 (p. 462): `Φ` is `L¹`-Lipschitz with constant `K`:
`|Φ(x₁) − Φ(x₂)| ≤ K ∫₀ᵀ |x₁(t) − x₂(t)| dt` for càdlàg `x₁, x₂` (the time integral is a lower
Lebesgue integral in `[0, ∞]`). -/
def IsL1Lipschitz {d : ℕ} (T : ℝ≥0) (K : ℝ) (Φ : (ℝ≥0 → EuclideanSpace ℝ (Fin d)) → ℝ) :
    Prop :=
  ∀ x₁ x₂ : ℝ≥0 → EuclideanSpace ℝ (Fin d), IsCadlagOn T x₁ → IsCadlagOn T x₂ →
    ENNReal.ofReal |Φ x₁ - Φ x₂| ≤
      ENNReal.ofReal K * ∫⁻ r in Icc (0 : ℝ) T, ‖x₁ r.toNNReal - x₂ r.toNNReal‖ₑ

/-- `Φ` takes the form `Φ(x) = g(x(T))` on càdlàg paths (Corollary 4.4, Theorem 6.1). -/
def IsMarkovian {d : ℕ} (T : ℝ≥0) (Φ : (ℝ≥0 → EuclideanSpace ℝ (Fin d)) → ℝ) : Prop :=
  ∃ g : EuclideanSpace ℝ (Fin d) → ℝ, ∀ x, IsCadlagOn T x → Φ x = g (x T)

/-- `φ ∈ C^{1/2,1}([0, T] × V)` with constant `K` (p. 461): `φ` is continuous on `[0, T] × V`,
`1/2`-Hölder in `t` with constant `K` uniformly in the spatial variable, and `K`-Lipschitz in the
spatial variable uniformly in `t ∈ [0, T]`. -/
def IsHalfHolderLip {V W' : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W']
    (T : ℝ≥0) (K : ℝ) (φ : ℝ≥0 → V → W') : Prop :=
  ContinuousOn (Function.uncurry φ) (Iic T ×ˢ univ) ∧
    (∀ t ≤ T, ∀ s ≤ T, ∀ v, ‖φ t v - φ s v‖ ≤ K * |(t : ℝ) - s| ^ (1 / 2 : ℝ)) ∧
    ∀ t ≤ T, ∀ v v', ‖φ t v - φ t v'‖ ≤ K * ‖v - v'‖

/-- The driver `f(t, x, y, z)` of (2.1) lies in `C^{1/2,1}` with constant `K`: continuous on
`[0, T] × ℝᵈ × ℝ × ℝ`, `1/2`-Hölder in `t` uniformly in `(x, y, z)`, and
`|f(t,x,y,z) − f(t,x',y',z')| ≤ K(|x − x'| + |y − y'| + |z − z'|)`. -/
def IsDriverReg {d : ℕ} (T : ℝ≥0) (K : ℝ)
    (f : ℝ≥0 → EuclideanSpace ℝ (Fin d) → ℝ → ℝ → ℝ) : Prop :=
  ContinuousOn (fun p : ℝ≥0 × EuclideanSpace ℝ (Fin d) × ℝ × ℝ => f p.1 p.2.1 p.2.2.1 p.2.2.2)
      (Iic T ×ˢ univ) ∧
    (∀ t ≤ T, ∀ s ≤ T, ∀ x y z, |f t x y z - f s x y z| ≤ K * |(t : ℝ) - s| ^ (1 / 2 : ℝ)) ∧
    ∀ t ≤ T, ∀ x x' y y' z z',
      |f t x y z - f t x' y' z'| ≤ K * (‖x - x'‖ + |y - y'| + |z - z'|)

/-- `b` and `σ` satisfy the conditions of Assumption 2.3 (Lemma 4.1, Theorem 4.2): `K > 0`,
`b, σ ∈ C^{1/2,1}` with constant `K`, and `|b(t, 0)| + |σ(t, 0)| ≤ K` for `t ∈ [0, T]`.
(`σ(t, x) ∈ ℝᵈ` because the Brownian motion is one-dimensional.) -/
structure ForwardCoeff {d : ℕ} (T : ℝ≥0) (K : ℝ)
    (b σ : ℝ≥0 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop where
  K_pos : 0 < K
  b_reg : IsHalfHolderLip T K b
  σ_reg : IsHalfHolderLip T K σ
  bound : ∀ t ≤ T, ‖b t 0‖ + ‖σ t 0‖ ≤ K

/-- Assumption 2.3 (p. 462): `b, σ, f ∈ C^{1/2,1}`, `Φ` is `L^∞`-Lipschitz, all with the common
constant `K > 0`, and `sup_{0≤t≤T} {|b(t,0)| + |σ(t,0)| + |f(t,0,0,0)|} + |Φ(0)| ≤ K`, where `0` is
the constant zero path. -/
structure Assumption23 {d : ℕ} (T : ℝ≥0) (K : ℝ)
    (b σ : ℝ≥0 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (f : ℝ≥0 → EuclideanSpace ℝ (Fin d) → ℝ → ℝ → ℝ)
    (Φ : (ℝ≥0 → EuclideanSpace ℝ (Fin d)) → ℝ) : Prop where
  K_pos : 0 < K
  forward : ForwardCoeff T K b σ
  driver : IsDriverReg T K f
  terminal : IsLinfLipschitz T K Φ
  bound : ∀ t ≤ T, ‖b t 0‖ + ‖σ t 0‖ + |f t 0 0 0| + |Φ (fun _ => 0)| ≤ K

/-- `f` is independent of `z` (Remark 5.5, Theorem 6.1). -/
def IndepZ {d : ℕ} (f : ℝ≥0 → EuclideanSpace ℝ (Fin d) → ℝ → ℝ → ℝ) : Prop :=
  ∀ t x y z z', f t x y z = f t x y z'

end ZhangBSDE.Scheme


