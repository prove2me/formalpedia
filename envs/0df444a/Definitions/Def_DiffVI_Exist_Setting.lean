-- Prove2me | Definitions.Def_DiffVI_Exist_Setting
-- name    : DiffVI_Exist_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:39.382813+00:00
-- url     : https://prove2.me/theorems/9910329e-8cf3-472e-8a21-fe741829ebbf
-- title:
--   §2, §2.1, §6, pp. 4–5, 28–37 — (A), (B), weak solutions of the DVI (6.2) and of a DI, the map 𝐅 of (6.4), (6.5), (6.6), VI kernel, R₀ pairs, psd-plus
-- statement:
--   Throughout, $\mathbb R^k$ is the Euclidean space with inner product $u^Tv$ and norm $\|\cdot\|$; matrices are linear maps, $\|B\|$ is the operator norm and $E^T$ the adjoint. $T>0$ is a terminal time and $\Omega=[0,T]\times\mathbb R^n$. For a map $\Phi:\mathbb R^m\to\mathbb R^m$ and a set $K\subseteq\mathbb R^m$, $\mathrm{SOL}(K,\Phi)$ is the solution set of the variational inequality: the $u\in K$ with $(u'-u)^T\Phi(u)\ge 0$ for all $u'\in K$ (the referenced definition `viSol`). This file fixes the objects of Sections 2 and 6 of Pang and Stewart.
--
--   1. **Lipschitz data on $\Omega$.** A map $g$ on $\Omega$ is Lipschitz with constant $L$ if $\|g(t,x)-g(t',x')\|\le L(|t-t'|+\|x-x'\|)$ for $(t,x),(t',x')\in\Omega$. **Assumption (A)**: $f:\Omega\to\mathbb R^n$, $B:\Omega\to\mathbb R^{n\times m}$, $G:\Omega\to\mathbb R^m$ are Lipschitz on $\Omega$ with positive constants $L_f,L_B,L_G$. **Assumption (B)**: $\sup_{(t,x)\in\Omega}\|B(t,x)\|<\infty$. $G(\Omega)$ is the range of $G$ on $\Omega$.
--   2. **Weak solution of the initial-value DVI (6.2)**
--   $$\dot x=f(t,x)+B(t,x)u,\quad x(0)=x^0,\qquad u\in\mathrm{SOL}(K,G(t,x)+F(\cdot)).$$
--   A pair $(x,u)$ is a weak (Carathéodory) solution on $[0,T]$ if $x(0)=x^0$; $u$ is integrable on $[0,T]$ with $u(t)\in K$ for almost every $t$; $t\mapsto f(t,x(t))+B(t,x(t))u(t)$ is integrable on $[0,T]$ and $x(t)-x(s)=\int_s^t\big(f(\tau,x(\tau))+B(\tau,x(\tau))u(\tau)\big)\,d\tau$ for $0\le s\le t\le T$; and for every continuous $\tilde u:[0,T]\to K$ the function $t\mapsto(\tilde u(t)-u(t))^T(G(t,x(t))+F(u(t)))$ is integrable on $[0,T]$ and
--   $$\int_0^T(\tilde u(t)-u(t))^T\big(G(t,x(t))+F(u(t))\big)\,dt\ \ge\ 0.\qquad(2.4)$$
--   3. **Monotonicity.** $H$ is monotone on $S$ if $(u-u')^T(H(u)-H(u'))\ge0$ for $u,u'\in S$, and strongly monotone on $S$ with modulus $\eta>0$ if $(u-u')^T(H(u)-H(u'))\ge\eta\|u-u'\|^2$.
--   4. **Cones.** The dual cone $C^*=\{v: u^Tv\ge0\ \forall u\in C\}$; the recession cone $K_\infty=\{d: x+\tau d\in K\ \forall x\in K,\ \tau\ge0\}$. A matrix $D$ is positive semidefinite if $u^TDu\ge0$ for all $u$ (symmetry is not assumed) and psd-plus if moreover $u^TDu=0$ implies $Du=0$. The **VI kernel** $\mathcal K(K,D)$ is the solution set of the homogeneous complementarity problem $K_\infty\ni v\perp Dv\in(K_\infty)^*$ (6.7), and $(K,D)$ is an **R₀ pair** if $\mathcal K(K,D)=\{0\}$. $K$ is a **polyhedron** if it is the solution set of finitely many inequalities $a_i^Tu\le b_i$, and **contains no lines** if $x+\tau d\in K$ for all real $\tau$ forces $d=0$.
--   5. **The set-valued map (6.4)** $\mathbf F(t,x)=\{f(t,x)+B(t,x)u: u\in\mathrm{SOL}(K,G(t,x)+F)\}$. The **linear growth (6.5)** with constant $\rho$: $\|u\|\le\rho(1+\|q\|)$ for all $q\in G(\Omega)$ and $u\in\mathrm{SOL}(K,q+F)$. The **coercivity (6.6)** at $u^{\mathrm{ref}}$: $\liminf_{u\in K,\|u\|\to\infty}(u-u^{\mathrm{ref}})^TF(u)/\|u\|^2>0$, written as: there are $c>0$ and $R$ with $(u-u^{\mathrm{ref}})^TF(u)\ge c\|u\|^2$ for all $u\in K$ with $\|u\|\ge R$.
--   6. **Differential inclusions.** A set-valued $\Phi:\Omega\rightrightarrows\mathbb R^n$ is upper semicontinuous on $\Omega$ if for every $(t,x)\in\Omega$ and every open $V\supseteq\Phi(t,x)$, $\Phi(t',x')\subseteq V$ for all $(t',x')\in\Omega$ near $(t,x)$. A weak solution on $[0,T]$ of $\dot x\in\Phi(t,x)$, $x(0)=x^0$, is an $x$ with $x(t)=x^0+\int_0^tv(s)\,ds$ on $[0,T]$ for some integrable $v$ with $v(t)\in\Phi(t,x(t))$ for almost every $t\in[0,T]$.
--
--   These are the objects of the existence theory for the initial-value DVI in Section 6 of the paper; every theorem of the mission is stated with them.
--
--   **Formalization Note** Functions on $\Omega$ are curried functions defined on all of $\mathbb R\times\mathbb R^n$, of which only the values on $[0,T]\times\mathbb R^n$ enter. The integrability requirements in the weak-solution definitions are explicit, because a Lean integral of a non-integrable function is $0$. The coercivity (6.6) is stated in its equivalent $\exists c,R$ form, which is vacuous for bounded $K$, as the page notes.
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, pp. 4–5 (§2, §2.1, (2.4)), pp. 28–30 ((6.1), (6.2), (A), (B), (6.4), (6.5)), pp. 32–34 ((6.6), monotone, strongly monotone composite, (6.7), R₀ pair), p. 37 (psd-plus)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol

namespace DiffVI.Exist

open MeasureTheory Filter Topology
open scoped InnerProductSpace InnerProduct

/-! Pang & Stewart, *Differential variational inequalities*, author's version hal-01366027v1,
§2 (p. 4), §2.1 (pp. 4–5), §6 (pp. 28–41). `SOL(K, Φ)` is the published
`SolodovSvaiterVI.Alg21.viSol Φ K`. -/

/-- The paper's metric on `Ω = [0, T] × ℝⁿ` is `|t − t'| + ‖x − x'‖` ((B₀), p. 22): `g` is
Lipschitz continuous on `Ω` with constant `L`. -/
def LipOnΩ {n : ℕ} {Y : Type*} [SeminormedAddCommGroup Y] (T : ℝ)
    (g : ℝ → EuclideanSpace ℝ (Fin n) → Y) (L : ℝ) : Prop :=
  ∀ t ∈ Set.Icc 0 T, ∀ t' ∈ Set.Icc 0 T, ∀ x x' : EuclideanSpace ℝ (Fin n),
    ‖g t x - g t' x'‖ ≤ L * (|t - t'| + ‖x - x'‖)

/-- Assumption (A), p. 29: `f`, `B` and `G` are Lipschitz continuous on `Ω` (with positive
constants `L_f`, `L_B`, `L_G`); `‖B(t, x)‖` is the operator norm. -/
def CondA {n m : ℕ} (T : ℝ)
    (f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (B : ℝ → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (G : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∃ Lf LB LG : ℝ, 0 < Lf ∧ 0 < LB ∧ 0 < LG ∧
    LipOnΩ T f Lf ∧ LipOnΩ T B LB ∧ LipOnΩ T G LG

/-- Assumption (B), p. 29: `B` is bounded on `Ω` in operator norm,
`σ_B = sup_{(t,x) ∈ Ω} ‖B(t, x)‖ < ∞`. -/
def CondB {n m : ℕ} (T : ℝ)
    (B : ℝ → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ σB : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ x, ‖B t x‖ ≤ σB

/-- The range `G(Ω) = {G(t, x) : (t, x) ∈ [0, T] × ℝⁿ}`. -/
def GOmega {n m : ℕ} (T : ℝ)
    (G : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {q | ∃ t ∈ Set.Icc 0 T, ∃ x, q = G t x}

/-- Weak (Carathéodory) solution of the initial-value DVI (6.2) on `[0, T]` (§2.1, pp. 4–5, with
`Γ(x, y) = x − x⁰` and `F(t, x, u) = G(t, x) + F(u)`):
`x(0) = x⁰`; `u` is integrable on `[0, T]` with values in `K` a.e.; `x` satisfies the integral
equation `x(t) − x(s) = ∫ₛᵗ (f(τ, x(τ)) + B(τ, x(τ)) u(τ)) dτ` for `0 ≤ s ≤ t ≤ T` with an integrable
integrand; and for every continuous `ũ : [0, T] → K` the integrand of (2.4) is integrable with
`∫₀ᵀ (ũ(t) − u(t))ᵀ (G(t, x(t)) + F(u(t))) dt ≥ 0`. -/
def IsWeakSolution {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (B : ℝ → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (G : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (T : ℝ)
    (x0 : EuclideanSpace ℝ (Fin n)) (x : ℝ → EuclideanSpace ℝ (Fin n))
    (u : ℝ → EuclideanSpace ℝ (Fin m)) : Prop :=
  x 0 = x0 ∧
  IntegrableOn u (Set.Icc 0 T) ∧
  (∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)), u t ∈ K) ∧
  IntegrableOn (fun τ => f τ (x τ) + B τ (x τ) (u τ)) (Set.Icc 0 T) ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
    x t - x s = ∫ τ in s..t, (f τ (x τ) + B τ (x τ) (u τ))) ∧
  ∀ ub : ℝ → EuclideanSpace ℝ (Fin m), ContinuousOn ub (Set.Icc 0 T) →
    (∀ t ∈ Set.Icc 0 T, ub t ∈ K) →
    IntegrableOn (fun t => ⟪ub t - u t, G t (x t) + F (u t)⟫_ℝ) (Set.Icc 0 T) ∧
    0 ≤ ∫ t in (0 : ℝ)..T, ⟪ub t - u t, G t (x t) + F (u t)⟫_ℝ

/-- `H` is monotone on `S`: `(u − u')ᵀ(H(u) − H(u')) ≥ 0` for `u, u' ∈ S` (p. 32). -/
def IsMonotoneOn {m : ℕ} (H : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (S : Set (EuclideanSpace ℝ (Fin m))) : Prop :=
  ∀ u ∈ S, ∀ u' ∈ S, 0 ≤ ⟪u - u', H u - H u'⟫_ℝ

/-- `H` is strongly monotone on `S` with modulus `η > 0`:
`(u − u')ᵀ(H(u) − H(u')) ≥ η ‖u − u'‖²` for `u, u' ∈ S` (p. 32). -/
def IsStronglyMonotoneOn {m : ℕ} (H : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (S : Set (EuclideanSpace ℝ (Fin m))) (η : ℝ) : Prop :=
  0 < η ∧ ∀ u ∈ S, ∀ u' ∈ S, η * ‖u - u'‖ ^ 2 ≤ ⟪u - u', H u - H u'⟫_ℝ

/-- The dual cone `C* = {v : uᵀv ≥ 0 ∀ u ∈ C}` (p. 4). -/
def dualCone {m : ℕ} (C : Set (EuclideanSpace ℝ (Fin m))) : Set (EuclideanSpace ℝ (Fin m)) :=
  {v | ∀ u ∈ C, 0 ≤ ⟪u, v⟫_ℝ}

/-- The recession cone `K∞ = {d : x + τ d ∈ K ∀ x ∈ K, τ ≥ 0}` (p. 29). -/
def recCone {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) : Set (EuclideanSpace ℝ (Fin m)) :=
  {d | ∀ x ∈ K, ∀ τ : ℝ, 0 ≤ τ → x + τ • d ∈ K}

/-- `D` is positive semidefinite (not necessarily symmetric): `uᵀDu ≥ 0` for all `u`. -/
def IsPSD {m : ℕ} (D : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ u, 0 ≤ ⟪u, D u⟫_ℝ

/-- `D` is psd-plus (p. 37): positive semidefinite and `uᵀDu = 0 ⇒ Du = 0`. -/
def IsPSDPlus {m : ℕ} (D : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) : Prop :=
  IsPSD D ∧ ∀ u, ⟪u, D u⟫_ℝ = 0 → D u = 0

/-- The VI kernel `𝒦(K, D)` (6.7), p. 34: the solutions of the homogeneous CP
`K∞ ∋ v ⊥ Dv ∈ (K∞)*`. -/
def viKernel {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (D : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    Set (EuclideanSpace ℝ (Fin m)) :=
  {v | v ∈ recCone K ∧ D v ∈ dualCone (recCone K) ∧ ⟪v, D v⟫_ℝ = 0}

/-- `(K, D)` is an R₀ pair (p. 34): `𝒦(K, D) = {0}`. -/
def IsR0Pair {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (D : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) : Prop :=
  viKernel K D = {0}

/-- `K` is a polyhedron: the solution set of finitely many linear inequalities `aᵢᵀu ≤ bᵢ`. -/
def IsPolyhedron {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) : Prop :=
  ∃ (p : ℕ) (a : Fin p → EuclideanSpace ℝ (Fin m)) (b : Fin p → ℝ),
    K = {u | ∀ i, ⟪a i, u⟫_ℝ ≤ b i}

/-- `K` contains no lines: no `x ∈ K` and `d ≠ 0` with `x + τ d ∈ K` for every real `τ`. -/
def ContainsNoLines {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) : Prop :=
  ∀ x ∈ K, ∀ d : EuclideanSpace ℝ (Fin m), (∀ τ : ℝ, x + τ • d ∈ K) → d = 0

/-- The set-valued map `𝐅(t, x) = {f(t, x) + B(t, x)u : u ∈ SOL(K, G(t, x) + F)}` of (6.4). -/
def bigF {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (B : ℝ → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (G : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∃ u ∈ SolodovSvaiterVI.Alg21.viSol (fun v => G t x + F v) K, y = f t x + B t x u}

/-- The linear growth property (6.5) on `G(Ω)`: `‖u‖ ≤ ρ (1 + ‖q‖)` for every `q ∈ G(Ω)` and every
`u ∈ SOL(K, q + F)` (no nonemptiness is asserted). -/
def LinGrowthSOL {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (G : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (T ρ : ℝ) : Prop :=
  ∀ q ∈ GOmega T G, ∀ u ∈ SolodovSvaiterVI.Alg21.viSol (fun v => q + F v) K,
    ‖u‖ ≤ ρ * (1 + ‖q‖)

/-- The coercivity condition (6.6), p. 32,
`liminf_{u ∈ K, ‖u‖ → ∞} (u − u^ref)ᵀF(u) / ‖u‖² > 0`, in the equivalent form: there are `c > 0`
and `R` with `(u − u^ref)ᵀF(u) ≥ c ‖u‖²` for all `u ∈ K` with `‖u‖ ≥ R`. -/
def Coercive66 {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (uref : EuclideanSpace ℝ (Fin m)) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ R : ℝ, ∀ u ∈ K, R ≤ ‖u‖ → c * ‖u‖ ^ 2 ≤ ⟪u - uref, F u⟫_ℝ

/-- A set-valued map `Φ : Ω ⇉ ℝⁿ` is upper semicontinuous on `Ω = [0, T] × ℝⁿ`: for every
`(t, x) ∈ Ω` and every open `V ⊇ Φ(t, x)`, `Φ(t', x') ⊆ V` for all `(t', x') ∈ Ω` near `(t, x)`. -/
def IsUSCOnΩ {n : ℕ} (T : ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ t ∈ Set.Icc 0 T, ∀ (x : EuclideanSpace ℝ (Fin n)) (V : Set (EuclideanSpace ℝ (Fin n))),
    IsOpen V → Φ t x ⊆ V →
      ∀ᶠ p in 𝓝[Set.Icc 0 T ×ˢ Set.univ] (t, x), Φ p.1 p.2 ⊆ V

/-- Weak (Carathéodory) solution on `[0, T]` of the differential inclusion `ẋ ∈ Φ(t, x)`,
`x(0) = x⁰`: `x(t) = x⁰ + ∫₀ᵗ v` on `[0, T]` for an integrable `v` with `v(t) ∈ Φ(t, x(t))` for
almost every `t ∈ [0, T]`. -/
def IsDIWeakSolution {n : ℕ} (T : ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (x0 : EuclideanSpace ℝ (Fin n)) (x : ℝ → EuclideanSpace ℝ (Fin n)) : Prop :=
  x 0 = x0 ∧ ∃ v : ℝ → EuclideanSpace ℝ (Fin n), IntegrableOn v (Set.Icc 0 T) ∧
    (∀ t ∈ Set.Icc 0 T, x t = x0 + ∫ s in (0 : ℝ)..t, v s) ∧
    ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)), v t ∈ Φ t (x t)

end DiffVI.Exist


