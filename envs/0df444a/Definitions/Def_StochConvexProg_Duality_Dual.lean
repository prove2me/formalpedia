-- Prove2me | Definitions.Def_StochConvexProg_Duality_Dual
-- name    : StochConvexProg_Duality_Dual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:10:41.352652+00:00
-- url     : https://prove2.me/theorems/55eb0a63-6562-4b22-8528-dcce2f1b183d
-- title:
--   The pairings (1.6), (2.11), the weak topologies, the Lagrangian L, the dual D, the perturbation function φ, the conjugates φ*, φ**, and X₀, X₀′, Y₀, L₁, L₂
-- statement:
--   Fix a problem as in the definition of the model, with $X=\mathbb R^{n_1}\times\mathcal L^\infty_{n_2}$ and $U=\mathbb R^{m_1}\times\mathcal L^\infty_{m_2}$.
--
--   1. **Paired spaces.** $Y=\mathbb R^{m_1}\times\mathcal L^1_{m_2}$ and $V=\mathbb R^{n_1}\times\mathcal L^1_{n_2}$, with the bilinear pairings
--   $$\langle u,y\rangle=u_1\cdot y_1+\int_S u_2(s)\cdot y_2(s)\,\sigma(ds)\quad(1.6),\qquad \langle x,v\rangle=x_1\cdot v_1+\int_S x_2(s)\cdot v_2(s)\,\sigma(ds)\quad(2.11).$$
--   2. **Weak topologies.** The weak topology on $U$ induced by $Y$ is the coarsest topology making every $u\mapsto\langle u,y\rangle$ continuous; likewise on $X$ induced by $V$, and on $\mathcal L^\infty_{n_2}$ induced by $\mathcal L^1_{n_2}$ through $x_2\mapsto\int_S x_2(s)\cdot v(s)\,\sigma(ds)$.
--   3. **Lagrangian, dual and values.**
--   $$L(x,y)=\inf_{u\in U}\{\langle u,y\rangle+F(x,u)\}\quad(1.7),\qquad g(y)=\inf_{x\in X}L(x,y),$$
--   $$\inf\mathbf P=\inf_{x\in X}F(x,0),\qquad \sup\mathbf D=\sup_{y\in Y}g(y)\quad(1.16),\qquad \varphi(u)=\inf_{x\in X}F(x,u)\quad(1.17).$$
--   4. **Conjugates with respect to (1.6).** For $\varphi:U\to[-\infty,+\infty]$,
--   $$\varphi^*(y)=\sup_{u\in U}\{\langle u,y\rangle-\varphi(u)\},\qquad \varphi^{**}(u)=\sup_{y\in Y}\{\langle u,y\rangle-\varphi^*(y)\}.$$
--   5. **Convex, proper.** An extended-real function is *convex* if its epigraph $\{(e,\alpha)\in E\times\mathbb R:\varphi(e)\le\alpha\}$ is convex, and *proper* if it never takes $-\infty$ and is not identically $+\infty$.
--   6. **Sets.** $X_0=\{x\in X: x_1\in C_1,\ x_2(s)\in C_2\text{ a.s.}\}$ (1.9), $X_0'=\{x_2\in\mathcal L^\infty_{n_2}: x_2(s)\in C_2\text{ a.s.}\}$ (4.9), $Y_0=\{y\in Y: y_1\ge0,\ y_2(s)\ge0\text{ a.s.}\}$ (1.10), componentwise.
--   7. **Integrands of (1.8).** $L_1(x_1,y_1)=f_{10}(x_1)+\sum_{i=1}^{m_1}y_{1i}f_{1i}(x_1)$ (1.11) and $L_2(s,x_1,x_2,y_2)=f_{20}(s,x_1,x_2)+\sum_{i=1}^{m_2}y_{2i}f_{2i}(s,x_1,x_2)$ (1.12).
--
--   These are the objects in which the duality theory of the paper (§§1, 2, 4) is stated.
--
--   **Formalization Note** Infima and suprema are taken in `EReal` (complete lattice), so no junk value arises from empty or unbounded sets. Every sum has a real first summand ($\langle u,y\rangle$ is real) and a second summand that is never $-\infty$ in the Lagrangian, so the `EReal` conventions $\top+\bot=\bot$ never bite; real minus an extended real is unambiguous. The integrands of the pairings are products of an $\mathcal L^\infty$ and an $\mathcal L^1$ function, hence integrable. The weak topologies are infima of induced topologies, and are passed explicitly where used, never left to instance resolution (which would pick the norm topology). The conjugates are with respect to the pairing (1.6), not the norm dual of $\mathcal L^\infty$.
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), p. 175 (1.6)–(1.12), p. 176 (1.16), p. 177 (1.17), p. 183 (2.11)–(2.12), p. 188 (φ*, φ**), p. 190 (4.9), p. 191 (proper)

import Mathlib
import Definitions.Def_StochConvexProg_Duality_Problem

open MeasureTheory

namespace StochConvexProg.Duality

/-- (1.6), p. 175: `Y = R^{m₁} × ℒ¹_{m₂}`, the space paired with `U`. -/
abbrev YSpace {S : Type*} [MeasurableSpace S] (σ : Measure S) (m₁ m₂ : ℕ) :=
  (Fin m₁ → ℝ) × Lp (Fin m₂ → ℝ) 1 σ

/-- (2.12), p. 183: `V = Rⁿ¹ × ℒ¹_{n₂}`, the space paired with `X`. -/
abbrev VSpace {S : Type*} [MeasurableSpace S] (σ : Measure S) (n₁ n₂ : ℕ) :=
  (Fin n₁ → ℝ) × Lp (Fin n₂ → ℝ) 1 σ

/-- (1.6), p. 175: `⟨u, y⟩ = u₁ · y₁ + ∫_S u₂(s) · y₂(s) σ(ds)`. -/
noncomputable def pairUY {S : Type*} [MeasurableSpace S] {σ : Measure S} {m₁ m₂ : ℕ}
    (u : USpace σ m₁ m₂) (y : YSpace σ m₁ m₂) : ℝ :=
  u.1 ⬝ᵥ y.1 + ∫ s, u.2 s ⬝ᵥ y.2 s ∂σ

/-- (2.11), p. 183: `⟨x, v⟩ = x₁ · v₁ + ∫_S x₂(s) · v₂(s) σ(ds)`. -/
noncomputable def pairXV {S : Type*} [MeasurableSpace S] {σ : Measure S} {n₁ n₂ : ℕ}
    (x : XSpace σ n₁ n₂) (v : VSpace σ n₁ n₂) : ℝ :=
  x.1 ⬝ᵥ v.1 + ∫ s, x.2 s ⬝ᵥ v.2 s ∂σ

/-- The weak topology on `U` induced by the pairing (1.6) with `Y` (pp. 183, 189): the coarsest
topology making every `u ↦ ⟨u, y⟩` continuous. -/
noncomputable def weakU {S : Type*} [MeasurableSpace S] (σ : Measure S) (m₁ m₂ : ℕ) :
    TopologicalSpace (USpace σ m₁ m₂) :=
  ⨅ y : YSpace σ m₁ m₂, TopologicalSpace.induced (fun u => pairUY u y) inferInstance

/-- The weak topology on `X` induced by `V` in the pairing (2.11)–(2.12) (pp. 183, 189). -/
noncomputable def weakX {S : Type*} [MeasurableSpace S] (σ : Measure S) (n₁ n₂ : ℕ) :
    TopologicalSpace (XSpace σ n₁ n₂) :=
  ⨅ v : VSpace σ n₁ n₂, TopologicalSpace.induced (fun x => pairXV x v) inferInstance

/-- The weak topology induced on `ℒ^∞_{n₂}` by `ℒ¹_{n₂}` (p. 190). -/
noncomputable def weakLinf {S : Type*} [MeasurableSpace S] (σ : Measure S) (n₂ : ℕ) :
    TopologicalSpace (Lp (Fin n₂ → ℝ) ⊤ σ) :=
  ⨅ v : Lp (Fin n₂ → ℝ) 1 σ,
    TopologicalSpace.induced (fun x₂ : Lp (Fin n₂ → ℝ) ⊤ σ => ∫ s, x₂ s ⬝ᵥ v s ∂σ) inferInstance

/-- (1.7), p. 175: the Lagrangian `L(x, y) = inf_{u ∈ U} {⟨u, y⟩ + F(x, u)}`. -/
noncomputable def Problem.Lag {S : Type*} [MeasurableSpace S] {σ : Measure S}
    {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) (x : XSpace σ n₁ n₂)
    (y : YSpace σ m₁ m₂) : EReal :=
  ⨅ u : USpace σ m₁ m₂, ((pairUY u y : ℝ) : EReal) + pr.F x u

/-- p. 176: the dual objective `g(y) = inf_{x ∈ X} L(x, y)`. -/
noncomputable def Problem.dualObj {S : Type*} [MeasurableSpace S] {σ : Measure S}
    {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) (y : YSpace σ m₁ m₂) : EReal :=
  ⨅ x : XSpace σ n₁ n₂, pr.Lag x y

/-- p. 175: `inf P = inf_{x ∈ X} F(x, 0)`. -/
noncomputable def Problem.infP {S : Type*} [MeasurableSpace S] {σ : Measure S}
    {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) : EReal :=
  ⨅ x : XSpace σ n₁ n₂, pr.F x 0

/-- (1.16), p. 176: `sup D = sup_{y ∈ Y} g(y)`. -/
noncomputable def Problem.supD {S : Type*} [MeasurableSpace S] {σ : Measure S}
    {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) : EReal :=
  ⨆ y : YSpace σ m₁ m₂, pr.dualObj y

/-- (1.17), p. 177: the perturbation function `φ(u) = inf_{x ∈ X} F(x, u)`. -/
noncomputable def Problem.phi {S : Type*} [MeasurableSpace S] {σ : Measure S}
    {n₁ n₂ m₁ m₂ : ℕ} (pr : Problem S σ n₁ n₂ m₁ m₂) (u : USpace σ m₁ m₂) : EReal :=
  ⨅ x : XSpace σ n₁ n₂, pr.F x u

/-- p. 188: the conjugate `φ*(y) = sup_{u ∈ U} {⟨u, y⟩ − φ(u)}` on `Y` with respect to (1.6). -/
noncomputable def conjU {S : Type*} [MeasurableSpace S] {σ : Measure S} {m₁ m₂ : ℕ}
    (φ : USpace σ m₁ m₂ → EReal) (y : YSpace σ m₁ m₂) : EReal :=
  ⨆ u : USpace σ m₁ m₂, ((pairUY u y : ℝ) : EReal) - φ u

/-- p. 188: the biconjugate `φ**(u) = sup_{y ∈ Y} {⟨u, y⟩ − φ*(y)}`. -/
noncomputable def biconjU {S : Type*} [MeasurableSpace S] {σ : Measure S} {m₁ m₂ : ℕ}
    (φ : USpace σ m₁ m₂ → EReal) (u : USpace σ m₁ m₂) : EReal :=
  ⨆ y : YSpace σ m₁ m₂, ((pairUY u y : ℝ) : EReal) - conjU φ y

/-- An extended-real-valued function is convex when its epigraph is convex. -/
def EConvex {E : Type*} [AddCommGroup E] [Module ℝ E] (φ : E → EReal) : Prop :=
  Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)}

/-- p. 191: proper — nowhere `−∞` and not identically `+∞`. -/
def EProper {E : Type*} (φ : E → EReal) : Prop :=
  (∀ e, φ e ≠ ⊥) ∧ ∃ e, φ e ≠ ⊤

/-- (1.9), p. 175: `X₀ = {x ∈ X | x₁ ∈ C₁ and almost surely x₂(s) ∈ C₂}`. -/
def Problem.X₀ {S : Type*} [MeasurableSpace S] {σ : Measure S} {n₁ n₂ m₁ m₂ : ℕ}
    (pr : Problem S σ n₁ n₂ m₁ m₂) : Set (XSpace σ n₁ n₂) :=
  {x | x.1 ∈ pr.C₁ ∧ ∀ᵐ s ∂σ, x.2 s ∈ pr.C₂}

/-- (4.9), p. 190: `X₀′ = {x₂ ∈ ℒ^∞_{n₂} | x₂(s) ∈ C₂ almost surely}`. -/
def Problem.X₀' {S : Type*} [MeasurableSpace S] {σ : Measure S} {n₁ n₂ m₁ m₂ : ℕ}
    (pr : Problem S σ n₁ n₂ m₁ m₂) : Set (Lp (Fin n₂ → ℝ) ⊤ σ) :=
  {x₂ | ∀ᵐ s ∂σ, x₂ s ∈ pr.C₂}

/-- (1.10), p. 175: `Y₀ = {y ∈ Y | y₁ ≥ 0 and almost surely y₂(s) ≥ 0}` (componentwise). -/
def Y₀ {S : Type*} [MeasurableSpace S] (σ : Measure S) (m₁ m₂ : ℕ) : Set (YSpace σ m₁ m₂) :=
  {y | (∀ i, 0 ≤ y.1 i) ∧ ∀ᵐ s ∂σ, ∀ i, 0 ≤ y.2 s i}

/-- (1.11), p. 176: `L₁(x₁, y₁) = f₁₀(x₁) + Σ_{i=1}^{m₁} y₁ᵢ f₁ᵢ(x₁)`. -/
def Problem.L₁ {S : Type*} [MeasurableSpace S] {σ : Measure S} {n₁ n₂ m₁ m₂ : ℕ}
    (pr : Problem S σ n₁ n₂ m₁ m₂) (x₁ : Fin n₁ → ℝ) (y₁ : Fin m₁ → ℝ) : ℝ :=
  pr.f₁₀ x₁ + ∑ i, y₁ i * pr.f₁ i x₁

/-- (1.12), p. 176: `L₂(s, x₁, x₂, y₂) = f₂₀(s, x₁, x₂) + Σ_{i=1}^{m₂} y₂ᵢ f₂ᵢ(s, x₁, x₂)`. -/
def Problem.L₂ {S : Type*} [MeasurableSpace S] {σ : Measure S} {n₁ n₂ m₁ m₂ : ℕ}
    (pr : Problem S σ n₁ n₂ m₁ m₂) (s : S) (x₁ : Fin n₁ → ℝ) (x₂ : Fin n₂ → ℝ)
    (y₂ : Fin m₂ → ℝ) : ℝ :=
  pr.f₂₀ s x₁ x₂ + ∑ i, y₂ i * pr.f₂ i s x₁ x₂

end StochConvexProg.Duality


