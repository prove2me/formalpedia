-- Prove2me | Definitions.Def_FuzzyGames_Values_Basic
-- name    : FuzzyGames_Values_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:13:17.340533+00:00
-- url     : https://prove2.me/theorems/c7dd3302-3bfa-4f68-817f-0a2ef6a73cf8
-- title:
--   §8 — smooth fuzzy games V^n, the C¹ seminorm, the axioms of a sequence of fuzzy values, the diagonal formula (4), the fuzzy core and Owen's extension
-- statement:
--   Let $N=\{1,\dots,n\}$ be the set of players. A **fuzzy coalition** is a vector $\tau\in[0,1]^n$ whose coordinate $\tau_i$ is the rate of participation of player $i$; the full coalition is $\tau^N=(1,\dots,1)$.
--
--   1. **Smooth fuzzy games.** $V^n$ is the vector space of coalitional worth functions $v$ that are continuously differentiable and vanish at $0$. It carries the C¹ seminorm of the cube,
--   $$\|v\|_{C^1}=\sup_{\tau\in[0,1]^n}|v(\tau)|+\sup_{\tau\in[0,1]^n}\|Dv(\tau)\|,$$
--   and a linear map $\psi_n:V^n\to\mathbb R^n$ is **continuous** if $\|\psi_n v\|\le C\,\|v\|_{C^1}$ for some constant $C$ and all $v\in V^n$.
--   2. **Pareto optimality.** For all $n\ge1$ and $v\in V^n$, $\sum_{i\in N}(\psi_n v)_i=v(\tau^N)$.
--   3. **Symmetry.** For every permutation $\theta$ of $N$, set $(\theta^*v)(\tau_1,\dots,\tau_n)=v(\tau_{\theta^{-1}(1)},\dots,\tau_{\theta^{-1}(n)})$ and $(\theta^*c)_i=c_{\theta(i)}$; then $\psi_n(\theta^*v)=\theta^*(\psi_n v)$.
--   4. **Atomicity.** A partition $P=\{A_1,\dots,A_m\}$ of $N$ into $m$ nonempty types induces, from a fuzzy coalition $\sigma\in[0,1]^m$ of types, the fuzzy coalition $(P\cdot\sigma)_i=\sigma_j$ for $i\in A_j$, and the $m$-type game $(P^*v)(\sigma)=v(P\cdot\sigma)$. The axiom requires $\psi_m(P^*v)_j=\sum_{i\in A_j}(\psi_n v)_i$.
--   5. A **sequence of fuzzy values** is a family of continuous linear maps $\psi_n:V^n\to\mathbb R^n$ satisfying Pareto optimality, symmetry and atomicity.
--   6. The **diagonal formula** (4) is
--   $$(\psi_n v)_i=\int_0^1 \frac{\partial v}{\partial\tau_i}(t\tau^N)\,dt .$$
--   7. The **core** of a fuzzy game with side payments $v$ is the set of $c\in\mathbb R^n$ with $\sum_i c_i=v(\tau^N)$ and $\sum_i\tau_i c_i\ge v(\tau)$ for every $\tau\in[0,1]^n$; $v$ is **positively homogeneous** if $v(t\tau)=t\,v(\tau)$ for all $t>0$ and $\tau\in\mathbb R^n_+$.
--   8. The **monomial** with exponent $k\in\mathbb N^n$ is $\tau^k=\tau_1^{k_1}\cdots\tau_n^{k_n}$, and **Owen's multilinear extension** of a coalitional worth function $f$ defined on all coalitions is $xv(\tau)=\sum_{A\subseteq N} f(A)\prod_{i\in A}\tau_i\prod_{j\notin A}(1-\tau_j)$.
--
--   These objects are the vocabulary of Theorem 8.1, which characterises the diagonal formula as the unique sequence of fuzzy values.
--
--   **Formalization Note** Players are `Fin n`. The elements of $V^n$ are functions on all of $\mathbb R^n$ that are $C^1$ there (`ContDiff ℝ 1`) and vanish at $0$; the paper's $C^1$ functions on the cube extend to such functions, and only values and derivatives on the cube enter the seminorm and the axioms. This global domain makes $v\circ A$ meaningful for every linear $A$. The norm on $\mathbb R^n$ is the sup norm and $\|Dv(\tau)\|$ the operator norm; every norm gives the same continuity notion. The axioms are stated for functions $\psi_n:V^n\to\mathbb R^n$ (not necessarily linear), so the lemmas that use only some axioms need no linearity; the games $\theta^*v$ and $P^*v$ are passed as elements $w\in V^n$, $w\in V^m$ with the defining identity, since they always lie in these spaces. A partition into $m$ nonempty types is a surjection $P:$ `Fin n → Fin m`. The paper's "$\forall n\in N$" in the symmetry axiom is read as $n\ge1$, and its "$\forall v\in V^m$" in (3) as $v\in V^n$, since $P^*v$ is defined by (2) for an $n$-player $v$. The core quantifies over the cube, as in §2 (4)(a).
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), §8 pp. 10–11 (axioms, (1)–(3), (4), Remark 8.2 (8)); §2 (1), (4)(a), p. 2–3

import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic
import Definitions.Def_FuzzyGames_TUCore_Basic

namespace FuzzyGames.Values

open Set Finset

/-- The space `V^n` of §8 (p. 10): coalitional worth functions that are continuously
differentiable and vanish at `0`. The functions are defined on all of `ℝ^n` (globally `C¹`);
only their values and derivatives on the FuzzyGames.NTUCore.cube enter the C¹ seminorm and the axioms. -/
def Vn (n : ℕ) : Submodule ℝ ((Fin n → ℝ) → ℝ) where
  carrier := {v | ContDiff ℝ 1 v ∧ v 0 = 0}
  add_mem' := fun ha hb => ⟨ha.1.add hb.1, by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨contDiff_const, rfl⟩
  smul_mem' := fun c _ hv => ⟨hv.1.const_smul c, by simp [hv.2]⟩

/-- The C¹ seminorm on the FuzzyGames.NTUCore.cube: `sup_{τ ∈ [0,1]^n} |v τ| + sup_{τ ∈ [0,1]^n} ‖Dv(τ)‖`.
Both suprema are finite for `v ∈ V^n` (continuous functions on a compact set). -/
noncomputable def c1seminorm {n : ℕ} (v : (Fin n → ℝ) → ℝ) : ℝ :=
  (⨆ τ : FuzzyGames.NTUCore.cube n, |v τ|) + ⨆ τ : FuzzyGames.NTUCore.cube n, ‖fderiv ℝ v τ‖

/-- A linear map `ψ : V^n → ℝ^n` is continuous for the C¹ norm of the FuzzyGames.NTUCore.cube. -/
def IsC1Continuous {n : ℕ} (ψ : Vn n →ₗ[ℝ] (Fin n → ℝ)) : Prop :=
  ∃ C : ℝ, ∀ v : Vn n, ‖ψ v‖ ≤ C * c1seminorm v.1

/-- PARETO OPTIMALITY (§8, p. 10): `∀ n ≥ 1, ∀ v ∈ V^n, ∑_{i ∈ N} (ψ_n v)^i = v(τ^N)`,
with `τ^N = (1, …, 1)`. -/
def IsParetoOptimal (ψ : (n : ℕ) → Vn n → (Fin n → ℝ)) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ v : Vn n, ∑ i, ψ n v i = v.1 1

/-- SYMMETRY AXIOM (§8, p. 10): for every permutation `θ` of the players,
`ψ_n(θ*v) = θ*(ψ_n v)`, where `(θ*v)(τ) = v(τ_{θ⁻¹(1)}, …, τ_{θ⁻¹(n)})` and
`(θ*c)_i = c_{θ(i)}`. Here `w` is the game `θ*v`. -/
def IsSymmetric (ψ : (n : ℕ) → Vn n → (Fin n → ℝ)) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ θ : Equiv.Perm (Fin n), ∀ v w : Vn n,
    (∀ τ : Fin n → ℝ, w.1 τ = v.1 (fun i => τ (θ.symm i))) →
      ∀ i : Fin n, ψ n w i = ψ n v (θ i)

/-- ATOMICITY AXIOM (§8, p. 10, (1)–(3)): a partition of the `n` players into `m` nonempty
types is a surjection `P : Fin n → Fin m` (type `A_j = P⁻¹{j}`); a fuzzy coalition `σ` of types
induces `(P · σ)_i = σ_{P i}`, and `(P*v)(σ) = v(P · σ)`. The axiom requires
`ψ_m(P*v)_j = ∑_{i ∈ A_j} (ψ_n v)_i`. Here `w` is the game `P*v`. -/
def IsAtomic (ψ : (n : ℕ) → Vn n → (Fin n → ℝ)) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ m : ℕ, ∀ P : Fin n → Fin m, Function.Surjective P →
    ∀ (v : Vn n) (w : Vn m), (∀ σ : Fin m → ℝ, w.1 σ = v.1 (fun i => σ (P i))) →
      ∀ j : Fin m, ψ m w j = ∑ i ∈ Finset.univ.filter (fun i => P i = j), ψ n v i

/-- A sequence of fuzzy values (§8, p. 10): continuous (for the C¹ norm) linear operators
`ψ_n : V^n → ℝ^n` satisfying Pareto optimality, symmetry and atomicity. -/
def IsSequenceOfFuzzyValues (ψ : (n : ℕ) → Vn n →ₗ[ℝ] (Fin n → ℝ)) : Prop :=
  (∀ n : ℕ, 0 < n → IsC1Continuous (ψ n)) ∧
    IsParetoOptimal (fun n => ⇑(ψ n)) ∧ IsSymmetric (fun n => ⇑(ψ n)) ∧
    IsAtomic (fun n => ⇑(ψ n))

/-- The diagonal formula (4) of Theorem 8.1 (p. 10):
`(ψ_n v)_i = ∫_0^1 ∂_i v(t τ^N) dt`, the integral of the gradient along the diagonal. -/
noncomputable def diagValue {n : ℕ} (v : (Fin n → ℝ) → ℝ) : Fin n → ℝ :=
  fun i => ∫ t in (0 : ℝ)..1, fderiv ℝ v (t • (1 : Fin n → ℝ)) (Pi.single i 1)

/-- Positive homogeneity on the orthant `ℝ^n_+` (§2, (1)–(2), p. 2):
`v(t τ) = t v(τ)` for all `t > 0` and `τ ≥ 0`. -/
def IsPosHomogeneous {n : ℕ} (v : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ τ : Fin n → ℝ, 0 ≤ τ → v (t • τ) = t * v τ

/-- A monomial `τ ↦ τ_1^{k_1} ⋯ τ_n^{k_n}`. -/
def monomial {n : ℕ} (k : Fin n → ℕ) : (Fin n → ℝ) → ℝ :=
  fun τ => ∏ i, τ i ^ k i

/-- Owen's multilinear extension (Remark 8.2, (8), p. 11) of a coalitional worth function
`f` defined on all coalitions: `xv(τ) = ∑_A f(A) ∏_{i∈A} τ_i ∏_{j∉A} (1 − τ_j)`. -/
noncomputable def owenExtension {n : ℕ} (f : Finset (Fin n) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun τ => ∑ A : Finset (Fin n), f A * (∏ i ∈ A, τ i) * ∏ j ∈ Aᶜ, (1 - τ j)

end FuzzyGames.Values


