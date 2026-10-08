-- Prove2me | Definitions.Def_QuantumWalkSearch_PhaseReflection_Walk
-- name    : QuantumWalkSearch_PhaseReflection_Walk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T08:45:04.607331+00:00
-- url     : https://prove2.me/theorems/078f876d-64f2-4305-9351-cfceee24b0fd
-- title:
--   The Szegedy walk $W(P)=\mathrm{ref}(\mathcal B)\cdot\mathrm{ref}(\mathcal A)$, the state $|\pi\rangle$, the discriminant $D(P)$ and the phase gap $\Delta(P)$ (§1.2, §2, §3.1)
-- statement:
--   Let $X$ be a finite state space and $P=(p_{xy})_{x,y\in X}$ a Markov chain on $X$ ($p_{xy}$ is the probability of a transition from $x$ to $y$). A **stationary distribution** is a vector $\pi=(\pi_x)$ with $\pi_x>0$, $\sum_x\pi_x=1$ and $\sum_x \pi_x p_{xy}=\pi_y$ for every $y$. The **time-reversed chain** $P^*=(p^*_{xy})$ is defined by $\pi_x p_{xy}=\pi_y p^*_{yx}$, and $P$ is **reversible** if $P^*=P$, i.e. $\pi_x p_{xy}=\pi_y p_{yx}$ for all $x,y$.
--
--   The **discriminant matrix** is the real $X\times X$ matrix
--   $$D(P)=\big(\sqrt{p_{xy}\,p^*_{yx}}\big)_{x,y\in X}.$$
--   A real number $c$ is a **singular value** of $D(P)$ if it is one of its $|X|$ singular values listed with repetition; the **multiplicity** of $c$ is the number of times it occurs in that list. The **phase gap** is $\Delta(P)=2\theta$, where $\theta$ is the smallest angle in $(0,\pi/2)$ such that $\cos\theta$ is a singular value of $D(P)$.
--
--   On the Hilbert space $\mathcal H=\mathbb C^{X\times X}$, with computational basis $|x\rangle|y\rangle$, put
--   $$|x\rangle|p_x\rangle=\sum_{y\in X}\sqrt{p_{xy}}\,|x\rangle|y\rangle,\qquad |p^*_y\rangle|y\rangle=\sum_{x\in X}\sqrt{p^*_{yx}}\,|x\rangle|y\rangle,$$
--   and let $\mathcal A=\mathrm{Span}(|x\rangle|p_x\rangle : x\in X)$ and $\mathcal B=\mathrm{Span}(|p^*_y\rangle|y\rangle : y\in X)$. For a subspace $\mathcal K$, $\mathrm{ref}(\mathcal K)=2\Pi_{\mathcal K}-\mathrm{Id}$ is the reflection through $\mathcal K$, $\Pi_{\mathcal K}$ being the orthogonal projector. The **quantum walk** based on $P$ is
--   $$W(P)=\mathrm{ref}(\mathcal B)\cdot\mathrm{ref}(\mathcal A),$$
--   and the initial state of the search is $|\pi\rangle=\sum_{x\in X}\sqrt{\pi_x}\,|x\rangle|p_x\rangle$.
--
--   Finally, the file names the left and right **singular subspaces** carried into $\mathcal H$: for $c\ge 0$, the image of $\{u\in\mathbb C^X : D D^{\mathsf T}u=c^2u\}$ under $u\mapsto\sum_x u_x|x\rangle|p_x\rangle$ (left singular vectors, mapped into $\mathcal A$), and the image of $\{v\in\mathbb C^X : D^{\mathsf T}Dv=c^2v\}$ under $v\mapsto\sum_y v_y|p^*_y\rangle|y\rangle$ (right singular vectors, mapped into $\mathcal B$).
--
--   These are the objects of Szegedy's spectral theorem (Theorem 4) and of the reflection circuit of Theorem 6; every statement of the mission is written with them.
--
--   **Formalization Note** $\pi$ is passed as data with the hypotheses above (`IsStationaryDist`); its uniqueness (Perron–Frobenius) is not used. $p^*_{yx}$ is computed as $\pi_x p_{xy}/\pi_y$. $\mathcal H$ is `EuclideanSpace ℂ (X × X)`, the first coordinate being the first register. $\mathrm{ref}(\mathcal K)$ is Mathlib's `Submodule.reflection` ($2\Pi_{\mathcal K}-\mathrm{Id}$, the paper's sign), and $W(P)$ applies $\mathrm{ref}(\mathcal A)$ first. Singular values are Mathlib's `LinearMap.singularValues` of $D(P)$ acting on the real space $\mathbb R^X$ (indices $<|X|$). **Convention for $\Delta(P)$:** when no singular value of $D(P)$ lies in $(0,1)$ the paper's definition is void; then $\Delta(P)=\pi$ (the angle $\theta=\pi/2$ of the eigenvalue $-1$).
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 2 (Section 1.2: stationary distribution, time-reversed chain, reversibility), p. 7 (Section 2: ref, A, B, Definition 1, discriminant D(P), phase gap), p. 8 (Section 3.1: the state |π⟩)

import Mathlib
open scoped ComplexConjugate
noncomputable section

namespace QuantumWalkSearch.PhaseReflection

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The paper's hypotheses on the stationary distribution `π` of `P` (§1.2, p. 2), taken as data:
positive coordinates summing to `1`, and `π` is a left eigenvector of `P` with eigenvalue `1`. -/
structure IsStationaryDist (P : Matrix X X ℝ) (πd : X → ℝ) : Prop where
  pos : ∀ x, 0 < πd x
  sum_eq_one : ∑ x, πd x = 1
  stationary : ∀ y, ∑ x, πd x * P x y = πd y

/-- The time-reversed chain `P* = (p*_{xy})`, defined by `π_x p_{xy} = π_y p*_{yx}` (§1.2, p. 2),
i.e. `p*_{yx} = π_x p_{xy} / π_y`. -/
def timeReversal (P : Matrix X X ℝ) (πd : X → ℝ) : Matrix X X ℝ :=
  fun y x => πd x * P x y / πd y

/-- `P` is reversible (with respect to `π`) if `P* = P`, i.e. `π_x p_{xy} = π_y p_{yx}` for all
`x, y` (§1.2, p. 2). -/
def IsReversible (P : Matrix X X ℝ) (πd : X → ℝ) : Prop :=
  ∀ x y, πd x * P x y = πd y * P y x

/-- The discriminant matrix `D(P) = (√(p_{xy} p*_{yx}))_{x,y}` (§2, p. 7), a real matrix. -/
def discriminant (P : Matrix X X ℝ) (πd : X → ℝ) : Matrix X X ℝ :=
  fun x y => Real.sqrt (P x y * timeReversal P πd y x)

/-- `c` is a singular value of `D(P)`: it is one of the `|X|` singular values (with
repetitions) of `D(P)` viewed as a linear map on the real Euclidean space `ℝ^X`. -/
def IsSingularValue (P : Matrix X X ℝ) (πd : X → ℝ) (c : ℝ) : Prop :=
  ∃ i < Fintype.card X,
    (Matrix.toEuclideanLin (discriminant P πd)).singularValues i = c

/-- The multiplicity of `c` as a singular value of `D(P)`: the number of indices
`i < |X|` with `σ_i(D(P)) = c`. -/
def singularValueMult (P : Matrix X X ℝ) (πd : X → ℝ) (c : ℝ) : ℕ :=
  ((Finset.range (Fintype.card X)).filter fun i =>
    (Matrix.toEuclideanLin (discriminant P πd)).singularValues i = c).card

open Classical in
/-- The phase gap `Δ(P) = 2θ`, where `θ` is the smallest angle in `(0, π/2)` such that `cos θ` is a
singular value of `D(P)` (§2, p. 7). The set of such angles is finite. **Convention:** if no
singular value of `D(P)` lies in `(0, 1)` the paper's definition is void; we then set
`Δ(P) = π` (i.e. `θ = π/2`, the angle of the eigenvalue `-1`). -/
def phaseGap (P : Matrix X X ℝ) (πd : X → ℝ) : ℝ :=
  let Θ : Set ℝ := {θ | θ ∈ Set.Ioo 0 (Real.pi / 2) ∧ IsSingularValue P πd (Real.cos θ)}
  if Θ.Nonempty then 2 * sInf Θ else Real.pi

/-- The Hilbert space `H = ℂ^{X×X}`; the basis vector of `(x, y)` is `|x⟩|y⟩`. -/
abbrev H (X : Type*) [Fintype X] := EuclideanSpace ℂ (X × X)

/-- The vector `|x⟩|p_x⟩ = Σ_y √(p_{xy}) |x⟩|y⟩` (§2, p. 7). -/
def vecA (P : Matrix X X ℝ) (x : X) : H X :=
  WithLp.toLp 2 fun xy => if xy.1 = x then ((Real.sqrt (P x xy.2) : ℝ) : ℂ) else 0

/-- The vector `|p*_y⟩|y⟩ = Σ_x √(p*_{yx}) |x⟩|y⟩` (§2, p. 7). -/
def vecB (P : Matrix X X ℝ) (πd : X → ℝ) (y : X) : H X :=
  WithLp.toLp 2 fun xy =>
    if xy.2 = y then ((Real.sqrt (timeReversal P πd y xy.1) : ℝ) : ℂ) else 0

/-- `A = Span(|x⟩|p_x⟩ : x ∈ X)` (§2, p. 7), a complex subspace of `H`. -/
def spaceA (P : Matrix X X ℝ) : Submodule ℂ (H X) :=
  Submodule.span ℂ (Set.range (vecA P))

/-- `B = Span(|p*_y⟩|y⟩ : y ∈ X)` (§2, p. 7), a complex subspace of `H`. -/
def spaceB (P : Matrix X X ℝ) (πd : X → ℝ) : Submodule ℂ (H X) :=
  Submodule.span ℂ (Set.range (vecB P πd))

/-- The quantum walk `W(P) = ref(B) · ref(A)` (Definition 1, p. 7), where `ref(K) = 2Π_K − Id` is
Mathlib's `Submodule.reflection` (first apply `ref(A)`, then `ref(B)`). -/
def walk (P : Matrix X X ℝ) (πd : X → ℝ) : H X →ₗ[ℂ] H X :=
  ((spaceB P πd).reflection : H X →ₗ[ℂ] H X) ∘ₗ ((spaceA P).reflection : H X →ₗ[ℂ] H X)

/-- The state `|π⟩ = Σ_x √π_x |x⟩|p_x⟩` (§3.1, p. 8). -/
def piState (P : Matrix X X ℝ) (πd : X → ℝ) : H X :=
  ∑ x, ((Real.sqrt (πd x) : ℝ) : ℂ) • vecA P x

/-- The isometric embedding `u ↦ Σ_x u_x |x⟩|p_x⟩` of `ℂ^X` onto `A`, as the
`(X × X) × X` matrix with entries `√(p_{xy})` at `((x, y), x)`. -/
def embedAMatrix (P : Matrix X X ℝ) : Matrix (X × X) X ℂ :=
  fun xy x => if xy.1 = x then ((Real.sqrt (P x xy.2) : ℝ) : ℂ) else 0

/-- The embedding `v ↦ Σ_y v_y |p*_y⟩|y⟩` of `ℂ^X` onto `B`, as the `(X × X) × X` matrix with
entries `√(p*_{yx})` at `((x, y), y)`. -/
def embedBMatrix (P : Matrix X X ℝ) (πd : X → ℝ) : Matrix (X × X) X ℂ :=
  fun xy y => if xy.2 = y then ((Real.sqrt (timeReversal P πd y xy.1) : ℝ) : ℂ) else 0

/-- The span of the left singular vectors of `D(P)` with singular value `c`, mapped into `A`:
the image under `u ↦ Σ_x u_x |x⟩|p_x⟩` of `{u ∈ ℂ^X : D Dᵀ u = c² u}`. -/
def leftSingularImage (P : Matrix X X ℝ) (πd : X → ℝ) (c : ℝ) : Submodule ℂ (H X) :=
  let D : Matrix X X ℂ := (discriminant P πd).map (fun r => (r : ℂ))
  (LinearMap.ker (Matrix.toEuclideanLin (D * D.transpose - ((c ^ 2 : ℝ) : ℂ) • 1))).map
    (Matrix.toEuclideanLin (embedAMatrix P))

/-- The span of the right singular vectors of `D(P)` with singular value `c`, mapped into `B`:
the image under `v ↦ Σ_y v_y |p*_y⟩|y⟩` of `{v ∈ ℂ^X : Dᵀ D v = c² v}`. -/
def rightSingularImage (P : Matrix X X ℝ) (πd : X → ℝ) (c : ℝ) : Submodule ℂ (H X) :=
  let D : Matrix X X ℂ := (discriminant P πd).map (fun r => (r : ℂ))
  (LinearMap.ker (Matrix.toEuclideanLin (D.transpose * D - ((c ^ 2 : ℝ) : ℂ) • 1))).map
    (Matrix.toEuclideanLin (embedBMatrix P πd))

end QuantumWalkSearch.PhaseReflection


