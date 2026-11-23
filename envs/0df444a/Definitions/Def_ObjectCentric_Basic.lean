-- Prove2me | Definitions.Def_ObjectCentric_Basic
-- name    : ObjectCentric_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T19:36:23.579067+00:00
-- url     : https://prove2.me/theorems/54fa530b-2c87-4136-90e5-47b085ec8d26
-- title:
--   Slotted latent model: compositional and irreducible generators, slot identifiability, compositional contrast
-- statement:
--   Objects of Sections 2-3 and Appendix A of Brady, Zimmermann, Sharma, Schölkopf, von Kügelgen and Brendel (ICML 2023).
--
--   1. **Latent and observation spaces.** A scene with $K$ objects has latent representation $\mathbf z=(\mathbf z_1,\dots,\mathbf z_K)\in\mathcal Z=\mathcal Z_1\times\cdots\times\mathcal Z_K$, where each slot space is $\mathcal Z_k=\mathbb R^M$. Observations are images with $N$ pixels, $\mathbf x\in\mathcal X\subseteq\mathbb R^N$.
--   2. **Diffeomorphisms.** A generator $\mathbf f:\mathcal Z\to\mathcal X$ with inverse $\mathbf g:\mathcal X\to\mathcal Z$ is a diffeomorphism: $\mathbf f$ is $C^1$, $\mathbf g$ is $C^1$ on $\mathcal X$, $\mathbf f(\mathcal Z)=\mathcal X$ and $\mathbf g(\mathbf f(\mathbf z))=\mathbf z$ for all $\mathbf z$. A diffeomorphism $\mathbf h:\mathbb R^M\to\mathbb R^M$ is a $C^1$ bijection with $C^1$ inverse.
--   3. **Jacobian and index sets (eq. 3).** $\mathbf J\mathbf f(\mathbf z)$ has rows indexed by pixels and columns by the latent coordinates $(k,m)$. For a pixel $n$, $\frac{\partial f_n}{\partial\mathbf z_k}(\mathbf z)\in\mathbb R^M$ is its gradient with respect to slot $k$, and $I_k(\mathbf z)=\{n\in[N]:\frac{\partial f_n}{\partial\mathbf z_k}(\mathbf z)\neq\mathbf 0\}$.
--   4. **Compositionality (Definition 1).** $\mathbf f$ is compositional if $I_k(\mathbf z)\cap I_j(\mathbf z)=\emptyset$ for all $\mathbf z$ and all $k\neq j$.
--   5. **Mechanisms (Definitions 2-4).** For $S\subseteq[N]$, $\mathbf J\mathbf f_S(\mathbf z)$ is the submatrix of $\mathbf J\mathbf f(\mathbf z)$ formed by the rows in $S$. The sub-mechanisms for $S_1,S_2$ are independent if $\operatorname{rank}\mathbf J\mathbf f_{S_1\cup S_2}(\mathbf z)=\operatorname{rank}\mathbf J\mathbf f_{S_1}(\mathbf z)+\operatorname{rank}\mathbf J\mathbf f_{S_2}(\mathbf z)$ and dependent if the left side is strictly smaller.
--   6. **Irreducibility (Definition 5).** $\mathbf f$ is irreducible if for all $\mathbf z$, all $k$, and every partition of $I_k(\mathbf z)$ into two nonempty disjoint sets $S_1,S_2$, the sub-mechanisms $\mathbf J\mathbf f_{S_1}(\mathbf z)$ and $\mathbf J\mathbf f_{S_2}(\mathbf z)$ are dependent.
--   7. **Slot identifiability (Definition 6).** $\hat{\mathbf g}:\mathcal X\to\mathcal Z$ slot-identifies $\mathbf z$ if for every $k\in[K]$ there is a unique $j\in[K]$ and a diffeomorphism $\mathbf h_k:\mathcal Z_k\to\mathcal Z_j$ with $\hat{\mathbf g}(\mathbf f(\mathbf z))_j=\mathbf h_k(\mathbf z_k)$ for all $\mathbf z\in\mathcal Z$.
--   8. **Slot blocks.** For a map $\mathbf h:\mathcal Z\to\mathcal Z$, $\mathbf z\mapsto\hat{\mathbf z}$, the $M\times M$ block $\frac{\partial\hat{\mathbf z}_j}{\partial\mathbf z_i}(\mathbf z)$ of $\mathbf J\mathbf h(\mathbf z)$.
--   9. **Compositional contrast (Definition 7, eq. 6).** $C_{\mathrm{comp}}(\mathbf f,\mathbf z)=\sum_{n=1}^N\sum_{k=1}^K\sum_{j=k+1}^K\big\|\frac{\partial f_n}{\partial\mathbf z_k}(\mathbf z)\big\|_2\big\|\frac{\partial f_n}{\partial\mathbf z_j}(\mathbf z)\big\|_2$.
--   10. **Objective (eq. 7).** For a latent law $p_{\mathbf z}$ on $\mathcal Z$, an encoder $\hat{\mathbf g}$, a decoder $\hat{\mathbf f}$ and $\lambda\in\mathbb R$, $\mathbb E_{\mathbf x\sim p_{\mathbf x}}\big[\|\hat{\mathbf f}(\hat{\mathbf g}(\mathbf x))-\mathbf x\|_2^2+\lambda C_{\mathrm{comp}}(\hat{\mathbf f},\hat{\mathbf g}(\mathbf x))\big]$ with $\mathbf x=\mathbf f(\mathbf z)$, $\mathbf z\sim p_{\mathbf z}$.
--
--   **Formalization Note** "Diffeomorphism" and "differentiable" are read as continuously differentiable ($C^1$). The observation space is a subset $\mathcal X$ of $\mathbb R^N$, and differentiability of a map defined on $\mathcal X$ is differentiability relative to $\mathcal X$. Partial derivatives are taken from the Fréchet derivative, which is $0$ at points where a map is not differentiable. Every statement that uses these notions therefore assumes the required differentiability. The objective is the expectation in $[0,\infty]$ of $\mathrm{ofReal}$ of the integrand, written as an integral over $\mathbf z\sim p_{\mathbf z}$ with $\mathbf x=\mathbf f(\mathbf z)$. This is the expectation under the push-forward $p_{\mathbf x}=\mathbf f_*p_{\mathbf z}$.
-- source:
--   Brady, Zimmermann, Sharma, Schölkopf, von Kügelgen and Brendel, Provably Learning Object-Centric Representations, ICML 2023, arXiv:2305.14229v1, Section 2 (eqs. (1)-(5), Definitions 1-5), Section 3 (Definitions 6-7, eqs. (6)-(7)), Appendix A (Notation), pp. 2-6, 15

import Mathlib

/-!
Brady, Zimmermann, Sharma, Schölkopf, von Kügelgen and Brendel, *Provably Learning Object-Centric
Representations*, ICML 2023, arXiv:2305.14229v1: the slotted latent space and the pixel space of
Section 2 (eq. (1), (2)), the index sets `I_k(z)` (eq. (3)), compositionality (Definition 1),
mechanisms, sub-mechanisms and their (in)dependence (Definitions 2-4), irreducibility
(Definition 5), slot identifiability (Definition 6), the compositional contrast (Definition 7,
eq. (6)) and the auto-encoder objective (eq. (7)) of Section 3.

Throughout, "diffeomorphism" and "differentiable" are read as continuously differentiable (`C¹`).
-/

open MeasureTheory

noncomputable section

namespace ObjectCentric

/-- Section 2.1: the latent space `Z = Z_1 × ... × Z_K` with `Z_k = ℝ^M`; a scene representation
`z` assigns to each slot `k ∈ [K]` its latent vector `z_k = z k ∈ ℝ^M`. -/
abbrev Lat (K M : ℕ) : Type := Fin K → Fin M → ℝ

/-- Section 2 and Appendix A (Notation): the ambient pixel space `ℝ^N` containing the observation
space `X`; pixel `n ∈ [N]` of an observation `x` is `x n`. -/
abbrev Obs (N : ℕ) : Type := Fin N → ℝ

variable {K M N : ℕ}

/-- Section 2: `f : Z → X` is a (`C¹`) diffeomorphism onto the observation space `X ⊆ ℝ^N`, with
inverse `g : X → Z`: `f` is `C¹`, `g` is `C¹` on `X`, `f(Z) = X`, and `g (f z) = z` for all `z`
(so also `f (g x) = x` for all `x ∈ X`). Footnote 1: a differentiable bijection with
differentiable inverse. -/
def IsDiffeoWithInv (f : Lat K M → Obs N) (g : Obs N → Lat K M) (X : Set (Obs N)) : Prop :=
  ContDiff ℝ 1 f ∧ ContDiffOn ℝ 1 g X ∧ Set.range f = X ∧ ∀ z, g (f z) = z

/-- Definition 6: a (`C¹`) diffeomorphism `h : Z_k → Z_j` between two slot spaces `ℝ^M`. -/
def IsSlotDiffeo (h : (Fin M → ℝ) → (Fin M → ℝ)) : Prop :=
  ContDiff ℝ 1 h ∧ ∃ h' : (Fin M → ℝ) → (Fin M → ℝ),
    ContDiff ℝ 1 h' ∧ Function.LeftInverse h' h ∧ Function.RightInverse h' h

/-- The Jacobian matrix `J f (z) = (∂f_n/∂z_{k,m}(z))`, with rows indexed by pixels `n ∈ [N]` and
columns by pairs (slot `k`, slot coordinate `m`). -/
def jac (f : Lat K M → Obs N) (z : Lat K M) : Matrix (Fin N) (Fin K × Fin M) ℝ :=
  fun n c => fderiv ℝ f z (Pi.single c.1 (Pi.single c.2 1)) n

/-- The partial derivative `∂f_n/∂z_k (z) ∈ ℝ^M` of pixel `n` with respect to slot `k`. -/
def slotGrad (f : Lat K M → Obs N) (z : Lat K M) (n : Fin N) (k : Fin K) : Fin M → ℝ :=
  fun m => jac f z n (k, m)

/-- Eq. (3): `I_k(z) = {n ∈ [N] : ∂f_n/∂z_k (z) ≠ 0}`, the pixels that functionally depend on
slot `k` at `z`. -/
def indexSet (f : Lat K M → Obs N) (z : Lat K M) (k : Fin K) : Set (Fin N) :=
  {n | slotGrad f z n k ≠ 0}

/-- Definition 1 (Compositionality), eq. (4): for all `z` and all slots `k ≠ j`,
`I_k(z) ∩ I_j(z) = ∅`. (The paper requires `f` differentiable; that hypothesis is stated
separately wherever this notion is used.) -/
def IsCompositional (f : Lat K M → Obs N) : Prop :=
  ∀ z : Lat K M, ∀ k j : Fin K, k ≠ j → Disjoint (indexSet f z k) (indexSet f z j)

/-- Definitions 2-3: the rank of the (sub-)mechanism `J f_S (z)`, the submatrix of the Jacobian
formed by the rows (pixels) in `S ⊆ [N]`. -/
def subRank (f : Lat K M → Obs N) (z : Lat K M) (S : Set (Fin N)) : ℕ :=
  ((jac f z).submatrix (fun n : S => (n : Fin N)) id).rank

/-- Definition 4, eq. (5) (first display): the sub-mechanisms `J f_{S₁}(z)` and `J f_{S₂}(z)` are
independent: `rank J f_{S₁ ∪ S₂}(z) = rank J f_{S₁}(z) + rank J f_{S₂}(z)`. -/
def SubmechIndependent (f : Lat K M → Obs N) (z : Lat K M) (S₁ S₂ : Set (Fin N)) : Prop :=
  subRank f z (S₁ ∪ S₂) = subRank f z S₁ + subRank f z S₂

/-- Definition 4 (second display): the sub-mechanisms `J f_{S₁}(z)` and `J f_{S₂}(z)` are
dependent: `rank J f_{S₁ ∪ S₂}(z) < rank J f_{S₁}(z) + rank J f_{S₂}(z)`. -/
def SubmechDependent (f : Lat K M → Obs N) (z : Lat K M) (S₁ S₂ : Set (Fin N)) : Prop :=
  subRank f z (S₁ ∪ S₂) < subRank f z S₁ + subRank f z S₂

/-- Definition 5 (Irreducibility): for all `z`, all slots `k` and every partition of `I_k(z)` into
two sets `S₁, S₂` (nonempty, as sub-mechanisms are by Definition 3, disjoint, with union
`I_k(z)`), the sub-mechanisms `J f_{S₁}(z)` and `J f_{S₂}(z)` are dependent. -/
def IsIrreducible (f : Lat K M → Obs N) : Prop :=
  ∀ (z : Lat K M) (k : Fin K) (S₁ S₂ : Set (Fin N)), S₁.Nonempty → S₂.Nonempty →
    Disjoint S₁ S₂ → S₁ ∪ S₂ = indexSet f z k → SubmechDependent f z S₁ S₂

/-- Definition 6 (Slot identifiability): the inference model `ĝ` slot-identifies `z = g(x)` via
`ẑ = ĝ(f(z))` if for every slot `k` there is a unique slot `j` and a diffeomorphism
`h_k : Z_k → Z_j` with `ẑ_j = h_k(z_k)` for all `z ∈ Z`. -/
def SlotIdentifies (f : Lat K M → Obs N) (ghat : Obs N → Lat K M) : Prop :=
  ∀ k : Fin K, ∃! j : Fin K, ∃ h : (Fin M → ℝ) → (Fin M → ℝ),
    IsSlotDiffeo h ∧ ∀ z : Lat K M, ghat (f z) j = h (z k)

/-- Appendix A, Propositions 1 and 3: the `M × M` block `∂ẑ_j/∂z_i (z)` of the Jacobian of a map
`h : Z → Z`, `z ↦ ẑ` (applied there to `h = ĝ ∘ f`). -/
def slotBlock (h : Lat K M → Lat K M) (z : Lat K M) (j i : Fin K) : Matrix (Fin M) (Fin M) ℝ :=
  fun a b => fderiv ℝ h z (Pi.single i (Pi.single b 1)) j a

/-- Euclidean (`L²`) norm of a vector of `ℝ^M`. -/
def l2norm (v : Fin M → ℝ) : ℝ := Real.sqrt (∑ m, v m ^ 2)

/-- Definition 7 (Compositional contrast), eq. (6):
`C_comp(f, z) = ∑_{n=1}^N ∑_{k=1}^K ∑_{j=k+1}^K ‖∂f_n/∂z_k (z)‖ ‖∂f_n/∂z_j (z)‖`. -/
def compContrast (f : Lat K M → Obs N) (z : Lat K M) : ℝ :=
  ∑ n, ∑ k, ∑ j ∈ Finset.Ioi k, l2norm (slotGrad f z n k) * l2norm (slotGrad f z n j)

/-- Squared Euclidean distance `‖x - y‖₂²` in pixel space. -/
def sqDist (x y : Obs N) : ℝ := ∑ n, (x n - y n) ^ 2

/-- Theorem 2, eq. (7): the objective
`E_{x ∼ p_x}[‖f̂(ĝ(x)) - x‖₂² + λ C_comp(f̂, ĝ(x))]` with `x = f(z)`, `z ∼ p_z`, as an expectation
in `[0, ∞]` of a nonnegative quantity (written over `z ∼ p_z`, i.e. against `p_x = f_* p_z`). -/
def aeObjective (f : Lat K M → Obs N) (pz : Measure (Lat K M)) (ghat : Obs N → Lat K M)
    (fhat : Lat K M → Obs N) (lam : ℝ) : ENNReal :=
  ∫⁻ z, ENNReal.ofReal (sqDist (fhat (ghat (f z))) (f z) + lam * compContrast fhat (ghat (f z)))
    ∂pz

end ObjectCentric


