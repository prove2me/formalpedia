-- Prove2me | Definitions.Def_Z2PostSamp_IndepMetropolis
-- name    : Z2PostSamp_IndepMetropolis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:08.45447+00:00
-- url     : https://prove2.me/theorems/0abfd22c-cfed-43ea-847f-94b332505a3d
-- title:
--   The independence Metropolis kernel and the warmness level $\delta=P(dP/dQ>M)$
-- statement:
--   For strictly positive probability laws $P,Q$ on a finite set, the **independence Metropolis process** starts at $X_0\sim Q$; given $X_t=y$ it proposes $z\sim Q$ independently and accepts with probability
--
--   $$\min\Big\{1,\frac{P(z)Q(y)}{P(y)Q(z)}\Big\},$$
--
--   setting $X_{t+1}=z$ on acceptance and $X_{t+1}=y$ otherwise. Its transition kernel $K$ is the stochastic matrix with $K(y,z)=Q(z)\min\{1,\cdot\}$ for $z\ne y$ and the remaining mass on the diagonal; the law after $t$ steps is $QK^t$. The **warmness level** at level $M$ is $\delta=P(dP/dQ>M)=\sum_{x:P(x)/Q(x)>M}P(x)$, and total variation is $\|p-q\|_{\mathrm{TV}}=\tfrac12\sum_x|p(x)-q(x)|$.
--
--   These are the objects of Lemma 2.1, which reduces sampling to building a warm proposal.
--
--   **Formalization Note** Laws are functions on a finite type.
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), §2.1, p.6, (2.1); Lemma 2.1

import Mathlib

set_option autoImplicit false

namespace Z2PostSamp

noncomputable section

/-!
# The independence Metropolis kernel and warmness

Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), §2.1, p.6: "For two strictly positive probability measures `P, Q` on a finite set,
the independence Metropolis process is the Markov chain `(X_t)_{t≥0}` initialized with `X_0 ∼ Q`.
Given `X_t = y`, independently propose `z ∼ Q` and accept the proposal with probability
`min{1, P(z)Q(y)/(P(y)Q(z))}` (2.1). On acceptance set `X_{t+1} = z`; otherwise set `X_{t+1} = y`."
Lemma 2.1: `Q` is `(δ, M)`-warm with respect to `P` if `P(dP/dQ > M) = δ`.

**Formalization Note.** Laws on a finite type are functions `α → ℝ`. The kernel is a stochastic
matrix: the off-diagonal entry `K(y, z)` is `Q(z)` times the acceptance probability, the diagonal
entry is the remaining mass (a proposal of the current state is always accepted). The law after `t`
steps from `X_0 ∼ Q` is the row vector `Q Kᵗ`. `finTV` is `½ Σ |p − q|` (the normalization in which
total variation is at most one, p.34).
-/

/-- Total variation `‖p − q‖_TV = ½ Σ_x |p(x) − q(x)|` on a finite type. -/
def finTV {α : Type} [Fintype α] (p q : α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, |p x - q x|

/-- The acceptance probability `min{1, P(z)Q(y)/(P(y)Q(z))}` of a move `y → z` (2.1). -/
def imAccept {α : Type} (P Q : α → ℝ) (y z : α) : ℝ :=
  min 1 (P z * Q y / (P y * Q z))

open Classical in
/-- The transition kernel `K` of the independence Metropolis process (2.1). -/
def imKernel {α : Type} [Fintype α] (P Q : α → ℝ) : Matrix α α ℝ := fun y z =>
  if y = z then 1 - ∑ w ∈ Finset.univ.filter (· ≠ y), Q w * imAccept P Q y w
  else Q z * imAccept P Q y z

open Classical in
/-- The warmness level `δ = P(dP/dQ > M) = Σ_{x : P(x)/Q(x) > M} P(x)` (Lemma 2.1). -/
def warmDelta {α : Type} [Fintype α] (P Q : α → ℝ) (M : ℝ) : ℝ :=
  ∑ x, if M < P x / Q x then P x else 0

end

end Z2PostSamp


