-- Prove2me | Definitions.Def_RegevRecon_Messages
-- name    : RegevRecon_Messages
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:48.011003+00:00
-- url     : https://prove2.me/theorems/f45e81bb-f29b-499f-be67-a72211fd6d53
-- title:
--   Probability vectors on $\mathbb F_p$: convolution, the channel $\mu$, $P_{\mathrm{err}}$, Fourier coefficients, the lift $\mathcal L$, exchangeable $\Lambda$
-- statement:
--   Fix a prime $p$. For vectors on $\mathbb F_p$, the **circular convolution** is $(\mu*\nu)_a=\sum_b\mu_b\nu_{a-b}$ (29). The **physical channel** for a target set $S$ with $r=|S|$ is
--
--   $$
--   w_\beta(u)=e^{-\beta}+(1-e^{-\beta})\mathbf 1\{u\in S\},\qquad c_\beta=r+(p-r)e^{-\beta},\qquad \mu_a=\frac{w_\beta(a)}{c_\beta}.
--   $$
--
--   The **error function** is $P_{\mathrm{err}}(\mu)=1-\frac1p\bigl(\sum_a\sqrt{\mu_a}\bigr)^2$ (33). With $\omega=e^{2\pi i/p}$, the Fourier coefficient is $\hat q(b)=\sum_a q_a\omega^{ab}$. The relabeling is $(R_\alpha q)_a=q_{\alpha a}$, and the parity output of $(q,r)$ at $s$ is $\pi_s=\sum_a q_ar_{a+s}$, $w_a=q_ar_{a+s}/\pi_s$ (32).
--
--   The **random posterior lift** of a probability vector $q$ is the law of the vector $z\mapsto q_{A-z}$ with $A\sim q$ (53). A law $\Lambda$ on $(\mathbb F_p^\times)^D$ is **exchangeable** if it is invariant under permuting the $D$ coordinates; the ratios $\gamma_t=c_t/c_0$ compare the coordinates of children with that of the parent.
--
--   These objects are shared by the BPQM recursion and the reconstruction recursion.
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), (29), p.10; (32), p.11; (33), p.12; (41), p.16; (43), p.18; Definition 2, p.4; (53), p.21; pp.22–23

import Mathlib
import Definitions.Def_RegevRecon_Law

namespace RegevRecon

open Finset

/-- A real vector indexed by `F_p`; the messages of the two recursions are probability vectors. -/
abbrev Vec (p : ℕ) := ZMod p → ℝ

variable {p : ℕ} [Fact p.Prime]

/-- A probability vector on `F_p`. -/
def IsProbVec (q : Vec p) : Prop := (∀ a, 0 ≤ q a) ∧ ∑ a, q a = 1

/-- **Circular convolution**, Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), (29), p.10: `(μ ∗ ν)_a = Σ_b μ_b ν_{a−b}`. -/
noncomputable def conv (μ ν : Vec p) : Vec p := fun a => ∑ b, μ b * ν (a - b)

/-- The iterated convolution `base ∗ q_1 ∗ ⋯ ∗ q_n` ((35), (39), (47)). -/
noncomputable def convAll (base : Vec p) {n : ℕ} (qs : Fin n → Vec p) : Vec p :=
  (List.ofFn qs).foldl conv base

/-- The point mass `e_0 = (1, 0, …, 0)` ((38), p.14; p.19). -/
noncomputable def e0 : Vec p := fun a => if a = 0 then 1 else 0

/-- The uniform vector `u = (1/p, …, 1/p)` (Theorem 4, p.21). -/
noncomputable def unif : Vec p := fun _ => (p : ℝ)⁻¹

/-- The Gibbs weight `w_β(u) = e^{−β} + (1 − e^{−β}) 1{u ∈ S}`, (43), p.18. -/
noncomputable def wBeta (S : Finset (ZMod p)) (β : ℝ) (u : ZMod p) : ℝ :=
  Real.exp (-β) + (1 - Real.exp (-β)) * (if u ∈ S then 1 else 0)

/-- The normalizer `c_β = r + (p − r) e^{−β}`, `r = |S|`, (43), p.18. -/
noncomputable def cBeta (S : Finset (ZMod p)) (β : ℝ) : ℝ :=
  (S.card : ℝ) + ((p : ℝ) - S.card) * Real.exp (-β)

/-- **The unshifted physical channel** `μ_a = w_β(a)/c_β`, (43), p.18, equal to (41), p.16. -/
noncomputable def channel (S : Finset (ZMod p)) (β : ℝ) : Vec p :=
  fun a => wBeta S β a / cBeta S β

/-- **The error function** `P_err(μ) = 1 − (1/p)(Σ_a √μ_a)²`, (33), p.12. -/
noncomputable def pErr (μ : Vec p) : ℝ := 1 - (p : ℝ)⁻¹ * (∑ a, Real.sqrt (μ a)) ^ 2

/-- The squared distance `‖q − u‖₂² = Σ_a (q_a − 1/p)²` (Theorem 4, (54), p.21). -/
noncomputable def distSq (q : Vec p) : ℝ := ∑ a, (q a - (p : ℝ)⁻¹) ^ 2

/-- `ω^a` for `ω = e^{2πi/p}` and `a ∈ F_p` (p.9). -/
noncomputable def zeta (a : ZMod p) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) / (p : ℂ))

/-- **The Fourier coefficient** `q̂(b) = Σ_a q_a ω^{ab}`, p.23. -/
noncomputable def fourier (q : Vec p) (b : ZMod p) : ℂ := ∑ a, (q a : ℂ) * zeta (a * b)

/-- The relabeling `(R_α q)_a = q_{αa}`, p.22; p.14: `ν_{t,a} = v_{t,α_t a}`. -/
def relabel (α : ZMod p) (q : Vec p) : Vec p := fun a => q (α * a)

/-- The parity output of `(q, r)` at outcome `s`, (32), p.11: `π_s = Σ_a q_a r_{a+s}`. -/
noncomputable def parityProb (q r : Vec p) (s : ZMod p) : ℝ := ∑ a, q a * r (a + s)

/-- The parity output of `(q, r)` at outcome `s`, (32), p.11: `w_a = q_a r_{a+s}/π_s`. Read only
with weight `π_s`, so a branch with `π_s = 0` never enters a law. -/
noncomputable def parityVec (q r : Vec p) (s : ZMod p) : Vec p :=
  fun a => q a * r (a + s) / parityProb q r s

/-- **The random posterior lift of `q`**, (53), p.21: the law of `z ↦ q_{A−z}`, `A ∼ q`. -/
noncomputable def liftVec (q : Vec p) : Law (Vec p) := Law.ofWeights q fun A z => q (A - z)

/-- **The lift of a law**: draw `q ∼ P`, then `𝓛(q)` ((53), (54), p.21). -/
noncomputable def liftLaw (P : Law (Vec p)) : Law (Vec p) := P.bind liftVec

/-- An exchangeable law of a coefficient tuple, Definition 2, p.4: "the probability law is
invariant under permuting the D variables". -/
def Exchangeable {D : ℕ} (Λ : PMF (Fin D → (ZMod p)ˣ)) : Prop :=
  ∀ (σ : Equiv.Perm (Fin D)) (c : Fin D → (ZMod p)ˣ), Λ (c ∘ σ) = Λ c

/-- The coefficient law `Λ` as a `Law`. -/
noncomputable def coeffLaw {D : ℕ} (Λ : PMF (Fin D → (ZMod p)ˣ)) : Law (Fin D → (ZMod p)ˣ) :=
  Law.ofWeights (fun c => (Λ c).toReal) id

/-- The coefficient `c_0` of a variable on its parent constraint (p.23: `(c_0, …, c_{D−1}) ∼ Λ`).

**Formalization Note** `D ≥ 4` in every statement of this mission; the value `1` at `D = 0` is never
read. -/
def coeff0 {D : ℕ} (c : Fin D → (ZMod p)ˣ) : (ZMod p)ˣ :=
  if h : 0 < D then c ⟨0, h⟩ else 1

/-- The position `t + 1` of the child constraint `t ∈ {0, …, D − 2}` in a coefficient tuple. -/
def childIdx {D : ℕ} (t : Fin (D - 1)) : Fin D := ⟨t.val + 1, by have := t.isLt; omega⟩

/-- **The coefficient ratio** `γ_t = c_t/c_0` of child `t` relative to the parent (p.19, p.23). -/
def gammaRatio {D : ℕ} (c : Fin D → (ZMod p)ˣ) (t : Fin (D - 1)) : ZMod p :=
  ((c (childIdx t) * (coeff0 c)⁻¹ : (ZMod p)ˣ) : ZMod p)

end RegevRecon


