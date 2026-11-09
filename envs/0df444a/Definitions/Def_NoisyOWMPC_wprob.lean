-- Prove2me | Definitions.Def_NoisyOWMPC_wprob
-- name    : NoisyOWMPC_wprob
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:39:22.352036+00:00
-- url     : https://prove2.me/theorems/cd38176f-991d-4073-bd41-4a75dc9c08ae
-- title:
--   Finite experiments: probabilities and statistical distance
-- statement:
--   Every experiment of the paper has finitely many outcomes, so a distribution is a weight function $w$ on a finite sample space $\Omega$. The probability of an event $E$ is
--   $$\Pr[E]=\sum_{\omega\in E} w(\omega),$$
--   the uniform weight on a finite set gives each point $1/|\Omega|$, and the **statistical distance** of the laws of two outcome maps $u_0,u_1$ is
--   $$\mathrm{SD}=\tfrac12\sum_b\bigl|\Pr[u_0=b]-\Pr[u_1=b]\bigr| .$$
--
--   These three objects are used to state correctness, the statistical security bounds and the sampling-correctness properties of the tests.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), §3 Notation and conventions, p.15

import Mathlib

namespace NoisyOWMPC

open Classical in
/-- The probability of an event `E` in a finite experiment with sample space `Ω` and point
weights `w` (Ishai, Lu, Zafar, STOC 2027 submission (manuscript sha256 3a9569fa…), §3, p.15: "We
use `x ←r D` to denote sampling from a distribution"): `Pr[E] = ∑_{ω ∈ E} w(ω)`.

**Formalization Note** Every experiment of the paper has finitely many outcomes (finite alphabets,
finitely many coins, exact reference distributions), so a distribution is a weight function on a
finite type; the weights of each experiment are nonnegative and sum to one by construction. -/
noncomputable def wprob {Ω : Type} [Fintype Ω] (w : Ω → ℝ) (E : Ω → Prop) : ℝ :=
  ∑ ω, if E ω then w ω else 0

/-- The uniform weight on a finite type: `1 / |Ω|` at every point (§3, p.15: "for a finite set
it denotes uniform sampling"). -/
noncomputable def unifW (Ω : Type) [Fintype Ω] : Ω → ℝ := fun _ => 1 / (Fintype.card Ω : ℝ)

open Classical in
/-- **Statistical distance** of the laws of two outcome maps `u₀ : Ω₀ → β`, `u₁ : Ω₁ → β` under
weights `w₀`, `w₁` (§3, p.15: "`SD(P, Q) = ½ ∑_x |Pr[P = x] − Pr[Q = x]|` denotes total variation
distance"); the sum runs over the finitely many values either map takes. -/
noncomputable def sdPush {Ω₀ Ω₁ β : Type} [Fintype Ω₀] [Fintype Ω₁] (w₀ : Ω₀ → ℝ) (u₀ : Ω₀ → β)
    (w₁ : Ω₁ → ℝ) (u₁ : Ω₁ → β) : ℝ :=
  (1 / 2) * ∑ b ∈ (Finset.univ.image u₀ ∪ Finset.univ.image u₁),
    |wprob w₀ (fun ω => u₀ ω = b) - wprob w₁ (fun ω => u₁ ω = b)|

end NoisyOWMPC


