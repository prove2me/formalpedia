-- Prove2me | Definitions.Def_NearLinIsing_Supplement_SpinLaws
-- name    : NearLinIsing_Supplement_SpinLaws
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:38:07.84579+00:00
-- url     : https://prove2.me/theorems/558f4d37-3d7e-4186-8546-81d7129072bb
-- title:
--   The XY law with couplings $K$, $\beta_{XY}(\Delta)$, the Potts law, $\beta_{od}(q,\Delta)$ and the random-cluster law
-- statement:
--   Let $G=(V,E)$ be the input graph, $V=\{0,\dots,n-1\}$, $E=\{0,\dots,m-1\}$.
--
--   1. **XY law.** For edge couplings $K=(K_e)_{e\in E}$,
--   $$Z_{XY}(G,K)=\int\exp\Big(\sum_{uv\in E}K_{uv}\cos(\theta_u-\theta_v)\Big)\prod_{v\in V}\frac{d\theta_v}{2\pi},$$
--   the integral over $\theta\in[0,2\pi)^V$ with normalized Haar measure, and the XY spin law has density $Z_{XY}(G,K)^{-1}\exp(\sum_{uv}K_{uv}\cos(\theta_u-\theta_v))$ against it (Appendix A). The law $\mu_{XY}(d\theta)\propto\beta^{\sum_{uv\in E}\cos(\theta_u-\theta_v)}\prod_v d\theta_v/2\pi$ of Theorem 1.2 is the case $K_e=\log\beta$.
--   2. **Robust tree threshold.** $\beta_{XY}(\Delta)$ is the unique $\beta>1$ with
--   $$(\Delta-1)\frac{I_1(\log\beta)}{I_0(\log\beta)}=1,\qquad(1)$$
--   where $I_k(x)=\frac1{2\pi}\int_0^{2\pi}e^{x\cos\theta}\cos(k\theta)\,d\theta$.
--   3. **Potts law.** For an integer $q\ge3$, $\mu_{q,\beta}(\sigma)=Z_{q,\beta}^{-1}\beta^{m_=(\sigma)}$ on $\sigma\in[q]^V$, where $m_=(\sigma)$ counts edges whose endpoints have equal spins, and
--   $$\beta_{od}(q,\Delta)=\frac{q-2}{(q-1)^{1-2/\Delta}-1}.$$
--   4. **Random-cluster law.** $\pi_{RC}(A)\propto(\beta-1)^{|A|}q^{k(A)}$ on $A\subseteq E$, where $k(A)$ counts the connected components of $(V,A)$, isolated vertices included. At $\beta=1$ it is the point mass on $A=\varnothing$.
--
--   These are the target laws of Theorems 1.2, 1.3 and A.1.
--
--   **Formalization Note** $\beta_{XY}(\Delta)$ is defined as $\sup\{b\ge1:(\Delta-1)I_1(\log b)/I_0(\log b)\le1\}$, which is the unique root of (1) because $I_1/I_0$ increases strictly from $0$ to $1$ on $[0,\infty)$; $I_k$ is the published series `QueueingFundamentals.Transient.besselI`, equal to the integral above for integer $k$. Potts colours $[q]$ are $0,\dots,q-1$; the Potts law is also given as a measure on $\mathbb R^V$ sitting on the colour vectors, and the random-cluster law as a measure on $\mathbb R^E$ sitting on the indicator vectors $1_A$, so that both can be compared with a machine's output law.
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, XY law and eq. (1), p. 2; Potts law and βod, p. 3; random-cluster law, §2.3, p. 9; Z_XY(G, K), Appendix A, p. 44

import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_besselI
import Definitions.Def_NearLinIsing_IncGraph

open MeasureTheory
open scoped ENNReal

namespace NearLinIsing

namespace Supplement

noncomputable section

open Classical

/-!
# The XY, Potts and random-cluster laws on an input graph

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786: the XY law and the threshold (1), p. 2; the Potts law and `βod`,
p. 3; the random-cluster law, §2.3, p. 9; the XY partition function with edge couplings `K`,
Appendix A, p. 44.

All laws live on the published input graph `NearLinIsing.IncGraph` (vertices `Fin n`, edges
`Fin m`, endpoints `ends`).

**Formalization Note.**
* XY: one law with edge couplings `K_e`, `xyLaw G K`. Theorem 1.2's law
  `Z⁻¹ β^{Σ_{uv∈E} cos(θ_u − θ_v)} ∏_v dθ_v/2π` is `xyLaw G (fun _ => log β)`, because
  `β^y = exp(y log β)` for `β > 0`. The reference measure is normalized Haar measure on
  `[0, 2π)^V`: Lebesgue measure on the box divided by `(2π)^n`, so `Z_XY = 1` when `E = ∅`.
  Angles are reals; the law gives no mass outside `[0, 2π)^V`.
* `βXY(Δ)` is defined as `sup {b ≥ 1 : (Δ − 1) I_1(log b)/I_0(log b) ≤ 1}`. Since `I_1/I_0`
  increases strictly from `0` to `1` on `[0, ∞)`, for `Δ ≥ 3` this is the unique `β > 1` with
  `(Δ − 1) I_1(log β)/I_0(log β) = 1`, eq. (1). `I_k` is the published
  `QueueingFundamentals.Transient.besselI` (the power series; for integer order it equals the
  paper's integral `(1/2π)∫_0^{2π} e^{x cos θ} cos(kθ) dθ`).
* Potts colours `[q] = {1, …, q}` are `Fin q` (`0, …, q − 1`); as a measure on `ℝ^V` the law sits
  on the colour vectors `(σ_v)_v`.
* The random-cluster law is on edge sets `A ⊆ E` (`Finset (Fin m)`); as a measure on `ℝ^E` it sits
  on the indicator vectors `1_A`. `k(A)` counts the connected components of `(V, A)`, isolated
  vertices included. At `β = 1` the weight is `0^{|A|} q^{k(A)}` with `0^0 = 1`: the point mass on
  `A = ∅`.
* `βod(q, Δ) = (q − 2)/((q − 1)^{1 − 2/Δ} − 1)` with a real power.
-/

/-- The XY energy `∑_{uv ∈ E} K_uv cos(θ_u − θ_v)`. -/
def xyEnergy (G : IncGraph) (K : Fin G.m → ℝ) (θ : Fin G.n → ℝ) : ℝ :=
  ∑ e, K e * Real.cos (θ (G.ends e).1 - θ (G.ends e).2)

/-- The box `[0, 2π)^V`. -/
def angleBox (G : IncGraph) : Set (Fin G.n → ℝ) :=
  Set.univ.pi fun _ => Set.Ico 0 (2 * Real.pi)

/-- Normalized Haar measure `∏_v dθ_v / 2π` on `[0, 2π)^V`. -/
def haarAngles (G : IncGraph) : Measure (Fin G.n → ℝ) :=
  (ENNReal.ofReal ((2 * Real.pi) ^ G.n))⁻¹ • (volume.restrict (angleBox G))

/-- The XY partition function
`Z_XY(G, K) = ∫ exp(∑_{uv ∈ E} K_uv cos(θ_u − θ_v)) ∏_v dθ_v/2π` (Appendix A, p. 44). -/
def xyZ (G : IncGraph) (K : Fin G.m → ℝ) : ℝ :=
  ∫ θ, Real.exp (xyEnergy G K θ) ∂(haarAngles G)

/-- The XY spin law with couplings `K`: density `exp(∑ K_uv cos(θ_u − θ_v)) / Z_XY(G, K)` against
normalized Haar measure on `[0, 2π)^V` (p. 2 and Appendix A, p. 44). -/
def xyLaw (G : IncGraph) (K : Fin G.m → ℝ) : Measure (Fin G.n → ℝ) :=
  (haarAngles G).withDensity fun θ => ENNReal.ofReal (Real.exp (xyEnergy G K θ) / xyZ G K)

/-- The robust tree threshold `βXY(Δ)` of the XY model, eq. (1), p. 2. -/
def betaXY (Δ : ℕ) : ℝ :=
  sSup {b : ℝ | 1 ≤ b ∧
    ((Δ : ℝ) - 1) * QueueingFundamentals.Transient.besselI 1 (Real.log b) /
      QueueingFundamentals.Transient.besselI 0 (Real.log b) ≤ 1}

/-- `m=(σ)` for a Potts colouring: the number of edges whose endpoints have equal colours. -/
def pottsEq (G : IncGraph) {q : ℕ} (σ : Fin G.n → Fin q) : ℕ :=
  (Finset.univ.filter fun e => σ (G.ends e).1 = σ (G.ends e).2).card

/-- The zero-field Potts law `µ_{q,β}(σ) = Z⁻¹ β^{m=(σ)}` on `σ ∈ [q]^V` (p. 3). -/
def pottsLaw (G : IncGraph) (q : ℕ) (β : ℝ) (σ : Fin G.n → Fin q) : ℝ :=
  β ^ pottsEq G σ / ∑ σ' : Fin G.n → Fin q, β ^ pottsEq G σ'

/-- The Potts law as a measure on `ℝ^V`, on the colour vectors. -/
def pottsMeasure (G : IncGraph) (q : ℕ) (β : ℝ) : Measure (Fin G.n → ℝ) :=
  ∑ σ : Fin G.n → Fin q,
    ENNReal.ofReal (pottsLaw G q β σ) • Measure.dirac (fun v => ((σ v : ℕ) : ℝ))

/-- The order–disorder threshold `βod(q, Δ) = (q − 2)/((q − 1)^{1 − 2/Δ} − 1)` (p. 3). -/
def betaOd (q Δ : ℕ) : ℝ :=
  ((q : ℝ) - 2) / (((q : ℝ) - 1) ^ (1 - 2 / (Δ : ℝ)) - 1)

/-- The graph `(V, A)` spanned by an edge set `A ⊆ E`. -/
def spanGraph (G : IncGraph) (A : Finset (Fin G.m)) : SimpleGraph (Fin G.n) :=
  SimpleGraph.fromEdgeSet {s | ∃ e ∈ A, s = s((G.ends e).1, (G.ends e).2)}

/-- `k(A)`: the number of connected components of `(V, A)`, isolated vertices included. -/
def numComponents (G : IncGraph) (A : Finset (Fin G.m)) : ℕ :=
  Nat.card (spanGraph G A).ConnectedComponent

/-- The random-cluster weight `(β − 1)^{|A|} q^{k(A)}` (edge activity `β − 1`, cluster weight
`q`). -/
def rcWeight (G : IncGraph) (q : ℕ) (β : ℝ) (A : Finset (Fin G.m)) : ℝ :=
  (β - 1) ^ A.card * (q : ℝ) ^ numComponents G A

/-- The random-cluster law `π_RC(A) ∝ (β − 1)^{|A|} q^{k(A)}` on `A ⊆ E` (§2.3, p. 9). -/
def rcLaw (G : IncGraph) (q : ℕ) (β : ℝ) (A : Finset (Fin G.m)) : ℝ :=
  rcWeight G q β A / ∑ A' : Finset (Fin G.m), rcWeight G q β A'

/-- The random-cluster law as a measure on `ℝ^E`, on the indicator vectors `1_A`. -/
def rcMeasure (G : IncGraph) (q : ℕ) (β : ℝ) : Measure (Fin G.m → ℝ) :=
  ∑ A : Finset (Fin G.m),
    ENNReal.ofReal (rcLaw G q β A) • Measure.dirac (fun e => if e ∈ A then (1 : ℝ) else 0)

end

end Supplement

end NearLinIsing


