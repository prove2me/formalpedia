-- Prove2me | Definitions.Def_LimitedEntanglementTomography_LowerBound_Measurement
-- name    : LimitedEntanglementTomography_LowerBound_Measurement
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:36.441501+00:00
-- url     : https://prove2.me/theorems/0454c130-2e3b-4907-b377-55d7fa565a52
-- title:
--   Measurable POVMs, Born probabilities and the classical Fisher information $\operatorname{tr} J_M(\rho)$
-- statement:
--   Let $\Omega$ be a measurable outcome space and $\mathcal H=\mathbb C^n$ (for $t$ copies of $\mathbb C^d$, $n=d^t$, indexed by $[d]^t$). A positive operator-valued measure (POVM) assigns to each measurable $B\subseteq\Omega$ a positive semidefinite matrix $M(B)$ with $M(\Omega)=I$, countably additive: for disjoint measurable $B_1,B_2,\dots$,
--   $$M\Big(\bigcup_iB_i\Big)=\sum_iM(B_i).$$
--   Measuring the input $R$ gives the Born probability $P_R(B)=\operatorname{tr}(M(B)R)$.
--
--   For a full-rank state $\rho$, an orthonormal basis $F_b$ of $\mathrm{Herm}_0(\mathbb C^d)$, and a finite observation with outcome probabilities $p_a(\sigma)$, the trace of the Fisher information at $\rho$ is
--   $$\operatorname{tr}J(\rho)=\sum_{b}\ \sum_{a:\,p_a(\rho)>0}\frac{\big(\partial_s p_a(\rho+sF_b)|_{s=0}\big)^2}{p_a(\rho)}\in[0,\infty].$$
--   For a POVM $M$ on $t$ copies, $\operatorname{tr}J_M(\rho)$ is the supremum of this quantity over all measurable maps $\varphi$ of the outcome into a finite set $A$, where $p_a(\sigma)=\operatorname{tr}\big(M(\varphi^{-1}(a))\,\sigma^{\otimes t}\big)$.
--
--   These are the measurement model of the paper and the quantity bounded in Corollary 4.7 and Theorem 8.1.
--
--   **Formalization Note** The source defines $\operatorname{tr}J_M=\mathbb E\|s_\theta\|^2$ through the Radon–Nikodym density $K(y)$ of $M$ with respect to $\operatorname{tr}M(\cdot)/D$; by the source's Fact 4.3, eq. (16), this equals the supremum over finite quantizations used here, which needs no choice of density version. A summand whose probability path is not differentiable at $0$ counts as $+\infty$, so no junk value can make a Fisher bound easier. Theorems quantifying over POVMs ask for a standard Borel outcome space, as the source does.
-- source:
--   Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, Tight Lower Bounds for State Tomography with Limited Entanglement, STOC 2027 submission #1625 (October 2026), source.pdf SHA-256 bdd8884c95899a0c563507d1c005e0dee86e418d52478a2e9e6682bb1f9d29c3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1625.pdf, §4.2, printed pp.9–11 / PDF pp.11–13 (POVM on a standard Borel space, Born law, classical Fisher information, Fact 4.3 eq. (16))

import Mathlib
import Definitions.Def_LimitedEntanglementTomography_LowerBound_Matrices

open scoped ENNReal ComplexOrder
noncomputable section

/-!
# Measurable POVMs and their classical Fisher information

Keskin, Luo, Majid, Radzihovsky, STOC 2027 submission #1625 (October 2026), §4.2
(printed pp.9–11 / PDF pp.11–13).
-/

namespace LimitedEntanglementTomography.LowerBound

open MeasureTheory Matrix

/-- §4.2, p.9: a positive-operator-valued measure on a measurable outcome space `Ω`, acting on
`ℂ^n` (for `t` copies, `n = Fin t → Fin d`): positive semidefinite effects on measurable sets,
normalization `M(Ω) = I`, and countable additivity (in a finite-dimensional space, entrywise
convergence of the partial sums). The source's outcome spaces are standard Borel; each theorem
that quantifies over POVMs asks for `[StandardBorelSpace Ω]`. -/
structure POVM (n : Type) [Fintype n] [DecidableEq n] (Ω : Type) [MeasurableSpace Ω] where
  /-- The effect `M(B)` of a set `B` of outcomes (meaningful on measurable sets). -/
  effect : Set Ω → Matrix n n ℂ
  posSemidef_effect : ∀ B, MeasurableSet B → (effect B).PosSemidef
  effect_univ : effect Set.univ = 1
  hasSum_effect : ∀ f : ℕ → Set Ω, (∀ i, MeasurableSet (f i)) →
    Pairwise (Function.onFun Disjoint f) → HasSum (fun i => effect (f i)) (effect (⋃ i, f i))

/-- §4.2, p.9: the Born probability `P_R(B) = tr(M(B) R)` of the outcome set `B` on input `R`. -/
def bornProb {n : Type} [Fintype n] [DecidableEq n] {Ω : Type} [MeasurableSpace Ω] (M : POVM n Ω)
    (R : Matrix n n ℂ) (B : Set Ω) : ℝ :=
  (trace (M.effect B * R)).re

open Classical in
/-- One summand `(∂ p)² / p` of a classical Fisher information at parameter `0`, for a scalar
outcome-probability path `p`: `0` when `p(0) = 0` (outcomes of probability zero are discarded),
and `+∞` when `p` is not differentiable at `0`. -/
def fisherTerm (p : ℝ → ℝ) : ℝ≥0∞ :=
  if p 0 = 0 then 0
  else if DifferentiableAt ℝ p 0 then ENNReal.ofReal (deriv p 0 ^ 2 / p 0) else ⊤

/-- §4.2, p.10: the trace `tr J(ρ) = ∑_b ∑_{a : p_a(ρ) > 0} (∂_b p_a)² / p_a` of the Fisher
information matrix of a finite observation with outcome probabilities `p_a(σ)`, along the
coordinate paths `ρ_s = ρ + s F_b` of an orthonormal basis of `Herm₀(ℂ^d)`. -/
def finiteFisherTrace {d m : ℕ} (F : Fin (d ^ 2 - 1) → Op d) (ρ : Op d)
    (p : Fin m → Op d → ℝ) : ℝ≥0∞ :=
  ∑ a, ∑ b, fisherTerm (fun s : ℝ => p a (ρ + ((s : ℝ) : ℂ) • F b))

/-- §4.2, pp.10–11: `tr J_M(ρ)`, the trace of the classical Fisher information of the outcome of
the POVM `M` on `t` copies at the state `ρ`, in the coordinates `ρ_θ = ρ + ∑ θ_b F_b`, as an
extended nonnegative real. It is the supremum, over measurable maps `φ` of the outcome into a
finite set, of the Fisher information of `φ(Y)`, whose outcome probabilities are
`tr(M(φ⁻¹(a)) ρ_θ^{⊗t})`. -/
def povmFisherTrace {d t : ℕ} {Ω : Type} [MeasurableSpace Ω] (F : Fin (d ^ 2 - 1) → Op d)
    (M : POVM (Fin t → Fin d) Ω) (ρ : Op d) : ℝ≥0∞ :=
  ⨆ (m : ℕ) (φ : Ω → Fin m) (_ : Measurable φ),
    finiteFisherTrace F ρ (fun a σ => bornProb M (ShadowTomography.ClassicalLB.tensorPow σ t)
      (φ ⁻¹' {a}))

end LimitedEntanglementTomography.LowerBound


