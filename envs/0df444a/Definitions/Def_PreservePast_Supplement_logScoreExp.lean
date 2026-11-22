-- Prove2me | Definitions.Def_PreservePast_Supplement_logScoreExp
-- name    : PreservePast_Supplement_logScoreExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:32:11.949499+00:00
-- url     : https://prove2.me/theorems/b84c2c45-c6b1-40fd-ade1-f488e424269e
-- title:
--   The log-score source exponent, the applicability of Lemma 13, affinity small-ball mass, and the general identification experiment
-- statement:
--   For a prior $\mu$ on records, a query channel $P_x$, a reference law $Q$ and a domain $\mathcal T$:
--
--   - the **actions** are normalized, strictly positive densities $f$ with respect to $Q$ with finite log-score expectations on $\mathcal T$, the **score** is $g_x(f)=\mathbb E_{P_x}\ln f$, and $\mathcal H_n(b;\mu)$ (`logScoreExp`) is the published finite-order source exponent `PreservePast.sourceExp` of this score with domain $\mathcal T$ (in nats);
--   - **Lemma 13 applies to every region of $Q$-mass at most $q_{\max}$ with threshold $s$ and score-loss bound $b$** (`CommonScoreApplies`) if there is $C$ with $D(P_x\|Q)\le C$ on $\mathcal T$ such that for every measurable region $A$ with $0<Q(A)\le q_{\max}$, writing $E=\mathcal T\cap\{x:P_x(A)\ge s\}$, if $\mu(E)>0$ then for $\mu$-almost every $x\in E$ the log-density $\ln f_\nu$ of the mixture $P_\nu=\int P_x\,\mu(dx\mid E)$ is $P_x$-integrable and
--   $$P_x\{\ln f_\nu-\mathbb E_{P_x}\ln f_\nu>\Gamma_A\}\le s/8,\qquad \Gamma_A=b-C+\ln\frac{s}{2Q(A)};$$
--   - the **small-ball mass** is $p_\mu(a_0)=\sup_{c\in\mathcal T}\mu\{x\in\mathcal T:a(x,c)\le a_0\}$ for the affinity distance $a(x,x')=-\ln\int\sqrt{dP_x\,dP_{x'}}$, and the **gap** is $G=(U+\ln p)_+$ (zero if $p=0$);
--   - in the **identification experiment** with $k$ independent records of law $\mu$ and a uniform independent query index, `idSuccess`, `idOptimum` and `idInfo` are the success, the full-data optimum $S^\ast$ and $I(X;M\mid R)$ in bits.
--
--   **Formalization Note** $\Gamma_A$ is the deviation threshold for which the score loss $\Delta=C-\ln(s/(2Q(A)))+\Gamma_A$ of Lemma 13 equals $b$. Divergences are in nats and infinite when not finite.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), §H.1–§H.3, pp.46–49 (PDF pp.48–51), Lemmas 13 and 14 and Theorem 13

import Mathlib
import Definitions.Def_PreservePast_sourceExp
import Definitions.Def_PreservePast_Supplement_StateProtocol

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace PreservePast.Supplement

/-- **The actions of the log-score problem**: normalized, strictly positive densities `f` with
respect to the reference law `Q` whose log-score expectation `𝔼_{P_x} ln f` is finite for every
record `x` of the domain `𝒯`. P. Xu, *Information Required to Preserve Past Learning*, STOC 2027
submission (held version, PDF sha256 48013ceb…d00fa), §H.1, p.46 (PDF p.48): "For normalized
densities with finite log-score expectations, set g_x(f) = 𝔼_{P_x} ln f, ∫ f dQ = 1,
V(x) = D(P_x‖Q)."

**Formalization Note.** Densities are real-valued and strictly positive everywhere, because
Lean's `Real.log 0 = 0` would otherwise give a density vanishing on a `P_x`-positive set a finite
score instead of `−∞`. Mixing any normalized density with the constant density `1` shows that
neither the value `V(x)` nor any deficit changes. -/
def LogScoreAction {X Z : Type} [MeasurableSpace Z] (P : X → Measure Z) (Q : Measure Z)
    (T : Set X) : Type :=
  {f : Z → ℝ // Measurable f ∧ (∀ z, 0 < f z) ∧ ∫⁻ z, ENNReal.ofReal (f z) ∂Q = 1 ∧
    ∀ x ∈ T, Integrable (fun z => Real.log (f z)) (P x)}

/-- The **log-likelihood score** `g_x(f) = 𝔼_{P_x} ln f` (§H.1, p.46). -/
noncomputable def logScore {X Z : Type} [MeasurableSpace Z] (P : X → Measure Z) (Q : Measure Z)
    (T : Set X) (x : X) (f : LogScoreAction P Q T) : ℝ :=
  ∫ z, Real.log (f.1 z) ∂P x

/-- **The finite-order source exponent of the log score**, `𝓗_n(b; μ)` with domain `𝒯`: the
published `PreservePast.sourceExp` for the score `g_x(f) = 𝔼_{P_x} ln f` over normalized
densities (§H.1, p.46, PDF p.48: "The profile uses the log score above and the domain 𝒯"; in
nats). -/
noncomputable def logScoreExp {X Z : Type} [MeasurableSpace X] [MeasurableSpace Z]
    (μ : Measure X) (P : X → Measure Z) (Q : Measure Z) (T : Set X) (n : ℕ) (b : ℝ) : EReal :=
  sourceExp (logScore P Q T) T μ n b

/-- The logarithm `ln f_ν` of the density `f_ν = dP_ν/dQ` of the mixture query law
`P_ν = ∫ P_x ν(dx)`, `ν = μ(· | E)` (Lemma 13, p.46). -/
noncomputable def mixLogDensity {X Z : Type} [MeasurableSpace X] [MeasurableSpace Z]
    (μ : Measure X) (P : X → Measure Z) (Q : Measure Z) (E : Set X) (z : Z) : ℝ :=
  Real.log ((((μ E)⁻¹ • (μ.restrict E).bind P).rnDeriv Q z).toReal)

/-- **Lemma 13 applies to every region of `Q`-mass at most `qmax`, with the domain `𝒯`, the
success threshold `s` and the score-loss bound `b`.** Lemma 13, p.46 (PDF p.48): "Let 𝒯 be a
measurable set of records on which D(P_x‖Q) ≤ C. Fix s ∈ (0, 1] and a region A with
q = Q(A) > 0, and put E = 𝒯 ∩ {x : P_x(A) ≥ s}. If μ(E) > 0, let ν = μ(· | E) and
f_ν = dP_ν/dQ, where P_ν = ∫ P_x ν(dx). Suppose, for μ-almost every x ∈ E,
P_x{ln f_ν − 𝔼_{P_x} ln f_ν > Γ} ≤ s/8, and assume the displayed expectations and divergences
are finite"; its conclusion holds "With Δ = C − L ≥ 0", `L = ln(s/(2q)) − Γ`. Theorem 13, p.49
(PDF p.51): "Suppose Lemma 13 applies to every region of Q-mass at most g/k, with the same domain
𝒯 and nonnegative score-loss bound b".

**Formalization Note.** There is a divergence bound `C` on `𝒯` such that, for every measurable
region `A` with `0 < Q(A) ≤ qmax` and `μ(E) > 0`, the tail hypothesis of Lemma 13 holds with the
deviation threshold `Γ_A = b − C + ln(s/(2Q(A)))`, i.e. with the threshold for which the
lemma's score loss `Δ = C − ln(s/(2Q(A))) + Γ_A` equals `b`. A hypothesis with a smaller
threshold (in particular one threshold `Γ` for all regions with `C − ln(s/(2qmax)) + Γ ≤ b`, as
in Appendix J.2) implies this one. Divergences are Mathlib's `klDiv` (in nats, `∞` when not
finite). -/
def CommonScoreApplies {X Z : Type} [MeasurableSpace X] [MeasurableSpace Z] (μ : Measure X)
    (P : X → Measure Z) (Q : Measure Z) (T : Set X) (s qmax b : ℝ) : Prop :=
  ∃ C : ℝ, (∀ x ∈ T, InformationTheory.klDiv (P x) Q ≤ ENNReal.ofReal C) ∧
    ∀ A : Set Z, MeasurableSet A → 0 < Q A → Q A ≤ ENNReal.ofReal qmax →
      0 < μ (T ∩ {x | ENNReal.ofReal s ≤ P x A}) →
      ∀ᵐ x ∂(μ.restrict (T ∩ {x | ENNReal.ofReal s ≤ P x A})),
        Integrable (mixLogDensity μ P Q (T ∩ {x | ENNReal.ofReal s ≤ P x A})) (P x) ∧
        P x {z | b - C + Real.log (s / (2 * (Q A).toReal)) <
            mixLogDensity μ P Q (T ∩ {x | ENNReal.ofReal s ≤ P x A}) z -
              ∫ z', mixLogDensity μ P Q (T ∩ {x | ENNReal.ofReal s ≤ P x A}) z' ∂P x} ≤
          ENNReal.ofReal (s / 8)

/-- The **Bhattacharyya coefficient** `∫ √(dp dq)` of two laws, computed with densities with
respect to `p + q`. The affinity distance of §H.2, p.47 (PDF p.49), is
`a(x, x') = −ln ∫ √(dP_x dP_{x'})`. -/
noncomputable def bhatCoef {Z : Type} [MeasurableSpace Z] (p q : Measure Z) : ENNReal :=
  ∫⁻ z, (p.rnDeriv (p + q) z * q.rnDeriv (p + q) z) ^ ((1 : ℝ) / 2) ∂(p + q)

/-- The **source small-ball mass** `p_μ(a₀) = sup_{c∈𝒯} μ{x ∈ 𝒯 : a(x, c) ≤ a₀}` (§H.2, p.47:
"The mass uses the original source, before conditioning on 𝒯").

**Formalization Note.** `a(x, c) ≤ a₀` is written `e^{−a₀} ≤ ∫ √(dP_x dP_c)`, which also covers
`a = +∞`. -/
noncomputable def affinityMass {X Z : Type} [MeasurableSpace X] [MeasurableSpace Z]
    (μ : Measure X) (P : X → Measure Z) (T : Set X) (a₀ : ℝ) : ENNReal :=
  ⨆ c ∈ T, μ {x | x ∈ T ∧ ENNReal.ofReal (Real.exp (-a₀)) ≤ bhatCoef (P x) (P c)}

/-- The **gap** `G = (U − h_Δ)₊`, `h_Δ = −ln p_μ(Δ + ln 2)` (Lemma 14, p.47), as a function of
`U` and of the small-ball mass `p = p_μ(Δ + ln 2)`: `(U + ln p)₊`, and `0` when `p = 0`
(`h_Δ = +∞`). -/
noncomputable def coverGap (U : ℝ) (p : ENNReal) : ℝ :=
  if p = 0 then 0 else max (U + Real.log p.toReal) 0

/-- The **success** of a protocol in the identification experiment with `k` independent records
of law `μ`, a uniform independent query index and query channel `P` (§H.3, p.48). -/
noncomputable def idSuccess {X Z : Type} [MeasurableSpace X] [MeasurableSpace Z] {k : ℕ}
    (μ : Measure X) (P : X → Measure Z) (π : StateProtocol (Fin k → X) Z (Fin k)) : ℝ :=
  π.success (Measure.pi fun _ : Fin k => μ) id (idTest P)

/-- The **full-data optimum** `S*` of the identification experiment. -/
noncomputable def idOptimum {X Z : Type} [MeasurableSpace X] [MeasurableSpace Z]
    (μ : Measure X) (P : X → Measure Z) (k : ℕ) : ℝ :=
  fullDataOptimum (Out := Fin k) (Measure.pi fun _ : Fin k => μ) id (idTest P)

/-- The **retained information** `I(X; M | R)` in bits in the identification experiment. -/
noncomputable def idInfo {X Z : Type} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Z] {k : ℕ} (μ : Measure X) [IsProbabilityMeasure μ]
    (π : StateProtocol (Fin k → X) Z (Fin k)) : ENNReal :=
  π.info (Measure.pi fun _ : Fin k => μ) id id (fun _ => ())

end PreservePast.Supplement


