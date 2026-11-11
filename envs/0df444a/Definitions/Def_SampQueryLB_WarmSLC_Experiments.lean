-- Prove2me | Definitions.Def_SampQueryLB_WarmSLC_Experiments
-- name    : SampQueryLB_WarmSLC_Experiments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:16:04.621559+00:00
-- url     : https://prove2.me/theorems/ed7b2d7a-7b71-4f31-af2c-f29ac1616c58
-- title:
--   §5.1, §5.4.1, §6.1, §7.1 — field-query algorithms, the parameters ζ, r, M, δ, e_i, the masses Z, Z_good, Z_bad, M, the warm initialization ν_{Ξ,v} and the experiments P_w, P̂
-- statement:
--   This file collects the objects built on the hard family.
--
--   **Field queries (§5.1).** A randomized algorithm with seed in $O$ making $q$ first-order queries to a function $f$ on $\mathbb R^{d_n}$: the query $y_t$ is a Borel function of the seed and the replies $(f(y_s),\nabla f(y_s))_{s<t}$, and the output $X$ is a Borel function of the seed and all $q$ replies. It is run on the field of level $i$ without gate, $x\mapsto\langle\Xi_i,\Phi_i(x)\rangle$. Also $\min_{p}a_{i,p}$, the node $T_t=T_i(X,y_t)$ if $C_i(X)C_i(y_t)>0$ and $0$ otherwise, and the span $O_A=\mathrm{span}\{\Phi_{j,p}(x),D_v\Phi_{j,p}(x):j<i,\,p\in\mathcal P,\,x\in A,\,v\}$ of Lemma 5.8.
--
--   **Parameters (§5.4.1).** $\zeta=e^{-Q^2}n^{-300}$, $r=\big(1204(Q+1)^2(Q^2+\log n)/K\big)^{1/2}$, $M=|\mathcal P|[Q(h+1)(d_n+1)+1]$, $\delta=\frac32\zeta M$, $e_0=\zeta$, $e_i=\zeta+2Q(e_{i-1}+\delta)$.
--
--   **Masses (§6.1).** $w(\Xi,x)=\exp[-\sum_iA^\Xi_i(x)U_i(H^\Xi_i(x))]$, $Z(\Xi)=\int w\,d\gamma_n$; the good event $F_n=\{x\in\mathcal R_n\}\cap\bigcap_i\{\max_p|H^\Xi_{i,p}(x)/(na_{i,p}^2)+\beta_i|\le\epsilon_g\beta_i/4\}$; $Z_{\mathrm{good}}=\int w1_{F_n}d\gamma_n$, $Z_{\mathrm{bad}}=\int w1_{F_n^c}d\gamma_n$; $m(x)=\mathbb E_{\Xi\sim\mu_n}\exp[-\sum_i\beta_iH^\Xi_i(x)]$ and $M=\int m\,d\gamma_n$.
--
--   **Warm initialization (§7.1).** For an even $\vartheta\in C^\infty(\mathbb R;[0,1])$ vanishing on $|t|\le 9/20$ and equal to $1$ on $|t|\ge1/2$, put $f=\frac1{100}+\frac{99}{100}\vartheta$ and
--   $$\nu_{\Xi,v}(dx)=\frac{f(v^\top x_h)\,\pi^\Xi(dx)}{Z^{\mathrm{init}}_{\Xi,v}},\qquad Z^{\mathrm{init}}_{\Xi,v}=\int f(v^\top x_h)\,\pi^\Xi(dx).$$
--   The warm experiment $P_w$ draws $\Xi\sim\mu_n(\cdot\mid E_n)$, $v$ uniform on $S^{n-1}$, $x^\circ\sim\nu_{\Xi,v}$ and a fresh seed $\omega\sim\mathrm{Unif}[0,1]$, and runs a warm-start algorithm on $V^\Xi_h$ from $x^\circ$. The reference experiment $\hat P$ of Lemma 7.2 draws $x^\circ\sim\lambda$, $v$ uniform, $\tilde\Xi\sim\mu_n$, sets $\Xi_{i,p}=\tilde\Xi_{i,p}-\beta_i\Phi_{i,p}(x^\circ)$, and runs the algorithm on $V^\Xi_h$ from $x^\circ$ with a fresh seed.
--
--   **Formalization Note.** A field-query algorithm makes exactly $q$ queries (a shorter run is padded with queries at the origin, where every field vanishes with its gradient, §5.4.1). Masses are in $[0,\infty]$; $m(x)$ is the defining expectation. An outcome is $(\Xi,v,x^\circ,\omega,\text{transcript},\text{output})$ with the transcript padded to length $q$; `Pwarm` and `Pref` are the iterated integrals of the indicator of an event of outcomes. The uniform law on $S^{n-1}$ is the normalized surface measure.
-- source:
--   Zhou, Suzuki, Towards the Query Complexity of Sampling under Strong Log-Concavity and Log-Sobolev Inequalities, arXiv:2611.05813 (held version dated November 3, 2026, sha256 966f8fc0…184c), p. 34, §5.1; p. 43, Lemma 5.8; p. 44, §5.4.1; pp. 49–50, §6.1 (Definition 6.1, (48)–(51)); pp. 56–57, §7.1 ((63)–(65))

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_SampQueryLB_WarmSLC_Model
import Definitions.Def_SampQueryLB_WarmSLC_HardFamily

/-!
# Field queries (§5.1), the parameters of §5.4.1, the masses of §6.1 and the warm-start
experiments of §7

Zhou, Suzuki, arXiv:2611.05813 (held version dated November 3, 2026), p. 34 (§5.1), p. 44
(§5.4.1), pp. 49–50 (§6.1, Definition 6.1, (48)–(51)), pp. 56–57 (§7.1, (63)–(65)).

Conventions.
* `FieldAlg n O q` is a randomized algorithm with seed space `O` making exactly `q` first-order
  queries to a function on `ℝ^{d_n}` (an algorithm that stops earlier is padded with queries at
  the origin, §5.4.1) and outputting a Borel function of its seed and its replies. The query of
  round `t` may not depend on the replies of rounds `≥ t`. `fieldReplies` runs it on the field
  of level `i`, `x ↦ ⟨Ξ_i, Φ_i(x)⟩` (no gate).
* §6.1: `wt c Ξ x = w(Ξ, x)`, `Zmass = Z(Ξ)`, `goodEv = F_n`, `Zgood`, `Zbad`, `mtilt = m(x)`
  (as the expectation that defines it), `Mmass = M`, all masses in `ℝ≥0∞`.
* §7: `IsSlabProfile ϑ` is the requirement on `ϑ`; `nuInit c ϑ Ξ v = ν_{Ξ,v}`,
  `Zinit = Z^init_{Ξ,v}`; `sphereUnif n` is the normalized surface measure on `S^{n−1}`; `shift`
  is the mean shift `(β_i Φ_{i,p}(x°))_{i,p}` of (65); an outcome of an experiment is
  `(Ξ, v, x°, ω, transcript, output)`; `Pwarm` is `P_w` and `Pref` is `P̂`, as iterated
  integrals of the indicator of an event.
-/

namespace SampQueryLB.WarmSLC

open MeasureTheory OAI.LogConcaveSampling ProbabilityTheory
open scoped ENNReal ContDiff RealInnerProductSpace

noncomputable section

/-! ## Algorithms querying one field (§5.1) -/

/-- Replies `(s_t, g_t)` of `q` first-order queries. -/
abbrev Replies (n q : ℕ) := Fin q → ℝ × Point (dn n)

/-- A randomized algorithm making `q` first-order queries to a function on `ℝ^{d_n}`. -/
structure FieldAlg (n : ℕ) (O : Type) [MeasurableSpace O] (q : ℕ) where
  /-- `query t (w, r)` is the query `y_{t+1}`; it may use only `r 0, …, r (t−1)`. -/
  query : Fin q → O × Replies n q → Point (dn n)
  /-- The output `X`, any Borel function of the seed and the replies. -/
  out : O × Replies n q → Point (dn n)
  query_measurable : ∀ t, Measurable (query t)
  out_measurable : Measurable out
  query_nonanticipating : ∀ t w (r r' : Replies n q), (∀ s, s < t → r s = r' s) →
    query t (w, r) = query t (w, r')

namespace FieldAlg

variable {n : ℕ} {O : Type} [MeasurableSpace O] {q : ℕ}

/-- The replies of the run on `f` with seed `ω` (fixed point of one round, reached after `q`
iterations). -/
def replies (A : FieldAlg n O q) (f : Point (dn n) → ℝ) (w : O) : Replies n q :=
  (fun r t => (f (A.query t (w, r)), gradient f (A.query t (w, r))))^[q] 0

/-- The queries `y_t` of the run on `f`. -/
def queries (A : FieldAlg n O q) (f : Point (dn n) → ℝ) (w : O) (t : Fin q) : Point (dn n) :=
  A.query t (w, A.replies f w)

/-- The output `X` of the run on `f`. -/
def output (A : FieldAlg n O q) (f : Point (dn n) → ℝ) (w : O) : Point (dn n) :=
  A.out (w, A.replies f w)

end FieldAlg

/-- The minimum amplitude `min_{p ∈ 𝒫} a_{i,p}` of level `i`. -/
def aMin (n : ℕ) (i : Lvl n) : ℝ := ⨅ p : Deg n, aa n i p

/-- `O_A = span{Φ_{j,p}(x), D_vΦ_{j,p}(x) : j < i, p ∈ 𝒫, x ∈ A, v ∈ ℝ^{(h+1)n}} ⊆ G_{<i}` of
Lemma 5.8, for a set `A` of points. -/
def obsSpan {n : ℕ} (i : Lvl n) (A : Set (Point (dn n))) : Submodule ℝ (Coef n) :=
  Submodule.span ℝ {a | ∃ (j : Lvl n) (p : Deg n) (x : Point (dn n)), j < i ∧ x ∈ A ∧
    (a = feat j p x ∨ ∃ v : Point (dn n), a = fderiv ℝ (feat j p) x v)}

/-- The node `T_t` of Theorem 6: `T_i(X, y)` when `C_i(X) C_i(y) > 0`, and `0` otherwise. -/
def Tnode {n : ℕ} (i : Lvl n) (X y : Point (dn n)) : ℝ :=
  if 0 < Ccut i X * Ccut i y then Tcorr i X y else 0

/-! ## The parameters of §5.4.1 -/

/-- `ζ = e^{−Q²} n^{−300}`. -/
def zetaP (n : ℕ) : ℝ := Real.exp (-((QQ n : ℝ) ^ 2)) * ((n : ℝ) ^ 300)⁻¹

/-- `r = (1204 (Q+1)² (Q² + log n) / K)^{1/2}`. -/
def rP (n : ℕ) : ℝ :=
  Real.sqrt (1204 * ((QQ n : ℝ) + 1) ^ 2 * ((QQ n : ℝ) ^ 2 + Real.log n) / KK n)

/-- `M = |𝒫| [Q (h+1)(d_n + 1) + 1]`. -/
def MP (n : ℕ) : ℕ := (degs n).card * (QQ n * (hh n + 1) * (dn n + 1) + 1)

/-- `δ = (3/2) ζ M`. -/
def deltaP (n : ℕ) : ℝ := 3 / 2 * zetaP n * MP n

/-- `e_0 = ζ`, `e_i = ζ + 2Q (e_{i−1} + δ)`. -/
def eP (n : ℕ) : ℕ → ℝ
  | 0 => zetaP n
  | i + 1 => zetaP n + 2 * QQ n * (eP n i + deltaP n)

/-! ## The masses of §6.1 -/

/-- The target weight `w(Ξ, x) = exp[−Σ_i A^Ξ_i(x) U_i(H^Ξ_i(x))]` of (48). -/
def wt (c : Consts) {n : ℕ} (Ξ : Coef n) (x : Point (dn n)) : ℝ :=
  Real.exp (-∑ i : Lvl n, gateProd c Ξ i x * Ucut c n i (field Ξ i x))

/-- `Z(Ξ) = ∫ w(Ξ, x) dγ_n(x)`. -/
def Zmass (c : Consts) {n : ℕ} (Ξ : Coef n) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (wt c Ξ x) ∂gammaN n

/-- The good event `F_n = {x ∈ R} ∩ ⋂_i D_i` of Definition 6.1. -/
def goodEv (c : Consts) (n : ℕ) : Set (Coef n × Point (dn n)) :=
  {z | z.2 ∈ shell n ∧ ∀ (i : Lvl n) (p : Deg n),
    |energy z.1 i p z.2 + beta c n i| ≤ epsG * beta c n i / 4}

/-- `Z_good(Ξ) = ∫ w 1_{F_n} dγ_n`. -/
def Zgood (c : Consts) {n : ℕ} (Ξ : Coef n) : ℝ≥0∞ :=
  ∫⁻ x, {x | (Ξ, x) ∈ goodEv c n}.indicator (fun x => ENNReal.ofReal (wt c Ξ x)) x ∂gammaN n

/-- `Z_bad(Ξ) = ∫ w 1_{F_n^c} dγ_n`. -/
def Zbad (c : Consts) {n : ℕ} (Ξ : Coef n) : ℝ≥0∞ :=
  ∫⁻ x, {x | (Ξ, x) ∉ goodEv c n}.indicator (fun x => ENNReal.ofReal (wt c Ξ x)) x ∂gammaN n

/-- `m(x) = E_{Ξ∼µ_n} exp[−Σ_i β_i H^Ξ_i(x)]`. -/
def mtilt (c : Consts) (n : ℕ) (x : Point (dn n)) : ℝ≥0∞ :=
  ∫⁻ Ξ, ENNReal.ofReal (Real.exp (-∑ i : Lvl n, beta c n i * field Ξ i x)) ∂mu n

/-- `M = ∫ m dγ_n`. -/
def Mmass (c : Consts) (n : ℕ) : ℝ≥0∞ := ∫⁻ x, mtilt c n x ∂gammaN n

/-! ## The warm initialization and the experiments of §7 -/

/-- `ϑ ∈ C^∞(ℝ; [0, 1])` even, `0` on `|t| ≤ 9/20` and `1` on `|t| ≥ 1/2`. -/
def IsSlabProfile (ϑ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ ϑ ∧ (∀ t, ϑ (-t) = ϑ t) ∧ (∀ t, 0 ≤ ϑ t ∧ ϑ t ≤ 1) ∧
    (∀ t, |t| ≤ 9 / 20 → ϑ t = 0) ∧ (∀ t, 1 / 2 ≤ |t| → ϑ t = 1)

/-- `f = 1/100 + (99/100) ϑ`. -/
def fInit (ϑ : ℝ → ℝ) (t : ℝ) : ℝ := 1 / 100 + 99 / 100 * ϑ t

/-- `v^⊤ x_h`. -/
def slabCoord {n : ℕ} (v : Point n) (x : Point (dn n)) : ℝ := ⟪v, blk x (lastLvl n)⟫

/-- `Z^init_{Ξ,v} = ∫ f(v^⊤ x_h) π^Ξ(dx)` of (64). -/
def Zinit (c : Consts) {n : ℕ} (ϑ : ℝ → ℝ) (Ξ : Coef n) (v : Point n) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (fInit ϑ (slabCoord v x)) ∂piHard c Ξ

/-- `ν_{Ξ,v}(dx) ∝ f(v^⊤ x_h) π^Ξ(dx)` of (64). -/
def nuInit (c : Consts) {n : ℕ} (ϑ : ℝ → ℝ) (Ξ : Coef n) (v : Point n) : Measure (Point (dn n)) :=
  (Zinit c ϑ Ξ v)⁻¹ • (piHard c Ξ).withDensity (fun x => ENNReal.ofReal (fInit ϑ (slabCoord v x)))

/-- The uniform law on `S^{n−1}` (normalized surface measure). -/
def sphereUnif (n : ℕ) : Measure (Metric.sphere (0 : Point n) 1) :=
  (volume : Measure (Point n)).toSphere[|Set.univ]

/-- The mean shift `(β_i Φ_{i,p}(x°))_{i,p}` of (65). -/
def shift (c : Consts) {n : ℕ} (x : Point (dn n)) : Coef n :=
  ∑ i : Lvl n, ∑ p : Deg n, beta c n i • feat i p x

/-- Outcomes `(Ξ, v, x°, ω, transcript, output)` of a run with at most `q` queries. -/
abbrev Outcome (n q : ℕ) :=
  Coef n × Point n × Point (dn n) × ℝ × (ℕ∞ × Hist (dn n) q) × Point (dn n)

/-- The outcome of a run of `A` on `V^Ξ_h` from `x°` with seed `ω`, the direction being `v`. -/
def outcome (c : Consts) {n : ℕ} (A : WarmAlgorithm (dn n)) (q : ℕ) (Ξ : Coef n) (v : Point n)
    (x : Point (dn n)) (w : ℝ) : Outcome n q :=
  (Ξ, v, x, w, A.transcript (Vhard c Ξ) x w q, A.output (Vhard c Ξ) x w)

/-- `P_w(S)`: `Ξ ∼ µ_n(· | E_n)`, `v` uniform, `x° ∼ ν_{Ξ,v}`, a fresh seed `ω ∼ Unif[0,1]`. -/
def Pwarm (c : Consts) {n : ℕ} (ϑ : ℝ → ℝ) (A : WarmAlgorithm (dn n)) (q : ℕ)
    (Sev : Set (Outcome n q)) : ℝ≥0∞ :=
  ∫⁻ Ξ, ∫⁻ v, ∫⁻ x, ∫⁻ w, Sev.indicator 1 (outcome c A q Ξ (v : Point n) x w) ∂seedLaw
    ∂nuInit c ϑ Ξ (v : Point n) ∂sphereUnif n ∂(mu n)[|Eadm c n]

/-- `P̂(S)`: `x° ∼ λ`, `v` uniform, `Ξ = Ξ̃ − shift x°` with `Ξ̃ ∼ µ_n`, a fresh seed. -/
def Pref (c : Consts) {n : ℕ} (lam : Measure (Point (dn n))) (A : WarmAlgorithm (dn n)) (q : ℕ)
    (Sev : Set (Outcome n q)) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ v, ∫⁻ Ξt, ∫⁻ w, Sev.indicator 1 (outcome c A q (Ξt - shift c x) (v : Point n) x w)
    ∂seedLaw ∂mu n ∂sphereUnif n ∂lam

end

end SampQueryLB.WarmSLC


