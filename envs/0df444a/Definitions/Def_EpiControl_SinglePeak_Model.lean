-- Prove2me | Definitions.Def_EpiControl_SinglePeak_Model
-- name    : EpiControl_SinglePeak_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:08:43.309052+00:00
-- url     : https://prove2.me/theorems/b8a29638-a1a0-4923-aa7f-47ec0dc92af9
-- title:
--   §2, §3, §3.1, §3.3, Lemma 9, pp. 4–15 — controlled SIR model, cost with vaccine at T, optimal policies, M, Assumption 1, multipliers and costate
-- statement:
--   This file fixes the optimal social-distancing problem of Kruse and Strack and the objects every statement of the mission refers to.
--
--   **Data.** A recovery rate $\gamma>0$, a vaccine date $T>0$, a compact interval $B=[\underline b,\bar b]\subset(0,\infty)$ of attainable transmission rates with $\underline b<\bar b$, initial shares $s_0,i_0\in(0,1)$ with $s_0+i_0\le 1$, a flow cost $v$ of infections and a cost $c$ of reducing the transmission rate.
--
--   **Standing assumptions** (§2, pp. 4–6). $v$ is convex and strictly increasing on $[0,1]$, continuously differentiable, with $v(0)=0$; $c$ is convex, non-increasing and continuous on $B$, with $c(\bar b)=0$ and $c(b)>0$ for $b\in[\underline b,\bar b)$.
--
--   **Controls and dynamics.** An admissible control is a measurable $\beta$ with $\beta(t)\in B$ for $t\in[0,T]$. Its SIR path $(s,i)$ solves
--   $$s'(t)=-\beta(t)i(t)s(t),\quad s(0)=s_0,\qquad i'(t)=\beta(t)i(t)s(t)-\gamma i(t),\quad i(0)=i_0 \tag{1}$$
--   on $[0,T]$.
--
--   **Cost and optimality.** With the terminal cost $\bar v(x)=\int_0^x \frac{v(z)}{z\gamma}\,dz$ of (4), the cost of $\beta$ is
--   $$J(\beta)=\int_0^T \big(v(i(t))+c(\beta(t))\big)\,dt+\bar v(i(T)), \tag{2}$$
--   and $\beta^*$ is optimal if it is admissible and $J(\beta^*)\le J(\beta)$ for every admissible $\beta$ (3).
--
--   **Auxiliary objects.** $M(y)=\min_{b\in B}[yb+c(b)]$ (p. 7); "$b$ minimizes $yb+c(b)$ over $B$"; the left derivative $c'(\bar b-)=\lim_{b\uparrow\bar b}\frac{c(\bar b)-c(b)}{\bar b-b}$ (footnote 13); **Assumption 1** (p. 10): $v$ is twice continuously differentiable and
--   $$\frac{v''(i)}{\gamma}<\frac{27}{4}\,\frac{\underline b}{\bar b-\underline b}\,\big|c'(\bar b-)\big|\qquad\text{for all } i\in[0,1].$$
--
--   **Multipliers of Lemma 9** (p. 15). Continuous $\lambda_1,\lambda_2$ on $[0,T]$ with $\lambda_1(T)=0$, $\lambda_2(T)=\frac{v(i(T))}{\gamma i(T)}$, satisfying the adjoint equations (11) $\lambda_1'=(\lambda_1-\lambda_2)\beta i$, $\lambda_2'=(\lambda_1-\lambda_2)\beta s+\gamma\lambda_2-v'(i)$, the optimality condition (12) $\beta(t)\in\arg\min_{b\in B}[(\lambda_2(t)-\lambda_1(t))i(t)s(t)b+c(b)]$ for almost every $t$, and the identity (13) $M((\lambda_2-\lambda_1)is)-\gamma\lambda_2 i+v(i)=M(v(i(T))s(T)/\gamma)$ for every $t\in[0,T]$.
--
--   **Costate of Proposition 1** (p. 6). A continuous $\eta$ on $[0,T]$ with $\eta(T)=\frac{v(i(T))}{\gamma i(T)}$, solving
--   $$\eta'(t)=\eta(t)\beta(t)i(t)-v'(i(t))+\frac{v(i(t))+c(\beta(t))-M\big(v(i(T))s(T)/\gamma\big)}{i(t)} \tag{5}$$
--   with $\beta(t)\in\arg\min_{b\in B}[\eta(t)i(t)s(t)b+c(b)]$ for almost every $t$ (6), and $\eta>0$ on $[0,T]$.
--
--   **Gain** (p. 7). $g(t)=\eta(t)i(t)s(t)$.
--
--   These objects are the setting of every statement in the mission.
--
--   **Formalization Note** The parameters are bundled in a structure `Params`; `bl` is $\underline b$, `bbar` is $\bar b$, `vT` is $\bar v$. Added relative to the page: $\underline b<\bar b$ (Assumption 1 divides by $\bar b-\underline b$); $c>0$ on $[\underline b,\bar b)$ (the page prints the sign slip "$c(\bar b)=0>c(b)$" while $c$ maps into $[0,\infty)$); $v$ is $C^1$ (resp. $C^2$ in Assumption 1) on all of $\mathbb R$, an extension of the page's $C^k$ on $[0,1]$ — only values on $[0,1]$ matter, and $v'(1)$, $v''$ at the endpoints are those of the extension. Admissibility constrains $\beta$ only on $[0,T]$, the only part entering $J$. All differential equations are in integral (Carathéodory) form on $[0,T]$ with continuous solutions, which is how "absolutely continuous" is carried; the integrands are bounded and measurable along admissible controls and continuous paths, so the integrals are genuine. Almost-everywhere statements are with respect to Lebesgue measure restricted to $[0,T]$. $M$ is an `sInf` over the image of the compact interval $B$ under a continuous function; the set is nonempty and compact, so it is the minimum. The left derivative $c'(\bar b-)$ is a real parameter `dc` together with the limit statement. The minimum in (5) is written $M(v(i(T))s(T)/\gamma)$, as in Lemma 11. The costate is a predicate, never a chosen function.
-- source:
--   Kruse & Strack, Optimal Control of an Epidemic through Social Distancing, Cowles Foundation Discussion Paper No. 2229R (rev. July 2020), pp. 4–15 (PDF 5–16): §2 (1), (2), (3), (4); Proposition 1 (5), (6); §3.1 g, M; Assumption 1 and footnote 13; Lemma 9 (11)–(13)

import Mathlib

namespace EpiControl.SinglePeak

open MeasureTheory Set Filter Topology

/-- The data of the controlled SIR problem of Kruse & Strack (§2, pp. 4–6):
recovery rate `γ`, vaccine date `T`, the transmission-rate bounds `bl` (b̲) and
`bbar` (b̄) of `B = [b̲, b̄]`, the initial shares `s0`, `i0`, the flow cost `v` of
infections and the cost `c` of reducing the transmission rate. -/
structure Params where
  γ : ℝ
  T : ℝ
  bl : ℝ
  bbar : ℝ
  s0 : ℝ
  i0 : ℝ
  v : ℝ → ℝ
  c : ℝ → ℝ

namespace Params

variable (P : Params)

/-- Standing assumptions of §2 (pp. 4–6). Additions disclosed in the item text:
`bl < bbar`, the positivity `0 < c b` on `[b̲, b̄)` (the page prints the sign slip
"c(b̄) = 0 > c(b)"), and global `C¹` smoothness of `v` (the page has `C¹` on `[0, 1]`). -/
structure Standing : Prop where
  γ_pos : 0 < P.γ
  bl_pos : 0 < P.bl
  bl_lt_bbar : P.bl < P.bbar
  T_pos : 0 < P.T
  s0_mem : P.s0 ∈ Ioo (0 : ℝ) 1
  i0_mem : P.i0 ∈ Ioo (0 : ℝ) 1
  s0_add_i0 : P.s0 + P.i0 ≤ 1
  v_convex : ConvexOn ℝ (Icc (0 : ℝ) 1) P.v
  v_strictMono : StrictMonoOn P.v (Icc (0 : ℝ) 1)
  v_zero : P.v 0 = 0
  v_C1 : ContDiff ℝ 1 P.v
  c_convex : ConvexOn ℝ (Icc P.bl P.bbar) P.c
  c_antitone : AntitoneOn P.c (Icc P.bl P.bbar)
  c_cont : ContinuousOn P.c (Icc P.bl P.bbar)
  c_bbar : P.c P.bbar = 0
  c_pos : ∀ b ∈ Ico P.bl P.bbar, 0 < P.c b

/-- Admissible controls (p. 5): measurable, with values in `B = [b̲, b̄]` on `[0, T]`
(only `[0, T]` enters the cost). -/
def Admissible (β : ℝ → ℝ) : Prop :=
  Measurable β ∧ ∀ t ∈ Icc 0 P.T, β t ∈ Icc P.bl P.bbar

/-- `(s, i)` solves the SIR dynamics (1) driven by `β` on `[0, T]`, in integral
(Carathéodory) form, with continuous `s` and `i`. -/
def IsSIRPath (β s i : ℝ → ℝ) : Prop :=
  ContinuousOn s (Icc 0 P.T) ∧ ContinuousOn i (Icc 0 P.T) ∧
    ∀ t ∈ Icc 0 P.T,
      s t = P.s0 - ∫ r in (0 : ℝ)..t, β r * i r * s r ∧
      i t = P.i0 + ∫ r in (0 : ℝ)..t, (β r * i r * s r - P.γ * i r)

/-- Terminal cost (4): `v̄(x) = ∫₀ˣ v(z)/(zγ) dz`. -/
noncomputable def vT (x : ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..x, P.v z / (z * P.γ)

/-- Cost functional (2): `J = ∫₀ᵀ (v(i(t)) + c(β(t))) dt + v̄(i(T))`. -/
noncomputable def J (β i : ℝ → ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..P.T, (P.v (i t) + P.c (β t))) + P.vT (i P.T)

/-- Optimality (3): `β` is admissible with SIR path `(s, i)`, and its cost is at most
that of every admissible control along its SIR path. -/
def IsOptimal (β s i : ℝ → ℝ) : Prop :=
  P.Admissible β ∧ P.IsSIRPath β s i ∧
    ∀ β' s' i' : ℝ → ℝ, P.Admissible β' → P.IsSIRPath β' s' i' →
      P.J β i ≤ P.J β' i'

/-- `M(y) = min_{b ∈ B} [y b + c(b)]` (p. 7); the minimum over the compact interval is
attained, so `sInf` is the minimum. -/
noncomputable def M (y : ℝ) : ℝ :=
  sInf ((fun b => y * b + P.c b) '' Icc P.bl P.bbar)

/-- `b` is a minimizer of `b ↦ y b + c(b)` over `B` (the argmin conditions (6), (12)). -/
def ArgminAt (y b : ℝ) : Prop :=
  b ∈ Icc P.bl P.bbar ∧ ∀ b' ∈ Icc P.bl P.bbar, y * b + P.c b ≤ y * b' + P.c b'

/-- Footnote 13: `dc = c′(b̄−) = lim_{b ↗ b̄} (c(b̄) − c(b))/(b̄ − b)`. -/
def LeftDeriv (dc : ℝ) : Prop :=
  Tendsto (fun b => (P.c P.bbar - P.c b) / (P.bbar - b)) (𝓝[<] P.bbar) (𝓝 dc)

/-- Assumption 1 (Limited Capacity Effects, p. 10), with `dc = c′(b̄−)`:
`v` is `C²` and `v″(i)/γ < (27/4) · b̲/(b̄ − b̲) · |c′(b̄−)|` for all `i ∈ [0, 1]`. -/
def Assumption1 (dc : ℝ) : Prop :=
  ContDiff ℝ 2 P.v ∧ P.LeftDeriv dc ∧
    ∀ x ∈ Icc (0 : ℝ) 1,
      deriv (deriv P.v) x / P.γ < 27 / 4 * (P.bl / (P.bbar - P.bl)) * |dc|

/-- The Lagrange multipliers of Lemma 9 (p. 15): continuous `λ₁, λ₂` on `[0, T]`
solving (11) in integral form from their terminal values, the optimality condition (12)
for almost every `t ∈ [0, T]`, and the identity (13) for every `t ∈ [0, T]`. -/
def IsMultiplier (β s i lam1 lam2 : ℝ → ℝ) : Prop :=
  ContinuousOn lam1 (Icc 0 P.T) ∧ ContinuousOn lam2 (Icc 0 P.T) ∧
    lam1 P.T = 0 ∧ lam2 P.T = P.v (i P.T) / (P.γ * i P.T) ∧
    (∀ t ∈ Icc 0 P.T,
      lam1 t = lam1 P.T - ∫ r in t..P.T, (lam1 r - lam2 r) * β r * i r) ∧
    (∀ t ∈ Icc 0 P.T,
      lam2 t = lam2 P.T - ∫ r in t..P.T,
        ((lam1 r - lam2 r) * β r * s r + P.γ * lam2 r - deriv P.v (i r))) ∧
    (∀ᵐ t ∂(volume.restrict (Icc 0 P.T)),
      P.ArgminAt ((lam2 t - lam1 t) * i t * s t) (β t)) ∧
    ∀ t ∈ Icc 0 P.T,
      P.M ((lam2 t - lam1 t) * i t * s t) - P.γ * lam2 t * i t + P.v (i t) =
        P.M (P.v (i P.T) * s P.T / P.γ)

/-- The costate `η` of Proposition 1 (p. 6): continuous on `[0, T]`, terminal value
`η(T) = v(i(T))/(γ i(T))`, the adjoint equation (5) in integral form, the argmin
condition (6) for almost every `t ∈ [0, T]`, and `η > 0` on `[0, T]`. The `min` in (5)
is `M(v(i(T)) s(T)/γ)`. -/
def IsCostate (β s i η : ℝ → ℝ) : Prop :=
  ContinuousOn η (Icc 0 P.T) ∧
    η P.T = P.v (i P.T) / (P.γ * i P.T) ∧
    (∀ t ∈ Icc 0 P.T,
      η t = η P.T - ∫ r in t..P.T,
        (η r * β r * i r - deriv P.v (i r) +
          (P.v (i r) + P.c (β r) - P.M (P.v (i P.T) * s P.T / P.γ)) / i r)) ∧
    (∀ᵐ t ∂(volume.restrict (Icc 0 P.T)), P.ArgminAt (η t * i t * s t) (β t)) ∧
    ∀ t ∈ Icc 0 P.T, 0 < η t

end Params

/-- The gain from reducing the transmission rate (p. 7): `g(t) = η(t) i(t) s(t)`. -/
def gain (η s i : ℝ → ℝ) (t : ℝ) : ℝ :=
  η t * i t * s t

end EpiControl.SinglePeak


