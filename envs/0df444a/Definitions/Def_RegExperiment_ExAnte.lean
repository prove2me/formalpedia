-- Prove2me | Definitions.Def_RegExperiment_ExAnte
-- name    : RegExperiment_ExAnte
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:44:36.861978+00:00
-- url     : https://prove2.me/theorems/0d7473e0-fe77-4e0e-8a59-443a55d11ba4
-- title:
--   Ex ante value $u^1(\sigma_0;s,S,z)$, welfare and the firm's flows
-- statement:
--   **Hitting kernels.** For standards $s<S$ and a belief $\sigma\in(s,S)$, the expected discounted probabilities, in state $G$, of reaching the adoption standard $S$ first and the rejection standard $s$ first are
--   $$
--   \Psi(\sigma,G,s,S)=\frac{e^{-R_1(\sigma-s)}-e^{-R_2(\sigma-s)}}{e^{-R_1(S-s)}-e^{-R_2(S-s)}},\qquad
--   \psi(\sigma,G,s,S)=\frac{e^{R_2(S-\sigma)}-e^{R_1(S-\sigma)}}{e^{R_2(S-s)}-e^{R_1(S-s)}},
--   $$
--   and in state $B$, $\Psi(\sigma,B,s,S)=e^{\sigma-S}\Psi(\sigma,G,s,S)$ and $\psi(\sigma,B,s,S)=e^{\sigma-s}\psi(\sigma,G,s,S)$.
--
--   **Ex ante value.** A player with flows $a=(a_G,a_B)$ who experiments from the prior $\sigma_0$ until the belief reaches $s$ (reject, payoff $0$) or $S$ (adopt, then withdraw at $z$) obtains, for $s<\sigma_0<S$,
--   $$
--   u^1(\sigma_0;s,S,z)=\sum_{\theta\in\{G,B\}}\pi_\theta(\sigma_0)\Bigl[-\frac cr+\Bigl(u^2_\theta(S,z)+\frac cr\Bigr)\Psi(\sigma_0,\theta,s,S)+\frac cr\,\psi(\sigma_0,\theta,s,S)\Bigr],
--   $$
--   where $u^2_\theta(S,z)=\frac{a_\theta}{r}(1-\psi(S,\theta,z))$. If $\sigma_0\le s$ the player rejects at once ($u^1=0$); otherwise, if $S\le\sigma_0$, it adopts at once ($u^1=u^2(\sigma_0,z)$).
--
--   **Welfare** is $u^1_p$, the value with the planner's flows $(v^G_p,v^B_p)$. The **firm** under liability $L$ has flows $(v_i,\ v_i-L)$ and the same cost, discount rate and learning speeds; liability is a transfer and does not enter welfare.
--
--   **Formalization Note** The page writes only the interior formula; the two boundary branches encode stopping at once, with rejection taking precedence.
-- source:
--   Henry–Loseto–Ottaviani, working paper (Nov. 2018): §3.2 display, p.10; Proof of Proposition 1, Step 2, p.34 and fn.37 (kernels); §5, p.15 (firm's payoff v_i − L in state B)

import Mathlib
import Definitions.Def_RegExperiment_Model

namespace RegExperiment

/-- `Ψ(σ, G, s, S)`: the expected discounted probability, in state `G`, of reaching the adoption
standard `S` before the rejection standard `s`, starting at belief `σ` (fn.37, p.34):
`Ψ(σ,G,s,S) = (e^{−R₁(σ−s)} − e^{−R₂(σ−s)}) / (e^{−R₁(S−s)} − e^{−R₂(S−s)})`.
It is used only for `s < σ < S`, where the denominator is nonzero. -/
noncomputable def PsiG (P : Params) (σ s S : ℝ) : ℝ :=
  (Real.exp (-(R1 P) * (σ - s)) - Real.exp (-(R2 P) * (σ - s))) /
    (Real.exp (-(R1 P) * (S - s)) - Real.exp (-(R2 P) * (S - s)))

/-- `ψ(σ, G, s, S)`: the expected discounted probability, in state `G`, of reaching the rejection
standard `s` before the adoption standard `S`, starting at belief `σ` (fn.37, p.34):
`ψ(σ,G,s,S) = (e^{R₂(S−σ)} − e^{R₁(S−σ)}) / (e^{R₂(S−s)} − e^{R₁(S−s)})`. -/
noncomputable def psiG (P : Params) (σ s S : ℝ) : ℝ :=
  (Real.exp (R2 P * (S - σ)) - Real.exp (R1 P * (S - σ))) /
    (Real.exp (R2 P * (S - s)) - Real.exp (R1 P * (S - s)))

/-- `Ψ(σ, B, s, S) = e^{σ−S} Ψ(σ, G, s, S)` (fn.37, p.34, "by their Lemma B0"). -/
noncomputable def PsiB (P : Params) (σ s S : ℝ) : ℝ := Real.exp (σ - S) * PsiG P σ s S

/-- `ψ(σ, B, s, S) = e^{σ−s} ψ(σ, G, s, S)` (fn.37, p.34, "by their Lemma B0"). -/
noncomputable def psiB (P : Params) (σ s S : ℝ) : ℝ := Real.exp (σ - s) * psiG P σ s S

/-- The ex ante value `u¹(σ₀; s, S, z)` of a player with flow payoffs `a = (a_G, a_B)` and research
cost `c` who, starting at belief `σ₀`, experiments until the belief reaches the rejection
standard `s` (payoff `0`) or the adoption standard `S` (ex post value under withdrawal standard
`z`) (§3.2 display, p.10; Proof of Proposition 1, Step 2, p.34):
`u¹ = Σ_θ π_θ(σ₀)·[−c/r + (u²(S,θ,z) + c/r) Ψ(σ₀,θ,s,S) + (c/r) ψ(σ₀,θ,s,S)]`.

**Formalization Note** The page writes only the interior formula (`s < σ₀ < S`). At `σ₀ ≤ s` the
player rejects at once (value `0`); otherwise, at `S ≤ σ₀`, it adopts at once (value
`u²(σ₀, z)`). Rejection takes precedence, so the interior branch always has `s < σ₀ < S`. -/
noncomputable def U1 (P : Params) (a : ℝ × ℝ) (σ₀ s S z : ℝ) : ℝ :=
  if σ₀ ≤ s then 0
  else if S ≤ σ₀ then U2 P a σ₀ z
  else
    piG σ₀ * (-(P.c / P.r) + (u2 P a.1 .G S z + P.c / P.r) * PsiG P σ₀ s S
        + P.c / P.r * psiG P σ₀ s S)
    + piB σ₀ * (-(P.c / P.r) + (u2 P a.2 .B S z + P.c / P.r) * PsiB P σ₀ s S
        + P.c / P.r * psiB P σ₀ s S)

/-- Social welfare `u¹_p(σ₀; s, S, z)`: the ex ante value with the planner's flows
`(v^G_p, v^B_p)` (p.10). Liability is a transfer and does not enter welfare. -/
noncomputable def Wel (P : Params) (σ₀ s S z : ℝ) : ℝ := U1 P (P.vG, P.vB) σ₀ s S z

/-- The firm's flow payoffs under externality rate `e` and liability rate `L`:
`v_i` in state `G` and `v_i − L` in state `B` (§5, p.15: "In state B, the firm thus obtains payoff
`v_i − L`"). -/
def firmFlows (P : Params) (e L : ℝ) : ℝ × ℝ := (vi P e, vi P e - L)

end RegExperiment


