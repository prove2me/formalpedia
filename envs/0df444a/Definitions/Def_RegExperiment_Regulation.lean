-- Prove2me | Definitions.Def_RegExperiment_Regulation
-- name    : RegExperiment_Regulation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:45:32.671152+00:00
-- url     : https://prove2.me/theorems/48ce40d5-994f-49e4-a216-8d7d04a8ea1a
-- title:
--   First best, the firm's best reply, optimal mix of instruments and the critical externality $\hat e$
-- statement:
--   Fix an externality rate $e$ and a prior $\sigma_0$.
--
--   1. $(s^*,S^*)$ are **first-best standards** if for every prior $\sigma_0\in(s^*,S^*)$, experimenting between $s^*$ and $S^*$ and withdrawing at $z^*$ maximizes welfare $u^1_p(\sigma_0;s,S,z)$ over all standards $(s,S,z)$.
--   2. Given the planner's commitment to an adoption standard $S$, a withdrawal standard $z$ and a liability $L$, a rejection standard $s$ is a **best reply of the firm** if no $s'$ gives the firm a higher ex ante value $u^1_i(\sigma_0;s',S,z)$. The firm controls only rejection.
--   3. A mix $(S,z,L)$ with a reply $s$ is **feasible** if $0\le L\le \bar L(e)=v_i-v^B_p$ and $s$ is a best reply of the firm.
--   4. A feasible $(S,z,L,s)$ is an **optimal mix** if no feasible $(S',z',L',s')$ gives higher welfare at $\sigma_0$ (the planner picks the commitment and, among the firm's best replies, the one it prefers).
--   5. The **first best is achieved** at $(e,\sigma_0)$ if some feasible $(S,z,L,s)$ attains welfare at least $u^1_p(\sigma_0;s',S',z')$ for all standards $(s',S',z')$.
--   6. $\hat e$ is a **critical externality** for $(s^*,S^*)$ if $\hat e\in(0,1)$ and, for every prior $\sigma_0\in(s^*,S^*)$ and $e\in[0,1]$, under the commitment $(S^*,z^*,L=0)$: at $e=\hat e$, $s^*$ is a best reply of the firm; for $e<\hat e$ every best reply of the firm is below $s^*$; for $e>\hat e$ every best reply is above $s^*$.
--
--   These are the objects of Propositions 1 and 6.
--
--   **Formalization Note** Policies are threshold policies valued by the closed forms of the paper. The first-best predicate does not itself assert $s^*<S^*$. "Optimal mix" is a strong-Stackelberg optimum over $(S,z,L)$ and the firm's best reply $s$.
-- source:
--   Henry–Loseto–Ottaviani, working paper (Nov. 2018): Proposition 1, pp.8–9, and fn.17, p.10 (first best); §5, p.15, and §5.3, p.21 (instruments, firm controls rejection); Proof of Proposition 6, Step 1, p.42 (ê)

import Mathlib
import Definitions.Def_RegExperiment_ExAnte

namespace RegExperiment

/-- `(s*, S*)` are first-best ex ante standards (Proposition 1, pp.8–9, with fn.17, p.10):
for every prior `σ₀ ∈ (s*, S*)`, experimenting between `s*` and `S*` and withdrawing at `z*`
maximizes welfare over all rejection, adoption and withdrawal standards `(s, S, z)`.

**Formalization Note** Policies are the paper's threshold policies with values given by the
closed forms of p.10 and pp.33–34 (fn.17: "`(s*, S*)` solves `û¹_p(σ₀) ≡ max_{s,S} u¹_p(σ₀,s,S)`").
The predicate does not itself assert `s* < S*`. -/
def IsFirstBest (P : Params) (sS SS : ℝ) : Prop :=
  ∀ σ₀ ∈ Set.Ioo sS SS, ∀ s S z : ℝ, Wel P σ₀ s S z ≤ Wel P σ₀ sS SS (zstar P)

/-- `s` is a best reply of the firm, at externality `e` and prior `σ₀`, to the planner's
commitment to adoption standard `S`, withdrawal standard `z` and liability `L`: no rejection
standard `s'` gives the firm a higher ex ante value (§5, p.15, and §5.3, p.21: "the firm only
controls rejection `s_pp`"). -/
def FirmBR (P : Params) (e σ₀ S z L s : ℝ) : Prop :=
  ∀ s' : ℝ, U1 P (firmFlows P e L) σ₀ s' S z ≤ U1 P (firmFlows P e L) σ₀ s S z

/-- A feasible mix with the firm's reply: a liability rate in `[0, v_i − v^B_p]` (§5, p.15), any
adoption and withdrawal standards, and a best reply `s` of the firm. -/
def Feasible (P : Params) (e σ₀ S z L s : ℝ) : Prop :=
  0 ≤ L ∧ L ≤ Lbar P e ∧ FirmBR P e σ₀ S z L s

/-- `(S, z, L)` with the firm's reply `s` is a socially optimal mix of the three instruments
(§5.3, p.21): it is feasible and no feasible mix with any best reply of the firm gives higher
welfare at the prior `σ₀` (strong Stackelberg). -/
def IsOptimalMix (P : Params) (e σ₀ S z L s : ℝ) : Prop :=
  Feasible P e σ₀ S z L s ∧
    ∀ S' z' L' s' : ℝ, Feasible P e σ₀ S' z' L' s' → Wel P σ₀ s' S' z' ≤ Wel P σ₀ s S z

/-- The first best is achieved at externality `e` and prior `σ₀` (Proposition 6, p.21): some
feasible mix and best reply of the firm attain the maximal welfare over all standards
`(s, S, z)`. -/
def FirstBestAchieved (P : Params) (e σ₀ : ℝ) : Prop :=
  ∃ S z L s : ℝ, Feasible P e σ₀ S z L s ∧ ∀ s' S' z' : ℝ, Wel P σ₀ s' S' z' ≤ Wel P σ₀ s S z

/-- `ê` is the critical externality of Proof of Proposition 6, Step 1 (p.42), relative to
first-best standards `(s*, S*)`: `ê ∈ (0, 1)` and, for every prior `σ₀ ∈ (s*, S*)` and every
`e ∈ [0, 1]`, when the planner commits to `S = S*`, `z = z*` and no liability,
* at `e = ê` the first-best rejection standard `s*` is a best reply of the firm;
* below `ê` every best reply of the firm is below `s*` (excessive experimentation);
* above `ê` every best reply of the firm is above `s*` (insufficient experimentation). -/
def IsCriticalExternality (P : Params) (sS SS ê : ℝ) : Prop :=
  ê ∈ Set.Ioo (0 : ℝ) 1 ∧
    ∀ σ₀ ∈ Set.Ioo sS SS, ∀ e ∈ Set.Icc (0 : ℝ) 1,
      (e = ê → FirmBR P e σ₀ SS (zstar P) 0 sS) ∧
      ∀ s : ℝ, FirmBR P e σ₀ SS (zstar P) 0 s → (e < ê → s < sS) ∧ (ê < e → sS < s)

end RegExperiment


